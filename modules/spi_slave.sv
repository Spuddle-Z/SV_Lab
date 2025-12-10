module spi_slave (
  // --- SPI 引脚（模式 0，低位先行）
  input  logic        sck,     // SPI 时钟（CLK）
  input  logic        ss_n,    // 片选，低有效
  input  logic        mosi,    // 主机输出，从机输入
  output logic        miso,    // 从机输出，主机输入

  // --- 系统时钟与复位
  input  logic        clk,     // 系统时钟
  input  logic        rst_n,   // 低有效复位

  // --- 数据与控制接口
  input  logic [31:0] tx_data,
  input  logic        tx_valid,

  output logic [31:0] rx_data,
  output logic        rx_valid,
);

// ============================================================================
// 同步外部与本地时钟域
// ============================================================================
logic [2:0] sck_sync, ss_n_sync, mosi_sync;
logic sck_synced, ss_n_synced, mosi_synced;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    sck_sync <= 3'b0;
    ss_n_sync  <= 3'b111;
    mosi_sync <= 3'bzzz;
  end else begin
    sck_sync <= {sck_sync[1:0], sck};
    ss_n_sync  <= {ss_n_sync[1:0], ss_n};
    mosi_sync <= {mosi_sync[1:0], mosi};
  end
end

assign sck_synced = sck_sync[2];
assign ss_n_synced  = ss_n_sync[2];
assign mosi_synced = mosi_sync[2];

// ============================================================================
// 边沿检测
// ============================================================================
logic sck_prev, sample_edge, shift_edge;
logic ss_n_prev, start_edge, stop_edge;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    sck_prev <= 1'b0;
    ss_n_prev <= 1'b1;
  end else begin
    sck_prev <= sck_synced;
    ss_n_prev <= ss_n_synced;
  end
end

assign sample_edge = sck_synced && !sck_prev;
assign shift_edge = !sck_synced && sck_prev;
assign start_edge = ss_n_prev && !ss_n_synced;
assign stop_edge = !ss_n_prev && ss_n_synced;

// ============================================================================
// 移位寄存器与位计数器
// ============================================================================
logic [31:0] shift_reg;
logic [4:0] bit_counter;

// 移位寄存器：采样 MOSI（上升沿），移位输出 MISO（下降沿）
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    shift_reg <= 32'b0;
    bit_counter <= 5'b0;
  end else if (start_edge) begin
    shift_reg <= tx_data;
    bit_counter <= 5'b0;
  end else if (!ss_n_synced && sample_edge) begin
    // 在片选期间的上升沿采样 MOSI，低位优先左移
    shift_reg <= {mosi_synced, shift_reg[31:1]};
    if (bit_counter == 5'd31) begin
      bit_counter <= 5'b0;
    end else begin
      bit_counter <= bit_counter + 5'd1;
    end
  end
end

// 接收数据：去掉接收缓冲，直接在片选上升时把移位寄存器数据作为接收数据输出
assign rx_data = shift_reg;
assign rx_valid = ss_n_rising && (bit_counter != 5'b0);

// ============================================================================
// MISO 三态输出（低位优先，下降沿出数据）
// ============================================================================
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    miso <= 1'bz;
  end else begin
    if (ss_n_synced) begin
      // 片选未选中，高阻态
      miso <= 1'bz;
    end else if (shift_edge) begin
      // 下降沿输出最低位
      miso <= shift_reg[0];
    end
  end
end

endmodule
