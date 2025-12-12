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
  output logic        tx_ready,

  output logic [31:0] rx_data,
  output logic        rx_done,
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
assign start_edge = !ss_n_synced && ss_n_prev;
assign stop_edge = ss_n_synced && !ss_n_prev;

// ============================================================================
// 移位寄存器
// ============================================================================
logic [31:0] tx_shift_reg;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    tx_shift_reg <= 32'bz;
    rx_shift_reg <= 32'b0;
    tx_ready <= 1'b0;
  end else if (start_edge && tx_valid) begin
    tx_shift_reg <= tx_data;
    tx_ready <= 1'b1;
  end else if (sample_edge) begin
    rx_data <= {mosi_synced, rx_data[31:1]};
  end else if (shift_edge) begin
    tx_shift_reg <= {1'bz, tx_shift_reg[31:1]};
  end
end

assign rx_done = stop_edge;
assign miso = tx_shift_reg[0];

endmodule
