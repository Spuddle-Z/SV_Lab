module spi_slave (
  // --- SPI 引脚（模式 0，低位先行）
  input  logic        sck,     // SPI 时钟
  input  logic        cs_n,    // SPI 片选
  input  logic        mosi,    // 主设备输出，从设备输入
  output logic        miso,    // 主设备输入，从设备输出

  // --- 系统时钟与复位
  input  logic        clk,     // 系统时钟
  input  logic        rst_n,   // 低有效复位

  // --- 数据与控制接口
  input  logic [31:0] tx_data,
  input  logic        tx_valid,

  output logic [31:0] rx_data,
  output logic        rx_done
);

// ============================================================================
// 同步外部与本地时钟域
// ============================================================================
logic [2:0] sck_sync, cs_n_sync, mosi_sync;
logic sck_synced, cs_n_synced, mosi_synced;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    sck_sync <= 3'b0;
    cs_n_sync  <= 3'b111;
    mosi_sync <= 3'bzzz;
  end else begin
    sck_sync <= {sck_sync[1:0], sck};
    cs_n_sync  <= {cs_n_sync[1:0], cs_n};
    mosi_sync <= {mosi_sync[1:0], mosi};
  end
end

assign sck_synced = sck_sync[2];
assign cs_n_synced  = cs_n_sync[2];
assign mosi_synced = mosi_sync[2];

// ============================================================================
// 边沿检测
// ============================================================================
logic sck_prev, sample_edge, shift_edge;
logic cs_n_prev, start_edge, stop_edge;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    sck_prev <= 1'b0;
    cs_n_prev <= 1'b1;
  end else begin
    sck_prev <= sck_synced;
    cs_n_prev <= cs_n_synced;
  end
end

assign sample_edge = sck_synced && !sck_prev;
assign shift_edge = !sck_synced && sck_prev;
assign start_edge = !cs_n_synced && cs_n_prev;
assign stop_edge = cs_n_synced && !cs_n_prev;

// ============================================================================
// 移位寄存器
// ============================================================================
logic [31:0] tx_shift_reg;
logic tx_en;

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    tx_shift_reg <= 32'b0;
    tx_en <= 1'b0;
  end else begin
    if (start_edge && tx_valid) begin
      tx_shift_reg <= tx_data;
      tx_en <= 1'b1;
    end else if (sample_edge) begin
      rx_data <= {mosi_synced, rx_data[31:1]};
    end else if (shift_edge) begin
      tx_shift_reg <= {1'b0, tx_shift_reg[31:1]};
    end else if (stop_edge) begin
      tx_en <= 1'b0;
    end
  end
end

assign rx_done = stop_edge;
assign miso= tx_en ? tx_shift_reg[0] : 1'bz;

endmodule
