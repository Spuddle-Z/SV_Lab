//===================================================================== 
/// Description: 
// this is the top file of our dut, this module should never be changed
// Designer : wangziyao1@sjtu.edu.cn
// ==================================================================== 
/* don't change the signal */
module dut_top(
  //input bus
  spi_bus.slave spi_bus,

  //ouput bus
  uart_bus.master uart_bus
);

  // ============================================================================
  // 信号定义
  // ============================================================================
  logic        clk;
  logic        rst_n;

  // SPI引脚
  logic        sck;      // SPI时钟
  logic        cs_n;     // SPI片选
  logic        mosi;     // 主设备输出，从设备输入
  logic        miso;     // 主设备输入，从设备输出

  // UART引脚
  logic        uart_tx;  // UART发送数据
  logic        uart_rx;  // UART接收数据

  // FIFO接口
  logic [15:0] tx_fifo_wr;
  logic [15:0] tx_fifo_rd;
  logic        tx_fifo_full;
  logic        tx_fifo_empty;
  logic        tx_fifo_wr_en;
  logic        tx_fifo_rd_en;
  logic [15:0] rx_fifo_wr;
  logic [15:0] rx_fifo_rd;
  logic        rx_fifo_full;
  logic        rx_fifo_empty;
  logic        rx_fifo_wr_en;
  logic        rx_fifo_rd_en;

  // Softmax接口
  logic        softmax_valid;
  logic        softmax_done;
  logic [127:0] softmax_packet;
  logic        softmax_en;

  // 控制信号
  logic [3:0]  state;
  logic [1:0]  control;
  logic [15:0] baud;

  assign softmax_en = control[1];

  // ============================================================================
  // 引脚连接
  // ============================================================================
  assign clk      = spi_bus.clk;
  assign rst_n    = spi_bus.rst_n;

  assign sck      = spi_bus.sck;
  assign cs_n     = spi_bus.cs_n;
  assign mosi     = spi_bus.mosi;
  assign spi_bus.miso = miso;

  assign uart_bus.tx = uart_tx;
  assign uart_rx     = uart_bus.rx;

  // ============================================================================
  // DUT实例化
  // ============================================================================
  // SPI CTL
  spi_ctl spi_ctl_inst (
    .clk(clk),
    .rst_n(rst_n),

    .sck(sck),
    .cs_n(cs_n),
    .mosi(mosi),
    .miso(miso),

    .tx_fifo_data(tx_fifo_wr),
    .tx_fifo_full(tx_fifo_full),
    .tx_fifo_en(tx_fifo_wr_en),
    .rx_fifo_data(rx_fifo_rd),
    .rx_fifo_empty(rx_fifo_empty),
    .rx_fifo_en(rx_fifo_rd_en),

    .state(state),
    .control(control),
    .baud(baud)
  );

  // Softmax
  softmax_top softmax_top_inst (
    .clk(clk),
    .rst_n(rst_n),
    .softmax_en(softmax_en),
    .empty(tx_fifo_empty),
    .data_in(tx_fifo_rd),
    .rd_en(tx_fifo_rd_en),
    .done(softmax_done),
    .valid(softmax_valid),
    .data_out(softmax_packet)
  );

  // UART CTL
  uart_ctl uart_ctl_inst (
    .clk(clk),
    .rst_n(rst_n),

    .tx(uart_tx),
    .rx(uart_rx),
    .tx_data(softmax_packet),
    .data_valid(softmax_valid & control[0]),
    .tx_done(softmax_done),
    .rx_data(rx_fifo_wr),
    .rx_full(rx_fifo_full),
    .rx_fifo_en(rx_fifo_wr_en),
    .baud_divisor(baud),
    .state(state)
  );

  // TX FIFO
  fifo tx_fifo_inst (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),

    .empty(tx_fifo_empty),
    .full(tx_fifo_full),
    .rd_data(tx_fifo_rd),
    .rd_en(tx_fifo_rd_en),
    .wr_data(tx_fifo_wr),
    .wr_en(tx_fifo_wr_en)
  );

  // RX FIFO
  fifo rx_fifo_inst (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),

    .empty(rx_fifo_empty),
    .full(rx_fifo_full),
    .rd_data(rx_fifo_rd),
    .rd_en(rx_fifo_rd_en),
    .wr_data(rx_fifo_wr),
    .wr_en(rx_fifo_wr_en)
  );

endmodule