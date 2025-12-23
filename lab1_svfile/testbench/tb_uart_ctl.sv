`timescale 1ns/1ps

module tb_uart_ctl;

  // 参数定义
  localparam CLK_PERIOD = 20;  // 50MHz时钟
  localparam BAUD_RATE = 115200;
  localparam SAMPLE_RATE = 16;
  localparam [15:0] BAUD_DIVISOR = 1e9 / (BAUD_RATE * SAMPLE_RATE * CLK_PERIOD);

  // 信号声明
  logic clk, rst_n;
  
  // TX FIFO 接口
  logic [15:0] input_data;
  logic push_en;
  logic [15:0] tx_data;
  logic tx_empty;
  logic tx_fifo_en;
  
  // RX FIFO 接口
  logic [15:0] output_data;
  logic pop_en;
  logic [15:0] rx_data;
  logic rx_full;
  logic rx_fifo_en;

  // 状态输出
  logic [15:0] baud_divisor = BAUD_DIVISOR;
  logic [2:0] uart_state;

  // UART 物理接口
  logic tx;
  logic rx;

  // 实例化 DUT
  uart_ctl dut (
    .clk(clk),
    .rst_n(rst_n),
    .baud_divisor(baud_divisor),
    .state(uart_state),
    .tx(tx),
    .rx(rx),
    .tx_data(tx_data),
    .tx_empty(tx_empty),
    .tx_fifo_en(tx_fifo_en),
    .rx_data(rx_data),
    .rx_full(rx_full),
    .rx_fifo_en(rx_fifo_en)
  );

  // 实例化 FIFO
  fifo tx_fifo (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),
    .empty(tx_empty),
    .full(),
    .rd_data(tx_data),
    .rd_en(tx_fifo_en),
    .wr_data(input_data),
    .wr_en(push_en)
  );

  fifo rx_fifo (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),
    .empty(),
    .full(rx_full),
    .rd_data(output_data),
    .rd_en(pop_en),
    .wr_data(rx_data),
    .wr_en(rx_fifo_en)
  );

  // 时钟生成
  always #(CLK_PERIOD/2) clk = ~clk;

  // 回环连接
  assign rx = tx;

  // 持续检查rx_fifo
  always @(posedge clk) begin
      pop_en = ~pop_en;
  end

  // 复位任务
  task reset_dut;
    $display("Applying reset...");
    rst_n = 0;
    #(CLK_PERIOD);
    rst_n = 1;
    #(CLK_PERIOD * 2);
  endtask

  // 压入初始数据
  task send_data;
    @(posedge clk);
    for (int i = 0; i < 4; i++) begin
      input_data = 16'hA500 + i;
      push_en = 1;
      @(posedge clk);
      push_en = 0;
    end
  endtask

  initial begin
    clk = 0;
    pop_en = 0;
    rst_n = 1;
    reset_dut();
    send_data();
    #(CLK_PERIOD * 50000);
    $stop;
  end

endmodule
