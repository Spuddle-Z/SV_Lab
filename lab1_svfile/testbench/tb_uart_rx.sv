`timescale 1ns/1ps

module tb_uart_rx;

  // 参数定义
  localparam CLK_PERIOD = 20;  // 50MHz时钟
  localparam BAUD_RATE = 115200;
  localparam SAMPLE_RATE = 16;
  localparam [15:0] BAUD_DIVISOR = 1e9 / (BAUD_RATE * SAMPLE_RATE * CLK_PERIOD);

  // 定义测试平台信号
  logic clk, rst_n, baud_tick;
  logic [7:0] tx_data, rx_data;
  logic tx_valid, tx_busy, rx_done;
  logic tx_to_rx;
  
  // 实例化相关模块
  baud_gen baud_generator (
  .clk(clk),
  .rst_n(rst_n),
  .baud_divisor(BAUD_DIVISOR),
  .baud_tick(baud_tick)
  );

  uart_tx u_uart_tx (
    .clk(clk),
    .rst_n(rst_n),
    .tx(tx_to_rx),
    .tx_valid(tx_valid),
    .tx_busy(tx_busy),
    .tx_data(tx_data),
    .baud_tick(baud_tick)
  );

  // 实例化被测试模块
  uart_rx dut (
    .clk(clk),
    .rst_n(rst_n),
    .rx(tx_to_rx),
    .rx_done(rx_done),
    .rx_data(rx_data),
    .baud_tick(baud_tick)
  );

  // 时钟生成
  always #(CLK_PERIOD/2) clk = ~clk;

  // 复位任务
  task reset_dut;
    begin
      $display("Applying reset...");
      rst_n = 0;
      #(CLK_PERIOD * 2);
      rst_n = 1;
      #(CLK_PERIOD * 10);
    end
  endtask

  task loop_data(input logic [7:0] data);
    tx_data = data;
    tx_valid = 1;
    @(posedge clk);
    tx_valid = 0;

    wait(rx_done);
    if (rx_data == data) begin
      $display("[TB] PASS: Received correct data 0x%h", rx_data);
    end else begin
      $display("[TB] FAIL: Expected 0x%h, got 0x%h", data, rx_data);
    end
    wait(!tx_busy);
  endtask

  // 主测试序列
  initial begin
    clk = 0;
    reset_dut();
    
    loop_data(8'hA5);
    loop_data(8'h3C);
    loop_data(8'h00);
    loop_data(8'hFF);
    
    // 测试完成
    $display("=== All tests completed ===");
    $finish;
  end

endmodule
