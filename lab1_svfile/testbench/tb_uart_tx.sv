`timescale 1ns/1ps

module tb_uart_tx;

  // 参数定义
  localparam CLK_PERIOD = 20;  // 50MHz时钟
  localparam BAUD_RATE = 115200;
  localparam SAMPLE_RATE = 16;
  localparam [15:0] BAUD_DIVISOR = 1e9 / (BAUD_RATE * SAMPLE_RATE * CLK_PERIOD);

  // 信号声明
  logic clk;
  logic rst_n;
  logic tx_valid;
  logic [7:0] tx_data;
  logic tx;
  logic tx_busy;
  logic baud_tick;

  // 实例化DUT
  uart_tx dut (
    .clk(clk),
    .rst_n(rst_n),
    .tx_valid(tx_valid),
    .tx_data(tx_data),
    .tx(tx),
    .tx_busy(tx_busy),
    .baud_tick(baud_tick)
  );

  baud_gen baud_generator (
    .clk(clk),
    .rst_n(rst_n),
    .baud_divisor(BAUD_DIVISOR),
    .baud_tick(baud_tick)
  );

  // 时钟生成
  always #(CLK_PERIOD/2) clk = ~clk;

  // 复位任务
  task reset_dut;
    $display("Applying reset...");
    rst_n = 0;
    #(CLK_PERIOD * 2);
    rst_n = 1;
    #(CLK_PERIOD * 10);
  endtask

  // 发送任务
  task send_data(input logic [7:0] data);
    tx_data = data;
    @(posedge clk);
    tx_valid = 1;
    @(posedge clk);
    tx_valid = 0;
  endtask

  // 检查UART帧
  task check_uart_frame(input logic [7:0] expected_data);
    automatic int bit_count = 0;
    automatic logic [7:0] received_data = 8'b0;

    // 等待起始位
    wait(tx == 0);
    $display("[%0t] Start bit detected", $time);
    
    // 等待到数据位中间采样（第8个baud_tick）
    repeat(SAMPLE_RATE/2) @(posedge baud_tick);
    
    // 采样8个数据位
    for (int i = 0; i < 8; i++) begin
      repeat(SAMPLE_RATE) @(posedge baud_tick); // 等待一个完整的位时间
      received_data[i] = tx;
      $display("[%0t] Sample bit %d: %b", $time, i, tx);
    end
    
    // 检查停止位
    repeat(SAMPLE_RATE) @(posedge baud_tick);
    if (tx !== 1'b1) begin
      $error("[%0t] Stop bit error, expected 1, got %b", $time, tx);
    end else begin
      $display("[%0t] Stop bit correct", $time);
    end
    
    // 验证数据
    if (received_data !== expected_data) begin
      $error( "[%0t] Data mismatch! Expected: 8'h%02h, Actual: 8'h%02h", $time, expected_data, received_data);
    end else begin
      $display("[%0t] Data verification successful: 8'h%02h", $time, received_data);
    end
  endtask

  // 测试 1: 发送 8'ha5
  task test_1;
    $display("\n=== Test 1: Send 8'ha5 ===");
    fork
      send_data(8'ha5);
      check_uart_frame(8'ha5);
    join
  endtask

  // 测试 2: 连续发送
  task test_2;
    $display("\n=== Test 2: Continuous Send Test ===");
    for (int i = 0; i < 3; i++) begin
      fork
        send_data(8'h30 + i);
        check_uart_frame(8'h30 + i);
      join
      wait(tx_busy == 0);
    end
  endtask

  // 主测试序列
  initial begin
    // 初始化
    clk = 0;
    rst_n = 0;
    tx_valid = 0;
    tx_data = 8'h00;
    
    // 复位
    reset_dut();
    
    // 测试1: 发送 8'ha5
    test_1();
    reset_dut();
    
    // 测试 2: 连续发送
    test_2();
    reset_dut();

    $display("\n=== All tests completed ===");
    $finish;
  end

endmodule
