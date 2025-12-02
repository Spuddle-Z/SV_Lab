/* 
  ### 波特率发生器测试平台
*/
`timescale 1ns/1ps

module tb_baud_gen();
  // 参数定义
  parameter CLK_PERIOD = 20; // 50 MHz 时钟周期 (单位: ns)
  parameter BAUD_RATE = 115200; // 波特率 (单位: bps)
  parameter SAMPLE_RATE = 16; // 采样率
  parameter BAUD_DIVISOR = 1e9 / (CLK_PERIOD * BAUD_RATE * SAMPLE_RATE); // 波特率分频系数

  // 信号声明
  logic clk;
  logic rst_n;
  logic [15:0] baud_divisor;
  logic baud_tick;

  // 实例化波特率发生器
  baud_gen u_baud_gen (
    .clk(clk),
    .rst_n(rst_n),
    .baud_divisor(baud_divisor),
    .baud_tick(baud_tick)
  );

  // 时钟生成
  always #(CLK_PERIOD/2) clk = ~clk;

  // 主测试流程
  initial begin
    // 信号初始化
    clk = 0;
    rst_n = 0;
    baud_divisor = BAUD_DIVISOR;
    #100;

    // Test 1: 复位测试
    test_1();
    $stop;
  end

  /*
    ===== 测试用例 1 =====
    仿真开始时处于复位状态，保持一段时间后释放复位信号，观察是否正常工作
  */
  task test_1;
    rst_n = 0;
    #100;
    rst_n = 1;
    #10000;
  endtask

endmodule