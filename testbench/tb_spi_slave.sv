`timescale 1ns/1ps

module tb_spi_slave;
  // ============================================================================
  // 1. 信号定义
  // ============================================================================
  // 参数定义
  localparam CLK_PERIOD = 20;  // 50MHz时钟

  // SPI 接口
  spi_bus.slave slave_if;
  
  // 系统接口
  logic        clk;      // 系统时钟
  logic        rst_n;    // 复位，低有效
  
  // 数据接口
  logic [31:0] tx_data;  // 发送数据
  logic        tx_valid; // 发送有效
  logic        tx_ready; // 发送准备好
  logic [31:0] rx_data;  // 接收数据
  logic        rx_done;  // 接收完成
  
  // ============================================================================
  // 2. DUT 实例化
  // ============================================================================
  spi_slave dut (
    .slave_if(slave_if),
    .clk(clk),
    .rst_n(rst_n),
    .tx_data(tx_data),
    .tx_valid(tx_valid),
    .tx_ready(tx_ready),
    .rx_data(rx_data),
    .rx_done(rx_done)
  );
  
  // ============================================================================
  // 3. 时钟生成
  // ============================================================================
  // 时钟生成
  always #(CLK_PERIOD / 2) clk = ~clk;
  
  // SPI 时钟生成 (5MHz)
  task generate_sck;
    begin
      for (int i = 0; i < 32; i++) begin
        slave_if.sck = 1'b1;
        #(CLK_PERIOD * 5);
        slave_if.sck = 1'b0;
        #(CLK_PERIOD * 5);
      end
    end
  endtask
  
  // ============================================================================
  // 4. 复位生成
  // ============================================================================
  initial begin
    rst_n = 1'b0;
    #(CLK_PERIOD * 5);
    rst_n = 1'b1;
  end
  
  // ============================================================================
  // 5. SPI 主设备发送任务
  // ============================================================================
  task spi_master_send(logic [31:0] data);
    begin
      // 设置片选有效（开始传输）
      slave_if.ss_n = 1'b0;
      #(CLK_PERIOD * 2);
      
      fork
        generate_sck();
        begin
          // 逐位发送数据（32位）
          for (int i = 0; i < 32; i++) begin
            // 在SCK下降沿（模式0的数据变化沿）改变slave_if.MOSI
            slave_if.mosi = data[i];
            wait(slave_if.sck == 1'b0);
          end
        end
      join
      
      slave_if.ss_n = 1'b1;
      slave_if.mosi = 1'bz;
    end
  endtask
  
  // ============================================================================
  // 6. 测试用例任务
  // ============================================================================
  // 测试用例1：基本功能测试
  task test_case_1;
    begin
      // 设置测试数据
      tx_data = 32'hA5A5A5A5;        // 从机要发送的数据
      tx_valid = 1'b1;               // 发送数据有效
      
      // 执行SPI传输
      spi_master_send(32'h5A5A5A5A);
      
      // 等待接收完成
      wait(rx_done == 1'b1);
      #(CLK_PERIOD * 5);
    end
  endtask
  
  // 测试用例2：连续传输测试
  task test_case_2;
    begin
      tx_data = 32'h12345678;
      tx_valid = 1'b1;
      
      spi_master_send(tx_data);
      wait(rx_done == 1'b1);
      
      #(CLK_PERIOD);
      tx_data = 32'hDEADBEEF;
      tx_valid = 1'b1;
      
      spi_master_send(tx_data);
      wait(rx_done == 1'b1);
      
      #(CLK_PERIOD);
    end
  endtask
  
  // ============================================================================
  // 7. 主测试流程
  // ============================================================================
  initial begin
    // 初始化所有信号
    slave_if.sck = 1'b0;
    slave_if.ss_n = 1'b1;
    slave_if.mosi = 1'bz;
    tx_data = 32'h0;
    tx_valid = 1'b0;
    
    // 等待复位完成
    wait(rst_n == 1'b1);
    #100;
    
    // 执行测试用例
    test_case_1();
    test_case_2();
    
    // 测试完成
    #1000;
    $finish;
  end

endmodule
