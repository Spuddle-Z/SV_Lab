`timescale 1ns/1ps

package sequence_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  parameter  CTRL_ADDR = 32'h2000_0000;
  parameter  STAT_ADDR = 32'h2000_0008;
  parameter  TXDATA_ADDR = 32'h2000_0010;
  parameter  RXDATA_ADDR = 32'h2000_0018;
  parameter  BAUD_ADDR = 32'h2000_0020;

  // =========================================================
  // 事务类定义
  // =========================================================
  class spi_trans extends uvm_sequence_item;
    `uvm_object_utils(spi_trans)
    rand logic        read; // 0: write; 1: read
    rand logic [15:0] wdata;
    rand logic [31:0] rdata;
    rand logic [31:0] addr;
  endclass // spi_trans

  class uart_trans extends uvm_sequence_item;
    `uvm_object_utils(uart_trans)
    rand logic [7:0] data;
    bit is_tx;
  endclass // uart_trans


  // =========================================================
  // 序列类定义
  // =========================================================
  class spi_reg_sequence extends uvm_sequence #(spi_trans);
    `uvm_object_utils(spi_reg_sequence)

    function new(string name = "spi_reg_sequence");
      super.new(name);
    endfunction : new

    virtual task body();
      spi_trans tx;
      tx = new();

      #500;

      // 写波特率寄存器
      start_item(tx);
        tx.read = 0;
        tx.addr = BAUD_ADDR;
        tx.wdata = 16'h0036; // Set baud rate
      finish_item(tx);

      // 读波特率寄存器
      start_item(tx);
        tx.read = 1;
        tx.addr = BAUD_ADDR;
      finish_item(tx);

      // 写状态寄存器
      start_item(tx);
        tx.read = 0;
        tx.addr = STAT_ADDR;
        tx.wdata = 16'h0000; // Clear status
      finish_item(tx);

      // 读状态寄存器
      start_item(tx);
        tx.read = 1;
        tx.addr = STAT_ADDR;
      finish_item(tx);

      // 写控制寄存器，启用UART，启用Softmax
      start_item(tx);
        tx.read = 0;
        tx.addr = CTRL_ADDR;
        tx.wdata = 16'h0003;
      finish_item(tx);

      // 读控制寄存器
      start_item(tx);
        tx.read = 1;
        tx.addr = CTRL_ADDR;
      finish_item(tx);

      // 写TXDATA寄存器
      start_item(tx);
        tx.read = 0;
        tx.addr = TXDATA_ADDR;
        tx.wdata = 16'hABCD; // Example data
      finish_item(tx);

      // 读TXDATA寄存器
      start_item(tx);
        tx.read = 1;
        tx.addr = TXDATA_ADDR;
      finish_item(tx);

      // 写RXDATA寄存器
      start_item(tx);
        tx.read = 0;
        tx.addr = RXDATA_ADDR;
        tx.wdata = 16'h0000; // Dummy write
      finish_item(tx);

      // 读RXDATA寄存器
      start_item(tx);
        tx.read = 1;
        tx.addr = RXDATA_ADDR;
      finish_item(tx);
    endtask : body
  endclass : spi_reg_sequence

  class spi_data_sequence extends uvm_sequence #(spi_trans);
    `uvm_object_utils(spi_data_sequence)

    function new(string name = "spi_data_sequence");
      super.new(name);
    endfunction : new

    virtual task body();
      spi_trans tx;
      int batch_count;
      int tx_count;
      int rx_valid_count;

      // 先设置波特率与控制寄存器
      tx = spi_trans::type_id::create("baud_tx");
      start_item(tx);
        tx.read = 0; // write
        tx.addr = BAUD_ADDR;
        tx.wdata = 16'h0036; // Set baud rate 
      finish_item(tx);
      tx = spi_trans::type_id::create("ctrl_tx");
      start_item(tx);
        tx.read = 0; // write
        tx.addr = CTRL_ADDR;
        tx.wdata = 16'h0003; // Enable UART and Softmax
      finish_item(tx);

      // 固定 batch_count 为 2
      batch_count = 2;

      // 发送 8*batch_count 次随机数据到 TXDATA_ADDR
      for (tx_count = 0; tx_count < 8 * batch_count; tx_count++) begin
        tx = spi_trans::type_id::create("tx");
        start_item(tx);
          tx.read = 0; // write
          tx.addr = TXDATA_ADDR;
          tx.wdata = $urandom(); // 随机 16bit 数据
        finish_item(tx);
      end

      // 等待一段时间，确保数据被处理
      #3_000_000;

      // 持续读取 RXDATA_ADDR，直到收到 4*batch_count 次有效数据 (rdata != 0)
      rx_valid_count = 0;
      while (rx_valid_count < 4 * batch_count) begin
        tx = spi_trans::type_id::create("rx");
        start_item(tx);
          tx.read = 1; // read
          tx.addr = RXDATA_ADDR;
        finish_item(tx);

        // 检查 rdata 是否有效 (非零)
        if (tx.rdata != 0) begin
          rx_valid_count++;
        end
      end
    endtask : body
  endclass : spi_data_sequence

  class uart_sequence extends uvm_sequence #(uart_trans);
    `uvm_object_utils(uart_sequence)

    function new(string name = "uart_sequence");
      super.new(name);
    endfunction : new

    virtual task body();
      uart_trans rx_item;

      for (int i = 0; i < 32; i++) begin
        // 随机化一条 TX 事务并发送
        rx_item = uart_trans::type_id::create("rx_item");
        rx_item.randomize();
        rx_item.is_tx = 1'b0; // RX 事务

        start_item(rx_item);
        finish_item(rx_item);
      end
    endtask : body
  endclass : uart_sequence

endpackage