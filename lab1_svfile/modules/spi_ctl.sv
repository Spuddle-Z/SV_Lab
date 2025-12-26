`timescale 1ns/1ps

module spi_ctl (
  input  logic        clk,
  input  logic        rst_n,

  // SPI引脚
  input  logic        sck,      // SPI时钟
  input  logic        cs_n,     // SPI片选
  input  logic        mosi,     // 主设备输出，从设备输入
  output logic        miso,     // 主设备输入，从设备输出

  // TX FIFO接口
  output logic [15:0] tx_fifo_data,
  input  logic        tx_fifo_full,
  output logic        tx_fifo_en,

  // RX FIFO接口
  input  logic [15:0] rx_fifo_data,
  input  logic        rx_fifo_empty,
  output logic        rx_fifo_en,
  
  // UART控制信号
  output logic [3:0]  state,
  output logic [15:0] baud
);

  // ============================================================================
  // 信号定义
  // ============================================================================
  // SPI与控制寄存器接口
  logic [31:0] spi_rx_data;
  logic        spi_rx_done;
  logic [31:0] spi_tx_data;
  logic        rx_reg_valid;

  // 控制寄存器与req接口
  logic [31:0] reg_data;
  logic        reg_req;
  logic        reg_ready;

  // ============================================================================
  // DUT实例化
  // ============================================================================
  spi_slave spi_slave_inst (
    .sck(sck),
    .cs_n(cs_n),
    .mosi(mosi),
    .miso(miso),

    .clk(clk),
    .rst_n(rst_n),

    .rx_data(spi_rx_data),
    .rx_done(spi_rx_done),
    .tx_data(spi_tx_data),
    .tx_valid(rx_reg_valid)
  );

  ctrl_reg dut (
    .clk(clk),
    .rst_n(rst_n),

    .spi_rx_data(spi_rx_data),
    .spi_rx_done(spi_rx_done),
    .spi_tx_data(spi_tx_data),
    .rx_reg_valid(rx_reg_valid),

    .tx_fifo_data(tx_fifo_data),
    .tx_fifo_full(tx_fifo_full),
    .tx_fifo_en(tx_fifo_en),
    .rx_fifo_data(reg_data),
    .rx_fifo_en(reg_req),
    .rx_fifo_ready(reg_ready),

    .state(state),
    .baud(baud)
  );

  rx_fifo_req rx_fifo_req_inst (
    .clk(clk),
    .rst_n(rst_n),

    .rx_fifo_data(rx_fifo_data),
    .rx_fifo_empty(rx_fifo_empty),
    .rx_fifo_en(rx_fifo_en),

    .reg_req(reg_req),
    .reg_data(reg_data),
    .reg_ready(reg_ready)
  );

endmodule