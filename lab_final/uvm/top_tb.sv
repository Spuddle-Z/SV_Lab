`timescale 1ns/1ps

import sequence_pkg::*;
import spi_agent_pkg::*;
import uart_agent_pkg::*;
import scoreboard_pkg::*;
import env_pkg::*;
import test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module testbench_top();

//=====================================================================
// Parameters
//=====================================================================

  parameter CLK_PERIOD = 10;

//=====================================================================
// Signals Declaration
//=====================================================================

  // uninterface signals 
  logic clk  ;
  logic rst_n;

  // interface signals
  spi_bus   spi(.*);
  uart_bus  uart(.*);

  // Signals for binding
  logic [1:0] tx_state;
  logic [1:0] rx_state;
  logic baud_tick;

  // FIFO signals
  logic tx_fifo_rst_n, tx_fifo_rd_clk, tx_fifo_wr_clk, tx_fifo_empty, tx_fifo_full, tx_fifo_wr_en, tx_fifo_rd_en;
  logic [3:0] tx_fifo_rd_ptr, tx_fifo_wr_ptr;

  logic rx_fifo_rst_n, rx_fifo_rd_clk, rx_fifo_wr_clk, rx_fifo_empty, rx_fifo_full, rx_fifo_wr_en, rx_fifo_rd_en;
  logic [3:0] rx_fifo_rd_ptr, rx_fifo_wr_ptr;

//=====================================================================
// Signals' Function
//=====================================================================
  
  initial begin 
    clk  = 0 ;
    forever #(CLK_PERIOD /2) clk = ~clk;
  end

  initial begin
    rst_n   = 0;
    repeat(10) @(posedge clk) ;
    rst_n   = 1;
  end

  dut_top i_dut(
    .spi_bus(spi),
    .uart_bus(uart)
  );

  // Assignments for binding
  assign tx_state = i_dut.uart_ctl_inst.state[3:2];
  assign rx_state = i_dut.uart_ctl_inst.state[1:0];
  assign baud_tick = i_dut.uart_ctl_inst.baud_tick;

  assign tx_fifo_rst_n = i_dut.tx_fifo_inst.rst_n;
  assign tx_fifo_rd_clk = i_dut.tx_fifo_inst.rd_clk;
  assign tx_fifo_wr_clk = i_dut.tx_fifo_inst.wr_clk;
  assign tx_fifo_empty = i_dut.tx_fifo_inst.empty;
  assign tx_fifo_full = i_dut.tx_fifo_inst.full;
  assign tx_fifo_wr_en = i_dut.tx_fifo_inst.wr_en;
  assign tx_fifo_rd_en = i_dut.tx_fifo_inst.rd_en;
  assign tx_fifo_rd_ptr = i_dut.tx_fifo_inst.rd_ptr;
  assign tx_fifo_wr_ptr = i_dut.tx_fifo_inst.wr_ptr;

  assign rx_fifo_rst_n = i_dut.rx_fifo_inst.rst_n;
  assign rx_fifo_rd_clk = i_dut.rx_fifo_inst.rd_clk;
  assign rx_fifo_wr_clk = i_dut.rx_fifo_inst.wr_clk;
  assign rx_fifo_empty = i_dut.rx_fifo_inst.empty;
  assign rx_fifo_full = i_dut.rx_fifo_inst.full;
  assign rx_fifo_wr_en = i_dut.rx_fifo_inst.wr_en;
  assign rx_fifo_rd_en = i_dut.rx_fifo_inst.rd_en;
  assign rx_fifo_rd_ptr = i_dut.rx_fifo_inst.rd_ptr;
  assign rx_fifo_wr_ptr = i_dut.rx_fifo_inst.wr_ptr;

  binding_module i_binding_module();

  initial begin
    uvm_config_db#(virtual spi_bus.master)::set(null, "uvm_test_top.env.spi_agt.driver", "vif", spi);
    uvm_config_db#(virtual spi_bus.monitor)::set(null, "uvm_test_top.env.spi_agt.monitor", "vif", spi);
    uvm_config_db#(virtual uart_bus.slave)::set(null, "uvm_test_top.env.uart_agt.driver", "vif", uart);
    uvm_config_db#(virtual uart_bus.master)::set(null, "uvm_test_top.env.uart_agt.monitor", "vif", uart);
  end

  initial begin
    run_test("my_test");
  end

endmodule