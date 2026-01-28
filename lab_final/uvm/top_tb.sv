`timescale 1ns/1ps

import spi_agent_pkg::*;
import uart_agent_pkg::*;
import sequence_pkg::*;
import env_pkg::*;
import scoreboard_pkg::*;
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