`timescale 1ns/1ns
`include "uvm_pkg.sv"
//`include "C:/questasim64_10.4c/verilog_src/uvm-1.2/src/uvm_pkg.sv"  //also ok by jiang
`include "../rtl/dut.sv"
`include "../rtl/dut_if.sv"
`include "my_sequence_pkg.sv"
`include "my_agent_pkg.sv"
`include "my_env_pkg.sv"
`include "my_test_pkg.sv"
module top;

  import uvm_pkg::*;
  import my_sequence_pkg::*;
  import my_agent_pkg::*;
  import my_env_pkg::*;
  import my_test_pkg::*;
  parameter NUM_ENV = 4;

  genvar i;

  generate
    for(i=0;i<NUM_ENV;i++) begin

      logic clock;
      initial begin
        clock = 0;
        forever #(5*(i+1)) clock = ~clock;
      end

      logic reset;
      initial begin
        reset = 1;
        repeat(3) @(negedge clock);
        reset = 0;
      end

      dut_if u_dut_if_i(clock, reset);
      dut_if u_dut_if_o(clock, reset);

      initial begin
        u_dut_if_i.cmd_valid = 0;
        u_dut_if_i.cmd = 0;
        u_dut_if_i.addr = 0;
        u_dut_if_i.data = 0;
      end

      dut #(.ID(i)) u_dut(.if_i(u_dut_if_i), .if_o(u_dut_if_o));

      initial begin
        uvm_config_db #(virtual dut_if)::set(null, "uvm_test_top", $sformatf("dut_vif_i%1d", i), u_dut_if_i);
        uvm_config_db #(virtual dut_if)::set(null, "uvm_test_top", $sformatf("dut_vif_o%1d", i), u_dut_if_o);
      end

    end //for
  endgenerate

  initial begin
    run_test();
  end

endmodule : top
