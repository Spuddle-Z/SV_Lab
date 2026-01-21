//===================================================================== 
/// Description: 
// the interface of uart
// Designer : wangziyao1@sjtu.edu.cn
// ==================================================================== 

/*
This is only the basic interface, you may change it by your own.
But don't change this signal description.
*/
`timescale 1ns/1ps

interface uart_bus(input logic clk,input logic rst_n);
  // Signal Definition
  // =======================================
  logic tx;
  logic rx;

  // Mod ports
  // =======================================
  modport master(
    input rx, clk, rst_n,
    output tx
  );
  modport slave(
    input clk, rst_n,
    clocking slv_cb
  );
  modport monitor(
    input clk, rst_n, tx, rx,
    clocking mnt_cb
  );

  // Clocking blocks
  // =======================================
  clocking slv_cb @(posedge clk);
    default input #1 output #1;
    input tx;
    output rx;
  endclocking

  clocking mnt_cb @(posedge clk);
    default input #1 output #1;
    input tx, rx;
  endclocking

endinterface:uart_bus //uart  