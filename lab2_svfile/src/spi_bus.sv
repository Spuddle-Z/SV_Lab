//===================================================================== 
/// Description: 
// the interface of spi
// Designer : wangziyao1@sjtu.edu.cn
// Revision History
// V0 date: 2025/10/23  Initial version wangziyao1@sjtu.edu.cn
// V1 date: 2025/11/01  Add clocking blocks zzz-jy@sjtu.edu.cn
// ==================================================================== 

/*
This is only the basic interface, you may change it by your own.
But don't change this signal discription.
*/
`timescale 1ns/1ps

interface spi_bus(input logic clk,input logic rst_n);

// Signal Definition
// =======================================
  logic cs_n;
  logic sck;
  logic mosi;
  logic miso;

// Clocking blocks
// =======================================
  clocking mst_cb @(posedge clk);
    default input #0.25 output #0.25;
    output cs_n, sck, mosi;
    input miso;
  endclocking

  clocking mnt_cb @(posedge clk);
    default input #0.25 output #0.25;
    input cs_n, sck, mosi, miso;
  endclocking

// Mod ports
// =======================================

  modport slave(
    input clk, rst_n, cs_n, sck, mosi,
    output miso
  );
  
  modport master(
    input clk, rst_n,
    clocking mst_cb
  );

  modport monitor(
    input clk, rst_n,
    clocking mnt_cb
  )

endinterface:spi_bus //spi