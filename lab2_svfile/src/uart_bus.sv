//===================================================================== 
/// Description: 
// the interface of uart
// Designer : wangziyao1@sjtu.edu.cn
// ==================================================================== 

/*
This is only the basic interface, you may change it by your own.
But don't change this signal description.
*/
interface uart_bus(input logic clk,input logic rst_n);
  // Signal Definition
  // =======================================
  logic tx;
  logic rx;

  // Clocking blocks
  // =======================================
  clocking mst_cb @(posedge clk);
    default input #0.25 output #0.25;
    output tx;
    input rx;
  endclocking

  clocking mnt_cb @(posedge clk);
    default input #0.25 output #0.25;
    input tx, rx;
  endclocking

  // Mod ports
  // =======================================
  modport master(
    output clk,rst_n,
    clocking mst_cb
  );
  modport slave(input tx,rx,clk,rst_n);
  modport monitor(
    input clk,rst_n,
    clocking mnt_cb
  );
endinterface:uart_bus //uart  