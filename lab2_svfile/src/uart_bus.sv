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
    logic tx;
    logic rx;

    modport master(output tx,clk,rst_n,
    input rx);
    modport slave(input tx,rx,clk,rst_n);
endinterface:uart_bus //uart  