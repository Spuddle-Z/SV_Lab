//===================================================================== 
/// Description: 
// the interface of spi
// Designer : wangziyao1@sjtu.edu.cn
// ==================================================================== 

/*
This is only the basic interface, you may change it by your own.
But don't change this signal description.
*/
interface spi_bus(input logic clk,input logic rst_n);
    logic cs_n;
    logic sck;
    logic mosi;
    logic miso;

    modport slave(input cs_n,sck,mosi,clk,rst_n,
    output miso);
    modport master(output cs_n,sck,mosi,
    input miso,clk,rst_n);
endinterface:spi_bus //spi