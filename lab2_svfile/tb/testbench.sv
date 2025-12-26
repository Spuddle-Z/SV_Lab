//=====================================================================
// Description:
// This file is the top testbench file. In the testbench_top module, build
// the instance of the module of dut and program of testbench, even the
// interface and some global signals. 'testbench' file control the total 
// sim process, here add your command to ENV object.
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module testbench_top ();

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

//=====================================================================
// Connections between DUT And Testbench
//=====================================================================

  testbench i_testbench(
    .clk   (    clk       ),
    .rst_n (    rst_n       ),

    // source channel connections
    .spi(       spi       ),

    // ...
  ); 

  dut i_dut(
    // input bus
    .spi(       spi       ),

    // output bus
    .uart(      uart      )
  );
endmodule

program testbench(
  input  logic      clk,
  input  logic      rst_n,

  spi_bus.master    spi
  uart_bus.slave    uart
);
  import env::*;   // import your ENV object
  env_ctrl envctrl; // first declare it

  initial begin
    
    $display("[TB- SYS ] welcome to sv testbench plateform !");

    // BUILD
    //=============================================================    
    // the first step in testbench is build your env object 
    // as your command manager, after that you can call it
    // also with its subordinates
    $display("[TB- SYS ] building");
    envctrl = new();

    // CONNECT
    //=============================================================
    // let your manager connected to your dut by interface
    $display("[TB- SYS ] connecting");
    envctrl.set_intf(
      spi,
      uart
    );

    // RUN
    //=============================================================
    // give command to your env object
    $display("[TB- SYS ] running");

    // (1) waiting for rst done in dut
    repeat(11) @(posedge clk);
    
    // (2) add your command here 
    // example :
    //envctrl.run("SPI Write");
  
    fork
      envctrl.run("SPI Write");             // The testcase you want to run
      envctrl.run("SPI RAW");
      envctrl.run("LOOPBACK");
      envctrl.run("Time_Run");            // time out limitation
    join_any
    disable fork;    

    // END
    //=============================================================  
    $display("[TB- SYS ] testbench system has done all the work, exit !");

  end
endprogram