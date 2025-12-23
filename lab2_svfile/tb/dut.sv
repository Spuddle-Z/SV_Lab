//=====================================================================
// Description:
// This file wraps the dut_top
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module dut (
  spi_bus   spi,
  uart_bus  uart
);
// dut top
  dut_top i_dut(
    // input bus
    .spi_bus(     spi.slave     ),

    // output bus
    .uart_bus(   uart.master   )
  );

// other testbench modules if needed
  
endmodule