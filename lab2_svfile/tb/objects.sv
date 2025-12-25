//=====================================================================
// Description:
// This file includes objects needed for the whole test environment
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package objects_pkg;
  class spi_trans;
    rand logic        read; // 0: write; 1: read
    rand logic [15:0] wdata;
    rand logic [31:0] rdata;
    rand logic [31:0] addr;
  endclass // spi_trans

  class uart_trans;
    rand logic [15:0] data;
  endclass // uart_trans
endpackage
