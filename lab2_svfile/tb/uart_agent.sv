//=====================================================================
// Description:
// This file realize the UART AGENT, includes data generator, driver and
// monitor.
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package uart_agent_pkg;
  import objects_pkg::*;

  // Generator: Generate data for driver to transfer
  class uart_generator;
    // BUILD
    //=============================================================
    // ...

    // FUNC
    //=============================================================
    // ...
  endclass //uart_generator

  // Driver: Converts the received packets to the format of the UART protocol
  class uart_driver;

    // BUILD
    //=============================================================
    // ...

    // CONNECT
    //=============================================================
    // ...

    // FUNC
    //=============================================================
    // ...

  endclass //uart_driver

  // **Optional** 
  // Monitor: Collect UART data and convert it to data package for
  //      scoreboard to compare result.
  class uart_monitor;

    // BUILD
    //=============================================================
    // ...

    // CONNECT
    //=============================================================
    // ...

    // FUNC
    //=============================================================
    // ...
  endclass //icb_monitor

  // Agent: The top class that connects generator, driver and monitor
  class uart_agent;
    
    // BUILD
    //=============================================================
    // ...

    // CONNECT
    //=============================================================
    // ...

    // FUN : single data tran
    //=============================================================
    // ...
    
  endclass //uart_agent
endpackage


