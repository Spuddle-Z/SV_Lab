//=====================================================================
// Description:
// This file build the environment for the whole test environment
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

// ATTENTION: mailbox only records handler, therefore, scoreboard and read/write should be parallel, 
//      or some address/data will be miss, especially for continuous read.

package env;
  
  import spi_agent_pkg::*;
  import uart_agent_pkg::*;
  import objects_pkg::*;

  class env_ctrl;

    // FUNC : grab data
    //=============================================================
    // the new function is to build the class object's subordinates

    // first declare subordinates
    // add the uart agents
    spi_agent     spi_agent;
    uart_agent    uart_agent;

    // new them
    function new();
      this.spi_gen2drv_mbx = new(1);
      this.uart_gen2drv_mbx = new(1);

      this.spi_agent  = new();
      this.uart_agent = new();
    endfunction //new()

    // CONNECT
    //=============================================================
    // the set_interface function is to connect the interface to itself
    // and then also connect to its subordinates
    // (only if used)
    function void set_intf(
      virtual spi_bus   spi,
      virtual uart_bus  uart
    );
      // connect to agent
      this.spi_agent.set_intf(spi);
      this.uart_agent.set_intf(uart);
    endfunction

    // RUN
    //=============================================================
    // manage your work here : 
    // (1) receive the command from the testbench
    // (2) call its subordinates to work
    task run(string state);
      localparam  CTRL_ADDR   = 32'h2000_0000;
      localparam  STAT_ADDR   = 32'h2000_0008;
      localparam  TXDATA_ADDR = 32'h2000_0010;
      localparam  RXDATA_ADDR = 32'h2000_0018;
      localparam  BAUD_ADDR   = 32'h2000_0020;

      fork
        this.uart_agent.single_channel_agent();

        case (state)
          "SPI Write": begin
            $display("=============================================================");
            $display("[TB- ENV ] Start work : SPI Write !");

            $display("[TB- ENV ] Write CTRL register.");
            this.spi_agent.single_tran(1'b0, 16'habcd, CTRL_ADDR);

            $display("[TB- ENV ] Write BAUD register.");
            this.spi_agent.single_tran(1'b0, 16'h0036, BAUD_ADDR);

            $display("[TB- ENV ] Write WDATA register for fifo depth.");
            for (int i = 0; i < 8; i = i + 1) begin
              this.spi_agent.single_tran(1'b0, 16'hf0f0, TXDATA_ADDR);
            end
          end

          "SPI RAW": begin
            $display("=============================================================");
            $display("[TB- ENV ] Start work : SPI RAW Test !");

            $display("[TB- ENV ] Write CTRL register.");
            this.spi_agent.single_tran(1'b0, 16'h0001, CTRL_ADDR);
            $display("[TB- ENV ] Read CTRL register.");
            this.spi_agent.single_tran(1'b1, 16'h0000, CTRL_ADDR);

            $display("[TB- ENV ] Write BAUD register.");
            this.spi_agent.single_tran(1'b0, 16'h0036, BAUD_ADDR);
            $display("[TB- ENV ] Read BAUD register.");
            this.spi_agent.single_tran(1'b1, 16'h0000, BAUD_ADDR);
          end

          "LOOPBACK": begin
            $display("=============================================================");
            $display("[TB- ENV ] Start work : LOOPBACK Test !");

            $display("[TB- ENV ] Write CTRL register.");
            this.spi_agent.single_tran(1'b0, 16'habcd, CTRL_ADDR);

            $display("[TB- ENV ] Write BAUD register.");
            this.spi_agent.single_tran(1'b0, 16'h0036, BAUD_ADDR);

            $display("[TB- ENV ] Write WDATA register for fifo depth.");
            fork
              begin
                for (int i = 0; i < 8; i = i + 1) begin
                  this.spi_agent.single_tran(1'b0, 16'hf0f0, TXDATA_ADDR);
                end
                while (1) begin
                  this.spi_agent.single_tran(1'b1, 16'h0000, RXDATA_ADDR);
                end
              end
              this.uart_agent.single_channel_agent();
            join_any
          end

          "Time_Run": begin
            $display("[TB- ENV ] start work : Time_Run !");
            #100000;
            $display("[TB- ENV ] =========================================================================================");
            $display("[TB- ENV ]  _|_|_|_|_|   _|_|_|   _|      _|   _|_|_|_|         _|_|     _|    _|   _|_|_|_|_|  ");
            $display("[TB- ENV ]      _|         _|     _|_|  _|_|   _|             _|    _|   _|    _|       _|      ");
            $display("[TB- ENV ]      _|         _|     _|  _|  _|   _|_|_|         _|    _|   _|    _|       _|      ");
            $display("[TB- ENV ]      _|         _|     _|      _|   _|             _|    _|   _|    _|       _|      ");
            $display("[TB- ENV ]      _|       _|_|_|   _|      _|   _|_|_|_|         _|_|       _|_|         _|      ");
            $display("[TB- ENV ] =========================================================================================");
          end
          default: begin
          end
        endcase
      join
    endtask
  endclass //env_ctrl
endpackage