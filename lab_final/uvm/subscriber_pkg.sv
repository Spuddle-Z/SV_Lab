package subscriber_pkg;

  import uvm_pkg::*;
  import sequence_pkg::*;
  `include "uvm_macros.svh"

  // =========================================================
  // Subscriber类定义
  // =========================================================
  class spi_subscriber extends uvm_subscriber #(spi_trans);
    `uvm_component_utils(spi_subscriber)
    
    bit read;
    bit [31:0] addr;
    bit [15:0] wdata;
    bit [31:0] rdata;

    covergroup spi_bus_cg;
      option.per_instance = 1;

      cov_spi_read : coverpoint read {
        bins read  = {1'b1};
        bins write = {1'b0};
      }

      cov_spi_addr : coverpoint addr {
        bins ctrl_read  = {CTRL_ADDR} iff (read == 1);
        bins ctrl_write = {CTRL_ADDR} iff (read == 0);

        bins stat_read  = {STAT_ADDR} iff (read == 1);
        bins stat_write = {STAT_ADDR} iff (read == 0);

        bins txdata_read  = {TXDATA_ADDR} iff (read == 1);
        bins txdata_write = {TXDATA_ADDR} iff (read == 0);

        bins rxdata_read  = {RXDATA_ADDR} iff (read == 1);
        bins rxdata_write = {RXDATA_ADDR} iff (read == 0);

        bins baud_read  = {BAUD_ADDR} iff (read == 1);
        bins baud_write = {BAUD_ADDR} iff (read == 0);

        bins other_addr = {[32'h2000_0028 : 32'h2000_FFFF]};
      }
    endgroup : spi_bus_cg

    function new(string name, uvm_component parent);
      super.new(name, parent);
      spi_bus_cg = new();
    endfunction : new

    virtual function void write(spi_trans t);
      read  = t.read;
      addr  = t.addr;
      wdata = t.wdata;
      rdata = t.rdata;

      spi_bus_cg.sample();
    endfunction : write
  endclass : spi_subscriber

  class uart_subscriber extends uvm_subscriber #(uart_trans);
    `uvm_component_utils(uart_subscriber)
    
    bit [7:0] data;
    bit is_tx;

    covergroup uart_bus_cg;
      option.per_instance = 1;

      cov_uart_is_tx : coverpoint is_tx {
        bins tx = {1'b1};
        bins rx = {1'b0};
      }

    endgroup : uart_bus_cg

    function new(string name, uvm_component parent);
      super.new(name, parent);
      uart_bus_cg = new();
    endfunction : new

    virtual function void write(uart_trans t);
      data  = t.data;
      is_tx = t.is_tx;

      uart_bus_cg.sample();
    endfunction : write
  endclass : uart_subscriber
endpackage : subscriber_pkg;