package env_pkg;

  import uvm_pkg::*;
  import sequence_pkg::*;
  import spi_agent_pkg::*;
  import uart_agent_pkg::*;
  import scoreboard_pkg::*;
  import subscriber_pkg::*;
  `include "uvm_macros.svh"

  // =========================================================
  // Environment类定义
  class my_env extends uvm_env;
    `uvm_component_utils(my_env)

    // 实例化agent
    spi_agent spi_agt;
    uart_agent uart_agt;
    my_model mdl;
    my_scoreboard scb;
    spi_subscriber spi_sub;

    // 实例化通信fifo
    uvm_tlm_analysis_fifo #(spi_trans) spi_mdl_fifo;
    uvm_tlm_analysis_fifo #(uart_trans) uart_mdl_fifo;
    uvm_tlm_analysis_fifo #(uart_trans) exp_uart_fifo;
    uvm_tlm_analysis_fifo #(uart_trans) act_uart_tx_fifo;
    uvm_tlm_analysis_fifo #(uart_trans) act_uart_rx_fifo;
    uvm_tlm_analysis_fifo #(spi_trans) act_spi_read_fifo;

    function new(string name = "my_env", uvm_component parent);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中实例化agent
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // 实例化agent和model
      spi_agt = spi_agent::type_id::create("spi_agt", this);
      uart_agt = uart_agent::type_id::create("uart_agt", this);
      mdl = my_model::type_id::create("mdl", this);
      scb = my_scoreboard::type_id::create("scb", this);
      spi_sub = spi_subscriber::type_id::create("spi_sub", this);

      // 实例化fifo
      spi_mdl_fifo = new("spi_mdl_fifo", this);
      uart_mdl_fifo = new("uart_mdl_fifo", this);
      exp_uart_fifo = new("exp_uart_fifo", this);
      act_uart_tx_fifo = new("act_uart_tx_fifo", this);
      act_uart_rx_fifo = new("act_uart_rx_fifo", this);
      act_spi_read_fifo = new("act_spi_read_fifo", this);
    endfunction : build_phase

    // 在connect_phase中连接analysis端口和fifo
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      // 连接SPI agent与UART agent的analysis端口到model的fifo
      spi_agt.spi_ap.connect(spi_mdl_fifo.analysis_export);
      spi_agt.spi_ap.connect(spi_sub.analysis_export);
      mdl.spi_bgp.connect(spi_mdl_fifo.blocking_get_export);
      uart_agt.uart_ap.connect(uart_mdl_fifo.analysis_export);
      mdl.uart_bgp.connect(uart_mdl_fifo.blocking_get_export);

      mdl.exp_uart_ap.connect(exp_uart_fifo.analysis_export);
      scb.exp_bgp.connect(exp_uart_fifo.blocking_get_export);
      mdl.act_uart_tx_ap.connect(act_uart_tx_fifo.analysis_export);
      scb.act_tx_bgp.connect(act_uart_tx_fifo.blocking_get_export);
      mdl.act_uart_rx_ap.connect(act_uart_rx_fifo.analysis_export);
      scb.act_rx_bgp.connect(act_uart_rx_fifo.blocking_get_export);
      mdl.act_spi_read_ap.connect(act_spi_read_fifo.analysis_export);
      scb.act_spi_bgp.connect(act_spi_read_fifo.blocking_get_export);
    endfunction : connect_phase
  endclass : my_env

endpackage : env_pkg