package my_agent_pkg;

  import uvm_pkg::*;
  import my_sequence_pkg::*;

  class my_agent_config extends uvm_object;
    virtual dut_if dut_vif;
    //other agent config variables
  endclass : my_agent_config

  typedef uvm_sequencer #(my_transaction) my_sequencer;   

  class my_driver extends uvm_driver #(my_transaction);

    `uvm_component_utils(my_driver)

    string report_id = get_type_name();

    my_agent_config agent_config;
    virtual dut_if dut_vif;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      if(!uvm_config_db #(my_agent_config)::get(this, "", "agent_config", agent_config))
        `uvm_fatal("NO_AGENT_CFG_IN_DRV", "Class agent_config was not set!")
      dut_vif = agent_config.dut_vif;
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      forever begin
        seq_item_port.get_next_item(req);

        @(posedge dut_vif.clock);
        #1;
        dut_vif.cmd_valid = 1;
        dut_vif.cmd  = req.cmd;
        dut_vif.addr = req.addr;
        dut_vif.data = req.data;

        @(posedge dut_vif.clock);
        #1;
        dut_vif.cmd_valid = 0;

        seq_item_port.item_done();
      end
    endtask : run_phase

  endclass : my_driver

  class my_monitor extends uvm_monitor;

    `uvm_component_utils(my_monitor)

    string report_id = get_type_name();

    uvm_analysis_port #(my_transaction) ap;

    my_agent_config agent_config;
    virtual dut_if dut_vif;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      ap = new("ap", this);
      if(!uvm_config_db #(my_agent_config)::get(this, "", "agent_config", agent_config))
        `uvm_fatal("NO_AGENT_CFG_IN_MON", "Class agent_config was not set!")
      dut_vif = agent_config.dut_vif;
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      forever begin
        my_transaction tx_monitor_o;

        @(posedge dut_vif.clock);
        if(dut_vif.cmd_valid == 1) begin
          tx_monitor_o = my_transaction::type_id::create("tx_monitor_o");
          tx_monitor_o.cmd  = dut_vif.cmd;
          tx_monitor_o.addr = dut_vif.addr;
          tx_monitor_o.data = dut_vif.data;
          `uvm_info(report_id, $sformatf("%b %x %x", tx_monitor_o.cmd, tx_monitor_o.addr, tx_monitor_o.data), UVM_HIGH);
          ap.write(tx_monitor_o);
        end
      end
    endtask : run_phase

  endclass : my_monitor

  class my_agent extends uvm_agent;

    `uvm_component_utils(my_agent)

    uvm_analysis_port #(my_transaction) ap;

    my_sequencer my_sequencer_h;
    my_driver    my_driver_h;
    my_monitor   my_monitor_h;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      //ap = new("ap", this);
      if(is_active == UVM_ACTIVE) begin
        my_sequencer_h = my_sequencer::type_id::create("my_sequencer_h", this);
        my_driver_h    = my_driver   ::type_id::create("my_driver_h"   , this);
      end
      my_monitor_h   = my_monitor  ::type_id::create("my_monitor_h"  , this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
      if(is_active == UVM_ACTIVE) begin
        my_driver_h.seq_item_port.connect(my_sequencer_h.seq_item_export);
      end
      //my_monitor_h.ap.connect(ap);
      ap = my_monitor_h.ap;
    endfunction : connect_phase

  endclass : my_agent

endpackage : my_agent_pkg
