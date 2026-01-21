package my_env_pkg;

  import uvm_pkg::*;
  import my_sequence_pkg::*;
  import my_agent_pkg::*;

  class my_env_config extends uvm_object;      
    virtual dut_if dut_vif_i;
    virtual dut_if dut_vif_o;
    //other env config variables
  endclass : my_env_config

  class my_subscriber extends uvm_subscriber #(my_transaction);

    `uvm_component_utils(my_subscriber)

    string report_id = get_type_name();

    bit cmd;
    int addr;
    int data;

    covergroup cover_bus;
      option.per_instance = 1;
      option.name = {get_full_name(), ".cover_bus"};
      coverpoint cmd;
      coverpoint addr[7:0] { 
        bins a[16] = {[0:255]};
      }
      coverpoint data[7:0] {
        bins d[16] = {[0:255]};
      }
    endgroup : cover_bus

    function new(string name, uvm_component parent);
      super.new(name, parent);
      cover_bus = new();
    endfunction : new

    function void write(my_transaction t);
      `uvm_info(report_id, "Get a transaction from AP", UVM_HIGH);
      //t.print();
      cmd = t.cmd;                  
      addr = t.addr;
      data = t.data;
      cover_bus.sample();
    endfunction : write

  endclass : my_subscriber

  class my_model extends uvm_component;

    `uvm_component_utils(my_model)

    uvm_blocking_get_port #(my_transaction) bgp;
    uvm_analysis_port #(my_transaction) ap;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      bgp = new("bgp", this);
      ap = new("ap", this);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      my_transaction tx_model_i;
      my_transaction tx_model_o;

      while(1) begin
        bgp.get(tx_model_i);
        tx_model_o = my_transaction::type_id::create("tx_model_o");
        tx_model_o.copy(tx_model_i);
        //modeling DUT behavior here
        tx_model_o.addr = {2'b10, tx_model_o.addr[7:0]};
        tx_model_o.data = {2'b01, tx_model_o.data[7:0]};
        //tx_model_o.print();
        ap.write(tx_model_o);
      end
    endtask : run_phase

  endclass : my_model

  class my_scoreboard extends uvm_scoreboard;

    `uvm_component_utils(my_scoreboard)

    string report_id = get_type_name();

    my_transaction exp_queue[$];
    uvm_blocking_get_port #(my_transaction) exp_bgp;
    uvm_blocking_get_port #(my_transaction) act_bgp;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      exp_bgp = new("exp_bgp", this);
      act_bgp = new("act_bgp", this);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      my_transaction exp_tx, act_tx, tmp_tx;
      bit cmp_result;

      fork
        while(1) begin
          exp_bgp.get(exp_tx);
          exp_queue.push_back(exp_tx);
        end //while(1)

        while(1) begin
          act_bgp.get(act_tx);
          if(exp_queue.size() > 0) begin
            tmp_tx = exp_queue.pop_front();
            cmp_result = act_tx.compare(tmp_tx);
            if(cmp_result) begin                                  
              `uvm_info(report_id, "Check PASSED", UVM_LOW);
              /*
              `uvm_info(report_id, "Expect transaction is:", UVM_LOW);
              tmp_tx.print();
              `uvm_info(report_id, "Actual transaction is:", UVM_LOW);
              act_tx.print();
              */
            end else begin
              `uvm_error(report_id, "Check FAILED");
              `uvm_info(report_id, "Expect transaction is:", UVM_LOW);
              tmp_tx.print();
              `uvm_info(report_id, "Actual transaction is:", UVM_LOW);
              act_tx.print();
            end
          end else begin //if(exp_queue.size() = 0)
            `uvm_error(report_id, "Received a transaction from DUT output, but expect queue is empty!");
            `uvm_info(report_id, "Unexpected transaction is:", UVM_LOW);
            act_tx.print();
          end //if(exp_queue.size() > 0)
        end //while(1)
      join
    endtask : run_phase

  endclass : my_scoreboard

  class my_env extends uvm_env;

    `uvm_component_utils(my_env)

    string report_id = get_type_name();

    my_env_config env_config;
    //virtual dut_if dut_vif_i;
    //virtual dut_if dut_vif_o;
    my_agent_config i_agt_cfg;
    my_agent_config o_agt_cfg;

    my_agent my_agent_i_h;
    my_agent my_agent_o_h;
    my_subscriber my_subscriber_i_h;
    my_subscriber my_subscriber_o_h;
    my_model my_model_h;
    my_scoreboard my_scoreboard_h;

    uvm_tlm_analysis_fifo #(my_transaction) i_agt_mdl_fifo;
    uvm_tlm_analysis_fifo #(my_transaction) o_agt_scb_fifo;
    uvm_tlm_analysis_fifo #(my_transaction) mdl_scb_fifo;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
      i_agt_cfg = new();
      o_agt_cfg = new();

      if(!uvm_config_db #(my_env_config)::get(this, "", "env_config", env_config))                
        `uvm_fatal("NO_ENV_CFG", "Class env_config was not set!")
      //dut_vif_i = env_config.dut_vif_i;
      //dut_vif_o = env_config.dut_vif_o;
      i_agt_cfg.dut_vif = env_config.dut_vif_i;
      o_agt_cfg.dut_vif = env_config.dut_vif_o;
      uvm_config_db #(my_agent_config)::set(this, "my_agent_i_h.*", "agent_config", i_agt_cfg);   
      uvm_config_db #(my_agent_config)::set(this, "my_agent_o_h.*", "agent_config", o_agt_cfg);
      `uvm_info(report_id, "AGENT_CFG(s) set into config_db", UVM_LOW);
      
      my_agent_i_h      = my_agent     ::type_id::create("my_agent_i_h", this);
      my_agent_o_h      = my_agent     ::type_id::create("my_agent_o_h", this);
      my_agent_i_h.is_active = UVM_ACTIVE;
      my_agent_o_h.is_active = UVM_PASSIVE;
      my_subscriber_i_h = my_subscriber::type_id::create("my_subscriber_i_h", this);
      my_subscriber_o_h = my_subscriber::type_id::create("my_subscriber_o_h", this);
      my_model_h = my_model::type_id::create("my_model_h", this);
      my_scoreboard_h = my_scoreboard::type_id::create("my_scoreboard_h", this);

      i_agt_mdl_fifo = new("i_agt_mdl_fifo", this);
      o_agt_scb_fifo = new("o_agt_scb_fifo", this);
      mdl_scb_fifo = new("mdl_scb_fifo", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
      my_agent_i_h.ap.connect(my_subscriber_i_h.analysis_export);                         
      my_agent_o_h.ap.connect(my_subscriber_o_h.analysis_export);

      //tlm_analysis_fifo connections
      my_agent_i_h.ap.connect(i_agt_mdl_fifo.analysis_export);                            
      my_model_h.bgp.connect(i_agt_mdl_fifo.blocking_get_export);

      my_agent_o_h.ap.connect(o_agt_scb_fifo.analysis_export);
      my_scoreboard_h.act_bgp.connect(o_agt_scb_fifo.blocking_get_export);

      my_model_h.ap.connect(mdl_scb_fifo.analysis_export);
      my_scoreboard_h.exp_bgp.connect(mdl_scb_fifo.blocking_get_export);

    endfunction : connect_phase

  endclass : my_env

endpackage : my_env_pkg
