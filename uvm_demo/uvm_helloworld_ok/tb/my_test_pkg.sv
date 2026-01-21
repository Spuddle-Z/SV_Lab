package my_test_pkg;

  parameter NUM_ENV = 4;

  import uvm_pkg::*;
  import my_sequence_pkg::*;
  import my_agent_pkg::*;
  import my_env_pkg::*;

  class my_vsequencer extends uvm_sequencer;          

    `uvm_component_utils(my_vsequencer)

    my_sequencer p_my_sequencer[NUM_ENV];             

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

  endclass : my_vsequencer

  class my_test extends uvm_test;

    `uvm_component_utils(my_test)

    string report_id = get_type_name();
    int i;

    my_env_config my_env_config_h[NUM_ENV];
    my_env my_env_h[NUM_ENV];                         
    my_vsequencer my_vsequencer_h;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);

      for(i=0;i<NUM_ENV;i++) begin
        my_env_config_h[i] = new();
      end

      for(i=0;i<NUM_ENV;i++) begin                      
        if(!uvm_config_db #(virtual dut_if)::get(this, "", $sformatf("dut_vif_i%1d", i), my_env_config_h[i].dut_vif_i))
          `uvm_fatal("NO_VIF", $sformatf("Virtual interface dut_vif_i%1d was not set!", i))
        if(!uvm_config_db #(virtual dut_if)::get(this, "", $sformatf("dut_vif_o%1d", i), my_env_config_h[i].dut_vif_o))
          `uvm_fatal("NO_VIF", $sformatf("Virtual interface dut_vif_o%1d was not set!", i))
      end

      for(i=0;i<NUM_ENV;i++) begin                    
        uvm_config_db #(my_env_config)::set(this, $sformatf("my_env_h[%1d]", i), "env_config", my_env_config_h[i]);
      end

      `uvm_info(report_id, "ENV_CFG(s) set into config_db", UVM_LOW);

      for(i=0;i<NUM_ENV;i++) begin
        my_env_h[i] = my_env::type_id::create($sformatf("my_env_h[%1d]", i), this);
      end

      my_vsequencer_h = my_vsequencer::type_id::create("my_vsequencer_h", this);   		

    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
      for(i=0;i<NUM_ENV;i++) begin
        my_vsequencer_h.p_my_sequencer[i] = my_env_h[i].my_agent_i_h.my_sequencer_h;     
      end																				

      uvm_top.print_topology();
    endfunction : connect_phase

    function void report_phase(uvm_phase phase);
      uvm_report_server report_server_h;
      int num_err;
      int num_fatal;

      report_server_h = uvm_report_server::get_server();
      num_err = report_server_h.get_severity_count(UVM_ERROR);
      num_fatal = report_server_h.get_severity_count(UVM_FATAL);

      //Final result
      if(num_err==0 && num_fatal==0) begin
        $display("###########################################");
        $display("############    TEST PASSED    ############");
        $display("###########################################");
      end else begin
        $display("###########################################");
        $display("############    TEST FAILED    ############");
        $display("###########################################");
      end
    endfunction : report_phase

  endclass : my_test

  class test0 extends my_test;

    `uvm_component_utils(test0)

    string report_id = get_type_name();

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    task run_phase(uvm_phase phase);
      read_seq rseq;
      write_seq wseq;
      rseq = read_seq::type_id::create("rseq");
      wseq = write_seq::type_id::create("wseq");

      phase.phase_done.set_drain_time(this, 100);

      phase.raise_objection(this);
      for(i=0;i<NUM_ENV;i++) begin
        wait(my_env_h[i].env_config.dut_vif_i.reset == 0);
        rseq.start(my_vsequencer_h.p_my_sequencer[i]);
        wseq.start(my_vsequencer_h.p_my_sequencer[i]);                          
      end
      phase.drop_objection(this);
    endtask : run_phase

  endclass : test0

  class test1 extends my_test;

    `uvm_component_utils(test1)

    string report_id = get_type_name();

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    task run_phase(uvm_phase phase);
      read_seq rseq;
      write_seq wseq;

      rseq = read_seq::type_id::create("rseq");
      wseq = write_seq::type_id::create("wseq");

      phase.phase_done.set_drain_time(this, 100);

      phase.raise_objection(this);
      fork
        begin
          wait(my_env_h[0].env_config.dut_vif_i.reset == 0);
          repeat(2) begin
            rseq.start(my_vsequencer_h.p_my_sequencer[0]);
          end
        end
        begin
          wait(my_env_h[1].env_config.dut_vif_i.reset == 0);
          repeat(2) begin
            wseq.start(my_vsequencer_h.p_my_sequencer[1]);
          end
        end
      join
      #100;
      fork
        begin
          repeat(2) begin
            wseq.start(my_vsequencer_h.p_my_sequencer[0]);
          end
        end
        begin
          repeat(2) begin
            rseq.start(my_vsequencer_h.p_my_sequencer[1]);
          end
        end
      join
      phase.drop_objection(this);
    endtask : run_phase

  endclass : test1

  class test2 extends my_test;

    `uvm_component_utils(test2)

    string report_id = get_type_name();

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    task run_phase(uvm_phase phase);
      read_modify_write_seq rmw_seq_1;
      read_modify_write_seq rmw_seq_2;

      rmw_seq_1 = read_modify_write_seq::type_id::create("rmw_seq_1");
      rmw_seq_2 = read_modify_write_seq::type_id::create("rmw_seq_2");

      phase.phase_done.set_drain_time(this, 100);

      phase.raise_objection(this);
      fork
        begin
          repeat(3) begin
            wait(my_env_h[0].env_config.dut_vif_i.reset == 0);
            rmw_seq_1.start(my_vsequencer_h.p_my_sequencer[0]);
          end
        end
        begin
          repeat(3) begin
            wait(my_env_h[1].env_config.dut_vif_i.reset == 0);
            rmw_seq_2.start(my_vsequencer_h.p_my_sequencer[1]);
          end
        end
      join
      phase.drop_objection(this);
    endtask : run_phase

  endclass : test2

  class test3_vseq extends uvm_sequence;            

    `uvm_object_utils(test3_vseq)
    `uvm_declare_p_sequencer(my_vsequencer)

    read_seq rseq;
    write_seq wseq;
    read_modify_write_seq rmw_seq;

    function new(string name = "");
      super.new(name);
    endfunction : new

    task body;

      rseq = read_seq::type_id::create("rseq");
      wseq = write_seq::type_id::create("wseq");
      rmw_seq = read_modify_write_seq::type_id::create("rmw_seq");

      fork
        begin
          repeat(6) begin
            wseq.start(p_sequencer.p_my_sequencer[0]);
            rseq.start(p_sequencer.p_my_sequencer[0]);
          end
        end

        begin
          repeat(3) begin
            rmw_seq.start(p_sequencer.p_my_sequencer[1]);
          end
        end
      join

    endtask : body

  endclass : test3_vseq

  class test3 extends my_test;

    `uvm_component_utils(test3)

    string report_id = get_type_name();

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    task run_phase(uvm_phase phase);
      test3_vseq vseq;

      vseq = test3_vseq::type_id::create("vseq");

      phase.phase_done.set_drain_time(this, 100);

      phase.raise_objection(this);
      #100; //wait for reset deassert
      vseq.start(my_vsequencer_h);
      phase.drop_objection(this);
    endtask : run_phase

  endclass : test3

endpackage : my_test_pkg
