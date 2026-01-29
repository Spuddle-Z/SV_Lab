package test_pkg;

  import uvm_pkg::*;
  import env_pkg::*;
  import sequence_pkg::*;
  `include "uvm_macros.svh"

  // =========================================================
  // Test类定义
  class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    // 实例化环境
    my_env env;

    function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中实例化环境
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = my_env::type_id::create("env", this);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
      spi_reg_sequence spi_reg_seq;
      spi_data_sequence spi_data_seq;
      uart_sequence uart_seq;
      spi_reg_seq = spi_reg_sequence::type_id::create("spi_reg_seq", this);
      spi_data_seq = spi_data_sequence::type_id::create("spi_data_seq", this);
      uart_seq = uart_sequence::type_id::create("uart_seq", this);

      phase.phase_done.set_drain_time(this, 1000ns);
      phase.raise_objection(this);  // 提出objection，表示test还在运行

      // 启动SPI寄存器操作序列
      spi_reg_seq.start(env.spi_agt.sequencer);

      fork
        // 启动SPI数据传输序列
        spi_data_seq.start(env.spi_agt.sequencer);
        // 启动UART数据传输序列
        uart_seq.start(env.uart_agt.sequencer);
      join

      phase.drop_objection(this);
    endtask : run_phase
  endclass : my_test
endpackage : test_pkg