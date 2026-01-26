package spi_agent_pkg;

  import uvm_pkg::*;
  import sequence_pkg::*;
  `include "uvm_macros.svh"

  // =========================================================
  // SPI Sequencer类定义
  class spi_sequencer extends uvm_sequencer #(spi_trans);
    `uvm_component_utils(spi_sequencer)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

  endclass : spi_sequencer

  // =========================================================
  // SPI Driver类定义
  class spi_driver extends uvm_driver #(spi_trans);
    `uvm_component_utils(spi_driver)

    // 定义接口
    local virtual spi_bus.master active_if;

    function new(string name = "spi_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中获取虚拟接口
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if(!uvm_config_db#(virtual spi_bus.master)::get(this, "", "vif", active_if)) begin
        `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name() + ".vif")
      end
    endfunction : build_phase

    // 实现驱动任务
    virtual task run_phase(uvm_phase phase);
      spi_trans tx;
      logic [31:0] mosi;
      logic [31:0] miso;
      int bit_count;

      // 接口初始化
      active_if.mst_cb.cs_n <= 1'b1;
      active_if.mst_cb.sck  <= 1'b0;
      active_if.mst_cb.mosi <= 1'bz;
      forever begin
        // 获取事务
        seq_item_port.get_next_item(tx);

        // 驱动事务到接口
        if (tx.read) begin
          mosi = {8'h01, tx.addr[7:0], 16'h0000};
        end else begin
          mosi = {8'h00, tx.addr[7:0], tx.wdata};
        end
        miso = 32'h0;

        // 开始事务
        active_if.mst_cb.cs_n <= 1'b0;

        @(active_if.mst_cb);
        for (bit_count = 0; bit_count < 32; bit_count = bit_count + 1) begin
          active_if.mst_cb.mosi <= mosi[bit_count];

          @(active_if.mst_cb);
          active_if.mst_cb.sck <= 1'b1;
          miso[bit_count] = active_if.mst_cb.miso;

          @(active_if.mst_cb);
          active_if.mst_cb.sck <= 1'b0;
        end

        // 结束事务
        active_if.mst_cb.mosi <= 1'bz;
        @(active_if.mst_cb);
        active_if.mst_cb.cs_n <= 1'b1;
        active_if.mst_cb.sck  <= 1'b0;
        @(active_if.mst_cb);

        if (tx.read) begin
          tx.rdata = miso;
        end

        seq_item_port.item_done();
      end
    endtask : run_phase
  endclass : spi_driver

  // =========================================================
  // SPI Monitor类定义
  class spi_monitor extends uvm_monitor;
    `uvm_component_utils(spi_monitor)

    // 定义接口
    local virtual spi_bus.monitor monitor_if;

    // 输出事务的TLM端口
    uvm_analysis_port #(spi_trans) spi_ap;

    function new(string name = "spi_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中获取虚拟接口
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if(!uvm_config_db#(virtual spi_bus.monitor)::get(this, "", "vif", monitor_if)) begin
        `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name() + ".vif")
      end
      spi_ap = new("spi_ap", this);
    endfunction : build_phase

    // 实现监视任务
    virtual task run_phase(uvm_phase phase);
      spi_trans monitor_trans;
      logic [31:0] mosi;
      logic [31:0] miso;
      int bit_count;

      forever begin
        monitor_trans = spi_trans::type_id::create("monitor_trans");

        // 等待片选信号拉低，表示传输开始
        wait (monitor_if.mnt_cb.cs_n == 1'b0);

        // 采样32位数据
        for (bit_count = 0; bit_count < 32; bit_count = bit_count + 1) begin
          @(posedge monitor_if.mnt_cb.sck);
          mosi[bit_count] = monitor_if.mnt_cb.mosi;
          miso[bit_count] = monitor_if.mnt_cb.miso;
          @(negedge monitor_if.mnt_cb.sck);
        end

        // 等待片选信号拉高，表示传输结束
        wait (monitor_if.mnt_cb.cs_n == 1'b1);

        // 解析监听到的数据
        monitor_trans.read  = (mosi[31:24] == 8'h01) ? 1'b1 : 1'b0;
        monitor_trans.wdata = mosi[15:0];
        monitor_trans.rdata = miso;
        monitor_trans.addr  = {24'h20_0000, mosi[23:16]};

        // 将解析后的数据发送到analysis端口
        spi_ap.write(monitor_trans);
      end
    endtask : run_phase
  endclass : spi_monitor

  // =========================================================
  // SPI Agent类定义
  class spi_agent extends uvm_agent;
    `uvm_component_utils(spi_agent)
    uvm_analysis_port #(spi_trans) spi_ap;

    spi_sequencer sequencer;
    spi_driver    driver;
    spi_monitor   monitor;

    function new(string name = "spi_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      sequencer = spi_sequencer::type_id::create("sequencer", this);
      driver    = spi_driver::type_id::create("driver", this);
      monitor   = spi_monitor::type_id::create("monitor", this);
    endfunction : build_phase

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction : connect_phase
  endclass : spi_agent

endpackage
