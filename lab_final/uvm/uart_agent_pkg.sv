package uart_agent_pkg;

  import uvm_pkg::*;
  import sequence_pkg::*;
  `include "uvm_macros.svh"

  // =========================================================
  // UART Sequencer类定义
  class uart_sequencer extends uvm_sequencer #(uart_trans);
    `uvm_component_utils(uart_sequencer)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

  endclass : uart_sequencer

  // =========================================================
  // UART Driver类定义
  class uart_driver extends uvm_driver #(uart_trans);
    `uvm_component_utils(uart_driver)

    // 定义接口
    local virtual uart_bus.slave active_if;

    function new(string name = "uart_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中获取虚拟接口
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if(!uvm_config_db#(virtual uart_bus.slave)::get(this, "", "vif", active_if)) begin
        `uvm_fatal("NOVIF", "Virtual interface must be set for: uart_driver.vif")
      end
    endfunction : build_phase

    // 实现驱动任务
    virtual task run_phase(uvm_phase phase);
      uart_trans tx;
      byte tx_data;
      int bit_count;
      localparam int BAUD_DIVISOR = 16'h0036;

      // 接口初始化
      active_if.slv_cb.rx <= 1'b1;
      forever begin
        // 获取事务
        seq_item_port.get_next_item(tx);

        // 驱动事务到接口
        tx_data = tx.data;

        // 起始位
        active_if.slv_cb.rx <= 1'b0;
        repeat (BAUD_DIVISOR * 16) @(posedge active_if.clk);

        // 数据位
        for (bit_count = 0; bit_count < 8; bit_count = bit_count + 1) begin
          active_if.slv_cb.rx <= tx_data[bit_count];
          repeat (BAUD_DIVISOR * 16) @(posedge active_if.clk);
        end

        // 停止位
        active_if.slv_cb.rx <= 1'b1;
        repeat (BAUD_DIVISOR * 16) @(posedge active_if.clk);

        // 完成事务
        seq_item_port.item_done();
      end
    endtask : run_phase
  endclass : uart_driver

  class uart_monitor extends uvm_monitor;
    `uvm_component_utils(uart_monitor)

    // 定义接口
    local virtual uart_bus.master monitor_if;

    // 输出分析端口
    uvm_analysis_port #(uart_trans) uart_ap;

    function new(string name = "uart_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 在build_phase中获取虚拟接口
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if(!uvm_config_db#(virtual uart_bus.master)::get(this, "", "vif", monitor_if)) begin
        `uvm_fatal("NOVIF", "Virtual interface must be set for: uart_monitor.vif")
      end
      uart_ap = new("uart_ap", this);
    endfunction : build_phase

    // 实现监视任务
    virtual task run_phase(uvm_phase phase);
      localparam int BAUD_DIVISOR = 16'h0036;

      fork
        begin : monitor_tx
          forever begin
            uart_trans tx_trans;
            byte tx_data;
            int bit_count;
            tx_trans = uart_trans::type_id::create("tx_trans");
            tx_data = 8'h00;

            @(negedge monitor_if.tx);
            repeat (BAUD_DIVISOR * 24) @(posedge monitor_if.clk);

            for (bit_count = 0; bit_count < 8; bit_count = bit_count + 1) begin
              tx_data[bit_count] = monitor_if.tx;
              repeat (BAUD_DIVISOR * 16) @(posedge monitor_if.clk);
            end

            repeat (BAUD_DIVISOR * 16) @(posedge monitor_if.clk);

            tx_trans.data = tx_data;
            tx_trans.is_tx = 1'b1;
            uart_ap.write(tx_trans);
          end
        end

        begin : monitor_rx
          forever begin
            uart_trans rx_trans;
            byte rx_data;
            int bit_count;
            rx_trans = uart_trans::type_id::create("rx_trans");
            rx_data = 8'h00;

            @(negedge monitor_if.rx);
            repeat (BAUD_DIVISOR * 24) @(posedge monitor_if.clk);

            for (bit_count = 0; bit_count < 8; bit_count = bit_count + 1) begin
              rx_data[bit_count] = monitor_if.rx;
              repeat (BAUD_DIVISOR * 16) @(posedge monitor_if.clk);
            end

            repeat (BAUD_DIVISOR * 16) @(posedge monitor_if.clk);

            rx_trans.data = rx_data;
            rx_trans.is_tx = 1'b0;
            uart_ap.write(rx_trans);
          end
        end
      join
    endtask : run_phase
  endclass : uart_monitor

  // =========================================================
  // UART Agent类定义
  class uart_agent extends uvm_agent;
    `uvm_component_utils(uart_agent)
    uvm_analysis_port #(uart_trans) uart_ap;

    uart_sequencer sequencer;
    uart_driver    driver;
    uart_monitor   monitor;

    function new(string name = "uart_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction : new

    // 构建组件
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      sequencer = uart_sequencer::type_id::create("sequencer", this);
      driver    = uart_driver::type_id::create("driver", this);
      monitor   = uart_monitor::type_id::create("monitor", this);
    endfunction : build_phase

    // 连接组件
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      driver.seq_item_port.connect(sequencer.seq_item_export);
      uart_ap = monitor.uart_ap;
    endfunction : connect_phase
  endclass : uart_agent

endpackage
