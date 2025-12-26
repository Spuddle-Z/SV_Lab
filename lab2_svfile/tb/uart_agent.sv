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
    mailbox #(uart_trans) gen2drv; // mailbox to transfer data to driver

    function new(
      mailbox #(uart_trans) gen2drv
    );
      this.gen2drv = gen2drv; // the mailbox will be created in agent
    endfunction //new()

    // FUNC
    //=============================================================
    task automatic data_gen(
      input [15:0]  data = 16'h0000
    );
      uart_trans tran_data;
      tran_data = new();

      // set tran data according to input
      tran_data.data = data;

      // send the generated data to driver
      this.gen2drv.put(tran_data);
    endtask //automatic data_gen
  endclass //uart_generator

  // Driver: Converts the received packets to the format of the UART protocol
  class uart_driver;

    // BUILD
    //=============================================================
    mailbox #(uart_trans) gen2drv; // receive the data from generator

    function new(
      mailbox #(uart_trans) gen2drv
    );
      this.gen2drv = gen2drv;
    endfunction //new()

    // CONNECT
    //=============================================================
    local virtual uart_bus.master active_channel;

    function void set_intf(
      virtual uart_bus.master uart
    );
      this.active_channel = uart;
    endfunction

    // FUNC
    //=============================================================
    task automatic data_trans(logic [15:0] baud_divisor = 16'h0036);
      uart_trans get_trans;

      logic [7:0] tx_data;
      logic [2:0]  bit_count;

      // get the input data from mailbox
      this.gen2drv.get(get_trans);
      tx_data = get_trans.data;

      // 起始位
      this.active_channel.mst_cb.tx <= 1'b0;
      repeat (baud_divisor * 16) @(posedge this.active_channel.clk);

      // 数据位
      for (bit_count = 0; bit_count < 8; bit_count++) begin
        this.active_channel.mst_cb.tx <= tx_data[bit_count];
        repeat (baud_divisor * 16) @(posedge this.active_channel.clk);
      end

      // 停止位
      this.active_channel.mst_cb.tx <= 1'b1;
      repeat (baud_divisor * 16) @(posedge this.active_channel.clk);
    endtask

  endclass //uart_driver

  // **Optional** 
  // Monitor: Collect UART data and convert it to data package for
  //      scoreboard to compare result.
  class uart_monitor;

    // BUILD
    //=============================================================
    mailbox #(uart_trans) mmnt2scb;
    mailbox #(uart_trans) smnt2scb;

    function new(
      mailbox #(uart_trans) mmnt2scb
      mailbox #(uart_trans) smnt2scb
    );
      this.mmnt2scb = mmnt2scb;
      this.smnt2scb = smnt2scb;
    endfunction

    // CONNECT
    //=============================================================
    local virtual uart_bus.monitor monitor_channel;

    function void set_intf(
      virtual uart_bus.monitor uart
    );
      this.monitor_channel = uart;
    endfunction

    // FUNC
    //=============================================================
    task automatic mst_monitor(
      logic [15:0] baud_divisor = 16'h0036
    );
      uart_trans put_trans;

      logic [7:0] data;
      logic [2:0] bit_count;

      put_trans = new();

      // wait for start bit
      @(negedge this.monitor_channel.mnt_cb.rx);
      repeat (baud_divisor * 24) @(posedge this.monitor_channel.clk); // mid bit

      // data bits
      for (bit_count = 0; bit_count < 8; bit_count++) begin
        data[bit_count] = this.monitor_channel.mnt_cb.rx;
        repeat (baud_divisor * 16) @(posedge this.monitor_channel.clk);
      end

      // stop bit
      repeat (baud_divisor * 16) @(posedge this.monitor_channel.clk);

      // put the received data into mailbox
      put_trans.data = data;
      this.mmnt2scb.put(put_trans);
    endtask //mst_monitor

    task automatic slv_monitor(
      logic [15:0] baud_divisor = 16'h0036
    );
      uart_trans put_trans;

      logic [7:0] data;
      logic [2:0] bit_count;

      put_trans = new();

      // wait for start bit
      @(negedge this.monitor_channel.mnt_cb.tx);
      repeat (baud_divisor * 24) @(posedge this.monitor_channel.clk); // mid bit

      // data bits
      for (bit_count = 0; bit_count < 8; bit_count++) begin
        data[bit_count] = this.monitor_channel.mnt_cb.tx;
        repeat (baud_divisor * 16) @(posedge this.monitor_channel.clk);
      end

      // stop bit
      repeat (baud_divisor * 16) @(posedge this.monitor_channel.clk);

      // put the received data into mailbox
      put_trans.data = data;
      this.smnt2scb.put(put_trans);
    endtask //mst_monitor
  endclass

  // Agent: The top class that connects generator, driver and monitor
  class uart_agent;
    
    // BUILD
    //=============================================================
    mailbox #(uart_trans)  gen2drv;
    uart_generator       uart_generator;
    uart_driver        uart_driver;
    uart_monitor       uart_monitor;

    // CONNECT
    //=============================================================
    function void set_intf(
      virtual uart_bus uart
    );   
      // connect to uart_driver
      this.uart_driver.set_intf(uart);
      this.uart_monitor.set_intf(uart);
    endfunction //automatic

    // FUN : single data tran
    //=============================================================
    task automatic single_channel_agent();
      uart_trans random_trans;
      random_trans = new();

      while (1) begin
        void'(random_trans.randomize());
        fork
          begin
            this.uart_monitor.mst_monitor();  // monitor data
            this.uart_generator.data_gen(random_trans.data);  // generate data
            this.uart_driver.data_trans(); // drive data
          end
          this.uart_monitor.slv_monitor();  // monitor data
        join
        #1;
      end
    endtask //automatic

  endclass //uart_agent
endpackage


