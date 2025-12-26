//=====================================================================
// Description:
// This file realize the SPI AGENT, includes data generator, driver and
// monitor.
// Designer : zzz-jy@sjtu.edu.cn
// Revision History
// V0 date:2025/11/01 Initial version, zzz-jy@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package spi_agent_pkg;
  import objects_pkg::*;
  
  // Generator: Generate data for driver to transfer
  class spi_generator;

    // BUILD
    //=============================================================
    // generator need a mailbox to transfer data to driver
    mailbox #(spi_trans)  gen2drv; 

    function new(
      mailbox #(spi_trans) gen2drv
    );
      this.gen2drv = gen2drv; // the mailbox will be create in agent
    endfunction //new()

    // FUNC : generate a data for transaction
    // **Optional** The random data generation can be realized here
    //=============================================================
    task automatic data_gen(
      input         read = 1'b0,
      input [15:0]  data = 16'h0000,
      input [31:0]  addr = 32'h2000_0000
    );
      spi_trans   tran_data;
      tran_data = new();
      
      // set tran data according to input
      tran_data.read = read;
      tran_data.wdata = data;
      tran_data.addr = addr;

      // send the generated data to driver
      this.gen2drv.put(tran_data);
    endtask
  endclass //spi_generator

  // Driver: Converts the received packets to the format of the SPI protocol
  class spi_driver;

    // BUILD
    //=============================================================
    mailbox #(spi_trans)  gen2drv; // receive the data from generator

    function new(
      mailbox #(spi_trans)  gen2drv
    );
      this.gen2drv = gen2drv;
    endfunction //new()
    
    // CONNECT
    //=============================================================
    local virtual spi_bus.master active_channel;

    function void set_intf(
      virtual spi_bus.master spi
    );
      this.active_channel = spi;

      // port initialization
      this.active_channel.mst_cb.cs_n <= 1'b1;
      this.active_channel.mst_cb.sck <= 1'b0;
      this.active_channel.mst_cb.mosi <= 1'bz;

    endfunction

    // FUNC : data transfer
    //=============================================================
    task automatic data_trans();
      spi_trans   get_trans;

      logic [31:0] tx_data;
      logic [5:0] bit_count;

      // get the input data and address from mailbox
      this.gen2drv.get(get_trans);

      // prepare transmission data
      if (get_trans.read) begin
        tx_data = {8'h01, get_trans.addr[7:0], 16'h0000};
      end else begin
        tx_data = {8'h00, get_trans.addr[7:0], get_trans.wdata[15:0]};
      end

      // setup the transaction
      this.active_channel.mst_cb.cs_n <= 1'b0;

      @(this.active_channel.mst_cb);
      for (bit_count = 0; bit_count < 32; bit_count++) begin
        this.active_channel.mst_cb.mosi <= tx_data[31 - bit_count];

        @(this.active_channel.mst_cb);
        this.active_channel.mst_cb.sck <= 1'b1;

        @(this.active_channel.mst_cb);
        this.active_channel.mst_cb.sck <= 1'b0;
      end

      // end the transaction
      this.active_channel.mst_cb.mosi <= 1'bz;
      @(this.active_channel.mst_cb);
      this.active_channel.mst_cb.cs_n <= 1'b1;
      this.active_channel.mst_cb.sck <= 1'b0;
      @(this.active_channel.mst_cb); 

    endtask //automatic

  endclass //spi_driver

  // **Optional** 
  // Monitor: Collect SPI data and convert it to data package for
  //      scoreboard to compare result.
  class spi_monitor;

    // BUILD
    //=============================================================
    mailbox #(spi_trans) mnt2scb;

    function new(
      mailbox #(spi_trans) mnt2scb
    );
      this.mnt2scb = mnt2scb;
    endfunction

    // CONNECT
    //=============================================================
    local virtual spi_bus.monitor monitor_channel;

    function void set_intf(
      virtual spi_bus.monitor spi
    );
      this.monitor_channel = spi;
    endfunction

    // FUNC
    //=============================================================
    task automatic data_monitor();
      spi_trans put_trans;

      logic [31:0] tx_data;
      logic [31:0] rx_data;
      logic [5:0]  bit_count;

      put_trans = new();

      // 等待片选信号拉低，表示传输开始
      wait (this.monitor_channel.mnt_cb.cs_n == 1'b0);

      // 采样32位数据
      for (bit_count = 0; bit_count < 32; bit_count++) begin
        @(posedge this.monitor_channel.mnt_cb.sck); // 在时钟上升沿采样数据
        tx_data[bit_count] = this.monitor_channel.mnt_cb.mosi;
        rx_data[bit_count] = this.monitor_channel.mnt_cb.miso;
        @(negedge this.monitor_channel.mnt_cb.sck);
      end

      // 等待片选信号拉高，表示传输结束
      wait (this.monitor_channel.mnt_cb.cs_n == 1'b1);

      // 解析监听到的数据
      put_trans.read = tx_data[31:24] == 8'h01 ? 1'b1 : 1'b0;
      put_trans.wdata = tx_data[15:0];
      put_trans.rdata = rx_data;
      put_trans.addr = {24'h20_0000, tx_data[23:16]};

      // 将解析后的数据发送到scoreboard
      this.mnt2scb.put(put_trans);
    endtask //automatic
  endclass //spi_monitor

  // Agent: The top class that connects generator, driver and monitor
  class spi_agent;
    
    // BUILD
    //=============================================================
    mailbox #(spi_trans)  gen2drv;
    mailbox #(spi_trans)  mnt2scb;
    spi_generator       spi_generator;
    spi_driver        spi_driver;
    spi_monitor       spi_monitor;

    function new();
      this.gen2drv = new(1);
      this.spi_generator = new(this.gen2drv);
      this.spi_driver = new(this.gen2drv);
      this.spi_monitor = new(this.mnt2scb);
    endfunction //new()

    // CONNECT
    //=============================================================
    function void set_intf(
      virtual spi_bus spi
    );   
      // connect to spi_driver
      this.spi_driver.set_intf(spi);
      this.spi_monitor.set_intf(spi);
    endfunction //automatic

    // FUN : single data tran
    //=============================================================
    task automatic single_tran(
      input        read = 1'b1,
      input [15:0] data = 16'h0000,
      input [31:0] addr = 32'h2000_0000
    );
      fork
        begin
          this.spi_generator.data_gen(read, data, addr);  // generate data
          this.spi_driver.data_trans(); // drive data
        end
        this.spi_monitor.data_monitor();  // monitor data
      join
    endtask //automatic
  endclass //spi_agent
endpackage


