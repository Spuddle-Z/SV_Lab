module binding_module();
  
  bind dut_top spi_assertion spi_assertion_bind_dut_top (
    .spi(spi_bus.monitor)
  );

  bind dut_top uart_assertion uart_assertion_bind_dut_top (
    .uart(uart_bus.monitor)
  );

  bind dut_top fifo_assertion #(.fifo_type(0)) tx_fifo_assertion_bind_dut_top (
    .rst_n(i_dut.tx_fifo_inst.rst_n),
    .rd_clk(i_dut.tx_fifo_inst.rd_clk),
    .wr_clk(i_dut.tx_fifo_inst.wr_clk),

    .empty(i_dut.tx_fifo_inst.empty),
    .full(i_dut.tx_fifo_inst.full),

    .wr_en(i_dut.tx_fifo_inst.wr_en),
    .rd_en(i_dut.tx_fifo_inst.rd_en)
  );
