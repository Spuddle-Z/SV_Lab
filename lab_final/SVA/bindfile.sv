module binding_module();
  
  bind dut_top spi_assertion spi_assertion_bind_dut_top (
    .spi(spi_bus.monitor)
  );

  bind dut_top uart_assertion uart_assertion_bind_dut_top (
    .uart(uart_bus.monitor),
    .tx_state(i_dut.uart_ctl_inst.tx_state),
    .rx_state(i_dut.uart_ctl_inst.rx_state),
    .baud_tick(i_dut.uart_ctl_inst.baud_tick)
  );

  bind dut_top fifo_assertion #(.fifo_type(0)) tx_fifo_assertion_bind_dut_top (
    .rst_n(i_dut.tx_fifo_inst.rst_n),
    .rd_clk(i_dut.tx_fifo_inst.rd_clk),
    .wr_clk(i_dut.tx_fifo_inst.wr_clk),

    .empty(i_dut.tx_fifo_inst.empty),
    .full(i_dut.tx_fifo_inst.full),

    .wr_en(i_dut.tx_fifo_inst.wr_en),
    .rd_en(i_dut.tx_fifo_inst.rd_en),

    .rd_ptr(i_dut.tx_fifo_inst.rd_ptr),
    .wr_ptr(i_dut.tx_fifo_inst.wr_ptr)  
  );
endmodule
