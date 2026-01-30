module binding_module();
  
  bind testbench_top spi_assertion spi_assertion_bind_tb (
    .spi(spi)
  );

  bind testbench_top uart_assertion uart_assertion_bind_tb (
    .uart(uart),
    .tx_state(tx_state),
    .rx_state(rx_state),
    .baud_tick(baud_tick)
  );

  bind testbench_top fifo_assertion #(.fifo_type(1)) tx_fifo_assertion_bind_tb (
    .rst_n(tx_fifo_rst_n),
    .rd_clk(tx_fifo_rd_clk),
    .wr_clk(tx_fifo_wr_clk),

    .empty(tx_fifo_empty),
    .full(tx_fifo_full),

    .wr_en(tx_fifo_wr_en),
    .rd_en(tx_fifo_rd_en),

    .rd_ptr(tx_fifo_rd_ptr),
    .wr_ptr(tx_fifo_wr_ptr)  
  );

  bind testbench_top fifo_assertion #(.fifo_type(0)) rx_fifo_assertion_bind_tb (
    .rst_n(rx_fifo_rst_n),
    .rd_clk(rx_fifo_rd_clk),
    .wr_clk(rx_fifo_wr_clk),

    .empty(rx_fifo_empty),
    .full(rx_fifo_full),

    .wr_en(rx_fifo_wr_en),
    .rd_en(rx_fifo_rd_en),

    .rd_ptr(rx_fifo_rd_ptr),
    .wr_ptr(rx_fifo_wr_ptr)  
  );
endmodule
