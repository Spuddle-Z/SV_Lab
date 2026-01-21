`timescale 1ns/1ps

module uart_assertion (
  uart_bus.monitor   uart,
  input logic [1:0] tx_state,
  input logic [1:0] rx_state,
  input logic baud_tick
);

  // Signal X Assertion
  property uart_tx_no_x_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    not ($isunknown(uart.tx));
  endproperty

  property uart_rx_no_x_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    not ($isunknown(uart.rx));
  endproperty

  check_uart_tx_no_x: assert property (uart_tx_no_x_check)
    else $error($stime, "\t\t FATAL: UART TX exists X!\n");
  check_uart_rx_no_x: assert property (uart_rx_no_x_check)
    else $error($stime, "\t\t FATAL: UART RX exists X!\n");

  // UART State Check
  property uart_tx_state_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    (tx_state == 2'b00) |-> (uart.tx == 1'b1) and
    (tx_state == 2'b01) |-> (uart.tx == 1'b0)
  endproperty

  property uart_rx_state_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    (rx_state == 2'b00) |-> (uart.rx == 1'b1) and
    (rx_state == 2'b01) |-> (uart.rx == 1'b0)
  endproperty

  check_uart_tx_state: assert property (uart_tx_state_check)
    else $error($stime, "\t\t FATAL: UART TX state check failed!\n");

  check_uart_rx_state: assert property (uart_rx_state_check)
    else $error($stime, "\t\t FATAL: UART RX state check failed!\n");

  // UART Baud Rate Check
  property uart_baud_rate_check;
      real last_time, period;
      @(posedge uart.clk) disable iff(!uart.rst_n)
      ($rose(baud_tick), last_time = $realtime) |=> 
      @(posedge uart.clk)
      ##1
      ($rose(baud_tick), period = $realtime - last_time) |->
      period <= 'h0036;
  endproperty

  assert_uart_baud_rate: assert property (uart_baud_rate_check)
    else $error($stime, "\t\t FATAL: UART baud rate check failed!\n");

  // 检查起始位和停止位
  property check_uart_start_stop;
    @(posedge uart.clk) disable iff (!uart.rst_n)
    // 检测到起始位后，在停止位时间检查停止位
    $rose(baud_tick) && (uart.rx == 0)  // 起始位
    |=> ##9 (uart.rx == 1);             // 停止位（第 10 个位）
  endproperty

  assert_uart_start_stop: assert property (check_uart_start_stop)
    else $error($stime, "\t\t FATAL: UART start/stop bit check failed!\n");

  // Stability Check
  property uart_tx_stability_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    $stable(uart.tx) |-> !$rose(baud_tick);
  endproperty

  property uart_rx_stability_check;
    @(posedge uart.clk) disable iff(!uart.rst_n)
    $stable(uart.rx) |-> !$rose(baud_tick);
  endproperty

  check_uart_tx_stability: assert property (uart_tx_stability_check)
    else $error($stime, "\t\t FATAL: UART TX stability check failed!\n");

  check_uart_rx_stability: assert property (uart_rx_stability_check)
    else $error($stime, "\t\t FATAL: UART RX stability check failed!\n");

endmodule