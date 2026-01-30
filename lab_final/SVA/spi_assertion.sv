`timescale 1ns/1ps

module spi_assertion (
  spi_bus.monitor   spi
);

  function bit has_x_only(logic value);
    has_x_only = 0;
    if (value === 1'bx) begin  // 使用 === 进行精确比较
      has_x_only = 1;
    end
  endfunction

  // Signal X Assertion
  property spi_sck_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.cs_n |-> not (has_x_only(spi.sck));
  endproperty

  property spi_mosi_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.cs_n |-> not (has_x_only(spi.mosi));
  endproperty

  property spi_miso_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.cs_n |-> not (has_x_only(spi.miso));
  endproperty

  check_spi_sck_no_x: assert property (spi_sck_no_x_check)
    else $error($stime, "\t\t FATAL: SPI SCK exists X when CS_N is low!\n");

  check_spi_mosi_no_x: assert property (spi_mosi_no_x_check)
    else $error($stime, "\t\t FATAL: SPI MOSI exists X when CS_N is low!\n");

  check_spi_miso_no_x: assert property (spi_miso_no_x_check)
    else $error($stime, "\t\t FATAL: SPI MISO exists X when CS_N is low!\n");

  property spi_ss_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    not (has_x_only(spi.cs_n));
  endproperty

  check_spi_ss_no_x: assert property (spi_ss_no_x_check)
    else $error($stime, "\t\t FATAL: SPI CS_N exists X!\n");

  // SPI CPOL与CPHA检查
  property spi_cpol_sck_check;
    @(negedge spi.cs_n) disable iff(!spi.rst_n)
    spi.sck == 1'b0;
  endproperty

  property spi_mosi_stable_check;
    @(posedge spi.clk) disable iff(!spi.rst_n || spi.cs_n)
    $rose(spi.sck)|->$stable(spi.mosi);
  endproperty

  property spi_miso_stable_check;
    @(posedge spi.clk) disable iff(!spi.rst_n || spi.cs_n)
    $rose(spi.sck)|->$stable(spi.miso);
  endproperty

  check_spi_cpol_sck: assert property (spi_cpol_sck_check)
    else $error($stime, "\t\t FATAL: SPI CPOL check failed! SCK should be low when CS_N goes low!\n");

  check_spi_mosi_stable: assert property (spi_mosi_stable_check)
    else $error($stime, "\t\t FATAL: SPI CPHA check failed! MOSI should be stable at SCK rising edge!\n");

  check_spi_miso_stable: assert property (spi_miso_stable_check)
    else $error($stime, "\t\t FATAL: SPI CPHA check failed! MISO should be stable at SCK rising edge!\n");

  // SCK周期与占空比检查
  parameter real CLK_PERIOD_MAX = 10.0;
  parameter real DUTY_CYCLE_MIN = 0.4;

  property spi_sck_period_check;
    real last_time, period;
    @(posedge spi.clk)
    (spi.cs_n == 0 && $rose(spi.sck)) |->
    (1, last_time = $realtime)
    ##1 @(posedge spi.clk)
    (spi.cs_n == 0 && $rose(spi.sck))
    |->
    (1, period = $realtime - last_time)
    |-> period <= CLK_PERIOD_MAX;
  endproperty

  property spi_sck_duty_cycle_check;
    real rise_time, high_time, period;
    @(posedge spi.clk) (spi.cs_n == 0 && $rose(spi.sck)) |->
    (1, rise_time = $realtime)
    ##1 @(negedge spi.clk) (spi.cs_n == 0 && $rose(spi.sck)) |->(1, high_time = $realtime - rise_time)
    ##1 @(posedge spi.clk) (spi.cs_n == 0 && $rose(spi.sck)) |->(1, period = $realtime - rise_time)
    |-> high_time/period >= DUTY_CYCLE_MIN;
  endproperty

  assert_sck_period: assert property (spi_sck_period_check) 
    else $error("SCK period error");

  assert_sck_duty_cycle: assert property (spi_sck_duty_cycle_check) 
    else $error("SCK duty cycle error");

  // CS_N上升沿检测
  property spi_cs_n_rise_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    $rose(spi.cs_n) |-> $past($fell(spi.sck), 1);
  endproperty

  assert_cs_n_rise_check: assert property (spi_cs_n_rise_check)
    else $error("SPI CS_N rise edge check failed: SCK should have a rising edge before CS_N rises.\n");

endmodule