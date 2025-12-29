`timescale 1ns/1ps

module spi_assertion (
  spi_bus.monitor   spi
);

  // Signal X Assertion
  property spi_sck_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.mnt_cb.cs_n |-> not ($isunknown(spi.mnt_cb.sck));
  endproperty

  property spi_mosi_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.mnt_cb.cs_n |-> not ($isunknown(spi.mnt_cb.mosi));
  endproperty

  property spi_miso_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    !spi.mnt_cb.cs_n |-> not ($isunknown(spi.mnt_cb.miso));
  endproperty

  check_spi_sck_no_x: assert property (spi_sck_no_x_check)
    else $error($stime, "\t\t FATAL: SPI SCK exists X when CS_N is low!\n");

  check_spi_mosi_no_x: assert property (spi_mosi_no_x_check)
    else $error($stime, "\t\t FATAL: SPI MOSI exists X when CS_N is low!\n");

  check_spi_miso_no_x: assert property (spi_miso_no_x_check)
    else $error($stime, "\t\t FATAL: SPI MISO exists X when CS_N is low!\n");

  property spi_ss_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    not ($isunknown(spi.mnt_cb.cs_n));
  endproperty

  check_spi_ss_no_x: assert property (spi_ss_no_x_check)
    else $error($stime, "\t\t FATAL: SPI CS_N exists X!\n");

  // SPI CPOL与CPHA检查
  property spi_cpol_sck_check;
    @(negedge spi.mnt_cb.cs_n) disable iff(!spi.rst_n)
    spi.mnt_cb.sck == 1'b0;
  endproperty

  property spi_mosi_stable_check;
    @(posedge spi.mnt_cb.sck) disable iff(!spi.rst_n || spi.mnt_cb.cs_n)
    $stable(spi.mnt_cb.mosi);

  check_spi_cpol_sck: assert property (spi_cpol_sck_check)
    else $error($stime, "\t\t FATAL: SPI CPOL check failed! SCK should be low when CS_N goes low!\n");













  property spi_cmd_read_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    spi.spi_cmd_valid |-> (not ($isunknown(spi.spi_cmd_read)));
  endproperty

  property spi_cmd_wdata_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_cmd_valid && !spi.spi_cmd_read) |-> (not ($isunknown(spi.spi_cmd_wdata)));
  endproperty

  property spi_cmd_wmask_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_cmd_valid && !spi.spi_cmd_read) |-> (not ($isunknown(spi.spi_cmd_wmask)));
  endproperty

  property spi_rsp_valid_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    not ($isunknown(spi.spi_rsp_valid));
  endproperty

  property spi_rsp_ready_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    not ($isunknown(spi.spi_rsp_ready));
  endproperty

  property spi_rsp_rdata_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_rsp_valid && cmd) |-> (not ($isunknown(spi.spi_rsp_rdata)));
  endproperty

  property spi_rsp_err_no_x_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    spi.spi_rsp_valid |-> (not ($isunknown(spi.spi_rsp_err)));
  endproperty

  check_spi_cmd_valid_no_x: assert property (spi_cmd_valid_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_valid exists X!\n");
  check_spi_cmd_ready_no_x: assert property (spi_cmd_ready_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_ready exists X!\n");
  check_spi_cmd_addr_no_x: assert property (spi_cmd_addr_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_addr exists X!\n");
	check_spi_cmd_read_no_x: assert property (spi_cmd_read_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_read exists X!\n");
  check_spi_cmd_wdata_no_x: assert property (spi_cmd_wdata_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_wdata exists X!\n");
	check_spi_cmd_wmask_no_x: assert property (spi_cmd_wmask_no_x_check) else $error($stime, "\t\t FATAL: spi_cmd_wmask exists X!\n");
	check_spi_rsp_valid_no_x: assert property (spi_rsp_valid_no_x_check) else $error($stime, "\t\t FATAL: spi_rsp_valid exists X!\n");
	check_spi_rsp_ready_no_x: assert property (spi_rsp_ready_no_x_check) else $error($stime, "\t\t FATAL: spi_rsp_ready exists X!\n");
  check_spi_rsp_rdata_no_x: assert property (spi_rsp_rdata_no_x_check) else $error($stime, "\t\t FATAL: spi_rsp_rdata exists X!\n");
  check_spi_rsp_err_no_x: assert property (spi_rsp_err_no_x_check) else $error($stime, "\t\t FATAL: spi_rsp_err exists X!\n");

  
// Signals keep while valid and no handshake
  property spi_cmd_addr_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_cmd_valid && !spi.spi_cmd_ready) |=>  $stable(spi.spi_cmd_addr);
  endproperty

	property spi_cmd_read_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_cmd_valid && !spi.spi_cmd_ready) |=>  $stable(spi.spi_cmd_read);
  endproperty

	property spi_cmd_wmask_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    ($past(spi.spi_cmd_valid && !spi.spi_cmd_ready) and !spi.spi_cmd_read) |->  $stable(spi.spi_cmd_wmask);
  endproperty
  
  property spi_cmd_wdata_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    ($past(spi.spi_cmd_valid && !spi.spi_cmd_ready) and !spi.spi_cmd_read) |->  $stable(spi.spi_cmd_wdata);
  endproperty

  property spi_rsp_err_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_rsp_valid && !spi.spi_rsp_ready) |=>  $stable(spi.spi_rsp_err);
  endproperty

	property spi_rsp_rdata_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_rsp_valid && !spi.spi_rsp_ready && cmd) |=>  $stable(spi.spi_rsp_rdata);
    //(spi.spi_cmd_valid && spi.spi_cmd_ready && spi.spi_cmd_read) |-> ##[0:$] ($stable(spi.spi_rsp_rdata) throughout ($past(spi.spi_rsp_valid))[*0:$]);
  endproperty

  check_spi_cmd_addr_keep: assert property (spi_cmd_addr_keep_check) else $error($stime, "\t\t FATAL: spi_cmd_addr does not keep!\n");
  check_spi_cmd_read_keep: assert property (spi_cmd_read_keep_check) else $error($stime, "\t\t FATAL: spi_cmd_read does not keep!\n");
  check_spi_cmd_wmask_keep: assert property (spi_cmd_wmask_keep_check) else $error($stime, "\t\t FATAL: spi_cmd_wmask does not keep!\n");
  check_spi_cmd_wdata_keep: assert property (spi_cmd_wdata_keep_check) else $error($stime, "\t\t FATAL: spi_cmd_wdata does not keep!\n");
  check_spi_rsp_err_keep: assert property (spi_rsp_err_keep_check) else $error($stime, "\t\t FATAL: spi_rsp_err does not keep!\n");
  check_spi_rsp_rdata_keep: assert property (spi_rsp_rdata_keep_check) else $error($stime, "\t\t FATAL: spi_rsp_rdata does not keep!\n");

// Valid must keep before handshaking
  property spi_cmd_valid_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_cmd_valid && !spi.spi_cmd_ready) |=> spi.spi_cmd_valid;
  endproperty 

  property spi_rsp_valid_keep_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (spi.spi_rsp_valid && !spi.spi_rsp_ready) |=> spi.spi_rsp_valid;
  endproperty
  
  check_spi_cmd_valid_keep: assert property (spi_cmd_valid_keep_check) else $error($stime, "\t\t FATAL: spi_cmd_valid does not keep!\n");
  check_spi_rsp_valid_keep: assert property (spi_rsp_valid_keep_check) else $error($stime, "\t\t FATAL: spi_rsp_valid does not keep!\n");

// Handshake
  property spi_cmd_handshake_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (($rose(spi.spi_cmd_valid)) or ($past(spi.spi_cmd_valid && spi.spi_cmd_ready) && spi.spi_cmd_valid)) |-> ##[0:$] spi.spi_cmd_valid && spi.spi_cmd_ready;
  endproperty

  property spi_rsp_handshake_check;
    @(posedge spi.clk) disable iff(!spi.rst_n)
    (($rose(spi.spi_rsp_valid)) or ($past(spi.spi_rsp_valid && spi.spi_rsp_ready) && spi.spi_rsp_valid)) |-> ##[0:$] spi.spi_rsp_valid && spi.spi_rsp_ready;
  endproperty

  check_spi_cmd_handshake: assert property (spi_cmd_handshake_check) else $error($stime, "\t\t FATAL: spi CMD Channel does not handshake!\n");
  check_spi_rsp_handshake: assert property (spi_rsp_handshake_check) else $error($stime, "\t\t FATAL: spi RSP Channel does not handshake!\n");

  bit cmd;

  always_ff @(spi.clk) begin
    if (spi.spi_cmd_valid && spi.spi_cmd_ready)
      cmd <= spi.spi_cmd_read;
    else
      cmd <= cmd;
  end
  
endmodule