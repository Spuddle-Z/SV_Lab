module dut #(parameter ID=0) (dut_if if_i, dut_if if_o);

  always @(posedge if_i.clock) begin
    if(if_i.cmd_valid && !if_i.reset)
      $display("[%8t ns] DUT#%1d received: cmd=%b, addr=%x, data=%x.", $time, ID, if_i.cmd, if_i.addr, if_i.data);
  end

  /*
  always @(posedge if_i.clock) begin
    if(if_o.cmd_valid && !if_i.reset)
      $display("[%8t ns] DUT#%1d sent    : cmd=%b, addr=%x, data=%x.", $time, ID, if_o.cmd, if_o.addr, if_o.data);
  end
  */

  always @(posedge if_i.clock or posedge if_i.reset) begin
    if(if_i.reset == 1) begin
      if_o.cmd_valid <= 0;
      if_o.cmd <= 0;
      if_o.addr <= 0;
      if_o.data <= 0;
    end else begin
      if_o.cmd_valid <= if_i.cmd_valid;
      if_o.cmd <= if_i.cmd;
      if_o.addr <= {2'b10, if_i.addr[7:0]};
      if_o.data <= {2'b01, if_i.data[7:0]};
    end
  end

endmodule : dut
