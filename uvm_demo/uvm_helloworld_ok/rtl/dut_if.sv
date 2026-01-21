interface dut_if(input clock, input reset);

  logic cmd_valid;
  logic cmd;
  logic [9:0] addr;
  logic [9:0] data;

    

endinterface : dut_if
