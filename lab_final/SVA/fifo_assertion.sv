`timescale 1ns/1ps

module fifo_assertion #(
  parameter fifo_type = 0
)
(
  input logic rd_clk,
  input logic wr_clk,
  input logic rst_n,
  input logic empty,
  input logic full,
  input logic wr_en,
  input logic rd_en,
  input logic [3:0] rd_ptr,
  input logic [3:0] wr_ptr
);

// empty and full assertion
  property fifo_empty_check;
    @(posedge rd_clk) disable iff(!rst_n)
    rd_ptr == wr_ptr |=> empty;
  endproperty

  property fifo_full_check;
    @(posedge wr_clk) disable iff(!rst_n)
    ((wr_ptr[2:0] == rd_ptr[2:0]) && (wr_ptr[3]!=rd_ptr[3])) |=> full;
  endproperty

  check_fifo_empty: assert property (fifo_empty_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO empty check failed");
    else $error("FATAL : TX FIFO empty check failed");
  end
  check_fifo_full: assert property (fifo_full_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO full check failed");
    else $error("FATAL : TX FIFO full check failed");
  end

// wr and rd function assertion
  property fifo_rd_function_check;
    @(posedge rd_clk) disable iff(!rst_n || empty)
    rd_en |=> rd_ptr == ($past(rd_ptr)+1);
  endproperty

  property fifo_wr_function_check;
    @(posedge wr_clk) disable iff(!rst_n || full)
    wr_en |=> wr_ptr == ($past(wr_ptr)+1);
  endproperty
  
  check_fifo_rd_function: assert property (fifo_rd_function_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO read data error");
    else $error("FATAL : TX FIFO read data error");
  end
  check_fifo_wr_function: assert property (fifo_wr_function_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO write data error");
    else $error("FATAL : TX FIFO write data error");
  end

endmodule