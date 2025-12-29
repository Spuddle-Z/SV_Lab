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
  input logic rd_en
);

  // function logic [3:0] bin2gray(input logic [3:0] bin);
  //   return (bin >> 1) ^ bin;
  // endfunction

// empty and full assertion
  property fifo_empty_check;
    @(posedge rd_clk) disable iff(!rst_n)
    rd_ptr == wr_ptr |-> empty;
  endproperty

  property fifo_full_check;
    @(posedge wr_clk) disable iff(!rst_n)
    ((wr_ptr[2:0] == rd_ptr[2:0]) && (wr_ptr[3]!=rd_ptr[3])) |-> full;
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
    @(posedge rd_clk) disable iff(!rst_n)
    rd_en |=> rd_ptr == ($past(rd_ptr)+1);
  endproperty

  property fifo_wr_function_check;
    @(posedge wr_clk) disable iff(!rst_n)
    wr_en |=> wr_ptr == ($past(wr_ptr)+1);
  endproperty
  
  check_fifo_wr_function: assert property (fifo_rd_function_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO read data error");
    else $error("FATAL : TX FIFO read data error");
  end
  check_fifo_rd_function: assert property (fifo_wr_function_check) else begin
    if(!fifo_type) $error("FATAL : RX FIFO write data error");
    else $error("FATAL : TX FIFO write data error");
  end

// // gray code assertion

//   property fifo_rptr_gray_code_check;
//     @(posedge rclk) disable iff(!rst_n)
//     (rptr!=($past(rptr))) |-> (rptr_gray == bin2gray(rptr));
//   endproperty

//   property fifo_rptr_gray_code_sync1_check;
//     @(posedge rclk) disable iff(!rst_n)
//     (rptr_gray!=($past(rptr_gray))) |=> (rptr_gray_sync1 == ($past(rptr_gray)));
//   endproperty

//   property fifo_rptr_gray_code_sync2_check;
//     @(posedge rclk) disable iff(!rst_n)
//     (rptr_gray_sync1!=($past(rptr_gray_sync1))) |=> (rptr_gray_sync2 == ($past(rptr_gray_sync1)));
//   endproperty

//   property fifo_wptr_gray_code_check;
//     @(posedge wclk) disable iff(!rst_n)
//     (wptr!=($past(wptr))) |-> (wptr_gray == bin2gray(wptr));
//   endproperty

//   property fifo_wptr_gray_code_sync1_check;
//     @(posedge wclk) disable iff(!rst_n)
//     (wptr_gray!=($past(wptr_gray))) |=> (wptr_gray_sync1 == ($past(wptr_gray)));
//   endproperty

//   property fifo_wptr_gray_code_sync2_check;
//     @(posedge wclk) disable iff(!rst_n)
//     (wptr_gray_sync1!=($past(wptr_gray_sync1))) |=> (wptr_gray_sync2 == ($past(wptr_gray_sync1)));
//   endproperty

//   check_fifo_rptr_gray_code: assert property (fifo_rptr_gray_code_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO rptr gray code error");
//     else $error("FATAL : WFIFO rptr gray code error");
//   end

//   check_fifo_rptr_gray_code_sync1: assert property (fifo_rptr_gray_code_sync1_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO rptr gray code sync1 error");
//     else $error("FATAL : WFIFO rptr gray code sync1 error");
//   end

//   check_fifo_rptr_gray_code_sync2: assert property (fifo_rptr_gray_code_sync2_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO rptr gray code sync2 error");
//     else $error("FATAL : WFIFO rptr gray code sync2 error");
//   end

//   check_fifo_wptr_gray_code: assert property (fifo_wptr_gray_code_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO wptr gray code error");
//     else $error("FATAL : WFIFO wptr gray code error");
//   end

//   check_fifo_wptr_gray_code_sync1: assert property (fifo_wptr_gray_code_sync1_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO wptr gray code sync1 error");
//     else $error("FATAL : WFIFO wptr gray code sync1 error");
//   end

//   check_fifo_wptr_gray_code_sync2: assert property (fifo_wptr_gray_code_sync2_check) else begin
//     if(!fifo_type) $error("FATAL : RFIFO wptr gray code sync2 error");
//     else $error("FATAL : WFIFO wptr gray code sync2 error");
//   end


endmodule