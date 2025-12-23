module fifo(
  // 时钟信号
  input  logic rst_n,   // 复位信号
  input  logic rd_clk,  // 读时钟
  input  logic wr_clk,  // 写时钟

  // FIFO状态
  output logic empty,
  output logic full,

  // 接口信号
  output logic [15:0] rd_data,
  input  logic rd_en,
  input  logic [15:0] wr_data,
  input  logic wr_en
);
  logic [15:0] mem [0:7];
  logic [3:0] wr_ptr, rd_ptr;
  logic [3:0] wr_ptr_gray, rd_ptr_gray;
  logic [3:0] rd_ptr_gray_sync, wr_ptr_gray_sync;

  // 写操作
  always_ff @(posedge wr_clk or negedge rst_n) begin
    if (!rst_n) begin
      // 复位信号
      wr_ptr <= 0;
    end else if (wr_en && !full) begin
      mem[wr_ptr[2:0]] <= wr_data;
      wr_ptr <= wr_ptr + 1;
    end
  end

  // 读操作
  always_ff @(posedge rd_clk or negedge rst_n) begin
    if (!rst_n) begin
      // 复位信号
      rd_ptr <= 0;
    end else if (rd_en && !empty) begin
      rd_ptr <= rd_ptr + 1;
    end
  end

  // 二进制转化为格雷码
  function logic [3:0] bin2gray(input logic [3:0] bin);
    return (bin >> 1) ^ bin;
  endfunction

  assign wr_ptr_gray = bin2gray(wr_ptr);
  assign rd_ptr_gray = bin2gray(rd_ptr);

  // 同步写指针到读时钟域
  always_ff @(posedge rd_clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr_gray_sync <= 0;
    end else begin
      wr_ptr_gray_sync <= wr_ptr_gray;
    end
  end

  // 同步读指针到写时钟域
  always_ff @(posedge wr_clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr_gray_sync <= 0;
    end else begin
      rd_ptr_gray_sync <= rd_ptr_gray;
    end
  end

  // 空标志与满标志逻辑
  assign empty = (rd_ptr_gray_sync == wr_ptr_gray_sync);
  assign full = (wr_ptr_gray_sync == {~rd_ptr_gray_sync[3:2], rd_ptr_gray_sync[1:0]});

  // 读取数据即时反映当前读指针指向的存储内容
  assign rd_data = mem[rd_ptr[2:0]];

endmodule
