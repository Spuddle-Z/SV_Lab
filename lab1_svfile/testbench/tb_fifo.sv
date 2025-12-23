`timescale 1ns/1ps

module tb_fifo();
  localparam CLK_PERIOD = 20;  // 50MHz
  
  // 信号定义
  logic rd_clk;
  logic wr_clk;
  logic rst_n;
  logic rd_en, wr_en;
  logic [15:0] rd_data, wr_data;
  logic empty, full;
  
  // 实例化FIFO
  fifo dut (
    .rd_clk(rd_clk),
    .wr_clk(wr_clk),
    .rst_n(rst_n),
    .rd_en(rd_en),
    .rd_data(rd_data),
    .wr_en(wr_en),
    .wr_data(wr_data),
    .empty(empty),
    .full(full)
  );
  
  // 时钟生成
  always #(CLK_PERIOD/2) rd_clk = ~rd_clk;
  always #(CLK_PERIOD/2) wr_clk = ~wr_clk;

  // 复位任务
  task reset_dut;
    $display("Applying reset...");
    rst_n = 0;
    #(CLK_PERIOD);
    rst_n = 1;
    #(CLK_PERIOD);
  endtask

  // 单个写入任务
  task write_data(input [15:0] data);
    @(posedge wr_clk);
    wr_data = data;
    wr_en = 1;
    @(posedge wr_clk);
    wr_en = 0;
  endtask

  // 单个读取任务
  task read_data();
    @(posedge rd_clk);
    rd_en = 1;
    @(posedge rd_clk);
    rd_en = 0;
  endtask

  // 写满测试
  task automatic write_full();
    int i;
    for (i = 0; i < 9; i++) begin
      write_data(i);
    end
  endtask

  // 读空测试
  task automatic read_empty();
    int i;
    for (i = 0; i < 9; i++) begin
      read_data();
    end
  endtask

  // 同时读写测试
  task automatic simultaneous_rw();
    fork
      begin
        begin
          for (int i = 4; i < 8; i++) begin
            wr_data = 16'h4000 + i;
            wr_en = 1'b1;
            @(posedge wr_clk);
          end
          wr_en = 1'b0;
        end
      end
        
      begin
        begin
          for (int i = 0; i < 4; i++) begin
            rd_en = 1'b1;
            @(posedge rd_clk);
            rd_en = 1'b0;
          end
        end
      end
    join
  endtask

  initial begin
    // 初始化信号
    rd_clk = 0;
    wr_clk = 1;
    rst_n = 1;
    rd_en = 0;
    wr_en = 0;
    wr_data = 0;

    // 复位
    reset_dut();

    // 单次写入和读取测试
    write_data(16'hA5A5);
    #(CLK_PERIOD);
    read_data();
    $display("Read data: %h", rd_data);

    // 写满测试
    write_full();

    // 读空测试
    read_empty();
    #(CLK_PERIOD * 4);

    // 同时读写测试
    simultaneous_rw();

    // 结束仿真
    $stop;
  end

endmodule
