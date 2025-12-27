module tb_softmax_in;

  // 输入信号
  logic    clk;
  logic    rst_n;
  logic [15:0] fifo_data;
  logic    fifo_empty;
  
  // 输出信号
  logic    rd_en;
  logic [255:0] data_out;
  logic    ready;
  
  // 测试向量 - 16个16位数
  logic [15:0] test_data [15:0] = '{
    16'h1234, 16'h5678, 16'h9ABC, 16'hDEF0,
    16'h1111, 16'h2222, 16'h3333, 16'h4444,
    16'hAAAA, 16'hBBBB, 16'hCCCC, 16'hDDDD,
    16'hEEEE, 16'hFFFF, 16'h0000, 16'h5555
  };
  
  integer data_index = 0; // 数据索引
  
  // 时钟生成
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // 实例化待测模块
  softmax_in dut (
    .clk(clk),
    .rst_n(rst_n),
    .fifo_data(fifo_data),
    .fifo_empty(fifo_empty),
    .rd_en(rd_en),
    .data_out(data_out),
    .ready(ready)
  );

  // FIFO数据模拟
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fifo_empty <= 1'b1;
      fifo_data <= 16'h0;
    end
    else if (rd_en && (data_index < 16)) begin
      // 模块读取时更新数据
      fifo_data <= test_data[data_index];
      data_index <= data_index + 1;
      fifo_empty <= 1'b0;
    end
    else if (data_index >= 16) begin
      // 所有数据已发送完毕
      fifo_empty <= 1'b1;
    end
  end

  logic [255:0] data_input;
  logic          data_valid;
  logic          data_ready;
  logic [7:0]    data_output[31:0];
  logic          core_ready;

  softmax_core dut_core (
    .clk(clk),
    .rst_n(rst_n),
    .enable(core_ready),
    .data_in(data_input),

    .data_out(data_output),
    .valid_out(data_valid),
    .ready(data_ready)
  );

  // 主测试流程
  initial begin
    // 初始化
    rst_n = 0;
    fifo_empty = 1'b1;
    
    // 复位
    #10 rst_n = 1;
    
    // 设置初始FIFO数据
    #10;
    fifo_data = test_data[0];
    fifo_empty = 1'b0;
    
    // 等待足够长时间以便处理16个数据
    #200;
    
    // 打印结果
    $display("Data out: %h", data_out[127:0]);

    data_input = data_out;
    core_ready = 1'b1;
    #(10);
    core_ready = 1'b0;
    wait (data_valid);
    #(1000)

    $finish;
  end
  
endmodule
