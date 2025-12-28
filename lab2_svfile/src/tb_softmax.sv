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
      16'h0001, 16'h0384, 16'h0FA0, 16'h2710,
      16'h4E20, 16'h7530, 16'h9C40, 16'hC350,
      16'hEA60, 16'h1117, 16'h3875, 16'h5F8B,
      16'h8692, 16'hADB3, 16'hD4D5, 16'hFBEF
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
  logic         data_valid;
  logic         data_ready;
  logic [7:0]   data_output[31:0];
  logic         core_ready;

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

module softmax_top_tb;

    // 输入信号
    logic        clk;
    logic        rst_n;
    logic [15:0] fifo_data;
    logic        fifo_empty;
    
    // 输出信号
    logic        rd_en;
    logic [15:0] tx_data;
    logic        tx_empty;
    
    // 测试信号
    logic        tx_fifo_en;
    
    // 测试向量 - 16个16位数
    logic [15:0] test_data [15:0] = '{
        16'h0001, 16'h0384, 16'h0FA0, 16'h2710,
        16'h4E20, 16'h7530, 16'h9C40, 16'hC350,
        16'hEA60, 16'h1117, 16'h3875, 16'h5F8B,
        16'h8692, 16'hADB3, 16'hD4D5, 16'hFBEF
    };

    integer data_index = 0;       // 发送到DUT的数据索引
    integer read_data_idx = 0;    // 从DUT读取的数据个数
    logic [15:0] read_data[31:0]; // 存储从DUT读取的数据
    
    // 时钟生成
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // 实例化待测模块
    softmax_top dut (
        .clk(clk),
        .rst_n(rst_n),
        .fifo_data(fifo_data),
        .fifo_empty(fifo_empty),
        .rd_en(rd_en),
        
        .tx_data(tx_data),
        .tx_empty(tx_empty),
        .tx_fifo_en(tx_fifo_en),

        .control(2'b01) // 设置为Softmax处理模式
    );
    
    // 上游FIFO数据模拟
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fifo_empty <= 1'b1;
            fifo_data <= 16'h0;
        end
        else if (rd_en && (data_index < 16)) begin
            // 模块读取时更新数据
            fifo_data <= test_data[data_index];
            data_index <= data_index + 1;
            
            // 如果还有数据，保持非空状态
            fifo_empty <= (data_index == 15) ? 1'b1 : 1'b0;
        end
        else if (data_index >= 16) begin
            // 所有数据已发送完毕
            fifo_empty <= 1'b1;
        end
    end

    // 下游FIFO读取控制
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_fifo_en <= 1'b0;
            read_data_idx <= 0;
        end
        else begin
            // 当下游FIFO非空时，读取数据
            if (!tx_empty) begin
                tx_fifo_en <= 1'b1;
                read_data[read_data_idx] <= tx_data;
                read_data_idx <= read_data_idx + 1;
                $display("Read time=%0t: data=%h (index=%0d)", 
                         $time, tx_data, read_data_idx);
            end
            else begin
                tx_fifo_en <= 1'b0;
            end
        end
    end

    // 主测试流程
    initial begin
        // 初始化
        rst_n = 0;
        fifo_empty = 1'b1;
        tx_fifo_en = 1'b0;
        
        // 复位
        #10 rst_n = 1;

        // 设置初始FIFO数据
        #10;
        fifo_data = test_data[0];
        fifo_empty = 1'b0;  // 拉低empty，表示有数据

        $display("Starting test at time=%0t", $time);
        
        // 等待足够长时间以便处理数据
        wait (!tx_empty);
        #(20);
        
        // 打印结果
        $display("\nTest completed:");
        $display("Sent %0d words to DUT", data_index);
        $display("Received %0d words from DUT", read_data_idx);
        
        if (read_data_idx > 0) begin
            $display("Received data:");
            for (int i = 0; i < read_data_idx; i++) begin
                $display("  [%0d] = %h", i, read_data[i]);
            end
        end
        
        $finish;
    end

endmodule
