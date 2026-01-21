module data_packer (
  input  logic         clk,
  input  logic         rst_n,

  // 上游接口
  input  logic         empty, // 上游数据为空标志
  input  logic [15:0]  data_in, // 上游数据
  output logic         enable,  // 读使能信号

  // 下游接口
  output logic         valid,   // 数据打包完成标志
  output logic [127:0] data_out // 输出数据 (16bit * 8 = 128bit)
);

  // 定义参数
  localparam DATA_WIDTH = 16;
  localparam PACKET_NUM = 8;
  
  // 计数器：用于记录已接收的数据包数量
  logic [$clog2(PACKET_NUM + 1)-1:0] count;
  
  // 内部移位寄存器：用于拼接数据
  logic [DATA_WIDTH * PACKET_NUM - 1:0] buffer;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count  <= '0;
      enable <= 1'b0;
      valid  <= 1'b0;
      buffer <= '0;
    end else begin
      valid  <= 1'b0;

      if (count < PACKET_NUM) begin
        if (!empty && !enable) begin
          enable <= 1'b1;
          buffer <= {data_in, buffer[127:16]};
          count  <= count + 1'b1;
        end else begin
          enable <= 1'b0;
        end
      end else begin
        valid <= 1'b1;
        count <= '0;
        enable <= 1'b0;
      end
    end
  end

  assign data_out = buffer;

endmodule

// 可综合的指数函数模块
module expu (
  input  logic signed [7:0] y,
  input  logic signed [7:0] lnF,
  output logic [19:0]     exp_y
);
  // 计算 diff = y - lnF（保持 q3.4 精度）
  logic signed [8:0] diff;
  assign diff = {y[7], y} - {lnF[7], lnF};

  // 扩展到 10bit，低 4bit 为小数位
  logic signed [9:0] A;
  logic signed [9:0] B;
  logic signed [9:0] D;
  logic [9:0] F;
  logic [9:0] mult_result;

  assign A = {diff[8], diff};
  assign B = A >>> 1;          // A/2
  assign D = A >>> 4;          // A/16
  assign F = ~D;              // 二进制补码的加法对应减去 D
  assign mult_result = A + B + F + 10'd1; // A + B - D = A + B + F + 1

  // 取整数与小数部分，mult_result 仍为 q?.4，小数位固定为 4bit
  logic signed [5:0] u_i;            // 整数部分，最多 6bit
  logic [3:0] v_i;            // 小数部分
  assign u_i = mult_result[9:4];
  assign v_i = mult_result[3:0];

  // 线性拟合 2^v_i，使用 2^x ≈ 1 + x * ln2，ln2≈0.693 -> 0.693*(2^8)/16 ≈ 11
  localparam logic [7:0] LN2_SLOPE = 8'd11; // 斜率在 q0.8 视角下的缩放系数
  logic [25:0] mantissa;     // q0.8 格式的尾数（含 8bit 小数）
  assign mantissa = 26'd256 + (v_i * LN2_SLOPE); // 1.0 对应 256

  // 通过位移乘以 2^u_i，保持 8bit 小数位
  logic [25:0] scaled;
  assign scaled = (u_i >= 0) ? (mantissa << u_i) : (mantissa >> -u_i);

  // 饱和到 uq12.8（20bit）：若溢出则钳位为全 1
  always_comb begin
    if (|scaled[25:20]) begin
      exp_y = 20'hFFFFF;
    end else begin
      exp_y = scaled[19:0];
    end
  end
endmodule

module softmax_out (
    input  logic        clk,         // 时钟信号，上升沿有效
    input  logic        rst_n,       // 复位信号，低电平有效
    input  logic [7:0]  data_out[31:0], // 输入数据数组，32个8位数据
    input  logic        valid_out,   // 输入数据有效指示，高电平时表示数据可用
    output logic [15:0] tx_data,     // 输出16位数据，发送到下游
    output logic        tx_empty,    // 输出缓冲区空指示，高电平时表示无数据可发送
    input  logic        tx_fifo_en   // 下游FIFO使能信号，高电平时请求读取数据
);

  // 内部数据缓冲区，存储16个16位数据
  logic [15:0] data_buffer[15:0];
  // 数据指针，指示下一个要发送的数据索引（0-15），当为5'd16时表示缓冲区为空
  logic [4:0] ptr;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // 复位初始化
      ptr <= 5'd16;               // 指针设为16，表示缓冲区空
      tx_empty <= 1'b1;           // 空标志置高
      tx_data <= 16'b0;           // 输出数据清零（可选）
      // 可选：初始化缓冲区为0，但并非必需
      for (int i = 0; i < 16; i++) begin
        data_buffer[i] <= 16'b0;
      end
    end else begin
      // 处理valid_out信号：当valid_out为高时，加载新数据到缓冲区
      if (valid_out) begin
        // 将32个8位数据两两组合成16个16位数据
        // 假设data_out[0]为第一个字节（低8位），data_out[1]为第二个字节（高8位），依此类推
        for (int i = 0; i < 16; i++) begin
          data_buffer[i] <= {data_out[2*i+1], data_out[2*i]};
        end
        ptr <= 5'd0;            // 重置指针到缓冲区起始位置
        tx_empty <= 1'b0;       // 缓冲区中有数据，空标志置低
      end

      if (tx_fifo_en && !tx_empty) begin
        // 输出当前指针指向的数据
        tx_data <= data_buffer[ptr];
        // 指针递增，准备下一个数据
        ptr <= ptr + 1;
        // 检查是否所有数据都已发送
        if (ptr == 5'd15) begin // 如果发送前指针为15，发送后缓冲区将为空
          tx_empty <= 1'b1;   // 缓冲区空，设置空标志
        end
      end
    end
  end

endmodule

module softmax_top (
  // 系统接口
  input  logic        clk,
  input  logic        rst_n,
  
  // 上游FIFO接口（连接到softmax_in）
  input  logic [15:0] fifo_data,
  input  logic        fifo_empty,
  output logic        rd_en,
  
  // 下游FIFO接口（连接到softmax_out）
  output logic [15:0] tx_data,
  output logic        tx_empty,
  input  logic        tx_fifo_en,

  // 控制信号
  input  logic [1:0] control
);

    // ================= 模块间连接信号 =================
    
    // softmax_in 到 softmax_core 的信号
    logic [255:0] softmax_in_data_out;   // 256位输出数据
    logic         softmax_in_ready;      // 数据准备好标志
    
    // softmax_core 到 softmax_out 的信号
    logic [7:0]   softmax_core_data_out[31:0];  // 32个8位输出数据
    logic         softmax_core_valid_out;       // 输出有效标志
    
    // softmax_core 内部模块信号
    logic [7:0]   unpacked_core_data_out[31:0]; // 用于信号解包

    // 片选信号定义
    logic softmax_rd_en;
    logic [15:0] softmax_result;
    logic softmax_result_empty;

    // ================= softmax_in 实例化 =================
    // 该模块从上游FIFO读取16位数据，组装成256位数据流
    softmax_in u_softmax_in (
        .clk       (clk),
        .rst_n     (rst_n),
        .fifo_data (fifo_data),
        .fifo_empty(fifo_empty),
        .rd_en     (softmax_rd_en),
        .data_out  (softmax_in_data_out),
        .ready     (softmax_in_ready)
    );

    // ================= softmax_core 实例化 =================
    // 该模块执行softmax计算，接受256位输入，输出32个8位数据
    softmax_core #(
        .DATA_WIDTH        (8),
        .VECTOR_SIZE       (32),
        .CORDIC_ITER       (16),
        .CORDIC_WIDTH      (18),
        .ACC_WIDTH         (20),
        .FIXED_POINT_FRAC  (12)
    ) u_softmax_core (
        .clk      (clk),
        .rst_n    (rst_n),
        .enable   (softmax_in_ready),         // softmax_in准备就绪时启动计算
        .data_in  (softmax_in_data_out),      // 256位输入数据
        .data_out (unpacked_core_data_out),   // 32个8位输出数据
        .valid_out(softmax_core_valid_out)    // 计算结果有效标志
    );

    // 将解包的数组信号分配给连接信号
    generate
        for (genvar i = 0; i < 32; i++) begin : assign_data_out
            assign softmax_core_data_out[i] = unpacked_core_data_out[i];
        end
    endgenerate

    // ================= softmax_out 实例化 =================
    // 该模块将32个8位数据转换成16位数据流输出
    softmax_out u_softmax_out (
        .clk       (clk),
        .rst_n     (rst_n),
        .data_out  (softmax_core_data_out),   // 32个8位输入数据
        .valid_out (softmax_core_valid_out),  // 输入数据有效标志
        .tx_data   (softmax_result),                 // 16位输出数据
        .tx_empty  (softmax_result_empty),                // 输出缓冲区空标志
        .tx_fifo_en(tx_fifo_en)               // 下游FIFO使能信号
    );

    // ================= 直通模式逻辑 =================
    // 当 control=00 时，直接将上游FIFO连接到下游FIFO
    logic bypass_mode;
    assign bypass_mode = (control == 2'b00);

    // 读使能选择
    assign rd_en = bypass_mode ? tx_fifo_en : softmax_rd_en;

    // 发送数据选择
    assign tx_data = bypass_mode ? fifo_data : softmax_result;

    // 发送空标志选择
    assign tx_empty = bypass_mode ? fifo_empty : softmax_result_empty;

endmodule
