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

// 可综合 ln 估算模块：输入 uq16.8 的 F，输出 sq4.4 的 lnF 近似值
// 步骤：
// 1) LOD 找到整数部分最高位 1 的位置 F1（0 表示 bit15），若整数为 0 则输出 0
// 2) 将 F 左移 F1 位得到 k，丢弃最高位，取其后 4bit 作为小数；w = 15 - F1 作为整数
// 3) 将 {w, fraction} 视为 q4.4，按 0.1011(=11/16≈ln2) 缩放：A*0.6875 = (A>>1)+(A>>3)+(A>>4)
module lnu (
  input  logic [23:0] F,      // uq16.8
  output logic signed [7:0] lnF // sq4.4
);
  logic [4:0]  F1;            // 0..16 (16 means no '1')
  logic signed [4:0]  w;             // 15 - F1
  logic [23:0] k;             // shifted F
  logic [22:0] frac;
  logic signed [27:0] A;             // sq5.23
  logic signed [30:0] scaled;        // sq8.23
  logic signed [30:0] scaled_shift;  // sq8.23 >> 19 -> sq4.4 对齐

  // LOD: leading-zero count on F_int
  always_comb begin
    F1 = 5'd24; // default no bit set
    for (int i = 0; i < 24; i++) begin
      if (F[23 - i] && (F1 == 5'd24)) begin
        F1 = i[4:0];
      end
    end
  end

  always_comb begin
    w    = 5'd15 - F1;
    k    = F << F1;
    frac = k[22:0];
    A    = {w, frac};

    // 乘以 0.1011 (11/16) ≈ ln2
    scaled = (A >>> 1) + (A >>> 3) + (A >>> 4);
    // 对齐到 sq4.4（移除 19 个小数位），再做符号饱和
    scaled_shift = scaled >>> 19; // 保留符号

    if (scaled_shift > 31'sd127) begin
      lnF = 8'sh7F; // 正饱和
    end else if (scaled_shift < -31'sd128) begin
      lnF = 8'sh80; // 负饱和
    end else begin
      lnF = scaled_shift[7:0];
    end
  end
endmodule

// 加法树：16 个 uq12.8 输入，输出 uq16.8
module add_tree (
  input  logic [19:0] in0,
  input  logic [19:0] in1,
  input  logic [19:0] in2,
  input  logic [19:0] in3,
  input  logic [19:0] in4,
  input  logic [19:0] in5,
  input  logic [19:0] in6,
  input  logic [19:0] in7,
  input  logic [19:0] in8,
  input  logic [19:0] in9,
  input  logic [19:0] in10,
  input  logic [19:0] in11,
  input  logic [19:0] in12,
  input  logic [19:0] in13,
  input  logic [19:0] in14,
  input  logic [19:0] in15,
  output logic [23:0] sum    // uq16.8
);
  // 第一层（16->8），每对相加，位宽 21
  logic [20:0] s0, s1, s2, s3, s4, s5, s6, s7;
  // 第二层（8->4），位宽 22
  logic [21:0] t0, t1, t2, t3;
  // 第三层（4->2），位宽 23
  logic [22:0] u0, u1;

  assign s0 = in0  + in1;
  assign s1 = in2  + in3;
  assign s2 = in4  + in5;
  assign s3 = in6  + in7;
  assign s4 = in8  + in9;
  assign s5 = in10 + in11;
  assign s6 = in12 + in13;
  assign s7 = in14 + in15;

  assign t0 = s0 + s1;
  assign t1 = s2 + s3;
  assign t2 = s4 + s5;
  assign t3 = s6 + s7;

  assign u0 = t0 + t1;
  assign u1 = t2 + t3;

  assign sum = u0 + u1;

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
