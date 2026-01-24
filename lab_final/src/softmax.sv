// 可综合的指数函数模块
module expu (
  input  logic signed [7:0] y,
  input  logic signed [8:0] lnF,
  output logic [19:0]     exp_y
);
  // 计算 diff = y - lnF（保持 q3.4 精度）
  logic signed [9:0] diff;
  assign diff = {{2{y[7]}}, y} - {lnF[8], lnF};

  // 扩展到 10bit，低 4bit 为小数位
  logic signed [10:0] A;
  logic signed [10:0] B;
  logic signed [10:0] D;
  logic [10:0] F;
  logic [10:0] mult_result;

  assign A = {diff[9], diff};
  assign B = A >>> 1;          // A/2
  assign D = A >>> 4;          // A/16
  assign F = ~D;              // 二进制补码的加法对应减去 D
  assign mult_result = A + B + F + 11'd1; // A + B - D = A + B + F + 1

  // 取整数与小数部分，mult_result 仍为 q?.4，小数位固定为 4bit
  logic signed [6:0] u_i;            // 整数部分，最多 6bit
  logic [3:0] v_i;            // 小数部分
  assign u_i = mult_result[10:4];
  assign v_i = mult_result[3:0];

  // 线性拟合 2^v_i，使用 2^x ≈ 1 + x * ln2，ln2≈0.693 -> 0.693*(2^8)/16 ≈ 11
  localparam logic [7:0] LN2_SLOPE = 8'd11; // 斜率在 q0.8 视角下的缩放系数
  logic [25:0] mantissa;     // q0.8 格式的尾数（含 8bit 小数）
  assign mantissa = 26'd246 + (v_i * LN2_SLOPE); // 1.0 对应 256

  // 通过位移乘以 2^u_i，保持 8bit 小数位
  logic [25:0] scaled;
  assign scaled = (u_i >= 0) ? (mantissa <<< u_i) : (mantissa >>> -u_i);

  // 饱和到 uq12.8（20bit）：若溢出则钳位为全 1
  always_comb begin
    if (|scaled[25:20]) begin
      exp_y = 20'hFFFFF;
    end else begin
      exp_y = scaled[19:0];
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

// 可综合 ln 估算模块：输入 uq16.8 的 F，输出 sq4.4 的 lnF 近似值
// 步骤：
// 1) LOD 找到整数部分最高位 1 的位置 F1（0 表示 bit15），若整数为 0 则输出 0
// 2) 将 F 左移 F1 位得到 k，丢弃最高位，取其后 4bit 作为小数；w = 15 - F1 作为整数
// 3) 将 {w, fraction} 视为 q4.4，按 0.1011(=11/16≈ln2) 缩放：A*0.6875 = (A>>1)+(A>>3)+(A>>4)
module lnu (
  input  logic [23:0] F,      // uq16.8
  output logic signed [8:0] lnF // sq5.4
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

    if (scaled_shift > 31'sd255) begin
      lnF = 9'sh0FF; // 正饱和
    end else if (scaled_shift < -31'sd256) begin
      lnF = 9'sh100; // 负饱和
    end else begin
      lnF = scaled_shift[8:0];
    end
  end
endmodule

// 独立 softmax 运算模块：start 拉高读取 128bit，busy 期间计算，两拍后输出并拉低 busy
module softmax (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        start,
  input  logic [127:0] data_in,
  output logic [127:0] data_out,
  output logic        done
);
  // 状态机
  typedef enum logic [1:0] {S_IDLE, S_PHASE0, S_PHASE1} sf_state_t;
  sf_state_t state, state_n;

  // 寄存输入向量
  logic signed [7:0] y[15:0];
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : Y_LATCH
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) y[gi] <= '0;
        else if (start && state == S_IDLE) y[gi] <= data_in[8*gi +: 8];
      end
    end
  endgenerate

  // 共享 expu
  logic signed [8:0] ln_sel;
  logic [19:0]       exp_out[15:0];
  logic [23:0]       sum_exp;
  logic signed [8:0] ln_sum_wire;
  logic signed [8:0] ln_sum_reg;

  generate
    for (gi = 0; gi < 16; gi++) begin : EXP_SHARED
      expu u_expu (
        .y    (y[gi]),
        .lnF  (ln_sel),
        .exp_y(exp_out[gi])
      );
    end
  endgenerate

  // 求和
  add_tree u_add (
    .in0 (exp_out[0]),  .in1 (exp_out[1]),  .in2 (exp_out[2]),  .in3 (exp_out[3]),
    .in4 (exp_out[4]),  .in5 (exp_out[5]),  .in6 (exp_out[6]),  .in7 (exp_out[7]),
    .in8 (exp_out[8]),  .in9 (exp_out[9]),  .in10(exp_out[10]), .in11(exp_out[11]),
    .in12(exp_out[12]), .in13(exp_out[13]), .in14(exp_out[14]), .in15(exp_out[15]),
    .sum (sum_exp)
  );

  // ln(sum)
  lnu u_ln (
    .F  (sum_exp),
    .lnF(ln_sum_wire)
  );

  // ln 选择：第一阶段 ln=0，第二阶段 ln=ln_sum_reg
  always_comb begin
    case (state)
      S_PHASE1: ln_sel = ln_sum_reg;
      default:  ln_sel = 9'sd0;
    endcase
  end

  // 状态机与 busy/done 控制
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state      <= S_IDLE;
      ln_sum_reg <= '0;
      done       <= 1'b0;
    end else begin
      state <= state_n;
      done  <= 1'b0;
      if (state == S_PHASE0)
        ln_sum_reg <= ln_sum_wire; // 锁存 ln(sum)
      if (state == S_PHASE1)
        done <= 1'b1; // 第二阶段完成时拉高 done
    end
  end

  always_comb begin
    state_n = state;
    case (state)
      S_IDLE:   state_n = (start ? S_PHASE0 : S_IDLE);
      S_PHASE0: state_n = S_PHASE1;
      S_PHASE1: state_n = S_IDLE;
      default:  state_n = S_IDLE;
    endcase
  end

  // 输出打包：先组合，再在 S_PHASE1 锁存，避免 S_IDLE/PHASE0 的中间值外泄
  logic [127:0] data_out_next;
  generate
    for (gi = 0; gi < 16; gi++) begin : PACK_OUT
      // 对最低 8bit 概率进行饱和裁剪，防止 >255 溢出
      assign data_out_next[8*gi +: 8] = (exp_out[gi][19:8] != 0) ? 8'hFF : exp_out[gi][7:0];
    end
  endgenerate

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= '0;
    end else if (state == S_PHASE1) begin
      data_out <= data_out_next; // 仅在最终阶段更新输出
    end
  end

endmodule

module softmax_top (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        softmax_en,

  // 上游接口
  input  logic        empty,
  input  logic [15:0] data_in,
  output logic        rd_en,

  // 下游接口
  input  logic        done,
  output logic        valid,
  output logic [127:0] data_out
);
  localparam int PACKET_NUM = 8;

  typedef enum logic [2:0] {
    ST_FILL,       // 等待并收集 8 个 16b 包
    ST_START_SF,   // 发出 softmax start 脉冲
    ST_WAIT_SF,    // 等待 softmax done
    ST_OUTPUT      // 有效数据待下游读取
  } sf_top_state_t;

  sf_top_state_t state, state_n;

  logic [$clog2(PACKET_NUM + 1)-1:0] pack_count, pack_count_n;
  logic [127:0] pack_buffer, pack_buffer_n;
  logic [127:0] data_out_n;
  logic rd_en_n;
  logic rd_cooldown, rd_cooldown_n; // 保证 rd_en 断续（高 1 周期、低 1 周期）
  logic valid_n;
  logic sf_start, sf_start_n;

  // softmax 实例
  logic        sf_done;
  logic [127:0] sf_data_out;

  softmax u_softmax (
    .clk      (clk),
    .rst_n    (rst_n),
    .start    (sf_start),
    .data_in  (pack_buffer),
    .data_out (sf_data_out),
    .done     (sf_done)
  );

  // 状态与寄存器
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state       <= ST_FILL;
      pack_count  <= '0;
      pack_buffer <= '0;
      data_out    <= '0;
      rd_en       <= 1'b0;
      rd_cooldown <= 1'b0;
      valid       <= 1'b0;
      sf_start    <= 1'b0;
    end else begin
      state       <= state_n;
      pack_count  <= pack_count_n;
      pack_buffer <= pack_buffer_n;
      data_out    <= data_out_n;
      rd_en       <= rd_en_n;
      rd_cooldown <= rd_cooldown_n;
      valid       <= valid_n;
      sf_start    <= sf_start_n;
    end
  end

  // 组合逻辑
  always_comb begin
    // 默认保持
    state_n       = state;
    pack_count_n  = pack_count;
    pack_buffer_n = pack_buffer;
    data_out_n    = data_out;
    rd_en_n       = 1'b0;
    rd_cooldown_n = rd_cooldown;
    valid_n       = valid;
    sf_start_n    = 1'b0;

    case (state)
      ST_FILL: begin
        valid_n = 1'b0;
        // rd_en 脉冲后插入一个低周期，避免连续高
        if (rd_cooldown)
          rd_cooldown_n = 1'b0;

        // 收集 8 个 16b 单元
        if (pack_count < PACKET_NUM) begin
          if (!empty && !rd_cooldown) begin
            rd_en_n       = 1'b1;
            pack_buffer_n = {data_in, pack_buffer[127:16]};
            pack_count_n  = pack_count + 1'b1;
            rd_cooldown_n = 1'b1; // 下一拍强制拉低
          end
        end else begin
          // 收齐 8 个字后，根据 softmax_en 决定路径
          if (softmax_en) begin
            state_n = ST_START_SF;
          end else begin
            data_out_n = pack_buffer;
            valid_n    = 1'b1;
            state_n    = ST_OUTPUT;
          end
        end
      end

      ST_START_SF: begin
        // 给 softmax 一个周期的 start 脉冲
        sf_start_n = 1'b1;
        state_n    = ST_WAIT_SF;
      end

      ST_WAIT_SF: begin
        // 等待 softmax 完成，将结果写入 buffer
        if (sf_done) begin
          pack_buffer_n = sf_data_out;
          data_out_n    = sf_data_out;
          valid_n       = 1'b1;
          state_n       = ST_OUTPUT;
        end
      end

      ST_OUTPUT: begin
        // 有效数据保持，等待下游 done
        rd_en_n = 1'b0;
        if (done) begin
          valid_n       = 1'b0;
          pack_count_n  = '0;
          pack_buffer_n = '0;
          state_n       = ST_FILL;
        end
      end

      default: begin
        state_n = ST_FILL;
      end
    endcase
  end

endmodule
