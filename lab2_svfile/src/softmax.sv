module softmax_in (
  input  logic     clk,
  input  logic     rst_n,
  input  logic [15:0]  fifo_data,
  input  logic     fifo_empty,
  
  output logic     rd_en,
  output logic [255:0] data_out,
  output logic     ready
);

  // 内部状态定义
  typedef enum logic [1:0] {
    IDLE,
    COLLECT,
    READY
  } state_t;

  state_t state;
  logic [5:0] count;    // 计数0-7，对应8个16位数据

  // 状态转移逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      count <= 6'b0;
      data_out <= '0;
    end else begin
      rd_en <= 1'b0;
      ready <= 1'b0;
      if (!fifo_empty) begin
        data_out <= {fifo_data, data_out[255:16]};
        count <= count + 1'b1;
        rd_en <= 1'b1;
        if (count == 6'b10_0000) begin
          state <= READY;
          count <= 6'b0;
          ready <= 1'b1;
        end
      end
    end
  end
endmodule

module softmax_core #(
  parameter DATA_WIDTH = 8,
  parameter VECTOR_SIZE = 32,
  parameter CORDIC_ITER = 16,     // CORDIC迭代次数
  parameter CORDIC_WIDTH = 18,    // CORDIC内部位宽
  parameter ACC_WIDTH = 20,
  parameter FIXED_POINT_FRAC = 12 // 定点数小数部分位宽
)(
  // 时钟和复位
  input logic clk,
  input logic rst_n,
  
  // 控制信号
  input logic enable,
  input logic signed [DATA_WIDTH*VECTOR_SIZE-1:0] data_in,
  
  // 输出
  output logic [DATA_WIDTH-1:0] data_out[VECTOR_SIZE-1:0],
  output logic valid_out,
  output logic ready
);

  // === 内部状态定义 ===
  enum logic [2:0] {
    IDLE          = 3'b000,
    FIND_MAX      = 3'b001,
    SHIFT_VALUES  = 3'b010,
    CALC_EXP      = 3'b011,
    CALC_SUM      = 3'b100,
    CALC_DIV      = 3'b101
  } state, next_state;
  
  // === 内部变量定义 ===
  logic signed [DATA_WIDTH-1:0] data_buffer[VECTOR_SIZE-1:0];
  logic signed [DATA_WIDTH-1:0] max_value;
  logic signed [CORDIC_WIDTH-1:0] shifted_values[VECTOR_SIZE-1:0];
  logic [ACC_WIDTH-1:0] exp_values[VECTOR_SIZE-1:0];
  logic [ACC_WIDTH-1:0] sum_exp;
  logic [DATA_WIDTH-1:0] output_reg[VECTOR_SIZE-1:0];
  logic valid_reg;
  
  logic [4:0] vector_counter;  // 向量索引计数器 (扩展到5位以支持VECTOR_SIZE=16)
  logic [4:0] cordic_counter;  // CORDIC迭代计数器
  logic cordic_done;
  
  // === CORDIC算法相关参数 ===
  // CORDIC双曲模式旋转角度查找表 (atanh(2^-i))
  logic signed [CORDIC_WIDTH-1:0] atanh_lut[0:CORDIC_ITER-1];
  
  // CORDIC缩放因子补偿查找表
  logic signed [CORDIC_WIDTH-1:0] cordic_scale_lut[0:CORDIC_ITER-1];
  
  // CORDIC双曲模式常数K (K = ∏(1-2^(-2i))^(-1/2))
  logic signed [CORDIC_WIDTH-1:0] K_CONSTANT;
  
  // === CORDIC迭代寄存器 ===
  logic signed [CORDIC_WIDTH-1:0] cordic_x, cordic_y, cordic_z;
  logic cordic_mode; // 0:指数模式, 1:除法模式
  logic cordic_dir;  // 旋转方向
  
  // === 定点数转换辅助函数 ===
  function logic signed [CORDIC_WIDTH-1:0] to_fixed(logic signed [DATA_WIDTH-1:0] val);
    return val << FIXED_POINT_FRAC;
  endfunction
  
  function logic signed [DATA_WIDTH-1:0] from_fixed(logic signed [CORDIC_WIDTH-1:0] val);
    return val >> FIXED_POINT_FRAC;
  endfunction
  
  // === 在initial块内部使用的变量声明 ===
  real atanh_val, scale_val, k_val;
  
  // === 初始化CORDIC查找表 ===
  initial begin
    // 初始化atanh查找表
    for (int i = 0; i < CORDIC_ITER; i++) begin
      // 避免除零错误，对i=0做特殊处理
      if (i == 0) begin
        atanh_val = 0.5493061443; // atanh(1) ≈ 无穷大，实际使用近似值
      end else begin
        atanh_val = $ln((1.0 + 2.0**(-i)) / (1.0 - 2.0**(-i))) / 2.0;
      end
      atanh_lut[i] = atanh_val * (1 << FIXED_POINT_FRAC);
    end
    
    // 初始化CORDIC缩放因子查找表
    scale_val = 1.0;
    for (int i = 0; i < CORDIC_ITER; i++) begin
      scale_val = scale_val * $sqrt(1.0 - 2.0**(-2*i));
      cordic_scale_lut[i] = scale_val * (1 << (FIXED_POINT_FRAC));
    end
    
    // 计算K_CONSTANT (1/K)
    k_val = 1.0;
    for (int i = 1; i < CORDIC_ITER + 1; i++) begin
      k_val = k_val * $sqrt(1.0 - 2.0**(-2*i));
    end
    K_CONSTANT = (1.0 / k_val) * (1 << FIXED_POINT_FRAC);
  end
  
  // === 查找最大值模块 ===
  function logic signed [DATA_WIDTH-1:0] find_max(logic signed [DATA_WIDTH-1:0] data_array[VECTOR_SIZE-1:0]);
    logic signed [DATA_WIDTH-1:0] max_val;
    max_val = data_array[0];
    for (int i = 1; i < VECTOR_SIZE; i++) begin
      if (data_array[i] > max_val)
        max_val = data_array[i];
    end
    return max_val;
  endfunction
  
  // === 在always_ff块中使用的局部变量 ===
  logic signed [ACC_WIDTH-1:0] reciprocal;
  logic [ACC_WIDTH*2-1:0] scaled_result;
  
  // === 状态机更新 ===
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      valid_reg <= 0;
      vector_counter <= 0;
      cordic_counter <= 0;
      cordic_done <= 0;
      max_value <= 0;
      
      // 初始化CORDIC寄存器
      cordic_x <= 0;
      cordic_y <= 0;
      cordic_z <= 0;
      cordic_mode <= 0;
      cordic_dir <= 0;
      
      for (int i = 0; i < VECTOR_SIZE; i++) begin
        data_buffer[i] <= 0;
        shifted_values[i] <= 0;
        exp_values[i] <= 0;
        output_reg[i] <= 0;
      end
    end else begin
      state <= next_state;
      valid_reg <= (state == CALC_DIV && vector_counter == VECTOR_SIZE-1);
      
      case (state)
        IDLE: begin
          if (enable) begin
            // 缓存输入数据
            for (int i = 0; i < VECTOR_SIZE; i++) begin
              data_buffer[i] <= data_in[(i+1)*DATA_WIDTH-1 -: DATA_WIDTH];
            end
            vector_counter <= 0;
            cordic_counter <= 0;
            cordic_done <= 0;
          end
          sum_exp <= 0;
        end
        
        FIND_MAX: begin
          // 查找最大值（流水线式）
          if (vector_counter == 0) begin
            max_value <= data_buffer[0];
            vector_counter <= 1;
          end else if (vector_counter < VECTOR_SIZE) begin
            if (data_buffer[vector_counter] > max_value) begin
              max_value <= data_buffer[vector_counter];
            end
            vector_counter <= vector_counter + 1;
          end
        end
        
        SHIFT_VALUES: begin
          // 重置计数器并开始减去最大值
          if (vector_counter < VECTOR_SIZE) begin
            shifted_values[vector_counter] <= to_fixed(data_buffer[vector_counter] - max_value);
            vector_counter <= vector_counter + 1;
          end
        end
        
        CALC_EXP: begin
          // 使用CORDIC计算指数
          if (vector_counter < VECTOR_SIZE) begin
            if (cordic_counter == 0) begin
              // 开始新的CORDIC计算
              cordic_x <= K_CONSTANT;
              cordic_y <= 0;
              cordic_z <= shifted_values[vector_counter];
              cordic_counter <= 1;
              cordic_mode <= 0; // 指数模式
            end else if (cordic_counter <= CORDIC_ITER) begin
              // CORDIC迭代
              cordic_dir <= (cordic_z >= 0);
              
              // CORDIC迭代公式
              if (cordic_mode == 0) begin
                // 指数模式
                if (cordic_dir) begin
                  cordic_x <= cordic_x + (cordic_y >>> (cordic_counter-1));
                  cordic_y <= cordic_y + (cordic_x >>> (cordic_counter-1));
                  cordic_z <= cordic_z - atanh_lut[cordic_counter-1];
                end else begin
                  cordic_x <= cordic_x - (cordic_y >>> (cordic_counter-1));
                  cordic_y <= cordic_y - (cordic_x >>> (cordic_counter-1));
                  cordic_z <= cordic_z + atanh_lut[cordic_counter-1];
                end
              end
              
              cordic_counter <= cordic_counter + 1;
              
              if (cordic_counter == CORDIC_ITER) begin
                // CORDIC计算完成
                exp_values[vector_counter] <= (cordic_x + cordic_y) >>> (FIXED_POINT_FRAC - (ACC_WIDTH - CORDIC_WIDTH));
                vector_counter <= vector_counter + 1;
                cordic_counter <= 0;
              end
            end
          end
        end
        
        CALC_SUM: begin
          // 计算指数和
          if (vector_counter == 0) begin
            sum_exp <= exp_values[0];
            vector_counter <= 1;
          end else if (vector_counter < VECTOR_SIZE) begin
            sum_exp <= sum_exp + exp_values[vector_counter];
            vector_counter <= vector_counter + 1;
          end
        end
        
        CALC_DIV: begin
          // 使用CORDIC计算倒数并归一化
          if (cordic_counter == 0) begin
            // 第一阶段：计算倒数的CORDIC迭代
            cordic_x <= sum_exp >>> (ACC_WIDTH - CORDIC_WIDTH);
            cordic_y <= (1 << FIXED_POINT_FRAC); // 1的定点表示
            cordic_z <= 0;
            cordic_mode <= 1; // 除法模式
            cordic_counter <= 1;
            vector_counter <= 0;
          end else if (cordic_counter <= CORDIC_ITER) begin
            // CORDIC迭代（除法模式）
            cordic_dir <= (cordic_y < 0);
            
            if (cordic_dir) begin
              cordic_x <= cordic_x - (cordic_y >>> (cordic_counter-1));
              cordic_y <= cordic_y - (cordic_x >>> (cordic_counter-1));
              cordic_z <= cordic_z - atanh_lut[cordic_counter-1];
            end else begin
              cordic_x <= cordic_x + (cordic_y >>> (cordic_counter-1));
              cordic_y <= cordic_y + (cordic_x >>> (cordic_counter-1));
              cordic_z <= cordic_z + atanh_lut[cordic_counter-1];
            end
            
            cordic_counter <= cordic_counter + 1;
            
            if (cordic_counter == CORDIC_ITER) begin
              // 倒数计算完成，开始归一化
              reciprocal = cordic_z << (ACC_WIDTH - CORDIC_WIDTH);
              
              // 归一化第一个元素
              scaled_result = exp_values[0] * reciprocal;
              output_reg[0] <= scaled_result >>> (ACC_WIDTH - DATA_WIDTH);
              
              vector_counter <= 1;
            end
          end else if (vector_counter < VECTOR_SIZE) begin
            // 对剩余元素进行归一化
            scaled_result = exp_values[vector_counter] * cordic_z;
            output_reg[vector_counter] <= scaled_result >>> (ACC_WIDTH - DATA_WIDTH);
            vector_counter <= vector_counter + 1;
          end
        end
      endcase
    end
  end
  
  // === 状态转移逻辑 ===
  always_comb begin
    next_state = state;
    ready = 1'b1;
    
    case (state)
      IDLE: begin
        if (enable) begin
          next_state = FIND_MAX;
          ready = 1'b0;
        end
      end
      
      FIND_MAX: begin
        ready = 1'b0;
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = SHIFT_VALUES;
        end else begin
          next_state = FIND_MAX;
        end
      end
      
      SHIFT_VALUES: begin
        ready = 1'b0;
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = CALC_EXP;
        end else begin
          next_state = SHIFT_VALUES;
        end
      end
      
      CALC_EXP: begin
        ready = 1'b0;
        if (vector_counter == VECTOR_SIZE-1 && cordic_counter == 0) begin
          next_state = CALC_SUM;
        end else begin
          next_state = CALC_EXP;
        end
      end
      
      CALC_SUM: begin
        ready = 1'b0;
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = CALC_DIV;
        end else begin
          next_state = CALC_SUM;
        end
      end
      
      CALC_DIV: begin
        ready = 1'b0;
        if (vector_counter == VECTOR_SIZE-1 && cordic_counter > CORDIC_ITER) begin
          next_state = IDLE;
        end else begin
          next_state = CALC_DIV;
        end
      end
      
      default: begin
        next_state = IDLE;
        ready = 1'b1;
      end
    endcase
  end

  // === 输出赋值 ===
  assign data_out = output_reg;
  assign valid_out = valid_reg;
  
endmodule

