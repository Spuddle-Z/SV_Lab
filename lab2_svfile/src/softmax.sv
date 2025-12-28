module softmax_in (
  input  logic clk,
  input  logic rst_n,
  input  logic [15:0] fifo_data,
  input  logic fifo_empty,
  output logic rd_en,
  output logic [255:0] data_out,
  output logic ready
);

  // 内部状态定义
  typedef enum logic [1:0] {
    IDLE,
    COLLECT,
    READY_ST
  } state_t;

  state_t state, next_state;
  logic [5:0] count;    // 计数0-15，对应16个16位数据（256位）

  // ===== 状态寄存器 =====
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // ===== 下一状态逻辑 =====
  always_comb begin
    case (state)
      IDLE: begin
        if (!fifo_empty) begin
          next_state = COLLECT;
        end else begin
          next_state = IDLE;
        end
      end
      
      COLLECT: begin
        if (!fifo_empty && count == 6'd15) begin  // 计数到15（共16次）
          next_state = READY_ST;
        end else begin
          next_state = COLLECT;
        end
      end
      
      READY_ST: begin
        next_state = IDLE;  // READY只保持一个周期
      end
      
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // ===== 输出逻辑 =====
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count <= 6'b0;
      data_out <= '0;
      rd_en <= 1'b0;
      ready <= 1'b0;
    end else begin
      // 默认值
      rd_en <= 1'b0;
      ready <= 1'b0;
      
      case (state)
        IDLE: begin
          count <= 6'b0;
          data_out <= '0;
        end
        
        COLLECT: begin
          if (!fifo_empty) begin
            // 读取数据并移位拼接
            data_out <= {fifo_data, data_out[255:16]};
            count <= count + 1'b1;
            rd_en <= 1'b1;
          end
        end
        
        READY_ST: begin
          ready <= 1'b1;  // 在READY状态输出ready=1
          count <= 6'b0;  // 重置计数器
        end
      endcase
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
  
  // 上游信号
  input logic enable,
  input logic signed [DATA_WIDTH*VECTOR_SIZE-1:0] data_in,
  
  // 下游信号
  output logic [DATA_WIDTH-1:0] data_out[VECTOR_SIZE-1:0],
  output logic valid_out
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
    
    case (state)
      IDLE: begin
        if (enable) begin
          next_state = FIND_MAX;
        end
      end
      
      FIND_MAX: begin
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = SHIFT_VALUES;
        end else begin
          next_state = FIND_MAX;
        end
      end
      
      SHIFT_VALUES: begin
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = CALC_EXP;
        end else begin
          next_state = SHIFT_VALUES;
        end
      end
      
      CALC_EXP: begin
        if (vector_counter == VECTOR_SIZE-1 && cordic_counter == 0) begin
          next_state = CALC_SUM;
        end else begin
          next_state = CALC_EXP;
        end
      end
      
      CALC_SUM: begin
        if (vector_counter == VECTOR_SIZE-1) begin
          next_state = CALC_DIV;
        end else begin
          next_state = CALC_SUM;
        end
      end
      
      CALC_DIV: begin
        if (vector_counter == VECTOR_SIZE-1 && cordic_counter > CORDIC_ITER) begin
          next_state = IDLE;
        end else begin
          next_state = CALC_DIV;
        end
      end
      
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // === 输出赋值 ===
  assign data_out = output_reg;
  assign valid_out = valid_reg;
  
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
    input  logic        tx_fifo_en
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

    // ================= softmax_in 实例化 =================
    // 该模块从上游FIFO读取16位数据，组装成256位数据流
    softmax_in u_softmax_in (
        .clk       (clk),
        .rst_n     (rst_n),
        .fifo_data (fifo_data),
        .fifo_empty(fifo_empty),
        .rd_en     (rd_en),
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
        .tx_data   (tx_data),                 // 16位输出数据
        .tx_empty  (tx_empty),                // 输出缓冲区空标志
        .tx_fifo_en(tx_fifo_en)               // 下游FIFO使能信号
    );

endmodule
