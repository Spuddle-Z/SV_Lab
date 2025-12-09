module spi_slave (
  // --- SPI 引脚（模式 0，低位先行）
  input  logic        SCK,     // SPI 时钟（CLK）
  input  logic        SS,    // 片选，低有效
  input  logic        MOSI,    // 主机输出，从机输入
  output logic        MISO,    // 从机输出，主机输入

  // --- 系统时钟与复位
  input  logic        clk,     // 系统时钟
  input  logic        rst_n,   // 低有效复位

  // --- 数据接口（固定 32 位，低位优先）
  input  logic [31:0] tx_data, // 待发送数据（32 位）
  input  logic        tx_valid,  // 发送数据有效
  output logic        tx_ready,  // 可接受新发送数据

  output logic [31:0] rx_data, // 接收数据（32 位）
  output logic        rx_valid,  // 接收数据有效
  output logic        rx_ready,  // 接收缓冲就绪
);

typedef enum logic [1:0] { STATE_IDLE, STATE_ACTIVE, STATE_COMPLETE } state_t;

// ============================================================================
// Internal Signals
// ============================================================================
logic [31:0] shift_reg;    // Shift register (32-bit)
logic [4:0]   bit_counter;  // Bit counter (0..31)
logic [31:0]  tx_buffer;    // Transmit buffer (32-bit)
logic [31:0]  rx_buffer;    // Receive buffer (32-bit)
logic tx_empty;     // Transmit buffer empty
logic rx_full;    // Receive buffer full
logic rx_valid_reg;   // Received data valid register
logic tx_valid_reg;   // Transmit data valid register
state_t           current_state;  // Current state
state_t           next_state;   // Next state
logic sck_sync;     // Synchronized SCK
logic sck_prev;     // Previous SCK value
logic sck_edge;     // SCK edge detection
logic cs_sync;    // Synchronized CS
logic cs_prev;    // Previous CS value
logic cs_falling;   // CS falling edge
logic cs_rising;    // CS rising edge
logic transfer_done;  // Transfer complete

// ============================================================================
// Clock and Chip Select Synchronization
// ============================================================================
// Synchronize asynchronous inputs to system clock domain
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    // 固定为模式0: 初始 CPOL = 0
    sck_sync <= 1'b0;
    cs_sync  <= 1'b1;
    sck_prev <= 1'b0;
    cs_prev  <= 1'b1;
  end else begin
    sck_sync <= SCK;
    cs_sync  <= SS;
    sck_prev <= sck_sync;
    cs_prev  <= cs_sync;
  end
end

// 边沿检测
assign sck_edge  = (sck_sync ^ sck_prev);
assign cs_falling = (cs_prev && !cs_sync);
assign cs_rising  = (!cs_prev && cs_sync);

// ============================================================================
// SPI 模式0 时钟边沿检测（上升沿采样，下降沿移位）
// ============================================================================
logic sample_edge;
logic shift_edge;
assign sample_edge = (sck_sync && !sck_prev);   // 上升沿采样
assign shift_edge  = (!sck_sync && sck_prev);   // 下降沿移位

// ============================================================================
// 状态机
// ============================================================================
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    current_state <= STATE_IDLE;
  end else begin
    current_state <= next_state;
  end
end

always_comb begin
  next_state = current_state;
  
  case (current_state)
    STATE_IDLE: begin
      if (cs_falling) begin
        next_state = STATE_ACTIVE;
      end
    end
    
    STATE_ACTIVE: begin
      if (cs_rising) begin
        next_state = STATE_COMPLETE;
      end else if (transfer_done) begin
        next_state = STATE_COMPLETE;
      end
    end
    
    STATE_COMPLETE: begin
      next_state = STATE_IDLE;
    end
    
    STATE_ERROR: begin
      if (cs_rising) begin
        next_state = STATE_IDLE;
      end
    end
    
    default: begin
      next_state = STATE_IDLE;
    end
  endcase
end

// ============================================================================
// 移位寄存器与位计数器
// ============================================================================
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    shift_reg <= '0;
    bit_counter <= '0;
    transfer_done <= 1'b0;
  end else begin
    case (current_state)
      STATE_IDLE: begin
        if (cs_falling) begin
          // 片选下降时将缓冲区数据加载到移位寄存器（双缓冲实现）
          if (!tx_empty) begin
            shift_reg <= tx_buffer;
          end else begin
            shift_reg <= '0;
          end
          bit_counter <= '0;
          transfer_done <= 1'b0;
        end
      end
      
      STATE_ACTIVE: begin
        if (sample_edge && !cs_sync) begin
          // 在上升沿采样 MOSI，并按低位优先（LSB-first）将采样位左移到寄存器高位
          shift_reg <= {MOSI, shift_reg[31:1]};

          // 位计数器递增，达到 31 时表示一帧完成
          if (bit_counter == 5'd31) begin
            bit_counter <= '0;
            transfer_done <= 1'b1;
          end else begin
            bit_counter <= bit_counter + 1;
          end
        end
      end
      
      STATE_COMPLETE: begin
        transfer_done <= 1'b0;
      end
      
      default: begin
        // Do nothing
      end
    endcase
  end
end

// ============================================================================
// 发送数据通路（固定为双缓冲实现）
// ============================================================================
// 双缓冲：内部缓冲区保存待发送数据，片选下降时将缓冲数据加载到移位寄存器
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    tx_buffer <= '0;
    tx_empty <= 1'b1;
    tx_valid_reg <= 1'b0;
  end else begin
    if (tx_valid && tx_ready) begin
      // Load new data into buffer
      tx_buffer <= tx_data;
      tx_empty <= 1'b0;
      tx_valid_reg <= 1'b1;
    end else if (cs_falling && !tx_empty) begin
      // Data transferred to shift register
      tx_empty <= 1'b1;
      tx_valid_reg <= 1'b0;
    end
  end
end

assign tx_ready = tx_empty;

// MISO 输出（三态控制）
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    MISO <= 1'bz;
  end else begin
    if (cs_sync) begin
      // 片选未选中，MISO 高阻态
      MISO <= 1'bz;
    end else if (shift_edge) begin
      // 下降沿出数据，低位优先输出最低位
      MISO <= shift_reg[0];
    end
  end
end

// ============================================================================
// 接收数据路径
// ============================================================================
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    rx_buffer <= '0;
    rx_full <= 1'b0;
    rx_valid_reg <= 1'b0;
  end else begin
    if (transfer_done && !rx_full) begin
      // 存储接收到的数据到接收缓冲
      rx_buffer <= shift_reg;
      rx_full <= 1'b1;
      rx_valid_reg <= 1'b1;
    end else if (rx_ready && rx_full) begin
      // Data read by host
      rx_full <= 1'b0;
      rx_valid_reg <= 1'b0;
    end
  end
end

assign rx_data = rx_buffer;
assign rx_valid = rx_valid_reg;
assign rx_ready = !rx_full;

endmodule
