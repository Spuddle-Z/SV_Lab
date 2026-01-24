module baud_gen (
  // 输入时钟和复位
  input  logic  clk,    // 系统主时钟 (例如 50MHz)
  input  logic  rst_n,  // 低电平有效的异步复位

  // 配置输入
  input  logic [15:0] baud_divisor, // 波特率分频系数

  // 输出
  output logic  baud_tick   // 波特率时钟使能脉冲 (一个时钟周期的高电平)
);

  // 内部信号定义
  logic [15:0] counter; // 分频计数器

  // 计数器逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // 异步复位：计数器清零
      counter <= 16'b0;
    end else begin
      if (counter >= baud_divisor) begin
        // 当计数器达到分频值时，清零并产生一个脉冲
        counter <= 16'b0;
      end else begin
        // 否则，计数器加1
        counter <= counter + 16'b1;
      end
    end
  end

  // 输出产生逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      baud_tick <= 1'b0;
    end else begin
      baud_tick <= (counter >= baud_divisor);
    end
  end

endmodule
module uart_tx (
  input  logic clk,
  input  logic rst_n,
  input  logic tx_valid,      // 发送开始信号
  input  logic [7:0] tx_data, // 发送数据
  output logic tx,            // 串行数据输出
  output logic tx_busy,       // 发送忙信号
  input  logic baud_tick
);

  // 定义状态
  typedef enum logic [1:0] { IDLE, START, DATA, STOP } tx_state_t;

  tx_state_t tx_state; // 当前状态
  logic [3:0] tick_counter; // 因为是16倍过采样，所以需要对baud_tick计数
  logic [2:0] bit_counter;  // 当前发送的位索引
  logic [7:0] tx_data_reg;  // 需要发送数据的寄存器，防止中途数据变化

  // 计数器，用于16倍过采样
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tick_counter <= 4'b0;
    end else if (baud_tick) begin
      if (tick_counter == 4'd15) begin
        tick_counter <= 4'b0;
      end else begin
        tick_counter <= tick_counter + 1;
      end
    end
  end

  // 状态转换逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_state <= IDLE;
      bit_counter <= 3'b0;
    end else begin
      case (tx_state)
        IDLE: begin
          if (tx_valid) begin
            tx_state <= START;
            tx_data_reg <= tx_data;
            tick_counter <= 4'b0;
          end
        end
        START: begin
          if (baud_tick && tick_counter == 4'd15) begin
            tx_state <= DATA;
          end
        end
        DATA: begin
          if (baud_tick && tick_counter == 4'd15) begin
            if (bit_counter == 3'd7) begin
              bit_counter <= 3'b0;
              tx_state <= STOP;
            end else begin
              bit_counter <= bit_counter + 1;
            end
          end
        end
        STOP: begin
          if (baud_tick && tick_counter == 4'd15) begin
            tx_state <= IDLE;
          end
        end
      endcase
    end
  end

  // 输出逻辑
  always_comb begin
    case (tx_state)
      IDLE: begin
        tx = 1'b1;
        tx_busy = tx_valid ? 1'b1 : 1'b0;
      end
      START: begin
        tx = 1'b0;
        tx_busy = 1'b1;
      end
      DATA: begin
        tx = tx_data_reg[bit_counter];
        tx_busy = 1'b1;
      end
      STOP: begin
        tx = 1'b1;
        tx_busy = 1'b1;
      end
    endcase
  end

endmodule

module uart_rx (
  input  logic clk,
  input  logic rst_n,
  input  logic rx,
  output logic rx_done,
  output logic [7:0] rx_data,
  input  logic baud_tick
);

  // 状态定义
  typedef enum logic [1:0] { IDLE, START, DATA, STOP } rx_state_t;
  
  rx_state_t rx_state;
  logic [2:0] bit_counter;
  logic [3:0] tick_counter;
  logic rx_sync;

  // 输入同步
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_sync <= 1'b1;
    end else begin
      rx_sync <= rx;
    end
  end

  // 计数器，用于16倍过采样
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tick_counter <= 4'b0;
    end else if (baud_tick) begin
      if (tick_counter == 4'd15) begin
        tick_counter <= 4'b0;
      end else begin
        tick_counter <= tick_counter + 1;
      end
    end
  end

  // 状态机和数据接收
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_state <= IDLE;
      bit_counter <= 3'b0;
      rx_done <= 1'b0;
      rx_data <= 8'b0;
    end else begin
      rx_done <= 1'b0;
      if (baud_tick) begin
        case (rx_state)
          IDLE: begin
            if (rx_sync == 1'b0) begin  // 检测起始位
              rx_state <= START;
              tick_counter <= 4'b0;
            end
          end
          START: begin
            if (tick_counter == 4'd7) begin // 再位时间的中间采样
              if (rx_sync == 1'b0) begin  // 确认起始位仍有效
                rx_state <= DATA;
                bit_counter <= 3'b0;
                tick_counter <= 4'b0;
              end else begin  // 并非起始位，回到空闲状态
                rx_state <= IDLE;
              end
            end
          end
          DATA: begin
            if (tick_counter == 4'd15) begin
              rx_data[bit_counter] <= rx_sync;
              if (bit_counter == 3'd7) begin
                rx_state <= STOP;
              end else begin
                bit_counter <= bit_counter + 1;
              end
            end
          end
          STOP: begin
            if (tick_counter == 4'd15) begin
              rx_done <= 1'b1;
              rx_state <= IDLE;
            end
          end
        endcase
      end
    end
  end

endmodule

module uart_ctl (
  input logic clk,
  input logic rst_n,

  // Controller接口
  input logic [15:0] baud_divisor,
  output logic [3:0] state,

  // UART物理接口
  input logic rx,
  output logic tx,
  
  // TX接口
  input logic [127:0] tx_data,
  input logic data_valid,
  output logic tx_done,
  
  // RX接口（连接到外部RX FIFO）
  output logic [15:0] rx_data,
  input logic rx_full,
  output logic rx_fifo_en
);

  // 内部信号定义
  logic baud_tick;
  logic tx_valid, tx_busy, rx_done;
  logic [7:0] tx_byte, rx_byte;

  // 状态机定义
  typedef enum logic [1:0] { TX_IDLE, TX_SEND, TX_END } tx_state_t;
  typedef enum logic [1:0] { RX_IDLE, RX_RECV, RX_END } rx_state_t;

  // 实例化子模块
  baud_gen baud_gen_inst (
    .clk(clk),
    .rst_n(rst_n),
    .baud_divisor(baud_divisor),
    .baud_tick(baud_tick)
  );

  uart_tx uart_tx_inst (
    .clk(clk),
    .rst_n(rst_n),
    .tx_valid(tx_valid),
    .tx_data(tx_byte),
    .tx(tx),
    .tx_busy(tx_busy),
    .baud_tick(baud_tick)
  );

  uart_rx uart_rx_inst (
    .clk(clk),
    .rst_n(rst_n),
    .rx_done(rx_done),
    .rx(rx),
    .rx_data(rx_byte),
    .baud_tick(baud_tick)
  );

  // 内部寄存器
  tx_state_t tx_state;
  rx_state_t rx_state;
  logic [127:0] tx_data_reg;
  logic [4:0]   tx_byte_idx; // 0..15
  logic [15:0] rx_data_reg;
  logic rx_byte_count;

  // 发送控制逻辑：data_valid 触发发送 16 个字节，逐字节握手 uart_tx
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_state    <= TX_IDLE;
      tx_valid    <= 1'b0;
      tx_data_reg <= '0;
      tx_byte_idx <= '0;
      tx_byte     <= 8'h00;
      tx_done     <= 1'b0;
    end else begin
      tx_valid <= 1'b0; // 默认不拉高
      tx_done  <= 1'b0;

      case (tx_state)
        TX_IDLE: begin
          if (data_valid) begin
            tx_data_reg <= tx_data;
            tx_byte_idx <= 5'd0;
            tx_state    <= TX_SEND;
          end
        end

        TX_SEND: begin
          if (!tx_busy) begin
            tx_byte  <= tx_data_reg[8*tx_byte_idx +: 8];
            tx_valid <= 1'b1; // 一个周期脉冲
            if (tx_byte_idx == 5'd15) begin
              tx_state <= TX_END; // 发送最后一个字节后等待 busy 结束
            end else begin
              tx_byte_idx <= tx_byte_idx + 1'b1;
              tx_state    <= TX_SEND; // 下一字节会在 busy 拉低后再次进入此分支
            end
          end
        end

        TX_END: begin
          // 等待最后一个字节的 busy 拉低，再宣告完成
          if (!tx_busy) begin
            tx_done  <= 1'b1; // 完成脉冲
            tx_state <= TX_IDLE;
          end
        end
      endcase
    end
  end

  // 接收控制逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rx_state <= RX_RECV;
        rx_data_reg <= 16'b0;
        rx_byte_count <= 1'b0;
        rx_fifo_en <= 1'b0;
        rx_data <= 16'b0;
    end else begin
      rx_fifo_en <= 1'b0;

      case (rx_state)
        RX_RECV: begin
          if (rx_done) begin
            case (rx_byte_count)
              1'b0: rx_data_reg[7:0] <= rx_byte;
              1'b1: rx_data_reg[15:8] <= rx_byte;
            endcase

            if (rx_byte_count == 1'b1) begin
              rx_byte_count <= 1'b0;
              rx_state <= RX_END;
            end else begin
              rx_byte_count <= rx_byte_count + 1;
            end
          end
        end

        RX_END: begin
          rx_data <= rx_data_reg;
          rx_fifo_en <= 1'b1;
          rx_state <= RX_RECV;
        end
      endcase
    end
  end

  // 状态输出
  assign state = {tx_state, rx_state};
endmodule