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
