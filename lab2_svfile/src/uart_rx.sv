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
