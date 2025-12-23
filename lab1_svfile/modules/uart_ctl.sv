module uart_ctl (
  input logic clk,
  input logic rst_n,

  // Controller接口
  input logic [15:0] baud_divisor,
  output logic [3:0] state,

  // UART物理接口
  input logic rx,
  output logic tx,
  
  // TX接口（连接到外部TX FIFO）
  input logic [15:0] tx_data,
  input logic tx_empty,
  output logic tx_fifo_en,
  
  // RX接口（连接到外部RX FIFO）
  output logic [15:0] rx_data,
  output logic rx_full,
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
  logic [15:0] tx_data_reg;
  logic tx_byte_count;
  logic [15:0] rx_data_reg;
  logic rx_byte_count;

  // 发送控制逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_state <= TX_IDLE;
      tx_fifo_en <= 1'b0;
      tx_valid <= 1'b0;
      tx_data_reg <= 16'b0;
      tx_byte_count <= 1'b0;
    end else begin
      tx_fifo_en <= 1'b0;
      tx_valid <= 1'b0;

      case (tx_state)
        TX_IDLE: begin
          if (!tx_empty) begin
            tx_fifo_en <= 1'b1;
            tx_data_reg <= tx_data;
            tx_byte_count <= 1'b0;
            tx_state <= TX_SEND;
          end
        end

        TX_SEND: begin
          if (!tx_busy) begin
            case (tx_byte_count)
              1'b0: tx_byte <= tx_data_reg[7:0];
              1'b1: tx_byte <= tx_data_reg[15:8];
            endcase
            tx_valid <= 1'b1;

            if (tx_byte_count == 1'b1) begin
              tx_state <= TX_END;
            end else begin
              tx_byte_count <= tx_byte_count + 1;
            end
          end
        end

        TX_END: begin
          if (!tx_busy) begin  // 等待最后一个字节发送完成
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