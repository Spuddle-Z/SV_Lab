module rx_fifo_req (
  input  logic        clk,
  input  logic        rst_n,
  
  // RX FIFO 接口
  input  logic [15:0] rx_fifo_data,
  input  logic        rx_fifo_empty,
  output logic        rx_fifo_en,

  // 控制寄存器接口
  input  logic        reg_req,
  output logic [31:0] reg_data,
  output logic        reg_ready
);

  typedef enum logic [2:0] { IDLE0, READ0, WAIT0, IDLE1, READ1, WAIT1 } state_t;
  logic [31:0] reg_data_buf;
  state_t state;

  // RX FIFO 写使能逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_fifo_en <= 1'b0;
      reg_data_buf <= 32'b0;
      reg_data <= 32'bz;
      state <= IDLE0;
    end else begin
      case (state)
        IDLE0: begin
          rx_fifo_en <= 1'b0;
          reg_ready <= 1'b0;
          if (reg_req) begin
            if (rx_fifo_empty) begin
              reg_data <= 32'bz;
            end else begin
              rx_fifo_en <= 1'b1;
              reg_data_buf[15:0] <= rx_fifo_data;
              state <= READ0;
            end
          end
        end
        READ0: begin
          rx_fifo_en <= 1'b0;
          state <= WAIT0;
        end
        WAIT0: begin
          state <= IDLE1;
        end
        IDLE1: begin
          if (!rx_fifo_empty) state <= READ1;
        end
        READ1: begin
          rx_fifo_en <= 1'b1;
          reg_data_buf[31:16] <= rx_fifo_data;
          state <= WAIT1;
        end
        WAIT1: begin
          rx_fifo_en <= 1'b0;
          reg_ready <= 1'b1;
          reg_data <= reg_data_buf;
          state <= IDLE0;
        end
      endcase
    end
  end

endmodule