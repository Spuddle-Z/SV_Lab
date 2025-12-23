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

  typedef enum logic [1:0] { IDLE0, READ0, IDLE1, READ1 } state_t;
  state_t state;

  // RX FIFO 写使能逻辑
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_fifo_en <= 1'b0;
      reg_data <= 32'b0;
      state <= IDLE0;
    end else begin
      case (state)
        IDLE0: begin
          rx_fifo_en <= 1'b0;
          reg_ready <= 1'b0;
          if (reg_req) state <= READ0;
        end
        READ0: begin
          rx_fifo_en <= 1'b1;
          reg_data[15:0] <= rx_fifo_empty ? 16'b0 : rx_fifo_data;
          state <= IDLE1;
        end
        IDLE1: begin
          rx_fifo_en <= 1'b0;
          state <= READ1;
        end
        READ1: begin
          rx_fifo_en <= 1'b1;
          reg_data[31:16] <= rx_fifo_empty ? 16'b0 : rx_fifo_data;
          reg_ready <= 1'b1;
          state <= IDLE0;
        end
      endcase
    end
  end
endmodule