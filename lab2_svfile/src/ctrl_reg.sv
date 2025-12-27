module ctrl_reg (
  // 时钟和复位
  input  logic    clk,
  input  logic    rst_n,
  
  // 总线接口
  input  logic [31:0] spi_rx_data,
  input  logic        spi_rx_done,
  output logic [31:0] spi_tx_data,
  output logic        rx_reg_valid,

  // FIFO接口
  output logic [15:0] tx_fifo_data,
  input  logic        tx_fifo_full,
  output logic        tx_fifo_en,
  input  logic [31:0] rx_fifo_data,
  output logic        rx_fifo_en,
  input  logic        rx_fifo_ready,

  // UART控制信号
  input  logic [3:0]  state,
  output logic [15:0] baud,
  output logic [1:0] control
);
  // ============================================================================
  // 寄存器定义
  // ============================================================================
  logic [1:0] control_reg;
  logic [3:0] state_reg;
  logic [15:0] baud_reg;
  logic [31:0] rx_data_reg;

  // ============================================================================
  // 解析命令
  // ============================================================================
  logic [7:0] command, addr;
  logic [15:0] data;

  assign command = spi_rx_data[31:24];
  assign addr    = spi_rx_data[23:16];
  assign data    = spi_rx_data[15:0];

  typedef enum logic [7:0] {
    CONTROL = 8'h00,
    STATE = 8'h08,
    TX_DATA = 8'h10,
    RX_DATA = 8'h18,
    BAUD = 8'h20
  } addr_t;

  // ============================================================================
  // 控制寄存器写逻辑
  // ============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      control_reg <= 2'b0;
      state_reg <= 4'b0;
      baud_reg <= 16'b0;
      rx_data_reg <= 32'b0;
      spi_tx_data <= 32'b0;
      rx_reg_valid <= 1'b0;
      tx_fifo_en <= 1'b0;
      rx_fifo_en <= 1'b0;
    end else begin // 处理接收到的数据
      tx_fifo_en <= 1'b0;
      rx_fifo_en <= 1'b0;
      rx_reg_valid <= 1'b0;
      if (spi_rx_done) begin
        case (command)
          8'h00: begin
            case (addr)
              CONTROL: control_reg <= data[1:0];
              TX_DATA: begin
                tx_fifo_data <= data;
                tx_fifo_en <= 1'b1;
              end
              BAUD: baud_reg <= data;
            endcase
          end
          8'h01: begin
            case (addr)
              CONTROL: spi_tx_data <= {30'b0, control_reg};
              STATE: spi_tx_data <= {28'b0, state_reg};
              RX_DATA: begin
                spi_tx_data <= rx_data_reg;
                rx_fifo_en <= 1'b1;
                rx_reg_valid <= 1'b1;
              end
              BAUD: spi_tx_data <= {16'b0, baud_reg};
            endcase
          end
        endcase
      end
    end
  end

  // ============================================================================
  // RX_FIFO接收
  // ============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_data_reg <= 32'b0;
    end else if (rx_fifo_ready) begin
      rx_data_reg <= rx_fifo_data;
    end
  end

  // ============================================================================
  // 输出信号赋值
  // ============================================================================
  assign control = control_reg;
  assign baud = baud_reg;

endmodule
