`timescale 1ns/1ps

module spi_slave (
    // --- SPI 引脚（模式 0，低位先行）
    input  logic        sck,     // SPI 时钟
    input  logic        cs_n,    // SPI 片选
    input  logic        mosi,    // 主设备输出，从设备输入
    output logic        miso,    // 主设备输入，从设备输出

    // --- 系统时钟与复位
    input  logic        clk,     // 系统时钟
    input  logic        rst_n,   // 低有效复位

    // --- 数据与控制接口
    input  logic [31:0] tx_data,
    input  logic        tx_valid,

    output logic [31:0] rx_data,
    output logic        rx_done
  );

  // ============================================================================
  // 同步外部与本地时钟域
  // ============================================================================
  logic [2:0] sck_sync, cs_n_sync, mosi_sync;
  logic sck_synced, cs_n_synced, mosi_synced;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      sck_sync <= 3'b0;
      cs_n_sync  <= 3'b111;
      mosi_sync <= 3'bzzz;
    end else begin
      sck_sync <= {sck_sync[1:0], sck};
      cs_n_sync  <= {cs_n_sync[1:0], cs_n};
      mosi_sync <= {mosi_sync[1:0], mosi};
    end
  end

  assign sck_synced = sck_sync[2];
  assign cs_n_synced  = cs_n_sync[2];
  assign mosi_synced = mosi_sync[2];

  // ============================================================================
  // 边沿检测
  // ============================================================================
  logic sck_prev, sample_edge, shift_edge;
  logic cs_n_prev, start_edge, stop_edge;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      sck_prev <= 1'b0;
      cs_n_prev <= 1'b1;
    end else begin
      sck_prev <= sck_synced;
      cs_n_prev <= cs_n_synced;
    end
  end

  assign sample_edge = sck_synced && !sck_prev;
  assign shift_edge = !sck_synced && sck_prev;
  assign start_edge = !cs_n_synced && cs_n_prev;
  assign stop_edge = cs_n_synced && !cs_n_prev;

  // ============================================================================
  // 移位寄存器
  // ============================================================================
  logic [31:0] tx_shift_reg;
  logic tx_en;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_shift_reg <= 32'b0;
      tx_en <= 1'b0;
    end else begin
      if (start_edge && tx_valid) begin
        tx_shift_reg <= tx_data;
        tx_en <= 1'b1;
      end else if (!cs_n_synced && sample_edge) begin
        rx_data <= {mosi_synced, rx_data[31:1]};
      end else if (!cs_n_synced && shift_edge) begin
        tx_shift_reg <= {1'b0, tx_shift_reg[31:1]};
      end else if (stop_edge) begin
        tx_en <= 1'b0;
      end
    end
  end

  assign rx_done = stop_edge;
  assign miso = tx_en ? tx_shift_reg[0] : 1'b0;

endmodule

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
            rx_reg_valid <= 1'b1;
            case (addr)
              CONTROL: spi_tx_data <= {30'b0, control_reg};
              STATE: spi_tx_data <= {28'b0, state_reg};
              RX_DATA: begin
                spi_tx_data <= rx_data_reg;
                rx_fifo_en <= 1'b1;
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

module spi_ctl (
  input  logic        clk,
  input  logic        rst_n,

  // SPI引脚
  input  logic        sck,      // SPI时钟
  input  logic        cs_n,     // SPI片选
  input  logic        mosi,     // 主设备输出，从设备输入
  output logic        miso,     // 主设备输入，从设备输出

  // TX FIFO接口
  output logic [15:0] tx_fifo_data,
  input  logic        tx_fifo_full,
  output logic        tx_fifo_en,

  // RX FIFO接口
  input  logic [15:0] rx_fifo_data,
  input  logic        rx_fifo_empty,
  output logic        rx_fifo_en,
  
  // UART控制信号
  input  logic [3:0]  state,
  output logic [1:0]  control,
  output logic [15:0] baud
);

  // ============================================================================
  // 信号定义
  // ============================================================================
  // SPI与控制寄存器接口
  logic [31:0] spi_rx_data;
  logic        spi_rx_done;
  logic [31:0] spi_tx_data;
  logic        rx_reg_valid;

  // 控制寄存器与req接口
  logic [31:0] reg_data;
  logic        reg_req;
  logic        reg_ready;

  // ============================================================================
  // DUT实例化
  // ============================================================================
  spi_slave spi_slave_inst (
    .sck(sck),
    .cs_n(cs_n),
    .mosi(mosi),
    .miso(miso),

    .clk(clk),
    .rst_n(rst_n),

    .rx_data(spi_rx_data),
    .rx_done(spi_rx_done),
    .tx_data(spi_tx_data),
    .tx_valid(rx_reg_valid)
  );

  ctrl_reg dut (
    .clk(clk),
    .rst_n(rst_n),

    .spi_rx_data(spi_rx_data),
    .spi_rx_done(spi_rx_done),
    .spi_tx_data(spi_tx_data),
    .rx_reg_valid(rx_reg_valid),

    .tx_fifo_data(tx_fifo_data),
    .tx_fifo_full(tx_fifo_full),
    .tx_fifo_en(tx_fifo_en),
    .rx_fifo_data(reg_data),
    .rx_fifo_en(reg_req),
    .rx_fifo_ready(reg_ready),

    .state(state),
    .control(control),
    .baud(baud)
  );

  rx_fifo_req rx_fifo_req_inst (
    .clk(clk),
    .rst_n(rst_n),

    .rx_fifo_data(rx_fifo_data),
    .rx_fifo_empty(rx_fifo_empty),
    .rx_fifo_en(rx_fifo_en),

    .reg_req(reg_req),
    .reg_data(reg_data),
    .reg_ready(reg_ready)
  );

endmodule