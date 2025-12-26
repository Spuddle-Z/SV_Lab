`timescale 1ns/1ps

module tb_spi_ctl;
  // ============================================================================
  // 参数定义
  // ============================================================================
  localparam CLK_PERIOD = 20;  // 50MHz时钟

  // ============================================================================
  // 信号定义
  // ============================================================================
  logic        clk;
  logic        rst_n;

  // SPI引脚
  logic        sck;      // SPI时钟
  logic        cs_n;     // SPI片选
  logic        mosi;     // 主设备输出，从设备输入
  logic        miso;     // 主设备输入，从设备输出

  // TX FIFO接口
  logic [15:0] tx_fifo_data;
  logic        tx_fifo_full;
  logic        tx_fifo_en;

  // RX FIFO接口
  logic [15:0] rx_fifo_data;
  logic        rx_fifo_empty;
  logic        rx_fifo_en;
  logic [15:0] test_data;
  logic        test_en;
  
  // UART控制信号
  logic [3:0]  state;
  logic [15:0] baud;

  // ============================================================================
  // DUT实例化
  // ============================================================================
  spi_ctl dut (
    .clk(clk),
    .rst_n(rst_n),

    .sck(sck),
    .cs_n(cs_n),
    .mosi(mosi),
    .miso(miso),

    .tx_fifo_data(tx_fifo_data),
    .tx_fifo_full(tx_fifo_full),
    .tx_fifo_en(tx_fifo_en),
    .rx_fifo_data(rx_fifo_data),
    .rx_fifo_empty(rx_fifo_empty),
    .rx_fifo_en(rx_fifo_en),

    .state(state),
    .baud(baud)
  );

  fifo tx_fifo (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),
    .empty(),
    .full(tx_fifo_full),
    .rd_data(),
    .rd_en(),
    .wr_data(tx_fifo_data),
    .wr_en(tx_fifo_en)
  );

  fifo rx_fifo (
    .rst_n(rst_n),
    .rd_clk(clk),
    .wr_clk(clk),
    .empty(rx_fifo_empty),
    .full(),
    .rd_data(rx_fifo_data),
    .rd_en(rx_fifo_en),
    .wr_data(test_data),
    .wr_en(test_en)
  );
  
  // ============================================================================
  // 时钟生成
  // ============================================================================
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // SPI 时钟参数（主设备产生）
  localparam SCK_HALF = 100; // ns (SCK period = 200 ns)

  // ============================================================================
  // SPI 主设备发送任务（模式 0，低位先行）
  // ============================================================================
  task automatic spi_master_send_word(input logic [31:0] word);
    integer i;
    begin
      // 确保 SCK 停止在 0
      sck = 1'b0;
      // 拉低片选并等待同步
      cs_n = 1'b0;
      #(CLK_PERIOD*5);

      // 逐位发送 LSB-first
      for (i = 0; i < 32; i = i + 1) begin
        mosi = word[i];
        // SCK low -> wait, then rising edge (master), then falling edge
        #(SCK_HALF);
        sck = 1'b1; // rising edge -> slave samples
        #(SCK_HALF);
        sck = 1'b0; // falling edge -> slave shifts / outputs
      end

      // 保持一段时间后释放片选
      #(CLK_PERIOD*3);
      cs_n = 1'b1;
      // 清空 MOSI
      mosi = 1'b0;
      // 等待若干时钟周期让从机处理
      #(CLK_PERIOD*10);
    end
  endtask

  // ============================================================================
  // 存入RX FIFO
  // ============================================================================
  task automatic push_rx_fifo(input logic [15:0] data);
    begin
      for (int i = 0; i < 4; i++) begin
        test_data = data + i;
        test_en = 1'b1;
        #(CLK_PERIOD);
        test_en = 1'b0;
        #(CLK_PERIOD);
      end
    end
  endtask

  // ============================================================================
  // 主测试流程
  // ============================================================================
  initial begin
    // 初始信号
    rst_n = 1'b0;
    sck = 1'b0;
    cs_n = 1'b1;
    mosi = 1'b0;
    tx_fifo_full = 1'b0;
    rx_fifo_empty = 1'b1;
    tx_fifo_data = 16'h0000;
    rx_fifo_data = 16'h0000;
    state = 4'h0;
    baud = 1'b0;

    // 复位
    #(CLK_PERIOD*2);
    rst_n = 1'b1;
    #(CLK_PERIOD*10);
    // 提前填充 RX FIFO 数据
    push_rx_fifo(16'h5A00);

    // 1) 发送写入 TX_DATA 命令: command=0x00, addr=0x10, data=0xA5A5
    spi_master_send_word({8'h00, 8'h10, 16'hA5A5});

    // 间隔
    #(CLK_PERIOD*50);

    // 2) 发送读取 RX_DATA 请求: command=0x01, addr=0x18
    spi_master_send_word({8'h01, 8'h18, 16'h0000});
    spi_master_send_word({8'h01, 8'h18, 16'h0000});

    // 3) 主机发起一次空传输以读回从机返回的 spi_tx_data（从机将于此传输输出数据）
    spi_master_send_word(32'h0000_0000);

    // 等待波形稳定后结束
    #(CLK_PERIOD*200);
    $stop;
  end

endmodule
