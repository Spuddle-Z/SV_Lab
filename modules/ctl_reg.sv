module ctl_reg (
    // 时钟和复位
    input  logic        clk,
    input  logic        rst_n,
    
    // 总线接口
    input  logic [7:0]  addr,           // 寄存器地址
    input  logic        wr_en,          // 写使能
    input  logic [31:0] wr_data,        // 写数据
    input  logic        rd_en,          // 读使能
    output logic [31:0] rd_data,        // 读数据
    output logic        rd_data_valid,  // 读数据有效
    
    // 控制信号输出到其他模块
    output logic        uart_enable,    // UART使能
    output logic [15:0] baud_rate_div,  // 波特率除数
    output logic        tx_fifo_rst,    // TX FIFO复位
    output logic        rx_fifo_rst,    // RX FIFO复位
    output logic        irq_enable,     // 中断使能
    
    // 状态信号输入
    input  logic        tx_fifo_empty,  // TX FIFO空
    input  logic        tx_fifo_full,   // TX FIFO满
    input  logic        rx_fifo_empty,  // RX FIFO空
    input  logic        rx_fifo_full,   // RX FIFO满
    input  logic        uart_busy,      // UART忙
    input  logic [7:0]  rx_error        // 接收错误状态
);

    // 基址: 0x2000_0000
    // 寄存器地址偏移 (相对于基址)
    // CONTROL : 0x00  (RW)
    // STATE   : 0x08  (R)
    // TX DATA : 0x10  (RW 可写用于发送，可读用于回读最近写入值)
    // RX DATA : 0x18  (R)
    // BAUD    : 0x20  (RW)
    localparam CTRL_REG_ADDR     = 8'h00;  // 控制寄存器 (offset 0x00)
    localparam STATUS_REG_ADDR   = 8'h08;  // 状态寄存器 (offset 0x08)
    localparam TX_DATA_REG_ADDR  = 8'h10;  // TX数据寄存器 (offset 0x10)
    localparam RX_DATA_REG_ADDR  = 8'h18;  // RX数据寄存器 (offset 0x18)
    localparam BAUD_REG_ADDR     = 8'h20;  // 波特率寄存器 (offset 0x20)
    
    // 寄存器定义
    logic [31:0] ctrl_reg;      // 控制寄存器
    logic [31:0] baud_reg;      // 波特率寄存器
    logic [31:0] tx_data_reg;   // TX数据寄存器（可写，可读回）
    logic [31:0] rx_data_reg;   // RX数据寄存器（只读）
    
    // 内部信号
    logic [31:0] status_reg;    // 状态寄存器（组合逻辑生成）
    logic        tx_data_valid; // TX数据有效
    logic        rx_data_ready; // RX数据准备好
    
    // =========================================================================
    // 控制寄存器 (CTRL) - 可读写
    // =========================================================================
    // 位定义:
    // [0]    : UART使能 (1=使能, 0=禁用)
    // [1]    : TX FIFO复位 (1=复位, 自动清零)
    // [2]    : RX FIFO复位 (1=复位, 自动清零)
    // [3]    : 中断使能 (1=使能, 0=禁用)
    // [31:4] : 保留
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 32'h0;
        end else if (wr_en && (addr == CTRL_REG_ADDR)) begin
            // 写入控制寄存器，但自动清除复位位
            ctrl_reg <= {wr_data[31:4], 2'b00, wr_data[1:0]};
        end else begin
            // 自动清除复位标志位
            ctrl_reg <= {ctrl_reg[31:4], 2'b00, ctrl_reg[1:0]};
        end
    end
    
    // 控制信号输出
    assign uart_enable = ctrl_reg[0];
    assign tx_fifo_rst = wr_en && (addr == CTRL_REG_ADDR) && wr_data[1];
    assign rx_fifo_rst = wr_en && (addr == CTRL_REG_ADDR) && wr_data[2];
    assign irq_enable  = ctrl_reg[3];
    
    // =========================================================================
    // 状态寄存器 (STATUS) - 只读
    // =========================================================================
    // 位定义:
    // [0]    : TX FIFO空
    // [1]    : TX FIFO满
    // [2]    : RX FIFO空
    // [3]    : RX FIFO满
    // [4]    : UART忙（正在发送或接收）
    // [7:5]  : 保留
    // [15:8] : RX错误状态
    // [31:16]: 保留
    
    assign status_reg = {
        16'h0000,           // [31:16] 保留
        rx_error,           // [15:8] RX错误状态
        3'b000,             // [7:5] 保留
        uart_busy,          // [4] UART忙
        rx_fifo_full,       // [3] RX FIFO满
        rx_fifo_empty,      // [2] RX FIFO空
        tx_fifo_full,       // [1] TX FIFO满
        tx_fifo_empty       // [0] TX FIFO空
    };
    
    // =========================================================================
    // 波特率寄存器 (BAUD) - 可读写
    // =========================================================================
    // 位定义:
    // [15:0] : 波特率除数（时钟分频系数）
    // [31:16]: 保留
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            baud_reg <= 32'd27;  // 默认值：50MHz/115200 ≈ 27
        end else if (wr_en && (addr == BAUD_REG_ADDR)) begin
            baud_reg <= {16'h0000, wr_data[15:0]};
        end
    end
    
    assign baud_rate_div = baud_reg[15:0];
    
    // =========================================================================
    // TX数据寄存器 (TX_DATA) - 只写
    // =========================================================================
    // 写入的数据将被发送到TX FIFO
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_data_reg <= 32'h0;
            tx_data_valid <= 1'b0;
        end else if (wr_en && (addr == TX_DATA_REG_ADDR)) begin
            tx_data_reg <= wr_data;
            tx_data_valid <= 1'b1;
        end else begin
            tx_data_valid <= 1'b0;
        end
    end
    
    // =========================================================================
    // RX数据寄存器 (RX_DATA) - 只读
    // =========================================================================
    // 从RX FIFO读取的数据
    
    // 注意：RX数据寄存器通常由外部FIFO模块直接更新
    // 这里假设外部模块会在数据准备好时更新rx_data_reg并设置rx_data_ready
    
    // =========================================================================
    // 读数据逻辑
    // =========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data <= 32'h0;
            rd_data_valid <= 1'b0;
        end else if (rd_en) begin
            rd_data_valid <= 1'b1;
            case (addr)
                CTRL_REG_ADDR:    rd_data <= ctrl_reg;
                STATUS_REG_ADDR:  rd_data <= status_reg;
                BAUD_REG_ADDR:    rd_data <= baud_reg;
                TX_DATA_REG_ADDR: rd_data <= tx_data_reg;   // 支持读回最近写入的TX数据
                RX_DATA_REG_ADDR: rd_data <= rx_data_reg;
                default:          rd_data <= 32'hDEADBEEF;  // 未定义地址
            endcase
        end else begin
            rd_data_valid <= 1'b0;
        end
    end
    
    // =========================================================================
    // 断言检查（用于仿真调试）
    // =========================================================================
    // synthesis translate_off
    always @(posedge clk) begin
        if (wr_en) begin
            case (addr)
                CTRL_REG_ADDR: 
                    $display("[CONTROL_REGS] Write CTRL: 0x%08h", wr_data);
                BAUD_REG_ADDR: 
                    $display("[CONTROL_REGS] Write BAUD: 0x%08h (divisor = %0d)", 
                            wr_data, wr_data[15:0]);
                    TX_DATA_REG_ADDR: 
                    $display("[CONTROL_REGS] Write TX_DATA: 0x%08h", wr_data);
                default: 
                    if (addr >= 8'h24) 
                        $display("[CONTROL_REGS] Write to invalid address: 0x%02h", addr);
            endcase
        end
        
        if (rd_en && rd_data_valid) begin
            case (addr)
                CTRL_REG_ADDR: 
                    $display("[CONTROL_REGS] Read CTRL: 0x%08h", rd_data);
                STATUS_REG_ADDR: 
                    $display("[CONTROL_REGS] Read STATUS: 0x%08h", rd_data);
                BAUD_REG_ADDR: 
                    $display("[CONTROL_REGS] Read BAUD: 0x%08h", rd_data);
                RX_DATA_REG_ADDR: 
                    $display("[CONTROL_REGS] Read RX_DATA: 0x%08h", rd_data);
                TX_DATA_REG_ADDR:
                    $display("[CONTROL_REGS] Read TX_DATA: 0x%08h", rd_data);
            endcase
        end
    end
    // synthesis translate_on

endmodule
