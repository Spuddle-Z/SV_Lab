/* 
  ### 波特率发生器
  通过时钟分频，产生UART通信所需的波特率时钟使能信号。
*/
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
