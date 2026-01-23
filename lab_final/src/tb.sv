`timescale 1ns/1ps

module tb_data_packer;

  // 1. 信号声明
  logic           clk;
  logic           rst_n;
  
  // 上游信号
  logic           empty;
  logic [15:0]    data_in;
  
  // 下游信号
  logic           enable;
  logic           valid;
  logic [127:0]   data_out;

  // 2. 模块例化
  data_packer u_dut (
    .clk(clk),
    .rst_n(rst_n),
    .empty(empty),
    .data_in(data_in),
    .enable(enable),
    .valid(valid),
    .data_out(data_out)
  );

  // 3. 时钟生成
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // 4. 激励与监测主逻辑
  initial begin
    // ---------------------------------------------------------
    // 【关键修改】：把所有需要用到的变量声明都放在这里！
    // ---------------------------------------------------------
    logic [127:0] expected_data;
    logic [127:0] received_data;
    
    // 初始化
    rst_n = 0;
    empty = 1; 
    data_in = 0;
    
    // 复位
    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(2) @(posedge clk);
    
    $display("-------------- Test Start --------------");
    $display("Time: %0tns, Reset released", $time);

    // === 场景 1: 连续发送 8 个数据 ===
    empty = 0; 
    
    for (int i = 0; i < 8; i++) begin
      data_in = i;  
      @(negedge clk);
      @(negedge clk);
      
      $display("Time: %0tns, Driving data_in=%0d, Enable observed: %0b", 
           $time, i, enable);
    end

    // === 等待 DUT 输出 ===
    wait(valid == 1);
    @(posedge clk); 
    received_data = data_out;

    // === 构造期望值 ===
    // RTL逻辑是高位移位：输入 0..7，输出应为 {7,6,5,4,3,2,1,0}
    expected_data = {16'd7, 16'd6, 16'd5, 16'd4, 16'd3, 16'd2, 16'd1, 16'd0};

    $display("-------------- Checking Result --------------");
    $display("Time: %0tns, Valid Asserted!", $time);
    $display("Expected Output: 0x%0h", expected_data);
    $display("Actual   Output: 0x%0h", received_data);

    if (received_data === expected_data) begin
      $display("\n*** TEST PASSED! ***\n");
    end else begin
      $display("\n*** TEST FAILED! ***\n");
    end

    // 结束仿真
    repeat(10) @(posedge clk);
    $finish;
  end

  // 波形 Dump
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, tb_data_packer);
  end

endmodule

`timescale 1ns/1ps

module tb_fifo();
  localparam CLK_PERIOD = 20;  // 50MHz
  
  // 信号定义
  logic rd_clk;
  logic wr_clk;
  logic rst_n;
  logic rd_en, wr_en;
  logic [15:0] rd_data, wr_data;
  logic empty, full;
  
  // 实例化FIFO
  fifo dut (
    .rd_clk(rd_clk),
    .wr_clk(wr_clk),
    .rst_n(rst_n),
    .rd_en(rd_en),
    .rd_data(rd_data),
    .wr_en(wr_en),
    .wr_data(wr_data),
    .empty(empty),
    .full(full)
  );
  
  // 时钟生成
  always #(CLK_PERIOD/2) rd_clk = ~rd_clk;
  always #(CLK_PERIOD/2) wr_clk = ~wr_clk;

  // 复位任务
  task reset_dut;
    $display("Applying reset...");
    rst_n = 0;
    #(CLK_PERIOD);
    rst_n = 1;
    #(CLK_PERIOD);
  endtask

  // 单个写入任务
  task write_data(input [15:0] data);
    @(posedge wr_clk);
    wr_data = data;
    wr_en = 1;
    @(posedge wr_clk);
    wr_en = 0;
  endtask

  // 单个读取任务
  task read_data();
    @(posedge rd_clk);
    rd_en = 1;
    @(posedge rd_clk);
    rd_en = 0;
  endtask

  // 写满测试
  task automatic write_full();
    int i;
    for (i = 0; i < 9; i++) begin
      write_data(i);
    end
  endtask

  // 读空测试
  task automatic read_empty();
    int i;
    for (i = 0; i < 9; i++) begin
      read_data();
    end
  endtask

  // 同时读写测试
  task automatic simultaneous_rw();
    fork
      begin
        begin
          for (int i = 4; i < 8; i++) begin
            wr_data = 16'h4000 + i;
            wr_en = 1'b1;
            @(posedge wr_clk);
          end
          wr_en = 1'b0;
        end
      end
        
      begin
        begin
          for (int i = 0; i < 4; i++) begin
            rd_en = 1'b1;
            @(posedge rd_clk);
            rd_en = 1'b0;
          end
        end
      end
    join
  endtask

  initial begin
    // 初始化信号
    rd_clk = 0;
    wr_clk = 1;
    rst_n = 1;
    rd_en = 0;
    wr_en = 0;
    wr_data = 0;

    // 复位
    reset_dut();

    // 单次写入和读取测试
    write_data(16'hA5A5);
    #(CLK_PERIOD);
    read_data();
    $display("Read data: %h", rd_data);

    // 写满测试
    write_full();

    // 读空测试
    read_empty();
    #(CLK_PERIOD * 4);

    // 同时读写测试
    simultaneous_rw();

    // 结束仿真
    $stop;
  end

endmodule

`timescale 1ns / 1ps

//------------------------------------------------------------------------------
// expu 单元测试
// 验证指数近似输出与理想 e^(y-lnF) 的误差，并粗略给出可计算/饱和范围
//------------------------------------------------------------------------------
module tb_expu;

  // 输入/输出信号
  logic signed [7:0] y;
  logic signed [7:0] lnF;
  logic [19:0]       exp_y;

  // 待测模块实例化
  expu dut (
    .y    (y),
    .lnF  (lnF),
    .exp_y(exp_y)
  );

  // 将 real 转 q3.4（带简单饱和保护）
  function automatic signed [7:0] to_q34(real r);
    int tmp;
    begin
      tmp = $rtoi(r * 16.0);
      if (tmp >  127) tmp =  127;
      if (tmp < -128) tmp = -128;
      to_q34 = tmp[7:0];
    end
  endfunction

  // q3.4 转 real
  function automatic real q34_to_real(input signed [7:0] v);
    q34_to_real = $itor(v) / 16.0;
  endfunction

  // real 转 uq12.8（带饱和）
  function automatic int to_q128(real r);
    int tmp;
    begin
      tmp = $rtoi(r * 256.0 + 0.5);
      if (tmp < 0) tmp = 0;
      if (tmp > 20'hFFFFF) tmp = 20'hFFFFF;
      to_q128 = tmp;
    end
  endfunction

  // 统计与结果记录
  int total_cnt;
  int pass_cnt;
  int abs_err;
  int max_abs_err;
  real sat_first_diff;
  bit  sat_seen;

  initial begin
    total_cnt     = 0;
    pass_cnt      = 0;
    abs_err       = 0;
    max_abs_err   = 0;
    sat_seen      = 0;
    sat_first_diff= 0.0;

    // 扫描 y 和 lnF：y 从 -8 到 7.5 步进 0.5，lnF 取 {-2, 0, 2}
    for (real y_r = -6.0; y_r <= 7.5; y_r += 0.5) begin
      real diff_r;
      real golden_r;
      int  golden_q;

      // 驱动输入
      y   = to_q34(y_r);
      lnF = to_q34(0);
      #1ns;

      // 理想值（使用 real 指数）
      diff_r    = q34_to_real(y) - q34_to_real(lnF);
      golden_r  = $exp(diff_r);
      golden_q  = to_q128(golden_r);

      abs_err = (exp_y > golden_q) ? (exp_y - golden_q) : (golden_q - exp_y);
      if (abs_err > max_abs_err) max_abs_err = abs_err;
      total_cnt++;

      // $display("Debug: y=%0.2f (%0b), lnF=%0.2f (%0b)", q34_to_real(y), y, q34_to_real(lnF), lnF);
      if (abs_err <= 64) begin
        pass_cnt++; // 允许约 0.25 LSB 的 q12.8 误差
        $display("[PASS] y=%0.2f golden_q=%0d dut=%0d err=%0d", q34_to_real(y), golden_q, exp_y, abs_err);
      end else begin
        $display("[FAIL] y=%0.2f golden_q=%0d dut=%0d err=%0d", q34_to_real(y), golden_q, exp_y, abs_err);
      end

      // 记录饱和发生位置
      if (!sat_seen && exp_y == 20'hFFFFF) begin
        sat_seen = 1'b1;
        sat_first_diff = diff_r;
      end
    end

    $display("\n================ expu TB Summary ================");
    $display("Total cases : %0d", total_cnt);
    $display("Pass  cases : %0d", pass_cnt);
    $display("Max abs err : %0d LSB (uq12.8)", max_abs_err);
    if (sat_seen) begin
      $display("Saturation  : first observed when (y-lnF) >= %0.2f (q3.4)", sat_first_diff);
    end else begin
      $display("Saturation  : not hit within sweep range");
    end
    $display("=================================================\n");

    #10ns;
    $finish;
  end

endmodule

`timescale 1ns / 1ps

//------------------------------------------------------------------------------
// lnF_uq16p8 单元测试
// 验证 ln(F) 近似输出与理想 ln(F) 的误差，并给出可计算/饱和范围
//------------------------------------------------------------------------------
module tb_lnu;

  // 输入/输出信号
  logic [23:0]       F;    // uq16.8 输入
  logic signed [7:0] lnF;  // sq4.4 输出

  // 待测模块实例化
  lnu dut (
    .F  (F),
    .lnF(lnF)
  );

  // real 转 uq16.8（带饱和）
  function automatic [23:0] to_q168(real r);
    int tmp;
    begin
      tmp = $rtoi(r * 256.0 + 0.5);
      if (tmp < 0) tmp = 0;
      if (tmp > 24'hFFFFFF) tmp = 24'hFFFFFF;
      to_q168 = tmp[23:0];
    end
  endfunction

  // uq16.8 转 real
  function automatic real q168_to_real(input [23:0] v);
    q168_to_real = $itor(v) / 256.0;
  endfunction

  // real 转 sq4.4（带饱和）
  function automatic signed [7:0] to_q44(real r);
    int tmp;
    begin
      tmp = $rtoi(r * 16.0);
      if (tmp > 127)  tmp = 127;
      if (tmp < -128) tmp = -128;
      to_q44 = tmp[7:0];
    end
  endfunction

  // 统计与结果记录
  int total_cnt;
  int pass_cnt;
  int max_abs_err;
  int abs_err;
  bit sat_pos_seen;
  bit sat_neg_seen;
  real sat_pos_at;
  real sat_neg_at;
  // 计算中间量（移出 initial，兼容纯 Verilog 声明规则）
  real golden_r;
  int  golden_q;
  real offset;
  real F_r;
  real base;
  int  frac_idx;

  initial begin
    total_cnt   = 0;
    pass_cnt    = 0;
    max_abs_err = 0;
    sat_pos_seen= 0;
    sat_neg_seen= 0;
    sat_pos_at  = 0.0;
    sat_neg_at  = 0.0;

    // 扫描 F：基值按 2 的幂递增，叠加 0/0.2/0.4/0.6/0.8 的小偏置
    for (base = 0.25; base <= 4096.0; base = base * 2.0) begin
      for (frac_idx = 0; frac_idx < 5; frac_idx++) begin
        offset = 0.2 * frac_idx;
        F_r    = base + offset;

        // 驱动输入
        F = to_q168(F_r);
        #1ns;

        golden_r = $ln(q168_to_real(F));
        golden_q = to_q44(golden_r);

        abs_err = (lnF > golden_q) ? (lnF - golden_q) : (golden_q - lnF);
        if (abs_err > max_abs_err) max_abs_err = abs_err;
        total_cnt++;

        // 允许 1 LSB 误差
        if (abs_err <= 1) begin
          pass_cnt++;
          $display("[PASS] F=%0.3f q=%0d lnF_dut=%0d err=%0d", q168_to_real(F), golden_q, lnF, abs_err);
        end else begin
          $display("[FAIL] F=%0.3f q=%0d lnF_dut=%0d err=%0d", q168_to_real(F), golden_q, lnF, abs_err);
        end

        // 记录正/负饱和位置
        if (!sat_pos_seen && lnF == 8'sh7F) begin
          sat_pos_seen = 1'b1;
          sat_pos_at   = q168_to_real(F);
        end
        if (!sat_neg_seen && lnF == 8'sh80) begin
          sat_neg_seen = 1'b1;
          sat_neg_at   = q168_to_real(F);
        end
      end
    end

    $display("\n================ lnu TB Summary ================" );
    $display("Total cases : %0d", total_cnt);
    $display("Pass  cases : %0d", pass_cnt);
    $display("Max abs err : %0d LSB (sq4.4)", max_abs_err);
    if (sat_pos_seen)
      $display("Pos saturation at F >= %0.3f", sat_pos_at);
    else
      $display("Pos saturation not hit in sweep");
    if (sat_neg_seen)
      $display("Neg saturation at F <= %0.3f", sat_neg_at);
    else
      $display("Neg saturation not hit in sweep");
    $display("=================================================\n");

    #10ns;
    $finish;
  end

endmodule












