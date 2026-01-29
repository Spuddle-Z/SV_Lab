`timescale 1ns/1ps

package scoreboard_pkg;

  import uvm_pkg::*;
  import sequence_pkg::*;
  `include "uvm_macros.svh"

  class my_model extends uvm_component;
    `uvm_component_utils(my_model)
    uvm_blocking_get_port #(spi_trans)  spi_bgp;
    uvm_blocking_get_port #(uart_trans) uart_bgp;
    uvm_analysis_port #(uart_trans)     exp_uart_ap;
    uvm_analysis_port #(uart_trans)     act_uart_tx_ap;
    uvm_analysis_port #(uart_trans)     act_uart_rx_ap;
    uvm_analysis_port #(spi_trans)      act_spi_read_ap;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      spi_bgp = new("spi_bgp", this);
      uart_bgp = new("uart_bgp", this);
      exp_uart_ap = new("exp_uart_ap", this);
      act_uart_tx_ap = new("act_uart_tx_ap", this);
      act_uart_rx_ap = new("act_uart_rx_ap", this);
      act_spi_read_ap = new("act_spi_read_ap", this);
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
      fork
        begin : spi_loop
          spi_trans spi_item;
          byte data_bytes[$];
          int i;
          real exp_vals[16];
          real sum_exp;

          forever begin
            spi_bgp.get(spi_item);

            // 处理写TXDATA_ADDR的事务，收集输入数据
            if (!spi_item.read && spi_item.addr == TXDATA_ADDR) begin
              data_bytes.push_back(spi_item.wdata[7:0]);
              data_bytes.push_back(spi_item.wdata[15:8]);

              // 当收集到16个字节时，进行softmax计算
              if (data_bytes.size() == 16) begin
                sum_exp = 0.0;
                // 计算每个输入的指数值
                for (i = 0; i < 16; i++) begin
                  exp_vals[i] = $exp($itor($signed(data_bytes[i])) / 16.0);
                  sum_exp += exp_vals[i];
                end

                // 计算softmax概率并量化到uq0.8格式
                for (i = 0; i < 16; i++) begin
                  uart_trans exp_item;
                  real soft_val;
                  int q_val;
                  exp_item = uart_trans::type_id::create($sformatf("exp_item_%0d", i));
                  soft_val = (sum_exp == 0.0) ? 0.0 : (exp_vals[i] / sum_exp);
                  q_val = int'(soft_val * 256.0);
                  if (q_val < 0) q_val = 0;
                  if (q_val > 255) q_val = 255;
                  exp_item.data = q_val[7:0];
                  exp_item.is_tx = 1'b1;
                  exp_uart_ap.write(exp_item);  // 发送期望值到scoreboard
                end

                data_bytes.delete();  // 清空数据队列
              end
            end

            // 处理读RXDATA_ADDR的事务，转发到scoreboard
            if (spi_item.read && spi_item.addr == RXDATA_ADDR) begin
              spi_trans spi_read_item;
              spi_read_item = spi_trans::type_id::create("spi_read_item");
              spi_read_item.read = spi_item.read;
              spi_read_item.addr = spi_item.addr;
              spi_read_item.rdata = spi_item.rdata;
              act_spi_read_ap.write(spi_read_item);
            end
          end
        end

        begin : uart_loop
          uart_trans uart_item;
          forever begin
            uart_bgp.get(uart_item);
            // 根据事务类型转发到相应的analysis端口
            if (uart_item.is_tx) begin
              act_uart_tx_ap.write(uart_item);  // 实际UART TX数据
            end else begin
              act_uart_rx_ap.write(uart_item);  // 实际UART RX数据
            end
          end
        end
      join
    endtask : run_phase
  endclass : my_model

  class my_scoreboard extends uvm_component;
    `uvm_component_utils(my_scoreboard)

    uvm_blocking_get_port #(uart_trans) exp_bgp;
    uvm_blocking_get_port #(uart_trans) act_tx_bgp;
    uvm_blocking_get_port #(uart_trans) act_rx_bgp;
    uvm_blocking_get_port #(spi_trans)  act_spi_bgp;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      exp_bgp = new("exp_bgp", this);
      act_tx_bgp = new("act_tx_bgp", this);
      act_rx_bgp = new("act_rx_bgp", this);
      act_spi_bgp = new("act_spi_bgp", this);
    endfunction : build_phase

    int pass_cnt = 0;
    int total_cnt = 0;

    virtual task run_phase(uvm_phase phase);
      byte exp_q[$];
      byte act_tx_q[$];
      byte act_rx_q[$];
      logic [31:0] spi_q[$];
      semaphore softmax_sem;
      semaphore rx_spi_sem;

      softmax_sem = new(1);
      rx_spi_sem = new(1);

      fork
        begin : collect_exp
          // 收集期望的UART TX数据（softmax结果）
          uart_trans exp_item;
          forever begin
            exp_bgp.get(exp_item);
            exp_q.push_back(exp_item.data);
          end
        end

        begin : collect_act_tx
          // 收集实际的UART TX数据，并与期望值比较softmax结果
          uart_trans act_item;
          forever begin
            act_tx_bgp.get(act_item);
            act_tx_q.push_back(act_item.data);
            softmax_sem.get();
            if (exp_q.size() >= 16 && act_tx_q.size() >= 16) begin
              int i;
              logic all_pass = 1;
              for (i = 0; i < 16; i++) begin
                logic [7:0] exp_b;
                logic [7:0] act_b;
                real exp_r;
                real act_r;
                real diff;
                exp_b = exp_q.pop_front();
                act_b = act_tx_q.pop_front();
                exp_r = $itor(exp_b) / 256.0;
                act_r = $itor(act_b) / 256.0;
                diff = (exp_r > act_r) ? (exp_r - act_r) : (act_r - exp_r);
                if (diff > 0.125) begin
                  `uvm_error("SOFTMAX_CMP", $sformatf("idx=%0d exp=%0.5f act=%0.5f diff=%0.5f", i, exp_r, act_r, diff))
                  all_pass = 0;
                end
              end
              if (all_pass) pass_cnt++;
              total_cnt++;
            end
            softmax_sem.put();
          end
        end

        begin : collect_act_rx
          // 收集实际的UART RX数据
          uart_trans rx_item;
          forever begin
            act_rx_bgp.get(rx_item);
            act_rx_q.push_back(rx_item.data);
          end
        end

        begin : collect_spi
          // 收集SPI读数据，并与UART RX数据比较
          spi_trans spi_item;
          forever begin
            act_spi_bgp.get(spi_item);
            spi_q.push_back(spi_item.rdata);
            rx_spi_sem.get();
            if (act_rx_q.size() >= 4 && spi_q.size() >= 1) begin
              logic [7:0] b0;
              logic [7:0] b1;
              logic [7:0] b2;
              logic [7:0] b3;
              logic [31:0] uart_word;
              logic [31:0] spi_word;
              b0 = act_rx_q.pop_front();
              b1 = act_rx_q.pop_front();
              b2 = act_rx_q.pop_front();
              b3 = act_rx_q.pop_front();
              uart_word = {b3, b2, b1, b0};
              spi_word = spi_q.pop_front();
              if (uart_word !== spi_word) begin
                `uvm_error("UART_SPI_CMP", $sformatf("uart=%08x spi=%08x", uart_word, spi_word))
              end else begin
                pass_cnt++;
              end
              total_cnt++;
            end
            rx_spi_sem.put();
          end
        end
      join
    endtask : run_phase

    virtual function void final_phase(uvm_phase phase);
      super.final_phase(phase);
      $display("--------------------- [SCOREBOARD] --------------------");
      $display("|     Pass / Total : %d / %d        |" , pass_cnt,total_cnt);
      $display("|     Pass Rate : %f%%                         |", pass_cnt*100.0/total_cnt);
      $display("------------------------------------------------------");
    endfunction : final_phase
  endclass : my_scoreboard

endpackage
