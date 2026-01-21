vlog +incdir+D:/Software/Questasim/verilog_src/uvm-1.2/src D:/Projects/Course/SV_Lab/uvm_demo/uvm_helloworld_ok/tb/top.sv

vsim -c -sv_lib D:/Software/Questasim/uvm-1.2/win64/uvm_dpi work.top -novopt +UVM_TESTNAME=test0
或者
vsim -c -sv_lib D:/Software/Questasim/uvm-1.2/win64/uvm_dpi work.top -novopt +UVM_TESTNAME=test1
或者
vsim -c -sv_lib D:/Software/Questasim/uvm-1.2/win64/uvm_dpi work.top -novopt +UVM_TESTNAME=test2
或者
vsim -c -sv_lib D:/Software/Questasim/uvm-1.2/win64/uvm_dpi work.top -novopt +UVM_TESTNAME=test3

注意：D:/Software/Questasim为Questasim安装路径，需要修改
