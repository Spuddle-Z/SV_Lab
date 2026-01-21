package my_sequence_pkg;

  import uvm_pkg::*;

  class my_transaction extends uvm_sequence_item;

    //`uvm_object_utils(my_transaction)

    rand bit cmd; //0 - read, 1 - write
    rand int addr;
    rand int data;

    `uvm_object_utils_begin(my_transaction)
      `uvm_field_int(cmd, UVM_ALL_ON)
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end

    constraint c_addr { addr >= 0 ; addr <= 255; }
    constraint c_data { data >= 0 ; data <= 255; }

    function new(string name = "");
      super.new(name);
    endfunction : new

  endclass : my_transaction

  class read_seq extends uvm_sequence #(my_transaction);

    `uvm_object_utils(read_seq)

    function new(string name = "");
      super.new(name);
    endfunction : new

    task body;

      my_transaction tx;

      tx = my_transaction::type_id::create("tx");   

      start_item(tx);
      assert( tx.randomize() with {cmd == 0;} );
      finish_item(tx);

    endtask : body

  endclass : read_seq

  class write_seq extends uvm_sequence #(my_transaction);

    `uvm_object_utils(write_seq)

    function new(string name = "");
      super.new(name);
    endfunction : new

    task body;

      my_transaction tx;

      tx = my_transaction::type_id::create("tx");

      start_item(tx);
      assert( tx.randomize() with {cmd == 1;} );
      finish_item(tx);

    endtask : body

  endclass : write_seq

  class read_modify_write_seq extends uvm_sequence #(my_transaction);

    `uvm_object_utils(read_modify_write_seq)

    int addr;
    int data;

    function new(string name = "");
      super.new(name);
    endfunction : new

    task body;

      my_transaction tx;

      tx = my_transaction::type_id::create("tx");

      start_item(tx);
      assert( tx.randomize() with {cmd == 0;} );
      finish_item(tx);

      addr = tx.addr;
      data = tx.data;

      start_item(tx);
      assert( tx.randomize() with {cmd == 1;} );
      tx.addr = addr;
      tx.data = 'h100 - data;
      finish_item(tx);

    endtask : body

  endclass : read_modify_write_seq

endpackage : my_sequence_pkg
