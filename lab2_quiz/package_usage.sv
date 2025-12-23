
package sky_pkg;

  class sun;
    typedef enum {RISE, FALL} state_e;
    state_e state = RISE;
  endclass

  class cloud;
  endclass
endpackage

package sea_pkg;

  class fish;
  endclass

  class island;
    string name;
    function new(string name = "island");
      this.name = name;
    endfunction
  endclass
  
  island hainan = new("hainan");
endpackage

module package_usage;
  import sky_pkg::cloud;
  import sky_pkg::sun;
  import sea_pkg::*;
  import sea_pkg::hainan;

  

  initial begin

    sun s;
    sun apollo = new();
    
    $display("sun state is %s", apollo.state);

    hainan = new("HAINAN");
    $display("hainan name is %s", hainan.name);
    $display("sea_pkg::hainan name is %s", sea_pkg::hainan.name);
  end
endmodule
