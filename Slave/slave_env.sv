package slave_env_pkg;
  import slave_coverage_pkg::*;
  import slave_scoreboard_pkg::*;
  import slave_agent_pkg::*;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  class slave_env extends uvm_env;
    `uvm_component_utils(slave_env)

    slave_agent agt;
    slave_coverage cov;
    slave_scoreboard sb;

    function new(string name = "slave_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agt = slave_agent::type_id::create("agt", this);
      cov = slave_coverage::type_id::create("cov", this);
      sb  = slave_scoreboard::type_id::create("sb", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      agt.agt_ap.connect(sb.sb_export);
      agt.agt_ap.connect(cov.cov_export);
    endfunction

  endclass  //slave_env extends uvm_env
endpackage


