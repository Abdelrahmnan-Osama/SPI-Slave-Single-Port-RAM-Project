package slave_test_pkg;
  import uvm_pkg::*;
  import slave_seq_pkg::*;
  import slave_env_pkg::*;
  import slave_config_pkg::*;
  `include "uvm_macros.svh"

  class slave_test extends uvm_test;
    `uvm_component_utils(slave_test)

    slave_env env;
    slave_config slave_cfg;
    slave_reset_seq reset_seq;
    slave_main_seq main_seq;

    function new(string name = "slave_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Disable transaction recording
      uvm_config_db#(int)::set(null, "", "recording_detail", 0);
      uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

      env = slave_env::type_id::create("env", this);
      slave_cfg = slave_config::type_id::create("slave_cfg");
      reset_seq = slave_reset_seq::type_id::create("reset_seq", this);
      main_seq = slave_main_seq::type_id::create("main_seq", this);

      if (!uvm_config_db#(virtual slave_if)::get(this, "", "slave_IF", slave_cfg.slave_vif)) begin
        `uvm_fatal("build_phase",
                   "Test - Unable to get virtual interface of the slave from uvm_config_db")
      end
      slave_cfg.is_active = UVM_ACTIVE;
      uvm_config_db#(slave_config)::set(this, "*", "slave_CFG", slave_cfg);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);

      `uvm_info("run_phase", "Reset Asserted", UVM_LOW)
      reset_seq.start(env.agt.sqr);
      `uvm_info("run_phase", "Reset Deasserted", UVM_LOW)

      `uvm_info("run_phase", "Stimulus Generation Started", UVM_LOW)
      main_seq.start(env.agt.sqr);
      `uvm_info("run_phase", " Stimulus Generation Ended", UVM_LOW)

      phase.drop_objection(this);
    endtask
  endclass  //slave_test extends uvm_test
endpackage
