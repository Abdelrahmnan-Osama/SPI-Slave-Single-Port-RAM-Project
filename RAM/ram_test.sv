package ram_test_pkg;
  import uvm_pkg::*;
  import ram_seq_pkg::*;
  import ram_env_pkg::*;
  import ram_config_pkg::*;
  `include "uvm_macros.svh"

  class ram_test extends uvm_test;
    `uvm_component_utils(ram_test)

    ram_env env;
    ram_config ram_cfg;
    ram_reset_seq reset_seq;
    ram_main_seq main_seq;

    function new(string name = "ram_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Disable transaction recording
      uvm_config_db#(int)::set(null, "", "recording_detail", 0);
      uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

      env = ram_env::type_id::create("env", this);
      ram_cfg = ram_config::type_id::create("ram_cfg");
      reset_seq = ram_reset_seq::type_id::create("reset_seq", this);
      main_seq = ram_main_seq::type_id::create("main_seq", this);

      if (!uvm_config_db#(virtual ram_if)::get(this, "", "RAM_IF", ram_cfg.ram_vif)) begin
        `uvm_fatal("build_phase",
                   "Test - Unable to get virtual interface of the ram from uvm_config_db")
      end
      ram_cfg.is_active = UVM_ACTIVE;
      uvm_config_db#(ram_config)::set(this, "*", "RAM_CFG", ram_cfg);
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
  endclass  //ram_test extends uvm_test
endpackage
