package wrapper_test_pkg;
  import uvm_pkg::*;
  import wrapper_seq_pkg::*;
  import wrapper_env_pkg::*;
  import ram_env_pkg::*;
  import slave_env_pkg::*;
  import wrapper_config_pkg::*;
  import ram_config_pkg::*;
  import slave_config_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_test extends uvm_test;
    `uvm_component_utils(wrapper_test)

    wrapper_env w_env;
    ram_env r_env;
    slave_env s_env;
    wrapper_config wrapper_cfg;
    ram_config ram_cfg;
    slave_config slave_cfg;
    wrapper_reset_seq reset_seq;
    wrapper_main_seq main_seq;

    function new(string name = "wrapper_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Disable transaction recording
      uvm_config_db#(int)::set(null, "", "recording_detail", 0);
      uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

      w_env = wrapper_env::type_id::create("w_env", this);
      r_env = ram_env::type_id::create("r_env", this);
      s_env = slave_env::type_id::create("s_env", this);

      wrapper_cfg = wrapper_config::type_id::create("wrapper_cfg");
      ram_cfg = ram_config::type_id::create("ram_cfg");
      slave_cfg = slave_config::type_id::create("slave_cfg");

      reset_seq = wrapper_reset_seq::type_id::create("reset_seq", this);
      main_seq = wrapper_main_seq::type_id::create("main_seq", this);

      if (!uvm_config_db#(virtual wrapper_if)::get(
              this, "", "wrapper_IF", wrapper_cfg.wrapper_vif
          )) begin
        `uvm_fatal("build_phase",
                   "Test - Unable to get virtual interface of the wrapper from uvm_config_db")
      end
      if (!uvm_config_db#(virtual ram_if)::get(this, "", "RAM_IF", ram_cfg.ram_vif)) begin
        `uvm_fatal("build_phase",
                   "Test - Unable to get virtual interface of the ram from uvm_config_db")
      end
      if (!uvm_config_db#(virtual slave_if)::get(this, "", "slave_IF", slave_cfg.slave_vif)) begin
        `uvm_fatal("build_phase",
                   "Test - Unable to get virtual interface of the slave from uvm_config_db")
      end

      wrapper_cfg.is_active = UVM_ACTIVE;
      ram_cfg.is_active = UVM_PASSIVE;
      slave_cfg.is_active = UVM_PASSIVE;

      uvm_config_db#(wrapper_config)::set(this, "*", "wrapper_CFG", wrapper_cfg);
      uvm_config_db#(ram_config)::set(this, "*", "ram_CFG", ram_cfg);
      uvm_config_db#(slave_config)::set(this, "*", "slave_CFG", slave_cfg);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      phase.raise_objection(this);

      `uvm_info("run_phase", "Reset Asserted", UVM_LOW)
      reset_seq.start(w_env.agt.sqr);
      `uvm_info("run_phase", "Reset Deasserted", UVM_LOW)

      `uvm_info("run_phase", "Stimulus Generation Started", UVM_LOW)
      main_seq.start(w_env.agt.sqr);
      `uvm_info("run_phase", " Stimulus Generation Ended", UVM_LOW)

      phase.drop_objection(this);
    endtask
  endclass  //wrapper_test extends uvm_test
endpackage
