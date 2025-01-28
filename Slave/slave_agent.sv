package slave_agent_pkg;
  import uvm_pkg::*;
  import slave_seq_item_pkg::*;
  import slave_monitor_pkg::*;
  import slave_config_pkg::*;
  import slave_sequencer_pkg::*;
  import slave_driver_pkg::*;
  `include "uvm_macros.svh"

  class slave_agent extends uvm_agent;
    `uvm_component_utils(slave_agent)

    slave_driver driver;
    slave_sequencer sqr;
    slave_monitor mon;
    slave_config slave_cfg;
    uvm_analysis_port #(slave_seq_item) agt_ap;

    function new(string name = "slave_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      if (!uvm_config_db#(slave_config)::get(this, "", "slave_CFG", slave_cfg)) begin
        `uvm_fatal("build_phase",
                   "Agent - Unable to get the configuratoin object of the slave from uvm_config_db")
      end

      if (slave_cfg.is_active == UVM_ACTIVE) begin
        driver = slave_driver::type_id::create("driver", this);
        sqr = slave_sequencer::type_id::create("sqr", this);
      end

      mon = slave_monitor::type_id::create("mon", this);
      agt_ap = new("agt_ap", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      if (slave_cfg.is_active == UVM_ACTIVE) begin
        driver.slave_vif = slave_cfg.slave_vif;
        driver.seq_item_port.connect(sqr.seq_item_export);
      end
      mon.slave_vif = slave_cfg.slave_vif;
      mon.mon_ap.connect(agt_ap);
    endfunction
  endclass  //slave_agent extends uvm_agent
endpackage
