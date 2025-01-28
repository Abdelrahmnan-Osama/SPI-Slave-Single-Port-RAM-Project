package ram_agent_pkg;
  import uvm_pkg::*;
  import ram_seq_item_pkg::*;
  import ram_monitor_pkg::*;
  import ram_config_pkg::*;
  import ram_sequencer_pkg::*;
  import ram_driver_pkg::*;
  `include "uvm_macros.svh"

  class ram_agent extends uvm_agent;
    `uvm_component_utils(ram_agent)

    ram_driver driver;
    ram_sequencer sqr;
    ram_monitor mon;
    ram_config ram_cfg;
    uvm_analysis_port #(ram_seq_item) agt_ap;

    function new(string name = "ram_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      if (!uvm_config_db#(ram_config)::get(this, "", "RAM_CFG", ram_cfg)) begin
        `uvm_fatal("build_phase",
                   "Agent - Unable to get the configuratoin object of the ram from uvm_config_db")
      end

      if (ram_cfg.is_active == UVM_ACTIVE) begin
        driver = ram_driver::type_id::create("driver", this);
        sqr = ram_sequencer::type_id::create("sqr", this);
      end

      mon = ram_monitor::type_id::create("mon", this);
      agt_ap = new("agt_ap", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      if (ram_cfg.is_active == UVM_ACTIVE) begin
        driver.ram_vif = ram_cfg.ram_vif;
        driver.seq_item_port.connect(sqr.seq_item_export);
      end
      mon.ram_vif = ram_cfg.ram_vif;
      mon.mon_ap.connect(agt_ap);
    endfunction
  endclass  //ram_agent extends uvm_agent
endpackage
