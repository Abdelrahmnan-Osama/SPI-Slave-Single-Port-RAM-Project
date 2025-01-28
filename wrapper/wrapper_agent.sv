package wrapper_agent_pkg;
  import uvm_pkg::*;
  import wrapper_seq_item_pkg::*;
  import wrapper_monitor_pkg::*;
  import wrapper_config_pkg::*;
  import wrapper_sequencer_pkg::*;
  import wrapper_driver_pkg::*;
  `include "uvm_macros.svh"

  class wrapper_agent extends uvm_agent;
    `uvm_component_utils(wrapper_agent)

    wrapper_driver driver;
    wrapper_sequencer sqr;
    wrapper_monitor mon;
    wrapper_config wrapper_cfg;
    uvm_analysis_port #(wrapper_seq_item) agt_ap;

    function new(string name = "wrapper_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction  //new()

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      if (!uvm_config_db#(wrapper_config)::get(this, "", "wrapper_CFG", wrapper_cfg)) begin
        `uvm_fatal(
            "build_phase",
            "Agent - Unable to get the configuratoin object of the wrapper from uvm_config_db")
      end

      if (wrapper_cfg.is_active == UVM_ACTIVE) begin
        driver = wrapper_driver::type_id::create("driver", this);
        sqr = wrapper_sequencer::type_id::create("sqr", this);
      end

      mon = wrapper_monitor::type_id::create("mon", this);
      agt_ap = new("agt_ap", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      if (wrapper_cfg.is_active == UVM_ACTIVE) begin
        driver.wrapper_vif = wrapper_cfg.wrapper_vif;
        driver.seq_item_port.connect(sqr.seq_item_export);
      end
      mon.wrapper_vif = wrapper_cfg.wrapper_vif;
      mon.mon_ap.connect(agt_ap);
    endfunction
  endclass  //wrapper_agent extends uvm_agent
endpackage
