# SPI Slave Interface with Single-Port RAM Verification

This repository showcases the design and verification of an SPI Slave Interface integrated with a Single-Port RAM. The project demonstrates efficient processor-to-RAM communication using the SPI protocol and robust UVM-based verification techniques.

## Project Overview

The project includes:
- **Design:** Implementation of the SPI Slave and Single-Port RAM modules using Verilog.
- **Verification:** Comprehensive validation using UVM, including active and passive verification environments.
- **Tools Used:** 
  - **Verilog**: Hardware description language for design.
  - **UVM**: Universal Verification Methodology for advanced functional verification.
  - **SVA**: SystemVerilog Assertions for protocol checks.
  - **QuestaSim**: Simulation tool for verification.
  - **Xilinx Vivado**: Used for synthesis and FPGA-based implementation.

## Design Highlights

1. **SPI Slave Module**:  
   - Designed to enable processor-to-RAM communication via the SPI protocol.  
   - Implemented a Finite State Machine (FSM) to manage operational states and ensure correct sequencing of operations.  

2. **Single-Port RAM**:  
   - Developed for efficient data storage and retrieval.  
   - Seamlessly integrated with the SPI Slave for effective communication and handling.  

3. **Integrated Wrapper**:  
   - Created a wrapper module combining the SPI Slave and Single-Port RAM for seamless data transfer and synchronization.

## Verification Highlights

- Independent UVM environments for active verification of SPI Slave and Single-Port RAM modules.  
- Passive verification of the integrated wrapper containing both components.  
- SystemVerilog Assertions (SVA) for protocol compliance and error detection.  
- Golden model and code/functional coverage for comprehensive validation.  
- Constraint randomization to test edge cases and ensure thorough coverage.  

## Repository Contents

- `design/`: Verilog source files for SPI Slave, Single-Port RAM, and the wrapper.  
- `verification/`: UVM testbench and test cases.  
- `sva/`: SystemVerilog Assertions for protocol validation.  
- `scripts/`: Simulation and synthesis scripts.  
- `docs/`: Documentation detailing the design and verification process.

## How to Run
1. Clone the repository.
2. Open in QuestaSim.
3. Run the `wrap.do` file to automate the tests and generate reports.

## Results
- Coverage reports for code, functional, and sequential domains.
