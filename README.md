This repository contains 2 blocks.
1. The original block with parmeters.
2. The generated signal design.

</br></br>

The original block has:
- A DUT with parameters- *fifo_with_params.sv*
- A testbench - *fifo_with_params_sva.sv*
- A generate loop for all parameter options - *generate_fifo_with_params_sva.sv* **- this should be the top module**

</br>

The generated signal design has:
- A DUT with input signals instead of parameters - *fifo_with_sig.sv*
- A single testbench for all parameter options - *fifo_with_sig_sva.sv* **- this should be the top module**

</br>

**Feel free to compare the results with your favorite formal verification tool.**
