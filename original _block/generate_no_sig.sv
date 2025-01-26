module fifo_no_sig_sva_params_sva
(
input	clk,
input	rstn

);




//////////////////////////////// DUT inst /////////////////////////////
genvar gen_FIFO_DEPTH, gen_FIFO_WIDTH, gen_NUM_LOOPS, gen_ADD_MODE;

generate

for (gen_FIFO_DEPTH = 2; gen_FIFO_DEPTH <= 8; gen_FIFO_DEPTH++)	begin: gen_FIFO_DEPTH_block
	if ((gen_FIFO_DEPTH ==  2) || (gen_FIFO_DEPTH ==  4) || (gen_FIFO_DEPTH ==  8))
		for (gen_FIFO_WIDTH = 8; gen_FIFO_WIDTH <= 11; gen_FIFO_WIDTH++)	begin: gen_FIFO_WIDTH_block
			if ((gen_FIFO_WIDTH ==  8) || (gen_FIFO_WIDTH ==  9) || (gen_FIFO_WIDTH ==  10) || (gen_FIFO_WIDTH ==  11))
				for (gen_NUM_LOOPS = 3; gen_NUM_LOOPS <= 6; gen_NUM_LOOPS++)	begin: gen_NUM_LOOPS_block
					if ((gen_NUM_LOOPS ==  3) || (gen_NUM_LOOPS ==  4) || (gen_NUM_LOOPS ==  5) || (gen_NUM_LOOPS ==  6))
						for (gen_ADD_MODE = 0; gen_ADD_MODE <= 1; gen_ADD_MODE++)	begin: gen_ADD_MODE_block
							if ((gen_ADD_MODE ==  0) || (gen_ADD_MODE ==  1))

begin

logic  push ;
logic [gen_FIFO_WIDTH-1:0] push_data ;
logic  pop ;
logic [gen_FIFO_WIDTH-1:0] pop_data ;
logic  empty ;
logic  full ;

fifo_no_sig_sva#(
.FIFO_DEPTH (gen_FIFO_DEPTH),
.FIFO_WIDTH (gen_FIFO_WIDTH),
.NUM_LOOPS (gen_NUM_LOOPS),
.ADD_MODE (gen_ADD_MODE)
)
u_dut_fifo_no_sig_sva
(
.*
);

end
end   //gen_FIFO_DEPTH_block
end   //gen_FIFO_WIDTH_block
end   //gen_NUM_LOOPS_block
end   //gen_ADD_MODE_block

endgenerate




endmodule
