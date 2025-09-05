`timescale 1ns / 1ps

module tb;

	reg I_clk;
	reg I_rst_n;
	reg I_intr_in;

        wire [31:2] O_address_next;
        wire [3:0] O_byte_we_next;

        wire [31:2] O_address;
        wire [3:0] O_byte_we;
        wire [31:0] O_data_w;
        reg [31:0] I_data_r;
        reg I_mem_pause;

        reg [31:0] I_a;
        reg [31:0] I_b;
        wire [31:0] O_r;
        reg I_f;
        reg [3:0] I_func;

	reg I_rst_btn = 0;
	wire  O_led;
	wire [31:0] IO_gpio;
	wire [31:0] IO_addr;

	initial begin
`ifdef CCSDF
	//	$sdf_annotate("cod5_00.sdf", dut);
`endif
		$dumpfile("soc_tb.vcd");
		$dumpvars(0, tb);
		I_rst_n = 0;
	end

	initial begin
		I_clk = 0;
		forever begin
			I_clk = #1 ~I_clk;
		end
	end

`ifndef BOB
	initial begin
		$monitor("led: %b gpio:%h addr:%h", O_led, IO_gpio, IO_addr);
		#1
		I_rst_btn = 1;
		#5

		#5 
		#200
		I_rst_btn = 0;
		#5 
		$finish;

	end
	soc dut(
		.I_clk(I_clk),
		.I_rst_btn(I_rst_btn),
		.IO_gpio(IO_gpio),
		.IO_addr(IO_addr),
		.O_led(O_led)	
	);
`else
	initial begin
		$monitor("a: %b + b: %b = %b", I_a, I_b, O_r);
		I_a = 2; I_b = 3; I_f = 1;
		#10
		I_b = 1;
		#5
		$finish;

	end
	c5_adder dut(
    		.I_a(I_a),
    		.I_b(I_b),
        	.O_result(O_r),
		.I_do_add(I_f)
	);
	c5_cpu dut(
    		.I_clk(I_clk),
    		.I_rst_n(I_rst_n),
		.I_intr_in(I_intr_in),
		.O_address_next(O_address_next),
        	.O_byte_we_next(O_byte_we_next),
        	.O_address(O_address),
        	.O_byte_we(O_byte_we),
        	.O_data_w(O_data_w),
        	.I_data_r(I_data_r),
        	.I_mem_pause(I_mem_pause)
	);
`endif

endmodule

module CC_PLL #(
parameter CI_FILTER_CONST = 0,
parameter CP_FILTER_CONST = 0,
parameter LOCK_REQ = 0,
parameter LOW_JITTER  = 0,
parameter OUT_CLK = 0,
parameter PERF_MD = 0,
parameter REF_CLK  = 0
) (
	input CLK_FEEDBACK,
	input USR_CLK_REF,
	input USR_LOCKED_STDY_RST,
	output USR_PLL_LOCKED_STDY,
	output USR_PLL_LOCKED,
	output CLK90,
	output CLK270,
	output CLK180,
	output CLK_REF_OUT,

	input CLK_REF,
	output CLK0
);

assign CLK0 = CLK_REF;

endmodule


