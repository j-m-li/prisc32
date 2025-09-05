`default_nettype none
module soc (
	input	I_clk,     
	input	I_rst_btn,
`ifdef SIM
	output	[31:0] IO_gpio,
	output	[31:0] IO_addr,
`endif
	output	O_led
);

wire clk270, clk180, clk90, usr_ref_out,clk;
wire usr_pll_lock_stdy, usr_pll_lock;

CC_PLL #(
	.REF_CLK("10.0"),      // reference input in MHz
	.OUT_CLK("48.0"),     // pll output frequency in MHz
	.PERF_MD("SPEED"), // LOWPOWER, ECONOMY, SPEED
	.LOCK_REQ(0),
	.LOW_JITTER(1),      // 0: disable, 1: enable low jitter mode
	.CI_FILTER_CONST(10), // optional CI filter constant
	.CP_FILTER_CONST(20)  // optional CP filter constant
	) pll_inst (
		.CLK_REF(I_clk), 
		.CLK_FEEDBACK(1'b0), 
		.USR_CLK_REF(1'b0),
		.USR_LOCKED_STDY_RST(1'b0), 
		.USR_PLL_LOCKED_STDY(usr_pll_lock_stdy), 
		.USR_PLL_LOCKED(usr_pll_lock),
		.CLK270(clk270), 
		.CLK180(clk180), 
		.CLK90(clk90), 
		.CLK0(clk), 
		.CLK_REF_OUT(usr_ref_out)
	);


wire [31:0] imem_addr;
wire [31:0] imem_data;

wire [31:0] dmem_addr;
wire [31:0] dmem_rdata;
wire [31:0] dmem_wdata;
wire [3:0] dmem_wmask;
wire dmem_we;
wire mem_stall;
wire [31:0] wgpio; 
wire [31:0] rgpio = 0; 


reg [3:0] cnt;
initial cnt = 0;
wire rst;
assign rst = ~cnt[3];

`ifdef SIM
assign IO_gpio = dmem_wdata; 
assign IO_addr = dmem_addr; 
`endif
assign O_led = dmem_we;

always @(posedge clk)
begin
	if (~I_rst_btn) begin
		cnt <= 4'h0;
	end else if (rst) begin
		cnt <= cnt + 1'h1;
	end else begin 
//		O_led <= imem_addr[2];
	end
end



cache data (
	.I_clk(clk),
	.I_rst(rst),
	.I_gpio(rgpio),
	.O_gpio(wgpio),
	.I_iaddr(imem_addr),
	.O_idata(imem_data),
	.I_addr(dmem_addr),
	.I_data(dmem_wdata),
	.I_mask(dmem_wmask),
	.I_we(dmem_we),
	.O_data(dmem_rdata),
	.O_stall(mem_stall)
);


riscv cpu (
	.I_clk(clk),
	.I_rst(rst),
	.I_stall(mem_stall),
	.O_imem_addr(imem_addr),
	.I_imem_data(imem_data),
	.O_dmem_addr(dmem_addr),
	.I_dmem_rdata(dmem_rdata),
	.O_dmem_wdata(dmem_wdata),
	.O_dmem_wmask(dmem_wmask),
	.O_dmem_we(dmem_we)
);

//assign O_led = (imem_addr < 32'h80000000) ? 1 : 0;

endmodule

