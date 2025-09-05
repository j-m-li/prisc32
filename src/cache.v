
module cache (
	input	I_clk,     
	input	I_rst,
	input	[31:0] I_gpio,
	output reg [31:0] O_gpio,
	input	[31:0] I_iaddr,
	output reg [31:0] O_idata,
	input	[31:0] I_addr,
	input  [31:0] I_data,
	input  [3:0] I_mask,
	input   I_we,
	output reg [31:0] O_data,
	output reg O_stall
);

reg [7:0] ram0[0:16383];
reg [7:0] ram1[0:16383];
reg [7:0] ram2[0:16383];
reg [7:0] ram3[0:16383];
reg [31:0] rom[0:4095];
initial $readmemh("../src/rom.hex", rom);

wire [31:0] data_addr;
wire [31:0] data_addrn;
reg [31:0] addr0;
reg [31:0] addr1;
reg [31:0] addr2;
reg [31:0] addr3;
reg [31:0] data;

assign data_addr = I_addr;
assign data_addrn = I_addr + 4;

always @* begin
		case (data_addr[1:0]) 
		2'h0: begin
			addr0 <= data_addr;
			addr1 <= data_addr;
			addr2 <= data_addr;
			addr3 <= data_addr;
			end
		2'h1: begin
			addr0 <= data_addrn;
			addr1 <= data_addr;
			addr2 <= data_addr;
			addr3 <= data_addr;
			end
		2'h2: begin
			addr0 <= data_addrn;
			addr1 <= data_addrn;
			addr2 <= data_addr;
			addr3 <= data_addr;
			end
		2'h3: begin
			addr0 <= data_addrn;
			addr1 <= data_addrn;
			addr2 <= data_addrn;
			addr3 <= data_addr;
			end
		endcase

end

always @(posedge I_clk) begin
       	if (I_rst) begin
		O_data <= 32'h00000000;
		O_idata <= 32'h00000000;
		O_gpio <= 32'h00000000;
		O_stall <= 1;
	end else begin
		O_stall <= 0; 
		if (I_we) begin
			if (I_addr == 0) begin
				O_gpio <= I_data;
			end else begin
				case(data_addr[1:0])
				2'h0: begin
					if (I_mask[0]) ram0[addr0[31:2]] <=
				       			I_data[7:0];
					if (I_mask[1]) ram1[addr1[31:2]] <=
				       			I_data[15:8];
					if (I_mask[2]) ram2[addr2[31:2]] <=
				       			I_data[23:16];
					if (I_mask[3]) ram3[addr3[31:2]] <=
				       			I_data[31:24];
					end
				2'h1: begin
					if (I_mask[0]) ram1[addr1[31:2]] <=
				       			I_data[7:0];
					if (I_mask[1]) ram2[addr2[31:2]] <=
				       			I_data[15:8];
					if (I_mask[2]) ram3[addr3[31:2]] <=
				       			I_data[23:16];
					if (I_mask[3]) ram0[addr0[31:2]] <=
				       			I_data[31:24];
					end
				2'h2: begin
					if (I_mask[0]) ram2[addr2[31:2]] <=
				       			I_data[7:0];
					if (I_mask[1]) ram3[addr3[31:2]] <=
				       			I_data[15:8];
					if (I_mask[2]) ram0[addr0[31:2]] <=
				       			I_data[23:16];
					if (I_mask[3]) ram1[addr1[31:2]] <=
				       			I_data[31:24];
					end
				2'h3: begin
					if (I_mask[0]) ram3[addr3[31:2]] <=
				       			I_data[7:0];
					if (I_mask[1]) ram0[addr0[31:2]] <=
				       			I_data[15:8];
					if (I_mask[2]) ram1[addr1[31:2]] <=
				       			I_data[23:16];
					if (I_mask[3]) ram2[addr2[31:2]] <=
				       			I_data[31:24];
					end
				endcase
			end
			O_data <= 32'h0;
		end else begin
			// FIXME we should sort bytes here (see riscv.v LW/LH)
			O_data <= {
				ram3[addr3[31:2]],
				ram2[addr2[31:2]],
				ram1[addr1[31:2]],
				ram0[addr0[31:2]]
				};
	
		end
		// FIXME
		if (I_iaddr & 32'hFFFFF000) begin
			O_idata <= 32'h0;
		end else begin
			O_idata <= rom[I_iaddr[15:2]];
		end
	end
end

endmodule

