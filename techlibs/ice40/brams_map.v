
module \$__ICE40_RAM4K (
	output [15:0] RDATA,
	input         RCLK, RCLKE, RE,
	input  [10:0] RADDR,
	input         WCLK, WCLKE, WE,
	input  [10:0] WADDR,
	input  [15:0] MASK, WDATA
);
	parameter integer READ_MODE = 0;
	parameter integer WRITE_MODE = 0;
	parameter [0:0] NEGCLK_R = 0;
	parameter [0:0] NEGCLK_W = 0;

	parameter [255:0] INIT_0 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_1 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_2 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_3 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_4 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_5 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_6 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_7 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_8 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_9 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
	parameter [255:0] INIT_F = 256'h0000000000000000000000000000000000000000000000000000000000000000;

	generate
		case ({NEGCLK_R, NEGCLK_W})
			2'b00:
				SB_RAM40_4K #(
					.READ_MODE(READ_MODE),
					.WRITE_MODE(WRITE_MODE),
					.INIT_0(INIT_0),
					.INIT_1(INIT_1),
					.INIT_2(INIT_2),
					.INIT_3(INIT_3),
					.INIT_4(INIT_4),
					.INIT_5(INIT_5),
					.INIT_6(INIT_6),
					.INIT_7(INIT_7),
					.INIT_8(INIT_8),
					.INIT_9(INIT_9),
					.INIT_A(INIT_A),
					.INIT_B(INIT_B),
					.INIT_C(INIT_C),
					.INIT_D(INIT_D),
					.INIT_E(INIT_E),
					.INIT_F(INIT_F)
				) _TECHMAP_REPLACE_ (
					.RDATA(RDATA),
					.RCLK (RCLK ),
					.RCLKE(RCLKE),
					.RE   (RE   ),
					.RADDR(RADDR),
					.WCLK (WCLK ),
					.WCLKE(WCLKE),
					.WE   (WE   ),
					.WADDR(WADDR),
					.MASK (MASK ),
					.WDATA(WDATA)
				);
			2'b01:
				SB_RAM40_4KNW #(
					.READ_MODE(READ_MODE),
					.WRITE_MODE(WRITE_MODE),
					.INIT_0(INIT_0),
					.INIT_1(INIT_1),
					.INIT_2(INIT_2),
					.INIT_3(INIT_3),
					.INIT_4(INIT_4),
					.INIT_5(INIT_5),
					.INIT_6(INIT_6),
					.INIT_7(INIT_7),
					.INIT_8(INIT_8),
					.INIT_9(INIT_9),
					.INIT_A(INIT_A),
					.INIT_B(INIT_B),
					.INIT_C(INIT_C),
					.INIT_D(INIT_D),
					.INIT_E(INIT_E),
					.INIT_F(INIT_F)
				) _TECHMAP_REPLACE_ (
					.RDATA(RDATA),
					.RCLK (RCLK ),
					.RCLKE(RCLKE),
					.RE   (RE   ),
					.RADDR(RADDR),
					.WCLK (WCLK ),
					.WCLKE(WCLKE),
					.WE   (WE   ),
					.WADDR(WADDR),
					.MASK (MASK ),
					.WDATA(WDATA)
				);
			2'b10:
				SB_RAM40_4KNR #(
					.READ_MODE(READ_MODE),
					.WRITE_MODE(WRITE_MODE),
					.INIT_0(INIT_0),
					.INIT_1(INIT_1),
					.INIT_2(INIT_2),
					.INIT_3(INIT_3),
					.INIT_4(INIT_4),
					.INIT_5(INIT_5),
					.INIT_6(INIT_6),
					.INIT_7(INIT_7),
					.INIT_8(INIT_8),
					.INIT_9(INIT_9),
					.INIT_A(INIT_A),
					.INIT_B(INIT_B),
					.INIT_C(INIT_C),
					.INIT_D(INIT_D),
					.INIT_E(INIT_E),
					.INIT_F(INIT_F)
				) _TECHMAP_REPLACE_ (
					.RDATA(RDATA),
					.RCLK (RCLK ),
					.RCLKE(RCLKE),
					.RE   (RE   ),
					.RADDR(RADDR),
					.WCLK (WCLK ),
					.WCLKE(WCLKE),
					.WE   (WE   ),
					.WADDR(WADDR),
					.MASK (MASK ),
					.WDATA(WDATA)
				);
			2'b11:
				SB_RAM40_4KNRNW #(
					.READ_MODE(READ_MODE),
					.WRITE_MODE(WRITE_MODE),
					.INIT_0(INIT_0),
					.INIT_1(INIT_1),
					.INIT_2(INIT_2),
					.INIT_3(INIT_3),
					.INIT_4(INIT_4),
					.INIT_5(INIT_5),
					.INIT_6(INIT_6),
					.INIT_7(INIT_7),
					.INIT_8(INIT_8),
					.INIT_9(INIT_9),
					.INIT_A(INIT_A),
					.INIT_B(INIT_B),
					.INIT_C(INIT_C),
					.INIT_D(INIT_D),
					.INIT_E(INIT_E),
					.INIT_F(INIT_F)
				) _TECHMAP_REPLACE_ (
					.RDATA(RDATA),
					.RCLK (RCLK ),
					.RCLKE(RCLKE),
					.RE   (RE   ),
					.RADDR(RADDR),
					.WCLK (WCLK ),
					.WCLKE(WCLKE),
					.WE   (WE   ),
					.WADDR(WADDR),
					.MASK (MASK ),
					.WDATA(WDATA)
				);
		endcase
	endgenerate
endmodule


module \$__ICE40_RAM4K_M0 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [0:0] CLKPOL2 = 1;
	parameter [0:0] CLKPOL3 = 1;

	parameter [4095:0] INIT = 4096'bx;

	input CLK2;
	input CLK3;

	input [7:0] A1ADDR;
	output [15:0] A1DATA;

	input [7:0] B1ADDR;
	input [15:0] B1DATA;
	input [15:0] B1EN;

	wire [10:0] A1ADDR_11 = A1ADDR;
	wire [10:0] B1ADDR_11 = B1ADDR;

	\$__ICE40_RAM4K #(
		.READ_MODE(0),
		.WRITE_MODE(0),
		.NEGCLK_R(!CLKPOL2),
		.NEGCLK_W(!CLKPOL3),
		.INIT_0(INIT[ 0*256 +: 256]),
		.INIT_1(INIT[ 1*256 +: 256]),
		.INIT_2(INIT[ 2*256 +: 256]),
		.INIT_3(INIT[ 3*256 +: 256]),
		.INIT_4(INIT[ 4*256 +: 256]),
		.INIT_5(INIT[ 5*256 +: 256]),
		.INIT_6(INIT[ 6*256 +: 256]),
		.INIT_7(INIT[ 7*256 +: 256]),
		.INIT_8(INIT[ 8*256 +: 256]),
		.INIT_9(INIT[ 9*256 +: 256]),
		.INIT_A(INIT[10*256 +: 256]),
		.INIT_B(INIT[11*256 +: 256]),
		.INIT_C(INIT[12*256 +: 256]),
		.INIT_D(INIT[13*256 +: 256]),
		.INIT_E(INIT[14*256 +: 256]),
		.INIT_F(INIT[15*256 +: 256])
	) _TECHMAP_REPLACE_ (
		.RDATA(A1DATA),
		.RADDR(A1ADDR_11),
		.RCLK(CLK2),
		.RCLKE(1'b1),
		.RE(1'b1),
		.WDATA(B1DATA),
		.WADDR(B1ADDR_11),
		.MASK(~B1EN),
		.WCLK(CLK3),
		.WCLKE(1'b1),
		.WE(|B1EN)
	);
endmodule

module \$__ICE40_RAM4K_M123 (CLK2, CLK3, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 8;

	parameter [0:0] CLKPOL2 = 1;
	parameter [0:0] CLKPOL3 = 1;

	parameter [4095:0] INIT = 4096'bx;

	localparam MODE =
		CFG_ABITS ==  9 ? 1 :
		CFG_ABITS == 10 ? 2 :
		CFG_ABITS == 11 ? 3 : 'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	wire [10:0] A1ADDR_11 = A1ADDR;
	wire [10:0] B1ADDR_11 = B1ADDR;

	wire [15:0] A1DATA_16, B1DATA_16;

	generate
		if (MODE == 1) begin
			assign A1DATA = {A1DATA_16[14], A1DATA_16[12], A1DATA_16[10], A1DATA_16[ 8],
			                 A1DATA_16[ 6], A1DATA_16[ 4], A1DATA_16[ 2], A1DATA_16[ 0]};
			assign {B1DATA_16[14], B1DATA_16[12], B1DATA_16[10], B1DATA_16[ 8],
			        B1DATA_16[ 6], B1DATA_16[ 4], B1DATA_16[ 2], B1DATA_16[ 0]} = B1DATA;
			`include "brams_init1.vh"
		end
		if (MODE == 2) begin
			assign A1DATA = {A1DATA_16[13], A1DATA_16[9], A1DATA_16[5], A1DATA_16[1]};
			assign {B1DATA_16[13], B1DATA_16[9], B1DATA_16[5], B1DATA_16[1]} = B1DATA;
			`include "brams_init2.vh"
		end
		if (MODE == 3) begin
			assign A1DATA = {A1DATA_16[11], A1DATA_16[3]};
			assign {B1DATA_16[11], B1DATA_16[3]} = B1DATA;
			`include "brams_init3.vh"
		end
	endgenerate

	\$__ICE40_RAM4K #(
		.READ_MODE(MODE),
		.WRITE_MODE(MODE),
		.NEGCLK_R(!CLKPOL2),
		.NEGCLK_W(!CLKPOL3),
		.INIT_0(INIT_0),
		.INIT_1(INIT_1),
		.INIT_2(INIT_2),
		.INIT_3(INIT_3),
		.INIT_4(INIT_4),
		.INIT_5(INIT_5),
		.INIT_6(INIT_6),
		.INIT_7(INIT_7),
		.INIT_8(INIT_8),
		.INIT_9(INIT_9),
		.INIT_A(INIT_A),
		.INIT_B(INIT_B),
		.INIT_C(INIT_C),
		.INIT_D(INIT_D),
		.INIT_E(INIT_E),
		.INIT_F(INIT_F)
	) _TECHMAP_REPLACE_ (
		.RDATA(A1DATA_16),
		.RADDR(A1ADDR_11),
		.RCLK(CLK2),
		.RCLKE(1'b1),
		.RE(1'b1),
		.WDATA(B1DATA_16),
		.WADDR(B1ADDR_11),
		.WCLK(CLK3),
		.WCLKE(1'b1),
		.WE(|B1EN)
	);
endmodule

