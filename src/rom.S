
.section .text
.global _start
_start:
	nop
	nop
	nop
	li t0,0
	nop
	nop
	lui t1,0x00004 # 20 bit
	nop
	nop
	nop
	addi t1,t1,-0x100 # 12 bit
	nop
	nop
1:
	bgt t0, zero, bob
	addi t0,t0,1
	nop
	nop
	j 1b

bob:
	addi t0,t0,1
	nop
	nop
	sw t0, 8(t1) 
	nop
	li t2, 0xAA
	nop
	sw t2, 4(t1) 
	nop
	lw t0, 4(t1)
	j bob

	nop
	nop
	nop
	nop
