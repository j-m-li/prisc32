
/*
 *                          cod5.com computer
 *
 *                   convert binary file to C header
 * 
 *                      17 may MMXXI PUBLIC DOMAIN
 *           The author disclaims copyright to this source code.
 *
 *
 */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static char hex[] = "0123456789ABCDEF";
int writeOut(FILE *out, int c)
{
	fwrite(hex + ((c >> 4) & 0xF), 1, 1, out);
	fwrite(hex + (c & 0xF), 1, 1, out);
	return 0;
}

int writeLine(FILE *out, int c)
{
	fwrite("/*", 1, 2, out);
	fwrite(hex + ((c >> 16) & 0xF), 1, 1, out);
	fwrite(hex + ((c >> 12) & 0xF), 1, 1, out);
	fwrite(hex + ((c >> 8) & 0xF), 1, 1, out);
	fwrite(hex + ((c >> 4) & 0xF), 1, 1, out);
	fwrite(hex + (c & 0xF), 1, 1, out);
	fwrite("*/ ", 1, 3, out);
	return 0;
}

int main(int argc, char *argv[])
{
	FILE *in;
	FILE *out;
	int n = 0;
	char c[4];
	char *vn;
	char *s;

	if (argc < 3)
	{
		fprintf(stderr, "USAGE: %s  infile outfile\n", argv[0]);
		exit(-1);
	}
	in = fopen(argv[1], "rb");
	if (!in)
	{
		fprintf(stderr, "cannot open %s\n", argv[1]);
		exit(-1);
	}
	out = fopen(argv[2], "w+b");
	if (!out)
	{
		fprintf(stderr, "cannot open %s\n", argv[2]);
		exit(-1);
	}
	while (fread(c, 1, 4, in) == 4)
	{
		//fprintf(out, "16'h%04x: ", n, n); 
	//	fprintf(out, "rom['h%04x] <= 8'h", n++); 
		//fprintf(out, "O_data <= 32'h", n); 
		writeOut(out, c[3]);
		//fprintf(out, "\n");
	//	fprintf(out, ";\nrom['h%04x] <= 8'h", n++); 
		writeOut(out, c[2]);
		//fprintf(out, "\n");
	//	fprintf(out, ";\nrom['h%04x] <= 8'h", n++); 
		writeOut(out, c[1]);
		//fprintf(out, "\n");
	//	fprintf(out, ";\nrom['h%04x] <= 8'h", n++); 
		writeOut(out, c[0]);
		fprintf(out, "\n");
		n += 4;
	}
	fclose(in);
	fclose(out);
	return 0;
}
