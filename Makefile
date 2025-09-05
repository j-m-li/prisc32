
all:   
	./configure.cmd .. build || configure.cmd .. build
	
wa:
#	clang --target=wasm32 -S -I d/ -o tk.s d/tk.c
#	clang --target=wasm32 -c -I d/ -o tk.o tk.s
#	wasm-ld -allow-undefined --no-entry  -o tk.wasm tk.o
	clang -ansi --target=wasm32 -nostdlib \
		-Wl,--export-all,-allow-undefined,--no-entry -fno-builtin\
	       	-D C90=1 \
		-I ~/.local/wpdcc/include/ \
		-I d/ -o edit.wasm \
		~/.local/wpdcc/lib/libwasm.a \
		d/main.c \
		d/edit.c \
		d/tk.c d/tk_inline.c d/tk_style.c d/tk_block.c d/tk_text.c \
		d/tk_range.c d/tk_tab.c
		zcat 3o3_exe.cmd.gz > test.cmd
		cat edit.wasm >> test.cmd
		http-server
#	llvm-objdump  --full-contents  -d tk.wasm


edit: d/edit.c d/main.c d/std.h
	cc -D C90=1 \
		-I d/ -o edit.exe d/main.c d/edit.c \
		d/tk.c d/tk_inline.c d/tk_style.c d/tk_block.c d/tk_text.c \
		d/tk_range.c d/tk_widget.c

mount:
	mkdir -p mnt
	sudo mount -o loop,umask=000,offset=$$((128*512)) -t vfat pdos.vhd mnt

run:
	qemu-system-i386 -drive file=pdos.vhd,index=0,media=disk,format=raw \
	-drive file=fat:rw:./d,id=fat32,format=raw,index=1


pdos: pdos.vhd run

pdos.vhd: pdos.zip
	unzip pdos.zip
	mv uc386.vhd pdos.vhd
	touch pdos.vhd

pdos.zip:
#	curl --output pdos.zip http://www.pdos.org/pdos.zip
	curl --output pdos.zip http://www.pdos.org/uc386.zip

clean:
	rm -f edit edit.exe
	rm -f *.zip *.vhd
	rm -f build/*.*
	rmdir build
fmt:
	clang-format --style="{BasedOnStyle: llvm,UseTab: Always,IndentWidth: 8,TabWidth: 8}" -i d/*.h d/*.c
	tidy -i -w 1024 --preserve-entities yes --show-info no --warn-proprietary-attributes no -m *.html
	js-beautify -n --no-preserve-newlines -w 79 -s 2 *.js

