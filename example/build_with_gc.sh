as --64 -g -o $1.o $1.s
ld -z noexecstack --dynamic-linker=/lib64/ld-linux-x86-64.so.2 -o $1 $1.o -lc ../c/runtime.o