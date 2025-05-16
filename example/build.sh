as --64 -g -o $1.o $1.s
gcc -z noexecstack -o $1 $1.o ../c/runtime.o