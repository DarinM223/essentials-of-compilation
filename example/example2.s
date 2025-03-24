.global _start
.text
_start:
  movq %rsp, %rbp
  subq $8, %rsp
start:

  movq $5, %rdx
  movq $6, %rbx
  movq $5, %rcx
  cmpq %rcx, %rdx
  jl block_t6
  jmp block_f13
block_t6:

  jmp block_f5
block_f13:

  movq $7, %rcx
  cmpq %rcx, %rbx
  je block_t9
  jmp block_f12
block_t9:

  movq $1, %rcx
  cmpq $0, %rcx
  je block_f8
  jmp block_t7
block_f12:

  movq $6, %rcx
  cmpq %rcx, %rbx
  je block_t10
  jmp block_f11
block_t7:

  jmp block_f5
block_f8:

  jmp block_t0
block_t10:

  jmp block_t0
block_f11:

  jmp block_f5
block_t0:

  movq $10, %rcx
  movq $1, %rbx
  negq %rbx
  movq %rcx, %rdx
  addq %rbx, %rdx
  movq %rdx, %rax
  addq %rcx, %rax
  jmp block_exit
block_f5:

  cmpq %rbx, %rdx
  jl block_t3
  jmp block_f4
block_t3:

  jmp block_t1
block_f4:

  jmp block_f2
block_t1:

  movq %rdx, %rax
  addq %rbx, %rax
  jmp block_exit
block_f2:

  negq %rbx
  movq %rdx, %rax
  addq %rbx, %rax
  jmp block_exit
block_exit:

  addq $8, %rsp
  retq
