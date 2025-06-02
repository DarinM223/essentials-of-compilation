.global main
.text
main:
  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
start:

  movq $5, %rdx
  movq $6, %rdi
  movq $5, %rsi
  cmpq %rsi, %rdx
  jl block_t6
  jmp block_f13
block_t6:

  jmp block_f5
block_f13:

  movq $7, %rsi
  cmpq %rsi, %rdi
  je block_t9
  jmp block_f12
block_t9:

  movq $1, %rsi
  cmpq $0, %rsi
  je block_f8
  jmp block_t7
block_f12:

  movq $6, %rsi
  cmpq %rsi, %rdi
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

  movq $10, %rdx
  movq $1, %rsi
  movq %rsi, %rdi
  negq %rdi
  movq %rdx, %rsi
  addq %rdi, %rsi
  movq %rsi, %rax
  addq %rdx, %rax
  jmp block_exit
block_f5:

  cmpq %rdi, %rdx
  jl block_t3
  jmp block_f4
block_t3:

  jmp block_t1
block_f4:

  jmp block_f2
block_t1:

  movq %rdx, %rax
  addq %rdi, %rax
  jmp block_exit
block_f2:

  movq %rdi, %rsi
  negq %rsi
  movq %rdx, %rax
  addq %rsi, %rax
  jmp block_exit
block_exit:

  # At this point %rax should be 19
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  retq
