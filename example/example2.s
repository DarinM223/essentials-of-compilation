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
  movq $6, %rcx
  movq $5, %rbx
  cmpq %rbx, %rdx
  jl block_t6
  jmp block_f13
block_t6:

  jmp block_f5
block_f13:

  movq $7, %rbx
  cmpq %rbx, %rcx
  je block_t9
  jmp block_f12
block_t9:

  movq $1, %rbx
  cmpq $0, %rbx
  je block_f8
  jmp block_t7
block_f12:

  movq $6, %rbx
  cmpq %rbx, %rcx
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
  movq %rbx, %rdx
  negq %rdx
  movq %rcx, %rbx
  addq %rdx, %rbx
  movq %rbx, %rax
  addq %rcx, %rax
  jmp block_exit
block_f5:

  cmpq %rcx, %rdx
  jl block_t3
  jmp block_f4
block_t3:

  jmp block_t1
block_f4:

  jmp block_f2
block_t1:

  movq %rdx, %rax
  addq %rcx, %rax
  jmp block_exit
block_f2:

  negq %rcx
  movq %rdx, %rax
  addq %rcx, %rax
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
