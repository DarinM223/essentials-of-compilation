.global main
.text
tmp0:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  addq $0, %r15
start4:

  movq $0, %rsi
  cmpq %rsi, %rdi
  je block_t2
  jmp block_f3
block_t2:

  jmp block_t0
block_f3:

  jmp block_f1
block_t0:

  movq $1, %rax
  jmp block_exit
block_f1:

  leaq tmp1(%rip), %rsi
  movq $1, %rdx
  negq %rdx
  addq %rdx, %rdi
  movq %rsi, %rax
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  jmp *%rax
block_exit:

  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  retq
tmp1:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  addq $0, %r15
start9:

  movq $0, %rsi
  cmpq %rsi, %rdi
  je block_t7
  jmp block_f8
block_t7:

  jmp block_t5
block_f8:

  jmp block_f6
block_t5:

  movq $0, %rax
  jmp block_exit1
block_f6:

  leaq tmp0(%rip), %rsi
  movq $1, %rdx
  negq %rdx
  addq %rdx, %rdi
  movq %rsi, %rax
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  jmp *%rax
block_exit1:

  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  retq
main:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  movq rootstack_begin(%rip), %r15
  movq $0, (%r15)
  addq $0, %r15
start10:

  # 24 is even, so exit code (from `echo $?`) should return 1.
  leaq tmp0(%rip), %rsi
  movq $24, %rdi
  movq %rsi, %rax
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  jmp *%rax
