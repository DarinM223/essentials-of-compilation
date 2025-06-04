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
start0:

  addq %rsi, %rdi
  addq %rdx, %rdi
  addq %rcx, %rdi
  addq %r8, %rdi
  movq %r9, %r11
  movq 8(%r11), %rsi
  addq %rsi, %rdi
  movq %r9, %r11
  movq 16(%r11), %rsi
  movq %rdi, %rax
  addq %rsi, %rax
  jmp block_exit
block_exit:

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
  subq $16, %rsp
  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  movq rootstack_begin(%rip), %r15
  movq $0, (%r15)
  addq $0, %r15
start6:

  leaq tmp0(%rip), %rax
  movq %rax, -8(%rbp)
  movq $1, -16(%rbp)
  movq $2, %r12
  movq $3, %r13
  movq $4, %r14
  movq $5, %rbx
  movq free_ptr(%rip), %rdx
  movq $24, %rsi
  addq %rsi, %rdx
  movq fromspace_end(%rip), %rsi
  cmpq %rsi, %rdx
  jl block_t4
  jmp block_f5
block_t4:

  jmp block_t2
block_f5:

  jmp block_f3
block_t2:

  movq $0, %rsi
  jmp block_body1
block_f3:

  movq %r15, %rdi
  movq $24, %rsi
  callq collect
  jmp block_body1
block_body1:

  movq free_ptr(%rip), %r9
  addq $16, free_ptr(%rip)
  movq %r9, %r11
  movq $5, (%r11)
  movq $6, %rsi
  movq %r9, %r11
  movq %rsi, 8(%r11)
  movq $0, %rsi
  movq $7, %rsi
  movq %r9, %r11
  movq %rsi, 16(%r11)
  movq $0, %rsi
  movq -16(%rbp), %rdi
  movq %r12, %rsi
  movq %r13, %rdx
  movq %r14, %rcx
  movq %rbx, %r8
  movq -8(%rbp), %rax
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  jmp *%rax
  # Should return 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28 visible with `echo $?`
