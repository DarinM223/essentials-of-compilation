.global main
.text
tmp6:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  addq $0, %r15
start0:

  movq %rdi, %r11
  movq 16(%r11), %rcx
  movq %rdi, %r11
  movq 24(%r11), %rdx
  addq %rdx, %rcx
  movq %rcx, %rax
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
tmp0:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  addq $0, %r15
start6:

  movq %rsi, %r14
  movq $4, %rbx
  movq free_ptr(%rip), %rdx
  movq $32, %rsi
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
  movq $32, %rsi
  callq collect
  jmp block_body1
block_body1:

  movq free_ptr(%rip), %rsi
  addq $16, free_ptr(%rip)
  movq %rsi, %r11
  movq $7, (%r11)
  leaq tmp6(%rip), %rdx
  movq %rsi, %r11
  movq %rdx, 8(%r11)
  movq $0, %rdx
  movq %rsi, %r11
  movq %r14, 16(%r11)
  movq $0, %rdx
  movq %rsi, %r11
  movq %rbx, 24(%r11)
  movq $0, %rdx
  movq %rsi, %rax
  jmp block_exit1
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
  addq $16, %r15
start17:

  movq %rdi, %rsi
  movq free_ptr(%rip), %rdx
  movq $16, %rsi
  addq %rsi, %rdx
  movq fromspace_end(%rip), %rsi
  cmpq %rsi, %rdx
  jl block_t15
  jmp block_f16
block_t15:

  jmp block_t13
block_f16:

  jmp block_f14
block_t13:

  movq $0, %rsi
  jmp block_body12
block_f14:

  movq %r15, %rdi
  movq $16, %rsi
  callq collect
  jmp block_body12
block_body12:

  movq free_ptr(%rip), %rdi
  addq $16, free_ptr(%rip)
  movq %rdi, %r11
  movq $3, (%r11)
  leaq tmp0(%rip), %rsi
  movq %rdi, %r11
  movq %rsi, 8(%r11)
  movq $0, %rsi
  movq %rdi, %r11
  movq 8(%r11), %rdx
  movq $5, %rsi
  callq *%rdx
  movq %rax, -8(%r15)
  movq free_ptr(%rip), %rdx
  movq $16, %rsi
  addq %rsi, %rdx
  movq fromspace_end(%rip), %rsi
  cmpq %rsi, %rdx
  jl block_t10
  jmp block_f11
block_t10:

  jmp block_t8
block_f11:

  jmp block_f9
block_t8:

  movq $0, %rsi
  jmp block_body7
block_f9:

  movq %r15, %rdi
  movq $16, %rsi
  callq collect
  jmp block_body7
block_body7:

  movq free_ptr(%rip), %rdi
  addq $16, free_ptr(%rip)
  movq %rdi, %r11
  movq $3, (%r11)
  leaq tmp0(%rip), %rsi
  movq %rdi, %r11
  movq %rsi, 8(%r11)
  movq $0, %rsi
  movq %rdi, %r11
  movq 8(%r11), %rdx
  movq $3, %rsi
  callq *%rdx
  movq %rax, -16(%r15)
  movq -8(%r15), %r11
  movq 8(%r11), %rdx
  movq $11, %rsi
  movq -8(%r15), %rdi
  callq *%rdx
  movq %rax, %rbx
  movq -16(%r15), %r11
  movq 8(%r11), %rdx
  movq $15, %rsi
  movq -16(%r15), %rdi
  callq *%rdx
  movq %rax, %rsi
  movq %rbx, %rax
  addq %rsi, %rax
  jmp block_exit2
block_exit2:

  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $16, %r15
  retq
  # Should return 42 visible with `echo $?`
