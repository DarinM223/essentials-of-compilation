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
  addq $16, %r15
start5:

  movq %rdi, %rbx
  movq %rsi, -8(%r15)
  movq free_ptr(%rip), %rdx
  movq $24, %rsi
  addq %rsi, %rdx
  movq fromspace_end(%rip), %rsi
  cmpq %rsi, %rdx
  jl block_t3
  jmp block_f4
block_t3:

  jmp block_t1
block_f4:

  jmp block_f2
block_t1:

  movq $0, %rsi
  jmp block_body0
block_f2:

  movq %r15, %rdi
  movq $24, %rsi
  callq collect
  jmp block_body0
block_body0:

  movq free_ptr(%rip), %rax
  movq %rax, -16(%r15)
  addq $16, free_ptr(%rip)
  movq -16(%r15), %r11
  movq $5, (%r11)
  movq -8(%r15), %r11
  movq 8(%r11), %rdi
  callq *%rbx
  movq %rax, %rsi
  movq -16(%r15), %r11
  movq %rsi, 8(%r11)
  movq $0, %rsi
  movq -8(%r15), %r11
  movq 16(%r11), %rdi
  callq *%rbx
  movq %rax, %rsi
  movq -16(%r15), %r11
  movq %rsi, 16(%r11)
  movq $0, %rsi
  movq -16(%r15), %rax
  jmp block_exit
block_exit:

  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $16, %r15
  retq
tmp3:

  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $0, %rsp
  addq $0, %r15
start6:

  movq $1, %rsi
  movq %rdi, %rax
  addq %rsi, %rax
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
  addq $0, %r15
start12:

  leaq tmp0(%rip), %r14
  leaq tmp3(%rip), %rbx
  movq free_ptr(%rip), %rdi
  movq $24, %rdx
  addq %rdx, %rdi
  movq fromspace_end(%rip), %rdx
  cmpq %rdx, %rdi
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
  movq $24, %rsi
  callq collect
  jmp block_body7
block_body7:

  movq free_ptr(%rip), %rsi
  addq $16, free_ptr(%rip)
  movq %rsi, %r11
  movq $5, (%r11)
  movq $0, %rdx
  movq %rsi, %r11
  movq %rdx, 8(%r11)
  movq $0, %rdx
  movq $41, %rdx
  movq %rsi, %r11
  movq %rdx, 16(%r11)
  movq $0, %rdx
  movq %rbx, %rdi
  callq *%r14
  movq %rax, %rsi
  movq %rsi, %r11
  movq 16(%r11), %rax
  jmp block_exit2
block_exit2:

  # At this point %rax should be 42
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $0, %r15
  retq
