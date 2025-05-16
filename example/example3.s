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
  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  movq rootstack_begin(%rip), %r15
  movq $0, (%r15)
  addq $8, %r15
start:

  movq free_ptr(%rip), %rcx
  movq $24, %rbx
  addq %rbx, %rcx
  movq fromspace_end(%rip), %rbx
  cmpq %rbx, %rcx
  jl block_t8
  jmp block_f9
block_t8:

  jmp block_t6
block_f9:

  jmp block_f7
block_t6:

  movq $0, %rbx
  jmp block_body5
block_f7:

  movq %r15, %rdi
  movq $24, %rsi
  callq collect
  jmp block_body5
block_body5:

  movq free_ptr(%rip), %rax
  movq %rax, -8(%r15)
  addq $16, free_ptr(%rip)
  movq -8(%r15), %r11
  movq $131, (%r11)
  movq free_ptr(%rip), %rcx
  movq $16, %rbx
  addq %rbx, %rcx
  movq fromspace_end(%rip), %rbx
  cmpq %rbx, %rcx
  jl block_t3
  jmp block_f4
block_t3:

  jmp block_t1
block_f4:

  jmp block_f2
block_t1:

  movq $0, %rbx
  jmp block_body0
block_f2:

  movq %r15, %rdi
  movq $16, %rsi
  callq collect
  jmp block_body0
block_body0:

  movq free_ptr(%rip), %rbx
  addq $16, free_ptr(%rip)
  movq %rbx, %r11
  movq $3, (%r11)
  movq $42, %rcx
  movq %rbx, %r11
  movq %rcx, 8(%r11)
  movq $0, %rcx
  movq -8(%r15), %r11
  movq %rbx, 8(%r11)
  movq $0, %rbx
  movq -8(%r15), %r11
  movq 8(%r11), %rbx
  movq %rbx, %r11
  movq 8(%r11), %rax
  jmp block_exit
block_exit:

  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  subq $8, %r15
  retq
