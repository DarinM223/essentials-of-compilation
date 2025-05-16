.global main
.text
main:
  pushq %rbp
  movq %rsp, %rbp
  pushq %r12
  pushq %rbx
  pushq %r13
  pushq %r14
  subq $32, %rsp
start:

  movq $20, -8(%rbp)
  movq $22, -16(%rbp)
  movq -8(%rbp), %rax
  movq %rax, -24(%rbp)
  movq -16(%rbp), %rax
  addq %rax, -24(%rbp)
  movq -24(%rbp), %rax
  # At this point %rax is 42, you can verify this in GDB
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  retq
