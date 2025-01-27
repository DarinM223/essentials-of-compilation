.global _start
.text
_start:
  movq %rsp, %rbp
  subq $24, %rsp
start:

  movq $22, -8(%rbp)
  movq $20, -16(%rbp)
  movq -16(%rbp), %rax
  movq %rax, -24(%rbp)
  movq -8(%rbp), %rax
  addq %rax, -24(%rbp)
  movq -24(%rbp), %rax
  # At this point %rax is 42, you can verify this in GDB
  addq $24, %rsp
  retq
