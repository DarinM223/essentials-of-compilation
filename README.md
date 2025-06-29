essentials-of-compilation
=========================

Code for the book Essentials of Compilation by Jeremy G Siek in OCaml using a pipeline of extensible well-typed tagless final DSLs described by [Oleg Kiselyov](https://okmij.org/ftp/tagless-final/). Each chapter file extends upon the code in the previous chapters, making it easy to see which parts changed in each chapter without having to go through the git history or to duplicate all of the ADTs and passes for each chapter.

To run the compilers for each chapter:
--------------------------------------

Each chapter file exports a `Compiler` functor that exposes a `res` type with a string of the compiled X86-64 assembly. You can run the compilers on the examples in each chapter in utop by running `dune utop`, opening the chapter module, applying the `Compiler` functor, and then printing the `res` value. So to view the generated assembly for Example 6 in Chapter 2, you would run this in `dune utop`:

```
utop # open Essentials.Chapter2;;
utop # module M = Compiler (Int) (Ex6) ();;
module M :
  sig
    val res :
      unit
      Essentials.Chapter2.SelectInstructions(Essentials.Chapter2.UncoverLocals(Essentials.Chapter2.C0_Pretty))(Essentials.Chapter2.AssignHomes(Essentials.Chapter2.PatchInstructions(Essentials.Chapter2.X86_0_Printer))).obs
  end
utop # print_endline M.res;;
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
  popq %r14
  popq %r13
  popq %rbx
  popq %r12
  movq %rbp, %rsp
  popq %rbp
  retq
- : unit = ()
```

You can write your own programs as modules in OCaml and then apply the `Compiler` functor on them to compile them to assembly. Try looking at
the examples in each chapter file to see how to use the DSL for each chapter.

To build and run the assembly:
------------------------------

The generated assembly needs to be assembled and linked with the runtime which contains the garbage collector. The `example/` folder contains assembly files generated by the compilers in each chapter. To build and run these example files, first you need to build the runtime by going into the `c/` folder and then running `./build.sh`.  Then change the directory to `example/` and run `./build.sh <file>` where `<file>` is the example file without the file extension. So to build and run Example 7, run:

```
> ./build.sh example7
> ./example7
> echo $?
42
```