theory ASM 
  imports AExp 
begin

subsection "Stack Machine"

datatype instr 
  = LOADI val (* Load immediate, puts n on top of the stack*)
  | LOAD vname (* puts the value of x on top of stack *)
  | ADD (* Replaces the two topmost elements of the stack by their sum *)

type_synonym stack = "val list"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

text{* Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.*}

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" 
  where "exec1 (LOADI n) _ stk = n # stk"
  | "exec1 (LOAD x) s stk = s(x) # stk"
  | "exec1  ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" 
  where "exec [] _ stk = stk" 
  | "exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done

subsection "Compilation"

fun comp :: "aexp \<Rightarrow> instr list" 
  where "comp (N n) = [LOADI n]" 
  | "comp (V x) = [LOAD x]" 
  | "comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

text{* Exercises *}
text{*
Exercise 3.10. A stack underflow occurs when executing an ADD instruction on a stack of size
               less than 2. In our semantics stack underflow lead to a term involving hd [],
               which is not an error or exception (HOL does not have those concepts) but some
               unspecified value. Modify theory ASM such that stack underflow is modelled by
               None and normal execution by Some, i.e. the execution functions have return type
               stack option. Modify all theorems and proofs accordingly.
*}

text{*
Exercise 3.11. This exercises is about a register machine and compiler for aexp.
               The machine instructions are
               datatype instr = LDI int reg | LD vname reg | ADD reg reg
               where type reg is a synonym for nat. Instruction LDI i r loads i into
               register r, LD x r loads the value of x into register r, and ADD r1 r2
               adds register r2 to register r1.
               Define the execution of an instruction given a state and a register state
               (= function from registers to integers); the result is the new register state:
               fun exec1 :: instr => state => (reg => int) => reg => int
               Define the execution exec of a list of instructions as for the stack machine.
               The compiler takes an arithmetic expression a and a register r and produces a
               list of instructions whose execution places the value of a into r.
               The registers > r should be used in a stack-like fashion for intermediate results,
               the ones < r should be left alone. Define the compiler and prove it correct:
               exec (comp a r) s rs r = aval a s
*}
type_synonym reg = "nat"
type_synonym reg_state = "(reg \<Rightarrow> int)"

datatype instr3
  = LDI int reg
  | LD vname reg
  | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg \<Rightarrow> int"
  where "exec1 (LDI n reg) _ rstate r = "
  | "exec1 (LD x r) state rstate r = " 
text{*
Exercise 3.12. This a variation on the previous exercise. Let the instruction set be
               datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg
               All instructions refer implicitly to register 0 as the source (MV0) or target
               (all others). Define a compiler pretty much as explained above except that the
               compiled code leaves the value of the expression in register 0. Prove that
               exec (comp a r) s rs 0 = aval a s
*}

end