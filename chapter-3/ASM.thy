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

text{* executes an instruction given a state *}
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" 
  where "exec1 (LOADI n) _ stk = n # stk"
  | "exec1 (LOAD x) state stk = state(x) # stk"
  | "exec1  ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

text{* executes a list of instructions given an initial state. (It's a fold) *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" 
  where "exec [] _ stk = stk" 
  | "exec (i#is) s stk = exec is s (exec1 i s stk)"

text{* examples *}
value "exec [LOAD ''x''] <''x'' := 2> [0]"
value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done

subsection "Compilation"

text{* compiles an arithmetic expression to a list of instructions  *}
fun comp :: "aexp \<Rightarrow> instr list" 
  where "comp (N n) = [LOADI n]" 
  | "comp (V x) = [LOAD x]" 
  | "comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

(* (x + 1) + z*)
value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

(*let x = 2 and z = 4, then (x+1) + z = (2+1) + 4 = 7 *)
value "exec (comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))) <''x'':=2, ''z'':=4> []"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

text{* Exercises *}
text{*
Exercise 3.10. 
A stack underflow occurs when executing an ADD instruction on a stack of size
less than 2. In our semantics stack underflow lead to a term involving hd [],
which is not an error or exception (HOL does not have those concepts) but some
unspecified value. Modify theory ASM such that stack underflow is modelled by
None and normal execution by Some, i.e. the execution functions have return type
stack option. Modify all theorems and proofs accordingly.
*}
fun exec1_opt :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" 
  where "exec1_opt (LOADI n) _ stk = Some(n # stk)"
  | "exec1_opt (LOAD x) state stk = Some(state(x) # stk)"
  | "exec1_opt  ADD _ stk = (if length(stk) \<ge> 2 
                             then Some( (hd2 stk + hd stk) # tl2 stk ) 
                             else None)"

text{* executes a list of instructions given an initial state. (It's a fold) *}
fun exec_opt :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" 
  where "exec_opt [] _ stk = Some(stk)" 
  | "exec_opt (i#is) s stk = 
    (case (exec1_opt i s stk) of 
       None       \<Rightarrow> None
     | Some(stk') \<Rightarrow> exec_opt is s stk' )"

text{* examples *}
value "exec_opt [LOAD ''x''] <''x'' := 2> [0]"
value "exec_opt [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

fun append_opt :: "('a list) option \<Rightarrow> ('a list) option \<Rightarrow> ('a list) option"
  where "append_opt None _ = None"
  | "append_opt (Some(l)) None = None"
  | "append_opt (Some(l1)) (Some(l2)) = Some(l1@l2)"

lemma exec_opt_append[simp]:
  "(case (exec_opt is1 s stk) of
      None       \<Rightarrow> None
    | Some(stk') \<Rightarrow> exec_opt is2 s stk') = exec_opt (is1@is2) s stk"

apply(induction is1 arbitrary: stk)
apply(auto split: option.split)
done


text{*
Exercise 3.11. 
This exercises is about a register machine and compiler for aexp.
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
  = LDI int reg (* LDI n r loads n into register r *)
  | LD vname reg (* LD x r loads the value of x into register r *)
  | ADD reg reg (* ADD r1 r2 adds register r2 to register r1 *)

fun exec1_instr3 :: "instr3 \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state"
  where "exec1_instr3 (LDI n reg) _ rstate = rstate(reg := n)"
  | "exec1_instr3 (LD x r) state rstate = (let a = state(x) in rstate(r := a))"
  | "exec1_instr3 (ADD r1 r2) state rstate = 
      (let (r1val, r2val) = (rstate(r1), rstate(r2)) 
       in rstate(r1 := r1val + r2val))"

fun exec_instr3 :: "instr3 list \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" 
  where "exec_instr3 [] _ rstate = rstate" 
  | "exec_instr3 (i#is) state rstate = 
      (let rstate' = exec1_instr3 i state rstate 
       in exec_instr3 is state rstate')"

lemma exec_instr3_append[simp]:
  "exec_instr3 (is1@is2) s stk = exec_instr3 is2 s (exec_instr3 is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done


fun comp_instr3 :: "aexp \<Rightarrow> reg \<Rightarrow> instr3 list"
  where "comp_instr3 (N n) r = [LDI n r]"
  | "comp_instr3 (V x) r = [LD x r]"
  | "comp_instr3 (Plus e1 e2) r 
      = (comp_instr3 e1 r) @ (comp_instr3 e2 (r+1)) @ [ADD r (r+1)]"

lemma exec_aval_equiv_instr3[simp]: 
  "exec_instr3 (comp_instr3 a r) s rs r = aval a s"
  apply(induction a arbitrary: r s rs)
  apply(auto)
  done (* this is failing *)

text{*
Exercise 3.12. This a variation on the previous exercise. Let the instruction set be
               datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg
               All instructions refer implicitly to register 0 as the source (MV0) or target
               (all others). Define a compiler pretty much as explained above except that the
               compiled code leaves the value of the expression in register 0. Prove that
               exec (comp a r) s rs 0 = aval a s
*}

datatype instr0
  = LDI0 val
  | LD0 vname
  | MV0 reg
  | ADD0 reg

end