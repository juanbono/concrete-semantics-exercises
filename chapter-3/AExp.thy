theory AExp 
  imports Main
begin
type_synonym vname = string

datatype aexp 
  = N int 
  | V vname
  | Plus aexp aexp

(* semantics *)
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val"
  where "aval (N n) s = n"
  | "aval (V x) s = s x"
  | "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"

text {* A little syntax magic to write larger states compactly: *}
  
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

(* We can now write a series of updates to the function \<lambda>x.0 compactly: *)
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2 :: int))" 
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

(* Constant folding: Replacing of constant sub expression for his value *)

(*constant folding in a bottom-up manner *)
fun asimp_const :: "aexp \<Rightarrow> aexp"
  where "asimp_const (N n) = N n"
  | "asimp_const (V x) = V x"
  | "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) 
      of (N n1, N n2) \<Rightarrow> N (n1 + n2)
      |  (b1,b2)      \<Rightarrow> Plus b1 b2)"

(* Correctness for asimp_const means that it doesn't change the semantics *)
lemma "aval (asimp_const a) s = aval a s" 
  apply(induction a)
  apply(auto split: aexp.split)
  done

(* An optimizing version of Plus *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"
  where "plus (N i1) (N i2) = N (i1 + i2)"
  |     "plus (N i) a = (if i = 0 then a else Plus (N i) a)"
  |     "plus a (N i) = (if i = 0 then a else Plus a (N i))"
  |     "plus a1 a2 = Plus a1 a2"

(*Proof that it behaves like Plus under evaluation*)
lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction rule:plus.induct)
  apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp"
  where "asimp (N n) = N n"
    |   "asimp (V x) = V x"
    |   "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
  apply(auto split: aexp.split simp: aval_plus)
  done
    
text{* Exercises *}
text{*
Exercise 3.1. To show that asimp_const really folds all subexpressions of
              the form Plus (N i) (N j), define a function optimal :: aexp => bool
              that checks that its argument does not contain a subexpression of the
              form Plus (N i) (N j). Then prove optimal (asimp_const a).
*}
fun optimal :: "aexp \<Rightarrow> bool"
  where "optimal (N n) = True"
    | "optimal (V x) = True"
    | "optimal (Plus (N _) (N _)) = False"
    | "optimal (Plus va vb) = (case optimal va 
        of True  \<Rightarrow> optimal vb
        |  False \<Rightarrow> False)"

lemma "optimal (asimp_const a)"
  apply(induction a)
  apply(auto split: aexp.split)
  done

text{*  
Exercise 3.2. In this exercise we verify constant folding for aexp where we
              sum up all constants, even if they are not next to each other.
              For example Plus (N 1) (Plus (V x) (N 2)) becomes Plus (V x) (N 3).
              This goes beyond asimp. Define a function full_asimp :: aexp => aexp
              that sums up all constants and prove its correctness:
              aval (full_asimp a) s = aval a s.
*}
fun full_asimp :: "aexp \<Rightarrow> aexp"
  where "full_asimp (N n) = N n"
  | "full_asimp (V x) = V x"
  | "full_asimp (Plus (N n1) (N n2)) = N (n1+n2)"
  | "full_asimp (Plus va vb) = Plus (full_asimp va) (full_asimp vb)"

lemma full_asimp_correctness: "aval (full_asimp a) s = aval a s"
  apply(induction rule: full_asimp.induct)
  apply(auto)
  done

text{*
Exercise 3.3. Substitution is the process of replacing a variable by an expression
              in an expression. Define a substitution function 
              subst :: vname => aexp => aexp such that subst x a e is the result
              of replacing every occurrence of variable x by a in e. For example:
              subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')
              Prove the so-called substitution lemma that says that we can either
              substitute first and evaluate afterwards or evaluate with an updated
              state: aval (subst x a e) s = aval e (s (x := aval a s)).
              As a consequence prove: 
              aval a1 s = aval a2 s => aval (subst x a1 e) s = aval (subst x a2 e) s
*}

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"
  where "subst x e (N n) = N n "
  | "subst x e (V y) = (if x=y then e else V y)"
  | "subst x e (Plus e1 e2) = Plus (subst x e e1) (subst x e e2)"

lemma substitution_lemma: 
  "aval (subst x a expr) state = aval expr (state (x := aval a state))"
  apply(induction expr)
  apply(auto)
  done

text{*
Exercise 3.4. Take a copy of theory AExp and modify it as follows. Extend type aexp
              with a binary constructor Times that represents multiplication.
              Modify the definition of the functions aval and asimp accordingly.
              You can remove asimp_const. Function asimp should eliminate 0 and 1
              from multiplication as well as evaluate constant subterms. Update
              all proofs concerned.
*}

text{*
Exercise 3.5. Define a datatype aexp2 of extended arithmetic expressions that has,
              in addition to constructors of aexp, a constructor for modelling
              a C-like post-increment operation x++, where x must be a variable.
              Define an evaluation function aval2 :: aval2 => state => val * state
              that returns both the value of the expression and the new state.
              The latter is required because post-increment changes the state.
              Extend aexp2 and aval2 with a division operation. Model partiality
              of division by changing the return type of aval2 to (val * state)
              option. In case of division by 0 let aval2 return None. Division
              on int is the infix div.
*}

text{*
Exercise 3.6. The following type add a LET construct to arithmetic expressions:
              datatype lexp = Nl int 
                            | Vl vname 
                            | Plusl lexp lexp 
                            | LET vname lexp lexp
              The LET constructor introduces a local variable: the value of
              LET x e1 e2 is the value of e2 in the state where x is bound to
              the value of e1 in the original state. Define a function
              lval :: lexp => state => int that evaluates lexp expressions.
              Remember s(x := i).
              Define a conversion inline :: lexp => aexp. The expression LET x e1 e2
              is inlined by substituting the converted form of e1 for x in the
              converted form of e2. See exercise 3.3 for more on substitution.
              Prove that inline is correct w.r.t evaluation.
*}

  
text {* Boolean Expressions *}
end