text{*
Exercise 3.4. Take a copy of theory AExp and modify it as follows. Extend type aexp
              with a binary constructor Times that represents multiplication.
              Modify the definition of the functions aval and asimp accordingly.
              You can remove asimp_const. Function asimp should eliminate 0 and 1
              from multiplication as well as evaluate constant subterms. Update
              all proofs concerned.
*}

theory AExpMul 
  imports Main 
begin
  
subsection "Arithmetic Expressions with multiplication"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp 
  = N int 
  | V vname 
  | Plus aexp aexp
  | Times aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" 
  where "aval (N n) s = n" 
  | "aval (V x) s = s x" 
  | "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"
  | "aval (Times a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s * aval a\<^sub>2 s"

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

value "aval (Times (N 3) (N 2)) (\<lambda>x.0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
  
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"

text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}. *}


subsection "Constant Folding"

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" 
  where "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" 
  | "plus (N i) a = (if i=0 then a else Plus (N i) a)" 
  | "plus a (N i) = (if i=0 then a else Plus a (N i))" 
  | "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
 apply(induction a1 a2 rule: plus.induct)
 apply(auto)
 done

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"
  where "times (N i\<^sub>1) (N i\<^sub>2) = N (i\<^sub>1 * i\<^sub>2)"
  | "times (N i) a = (if i=1 then a else (if i=0 then N 0 else Times (N i) a))"
  | "times a (N i) = (if i=1 then a else (if i=0 then N 0 else Times (N i) a))"
  | "times a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"

lemma aval_times [simp]: "aval (times a1 a2) s = aval a1 s * aval a2 s"
 apply(induction a1 a2 rule: times.induct)
 apply simp_all
 done
    
fun asimp :: "aexp \<Rightarrow> aexp" 
  where "asimp (N n) = N n" 
  | "asimp (V x) = V x" 
  | "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"
  | "asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]: "aval (asimp a) s = aval a s"
  apply(induction a rule: asimp.induct)
  apply(auto)
  done

end