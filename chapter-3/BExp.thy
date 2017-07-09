theory BExp
  imports AExp 
begin

subsection "Boolean Expressions"

datatype bexp = Bc bool 
              | Not bexp 
              | And bexp bexp 
              | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" 
  where "bval (Bc v) s = v" 
  | "bval (Not b) s = (\<not> bval b s)" 
  | "bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" 
  | "bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
            <''x'' := 3, ''y'' := 1>"


subsection "Constant Folding"

text{* Optimizing constructors: *}

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" 
  where "less (N n\<^sub>1) (N n\<^sub>2) = Bc(n\<^sub>1 < n\<^sub>2)" 
  | "less a\<^sub>1 a\<^sub>2 = Less a\<^sub>1 a\<^sub>2"


lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction a1 a2 rule: less.induct)
apply(simp_all)
done


fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" 
  where "and (Bc True) b = b" 
  | "and b (Bc True) = b" 
  | "and (Bc False) b = Bc False" 
  | "and b (Bc False) = Bc False" 
  | "and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"


lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
apply(induction b1 b2 rule: and.induct)
apply(simp_all)
done


fun not :: "bexp \<Rightarrow> bexp" 
  where "not (Bc True) = Bc False" 
  | "not (Bc False) = Bc True" 
  | "not b = Not b"

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
apply(induction b rule: not.induct)
apply(simp_all)
done

text{* Now the overall optimizer: *}

fun bsimp :: "bexp \<Rightarrow> bexp" 
  where "bsimp (Bc v) = Bc v" 
  | "bsimp (Not b) = not(bsimp b)" 
  | "bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)" 
  | "bsimp (Less a\<^sub>1 a\<^sub>2) = less (asimp a\<^sub>1) (asimp a\<^sub>2)"

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

theorem "bval (bsimp b) s = bval b s"
 apply(induction b)
 apply(auto) 
done

text{* Exercises *}
text{*
Exercise 3.7. Define functions Eq, Le :: aexp => aexp => bexp and prove 
              bval (Eq a1 a2) s = (aval a1 s = aval a2 s) and
              bval (Le a1 a2) s = (aval a1 s <= aval a2 s)
*}
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp"
  where "Eq l r = And (Not (Less l r)) (Not ((Less r l)))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp"
  where "Le l r = Not (Less r l)"

lemma "bval (Eq a\<^sub>1 a\<^sub>2) state = (aval a\<^sub>1 state = aval a\<^sub>2 state)"  
  apply(induction a\<^sub>1 arbitrary: a\<^sub>2)
  apply(auto)
  done

lemma "bval (Le a\<^sub>1 a\<^sub>2) state = (aval a\<^sub>1 state \<le> aval a\<^sub>2 state)"
  apply(induction a\<^sub>1 arbitrary: a\<^sub>2)
  apply(auto)
  done

text{*
Exercise 3.8. Consider an alternative type of boolean expressions featuring a
              conditional:
              datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
              First define an evaluation function 
              ifval :: ifexp => state => bool analogously to bval. Then define two
              functions b2ifexp :: bexp => ifexp and if2bexp :: ifexp => bexp and
              prove their correctness, i.e., that they preserve the value of an exp.
*}
datatype ifexp 
  = Bc2 bool 
  | If ifexp ifexp ifexp 
  | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool"
  where "ifval (Bc2 b) s = b"
  | "ifval (If e\<^sub>1 e\<^sub>2 e\<^sub>3) s = (if (ifval e\<^sub>1 s) then (ifval e\<^sub>2 s) else (ifval e\<^sub>3 s))"
  | "ifval (Less2 a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" 
  where "b2ifexp (Bc b) = (Bc2 b)" 
  | "b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" 
  | "b2ifexp (And l r) = (If (b2ifexp l) (b2ifexp r) (Bc2 False))" 
  | "b2ifexp (Less l r) = (Less2 l r)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" 
  where "if2bexp (Bc2 b) = (Bc b)" 
  | "if2bexp (If t l r) = (Not (And (Not (And (if2bexp t) (if2bexp l)))
                                  (Not (And (Not (if2bexp t)) (if2bexp r)))))" 
  | "if2bexp (Less2 l r) = (Less l r)"

lemma "ifval (b2ifexp bexpr) state = bval bexpr state"
  apply(induction bexpr)
  apply(auto)
  done

text{*
Exercise 3.9. Define a new type of purely boolean expressions
              datatype pbexp = Var vname | Not pbexp | And pbexp pbexp | Or pbexp pbexp
              where variables range over values of type bool.
              Define a function is_nnf :: pbexp => bool that checks whether a boolean
              expression is in NNF (negation normal form), i.e, if NOT is only applied
              directly to VARs. Also define a function nnf :: pbexp => pbexp that 
              converts a pbexp into NNF by pushing NOT inwards as much as possible.
              Prove that nnf preserves the value (pbval (nnf b) s = pbval b s) and
              returns a NNF (is_nnf (nnf b)).
              
              An expression is DNF (disjunctive normal form) if it is in NNF and if
              no OR occurs below and AND. Define a corresponding test 
              is_dnf :: pbexp => bool. An NNF can be converted into a DNF in a
              bottom-up manner. The critical case is the conversion AND b1 b2.
              Having converted b1 and b2, apply distributivity of AND over OR.
              Define a conversion function dnf_of_nnf :: pbexp => pbexp from NNF
              to DNF. Prove that your function preservers the value
              (pbval (dnf_of_nnf b) s = pbval b s) and converts an NNF into a DNF
              (is_nnf b ==> is_dnf (dnf_of_nnf b)).
*}
datatype pbexp 
  = VAR vname 
  | NOT pbexp 
  | AND pbexp pbexp 
  | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool"
  where "pbval (VAR x) s = s x"
  | "pbval (NOT b) s = (\<not> pbval b s)"
  | "pbval (AND b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<and> pbval b\<^sub>2 s)"
  | "pbval (OR b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<or> pbval b\<^sub>2 s)"
 


end