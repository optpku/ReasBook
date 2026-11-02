module

public import Mathlib.Logic.Basic

public section

/-
Proposition 2.27. The source proposition is exact canonical reuse of
`imp_iff_not_or`: for propositions `A` and `B`, the implication `A → B`
is satisfied if and only if the logic statement `¬ A ∨ B` is satisfied.
-/
#check imp_iff_not_or

end
