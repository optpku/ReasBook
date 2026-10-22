/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} {m : ℕ}

/- This file isolates the primitive feasible-set owner from Lemma 3.5. The owner abstraction is
the set cut out by a finite family of scalar inequalities; later residual-objective results are
derived API that should import this owner, not own it. -/

/-- The feasible set of the inequality-constrained problem cut out by the family `g`. -/
def inequality_feasible_set (g : Fin m → E → ℝ) : Set E :=
  {x | ∀ i, g i x ≤ 0}

variable {g : Fin m → E → ℝ}

/-- Membership in `inequality_feasible_set g` means satisfying every inequality constraint
`g i x ≤ 0`. -/
@[simp] theorem mem_inequality_feasible_set {x : E} :
    x ∈ inequality_feasible_set g ↔ ∀ i, g i x ≤ 0 :=
  Iff.rfl

end
