/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/- Definition 8.12 is `source-facing`: the textbook introduces the pointwise notion of an
`ε`-optimal feasible point for a constrained minimization problem. In this chapter the canonical
owner data for that notion is the feasible real sublevel set `C ∩ f ⁻¹' Set.Iic (fOpt + ε)`, so
the public API records the point predicate directly as membership in that set, with no extra
problem wrapper. -/

/-- Definition 8.12: a vector `x` is an `ε`-optimal solution of `min {f(x) : x ∈ C}` when `x`
lies in `C` and its objective value is at most `fOpt + ε`. -/
def is_epsilon_optimal_solution
    (f : E → EReal) (C : Set E) (fOpt ε : ℝ) (x : E) : Prop :=
  x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal)

-- Proof sketch: unfold `is_epsilon_optimal_solution`; the predicate was defined to be membership
-- in the feasible sublevel set `C ∩ f ⁻¹' Set.Iic (fOpt + ε)`.
/-- Unfolding `is_epsilon_optimal_solution` identifies it with membership in the feasible
`(fOpt + ε)`-sublevel set. -/
theorem is_epsilon_optimal_solution_def
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_solution f C fOpt ε x ↔
      x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal) := by
  -- The theorem is just the defining equation of the point predicate.
  simp [is_epsilon_optimal_solution]

/-- Helper for Definition 8.12: membership in the feasible sublevel set is equivalent to
feasibility together with the objective-value bound. -/
lemma mem_feasible_sublevel_iff
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    x ∈ C ∩ f ⁻¹' Set.Iic (fOpt + ε : EReal) ↔
      x ∈ C ∧ f x ≤ (fOpt + ε : EReal) := by
  -- Normalize the intersection, preimage, and interval membership into a conjunction.
  simp [Set.mem_preimage]

-- Proof sketch: unfold `is_epsilon_optimal_solution`; membership in the intersection is exactly
-- feasibility together with membership in the real sublevel set `Set.Iic (fOpt + ε)`.
/-- A point is `ε`-optimal exactly when it is feasible and its objective value is at most
`fOpt + ε`. -/
@[simp] theorem is_epsilon_optimal_solution_iff
    {f : E → EReal} {C : Set E} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_solution f C fOpt ε x ↔ x ∈ C ∧ f x ≤ (fOpt + ε : EReal) := by
  -- Rewrite the predicate into feasible-sublevel membership and then flatten that membership.
  rw [is_epsilon_optimal_solution_def, mem_feasible_sublevel_iff]

end
