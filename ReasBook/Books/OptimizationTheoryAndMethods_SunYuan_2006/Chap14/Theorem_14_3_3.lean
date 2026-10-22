/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1

noncomputable section

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Source/core/bridge triage for this item:
-- * source-facing theorem: Theorem 14.3.3
-- * canonical upstream owners reused from `Algorithm_14_3_1`: `S⋆[f]`, `f⋆[f]`, `SubgradientMethod`
-- * bridge/view kept here: `SubgradientMethod.HasConstantStepSize`

namespace SubgradientMethod

/-- `method.HasConstantStepSize α` means that the Algorithm 14.3.1 execution `method` uses the
same positive stepsize `α` at every stage `k ≥ 1`. -/
def HasConstantStepSize (method : SubgradientMethod E) (α : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → method.stepSize k = α

/-- Unfolding `method.HasConstantStepSize α` gives the constant-stepsize condition for all
stages `k ≥ 1`. -/
theorem hasConstantStepSize_iff
    (method : SubgradientMethod E) (α : ℝ) :
    method.HasConstantStepSize α ↔
      ∀ k : ℕ, 1 ≤ k → method.stepSize k = α :=
  Iff.rfl

/-- A constant stepsize in a subgradient-method execution is automatically positive because every
recorded stepsize of Algorithm 14.3.1 is positive. -/
theorem hasConstantStepSize_pos
    (method : SubgradientMethod E) {α : ℝ}
    (hα : method.HasConstantStepSize α) :
    0 < α := by
  simpa [hα 1 le_rfl] using method.stepSize_pos 1 le_rfl

end SubgradientMethod

/-- Chapter14 Theorem 14.3.3: if `f` is convex and `S⋆[f]` is nonempty, then for
every `δ > 0` there exists `r > 0` such that every constant-step execution of Algorithm 14.3.1
for the fixed objective `f` with constant stepsize `α < r` satisfies
`liminf_(k → ∞) f (x_k) ≤ f⋆[f] + δ`. The separate positivity assumption on `α` is
redundant here, because `method.HasConstantStepSize α` together with Algorithm 14.3.1 already
forces `0 < α`. The execution is expressed through the canonical chapter owner
`SubgradientMethod E`, and the liminf uses the owner companion `method.objectiveValueAt`. -/
theorem exists_pos_constant_subgradient_stepsize_liminf_le_optimalValue_add_of_convexOn
    (f : E → ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty (S⋆[f]))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (method : SubgradientMethod E)
        (h_objective : method.objective = f)
        (α : ℝ)
        (hα_lt : α < r)
        (h_constant : method.HasConstantStepSize α),
        Filter.liminf (fun k : ℕ ↦ method.objectiveValueAt (k + 1)) Filter.atTop ≤
          f⋆[f] + δ :=
  -- Route correction: `Lemma_14_3_2` only gives a pointwise threshold depending on the current
  -- iterate and chosen subgradient. Turning that local threshold into one global `r` for every
  -- constant-step execution needs an extra quantitative hypothesis such as a bounded-subgradient
  -- condition on the relevant level shell, or a finite-dimensional compactness assumption.
  sorry

#print axioms SubgradientMethod.HasConstantStepSize

end
