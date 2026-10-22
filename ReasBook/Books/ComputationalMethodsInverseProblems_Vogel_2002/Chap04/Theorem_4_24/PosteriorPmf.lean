/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_18.JointPmf

public section

noncomputable section

open scoped BigOperators

namespace ProbabilityTheory.JointPmf

universe v w

variable {α : Type v} {β : Type w}

/-- A nonzero second marginal forces the `x`-fiber sum at `y` to be nonzero. -/
theorem tsum_fstFiber_ne_zero
    (joint : PMF (α × β)) (y : β) (hy : sndMarginal joint y ≠ 0) :
    ∑' x, joint (x, y) ≠ 0 := by
  -- Rewrite the fiber sum as the second marginal at `y`.
  simpa [sndMarginal_apply] using hy

/-- The `x`-fiber sum of a joint PMF is finite in `ℝ≥0∞`. -/
theorem tsum_fstFiber_ne_top (joint : PMF (α × β)) (y : β) :
    ∑' x, joint (x, y) ≠ ⊤ := by
  -- Each PMF value is bounded by `1`, hence in particular it is not `⊤`.
  rw [← sndMarginal_apply]
  exact ne_of_lt <| lt_of_le_of_lt ((sndMarginal joint).coe_le_one y) ENNReal.one_lt_top

/-- The conditional PMF of `X` given the event `Y = y`, assuming the second marginal at `y`
is nonzero. -/
def condFstGivenSnd (joint : PMF (α × β)) (y : β) (hy : sndMarginal joint y ≠ 0) : PMF α :=
  PMF.normalize
    (fun x ↦ joint (x, y))
    (tsum_fstFiber_ne_zero joint y hy)
    (tsum_fstFiber_ne_top joint y)

/-- The defining ratio formula for the conditional PMF of `X` given `Y = y`. -/
theorem condFstGivenSnd_apply
    (joint : PMF (α × β)) (y : β) (hy : sndMarginal joint y ≠ 0) (x : α) :
    condFstGivenSnd joint y hy x = joint (x, y) / sndMarginal joint y := by
  -- Expand the normalization and identify the normalizing constant with the second marginal.
  rw [condFstGivenSnd, PMF.normalize_apply, sndMarginal_apply, div_eq_mul_inv]

end ProbabilityTheory.JointPmf
