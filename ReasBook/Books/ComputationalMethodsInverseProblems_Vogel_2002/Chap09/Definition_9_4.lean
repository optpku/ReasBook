/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Group.Basic

public section

noncomputable section

namespace IterativeSolutionError

universe u

variable {H : Type u} [NormedAddCommGroup H]

/-- Definition 9.4-extra-1. The relative iterative solution error norm at step
`v` for an iterate sequence `iterates`, where `iterates v` is the approximate
solution after `v` iterations and `fStar` is a numerically exact solution. The
experimental setup sentence `f₀ = 0` is not part of this generic owner. -/
def norm (iterates : ℕ → H) (fStar : H) (v : ℕ) : ℝ :=
  ‖iterates v - fStar‖ / ‖fStar‖

/-- The defining formula for `IterativeSolutionError.norm`. -/
@[simp] theorem norm_eq (iterates : ℕ → H) (fStar : H) (v : ℕ) :
    norm iterates fStar v = ‖iterates v - fStar‖ / ‖fStar‖ := by
  simp [norm]

/-- The relative iterative solution error is always nonnegative. -/
theorem norm_nonneg (iterates : ℕ → H) (fStar : H) (v : ℕ) :
    0 ≤ norm iterates fStar v := by
  rw [norm_eq]
  exact div_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _)

/-- If the iterate at step `v` equals the exact solution, then the relative
iterative solution error vanishes. -/
@[simp] theorem norm_eq_zero_of_iterates_eq
    (iterates : ℕ → H) (fStar : H) (v : ℕ)
    (h : iterates v = fStar) :
    norm iterates fStar v = 0 := by
  rw [norm_eq, h, sub_self, norm_zero, zero_div]

/-- When `fStar ≠ 0`, vanishing relative iterative solution error at step `v`
is equivalent to exact recovery at that step. -/
theorem norm_eq_zero_iff
    (iterates : ℕ → H) (fStar : H) (hfStar : fStar ≠ 0) (v : ℕ) :
    norm iterates fStar v = 0 ↔ iterates v = fStar := by
  rw [norm_eq]
  have hfStar_norm_ne : ‖fStar‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hfStar
  constructor
  · intro h
    have hnum : ‖iterates v - fStar‖ = 0 := by
      rcases (div_eq_zero_iff.mp h) with hzero | hzero
      · exact hzero
      · exact (hfStar_norm_ne hzero).elim
    exact sub_eq_zero.mp (norm_eq_zero.mp hnum)
  · intro h
    rw [h, sub_self, norm_zero, zero_div]

end IterativeSolutionError
