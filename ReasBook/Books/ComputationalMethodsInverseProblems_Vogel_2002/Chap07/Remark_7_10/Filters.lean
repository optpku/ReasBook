/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5.Filters

public section

noncomputable section

namespace SpectralFilter

/-- The Chapter 7 discrete TSVD scalar filter rescales the regularization parameter by `n`. -/
@[expose]
def discreteTsvd (n : ℕ) (α lam : ℝ) : ℝ :=
  tsvd ((n : ℝ) * α) lam

/-- Rewriting `discreteTsvd` through the base TSVD scalar filter. -/
theorem discreteTsvd_eq_tsvd (n : ℕ) (α lam : ℝ) :
    discreteTsvd n α lam = tsvd ((n : ℝ) * α) lam := by
  unfold discreteTsvd
  rfl

/-- The Chapter 7 discrete TSVD scalar filter has the expected cutoff formula. -/
theorem discreteTsvd_eq (n : ℕ) (α lam : ℝ) :
    discreteTsvd n α lam = if ((n : ℝ) * α) ≤ lam then 1 else 0 := by
  unfold discreteTsvd tsvd
  rfl

/-- The Chapter 7 discrete Tikhonov scalar filter rescales the regularization parameter by `n`. -/
@[expose]
def discreteTikhonov (n : ℕ) (α lam : ℝ) : ℝ :=
  tikhonov ((n : ℝ) * α) lam

/-- Rewriting `discreteTikhonov` through the base Tikhonov scalar filter. -/
theorem discreteTikhonov_eq_tikhonov (n : ℕ) (α lam : ℝ) :
    discreteTikhonov n α lam = tikhonov ((n : ℝ) * α) lam := by
  unfold discreteTikhonov
  rfl

/-- The Chapter 7 discrete Tikhonov scalar filter has the expected rational formula. -/
theorem discreteTikhonov_eq (n : ℕ) (α lam : ℝ) :
    discreteTikhonov n α lam = lam / (lam + (n : ℝ) * α) := by
  unfold discreteTikhonov tikhonov
  rw [add_comm]

end SpectralFilter
