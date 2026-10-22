/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace SpectralFilter

/-- The Landweber scalar filter `w_v(λ) = 1 - (1 - τ * λ)^v` from equation `(1.38)`. -/
def landweber (τ : ℝ) (v : ℕ) (lam : ℝ) : ℝ :=
  1 - (1 - τ * lam) ^ v

/-- The Landweber scalar filter expands to the defining formula from equation `(1.38)`. -/
theorem landweber_eq (τ : ℝ) (v : ℕ) (lam : ℝ) :
    landweber τ v lam = 1 - (1 - τ * lam) ^ v := by
  -- Unfold the canonical owner once; the theorem is exactly its defining equation.
  rfl

end SpectralFilter
