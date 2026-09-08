module

public import ReasLib.Analysis.Calculus.Deriv.GlobalInverse
public import Mathlib.Geometry.Manifold.Diffeomorph

public section

open scoped Manifold NNReal

namespace Real

/-- A real function of positive finite smoothness is differentiable. -/
private theorem differentiable_of_contDiff_posOrder {f : ℝ → ℝ} {ν : ℕ}
    (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν) :
    Differentiable ℝ f := by
  have hν0 : ν ≠ 0 := Nat.ne_of_gt hν
  exact hf.differentiable (by simpa using hν0)

/-- The inverse selected by `Function.invFun` is a left inverse under a positive
uniform derivative lower bound. -/
private theorem leftInverse_invFun_of_pos_le_deriv {f : ℝ → ℝ} {ν : ℕ}
    {lower : ℝ≥0} (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν)
    (h_lower_pos : 0 < lower) (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Function.LeftInverse (Function.invFun f) f := by
  exact Function.leftInverse_invFun
    (bijective_of_pos_le_deriv (differentiable_of_contDiff_posOrder hf hν)
      h_lower_pos h_lower).1

/-- The inverse selected by `Function.invFun` is a right inverse under a positive
uniform derivative lower bound. -/
private theorem rightInverse_invFun_of_pos_le_deriv {f : ℝ → ℝ} {ν : ℕ}
    {lower : ℝ≥0} (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν)
    (h_lower_pos : 0 < lower) (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Function.RightInverse (Function.invFun f) f := by
  exact Function.rightInverse_invFun
    (bijective_of_pos_le_deriv (differentiable_of_contDiff_posOrder hf hν)
      h_lower_pos h_lower).2

/-- A finitely smooth real function with a positive uniform derivative lower bound,
bundled as a diffeomorphism whose inverse is `Function.invFun`. -/
noncomputable def diffeomorphOfPosLEDeriv (f : ℝ → ℝ) (ν : ℕ) (lower : ℝ≥0)
    (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ν where
  toEquiv :=
    { toFun := f
      invFun := Function.invFun f
      left_inv := leftInverse_invFun_of_pos_le_deriv hf hν h_lower_pos h_lower
      right_inv := rightInverse_invFun_of_pos_le_deriv hf hν h_lower_pos h_lower }
  contMDiff_toFun := hf.contMDiff
  contMDiff_invFun :=
    (contDiff_invFun_of_pos_le_deriv hf hν h_lower_pos h_lower).contMDiff

/-- Evaluating `diffeomorphOfPosLEDeriv` applies its forward function. -/
theorem diffeomorphOfPosLEDeriv_apply (f : ℝ → ℝ) (ν : ℕ) (lower : ℝ≥0)
    (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) (x : ℝ) :
    diffeomorphOfPosLEDeriv f ν lower hf hν h_lower_pos h_lower x = f x := by
  rfl

/-- Evaluating the inverse of `diffeomorphOfPosLEDeriv` applies `Function.invFun`. -/
theorem diffeomorphOfPosLEDeriv_symm_apply (f : ℝ → ℝ) (ν : ℕ) (lower : ℝ≥0)
    (hf : ContDiff ℝ ν f) (hν : 1 ≤ ν) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) (x : ℝ) :
    (diffeomorphOfPosLEDeriv f ν lower hf hν h_lower_pos h_lower).symm x =
      Function.invFun f x := by
  rfl

end Real
