module

public import Mathlib.Analysis.InnerProductSpace.Basic

public section

universe u

namespace LineSearch

/-- A lower bound on a normalized scalar decrease yields the corresponding Armijo
inequality whenever the directional pairing is the negative predicted decrease. -/
theorem armijo_of_decrease_ratio_lower_bound
    {before after pairing c₁ q r : ℝ}
    (hq : 0 < q) (hpairing : pairing = -q)
    (h_ratio : r ≤ (before - after) / q) (h_coeff : c₁ ≤ r) :
    after ≤ before + c₁ * pairing := by
  have h_ratio_mul : r * q ≤ before - after :=
    (le_div_iff₀ hq).mp h_ratio
  have h_coeff_mul : c₁ * q ≤ r * q :=
    mul_le_mul_of_nonneg_right h_coeff hq.le
  have h_decrease : c₁ * q ≤ before - after := h_coeff_mul.trans h_ratio_mul
  rw [hpairing]
  linarith

/-- A normalized objective decrease bound gives Armijo for a function and a certified
directional pairing at the initial endpoint. -/
theorem armijo_of_function_decrease_ratio_lower_bound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x s g : E} {c₁ q r : ℝ}
    (hq : 0 < q) (hpairing : inner ℝ g s = -q)
    (h_ratio : r ≤ (f x - f (x + s)) / q) (h_coeff : c₁ ≤ r) :
    f (x + s) ≤ f x + c₁ * inner ℝ g s := by
  exact armijo_of_decrease_ratio_lower_bound hq hpairing h_ratio h_coeff

/-- A half-unit normalized decrease is enough for Armijo with the standard coefficient
`c₁ = 1 / 4`. -/
theorem armijo_of_half_function_decrease_ratio
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x s g : E} {qValue : ℝ}
    (hq : 0 < qValue) (hpairing : inner ℝ g s = -qValue)
    (h_ratio : (1 / 2 : ℝ) ≤ (f x - f (x + s)) / qValue) :
    f (x + s) ≤ f x + (1 / 4 : ℝ) * inner ℝ g s := by
  apply armijo_of_function_decrease_ratio_lower_bound hq hpairing h_ratio
  norm_num

/-- The standard `q = -⟪g, s⟫` presentation of the half-decrease Armijo bridge. -/
theorem armijo_of_half_decrease_ratio
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x s g : E}
    (hq : 0 < -inner ℝ g s)
    (h_ratio : (1 / 2 : ℝ) ≤
      (f x - f (x + s)) / (-inner ℝ g s)) :
    f (x + s) ≤ f x + (1 / 4 : ℝ) * inner ℝ g s := by
  have hpairing : inner ℝ g s = -(-inner ℝ g s) := by
    ring
  exact armijo_of_half_function_decrease_ratio hq hpairing h_ratio

end LineSearch
