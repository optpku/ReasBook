/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}

-- Proof sketch: substitute the defining formulas for `μ₁` and `μ₂` into the assumed duality-gap
-- bound, use `D₁ > 0` and `D₂ > 0` to simplify
-- `Real.sqrt (D₂ / D₁) * D₁ = Real.sqrt (D₁ * D₂)` and
-- `Real.sqrt (D₁ / D₂) * D₂ = Real.sqrt (D₁ * D₂)`, and then factor the common term
-- `opNorm12 * Real.sqrt (D₁ * D₂)`.
/-- Helper for Proposition 6.27: multiplying `√(a / b)` by the scale `b`
recovers the geometric mean `√(a b)`. -/
lemma sqrt_div_mul_eq_sqrt_mul_prop_6_27 {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a / b) * b = Real.sqrt (a * b) := by
  -- Rewrite the quotient square root as a quotient of square roots.
  calc
    Real.sqrt (a / b) * b = (Real.sqrt a / Real.sqrt b) * b := by
      rw [Real.sqrt_div ha b]
    _ = Real.sqrt a * (b / Real.sqrt b) := by
      ring
    _ = Real.sqrt a * Real.sqrt b := by
      rw [Real.div_sqrt]
    _ = Real.sqrt (a * b) := by
      rw [← Real.sqrt_mul ha b]

/-- Helper for Proposition 6.27: the first smoothing contribution collapses to the common
scale `λ₁ ‖A‖_{1,2} √(D₁ D₂)`. -/
lemma first_smoothing_contribution_eq_common_scale
    {D₁ D₂ lambda₁ μ₁ opNorm12 : ℝ}
    (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁)) :
    μ₁ * D₁ = lambda₁ * opNorm12 * Real.sqrt (D₁ * D₂) := by
  -- Substitute the parametrization of `μ₁` and normalize the square root factor.
  calc
    μ₁ * D₁ = (lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁)) * D₁ := by
      rw [hμ₁]
    _ = lambda₁ * opNorm12 * (Real.sqrt (D₂ / D₁) * D₁) := by
      ring
    _ = lambda₁ * opNorm12 * Real.sqrt (D₂ * D₁) := by
      rw [sqrt_div_mul_eq_sqrt_mul_prop_6_27 hD₂.le]
    _ = lambda₁ * opNorm12 * Real.sqrt (D₁ * D₂) := by
      rw [mul_comm D₂ D₁]

/-- Helper for Proposition 6.27: the second smoothing contribution collapses to the common
scale `λ₂ ‖A‖_{1,2} √(D₁ D₂)`. -/
lemma second_smoothing_contribution_eq_common_scale
    {D₁ D₂ lambda₂ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁)
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂)) :
    μ₂ * D₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ * D₂) := by
  -- Substitute the parametrization of `μ₂` and normalize the symmetric square root factor.
  calc
    μ₂ * D₂ = (lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂)) * D₂ := by
      rw [hμ₂]
    _ = lambda₂ * opNorm12 * (Real.sqrt (D₁ / D₂) * D₂) := by
      ring
    _ = lambda₂ * opNorm12 * Real.sqrt (D₁ * D₂) := by
      rw [sqrt_div_mul_eq_sqrt_mul_prop_6_27 hD₁.le]

/-- Proposition 6.27 [Chapter6_1.json:79]: if
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`,
then the assumed duality-gap bound
`f(x̄) - φ(ū) ≤ μ₁ D₁ + μ₂ D₂`
implies the symmetric estimate
`f(x̄) - φ(ū) ≤ (λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)`. The positivity assumptions
`λ₁, λ₂ > 0` and `μ₁, μ₂ > 0` from the source are omitted because they are redundant
for the inequality statement itself. -/
theorem duality_gap_le_symmetric_bound_of_parametrized_smoothing_parameters
    {f : X → ℝ} {φ : U → ℝ} {xBar : X} {uBar : U}
    {D₁ D₂ lambda₁ lambda₂ μ₁ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁))
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂))
    (hgap : f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂) :
    f xBar - φ uBar ≤ (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := by
  -- Rewrite both smoothing contributions to the same geometric-mean scale.
  rw [first_smoothing_contribution_eq_common_scale hD₂ hμ₁,
    second_smoothing_contribution_eq_common_scale hD₁ hμ₂] at hgap
  -- Factor the common term `opNorm12 * √(D₁ D₂)` from the budget.
  calc
    f xBar - φ uBar
        ≤ lambda₁ * opNorm12 * Real.sqrt (D₁ * D₂) +
            lambda₂ * opNorm12 * Real.sqrt (D₁ * D₂) := hgap
    _ = (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := by
      ring

end
