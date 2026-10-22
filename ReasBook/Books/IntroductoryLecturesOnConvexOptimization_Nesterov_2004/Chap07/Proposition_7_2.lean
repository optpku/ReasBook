/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Sqrt

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.2 lies in the Euclidean direct-structure first-order complexity domain.

Sampled owner-style declarations:
- mathlib `EuclideanSpace ℝ (Fin n)` for the ambient model `ℝⁿ`;
- real scalars for the source parameters `γ₁(F)` and `R`, with positivity of `R` kept explicit;
- mathlib `Real.sqrt` for the factor `√(N (N + 1))`;
- the chapter-style lower-level scheme surface `ℕ+ → ℝ → Eₙ → Eₙ`, matching the notation
  `S_N(R)`.

Best owner abstraction:
- source-facing: the textbook output guarantee for the method `S_N(R)` on every start point
  within Euclidean distance `R` of a chosen optimal point `x*`;
- core/canonical: a scheme `S` taking an iteration count, a radius parameter, and a start point;
- bridge/view: the positivity side condition on `R` is kept as a separate hypothesis.

Primitive data:
- the objective `f`;
- the method surface `S`;
- the coefficient `γ₁(F)`, the radius `R`, the iteration count `N`, the reference point `xStar`,
  and the start point `x₀`.

Derived API:
- the displayed complexity bound
  `f (S_N(R)) - f(x*) ≤ 2 γ₁(F) R / √(N (N + 1))`.

Source/core/bridge triage:
- source-facing: Proposition 7.2 itself;
- core/canonical: the scheme `S : ℕ+ → ℝ → Eₙ → Eₙ`;
- bridge/view: no coercion wrapper is needed for the source scalars in the displayed bound.

As in nearby Chapter 7 item files, the proposition is stated directly on the method surface
`S_N(R)` and keeps the source hypotheses explicit: whole-space convexity of `f`, positivity of the
radius `R`, and the attained-optimum witness `IsMinOn f Set.univ xStar` so that `f xStar` is the
source minimum value `f*`.
-/

-- Proof sketch: specialize the source-uniform method guarantee on the radius-`R` ball
-- and combine it with the bound `‖x₀ - x*‖ ≤ R`.
/-- Proposition 7.2 [Chapter7_1.json:26]: if `f` is convex on `ℝⁿ`, `R` is positive, and the
Chapter 7 direct-structure method `S_N(R)` satisfies the source intermediate estimate
`f (S_N(R)) - f(x*) ≤ (2 γ₁(F) / √(N (N + 1))) ‖x₀ - x*‖` for every start point `x₀`
with `‖x₀ - x*‖ ≤ R`, where the source complexity coefficient `γ₁(F)` is nonnegative, and a
chosen global minimizer `x*` of `f`, then for every such `x₀` its output also satisfies the
displayed bound `2 γ₁(F) R / √(N (N + 1))`. -/
theorem direct_structure_method_output_sub_optimalValue_le
    (f : Eₙ → ℝ) (S : ℕ+ → ℝ → Eₙ → Eₙ) (γ₁ : ℝ) (N : ℕ+) (R : ℝ)
    (xStar : Eₙ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hR_pos : 0 < R)
    (hγ₁_nonneg : 0 ≤ γ₁)
    (hxStar : IsMinOn f Set.univ xStar)
    (h_method :
      ∀ {x₀ : Eₙ}, ‖x₀ - xStar‖ ≤ R →
        f (S N R x₀) - f xStar ≤
          (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * ‖x₀ - xStar‖) :
    ∀ {x₀ : Eₙ}, ‖x₀ - xStar‖ ≤ R →
      f (S N R x₀) - f xStar ≤
        (2 * γ₁ * R) /
          Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
  intro x₀ hx₀
  -- The source method estimate applies directly at the chosen starting point.
  have h_method_bound := h_method hx₀
  -- The square-root denominator is positive because the iteration count `N` is positive.
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast N.2
  have hsqrt_pos : 0 < Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    apply Real.sqrt_pos.2
    have hN_succ_pos : 0 < (N : ℝ) + 1 := by linarith
    exact mul_pos hN_pos hN_succ_pos
  -- The displayed coefficient is therefore nonnegative, so we may scale the radius bound.
  have hcoeff_nonneg :
      0 ≤ (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) := by
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    exact div_nonneg (mul_nonneg htwo_nonneg hγ₁_nonneg) hsqrt_pos.le
  have h_scaled_radius :
      (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * ‖x₀ - xStar‖ ≤
        (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * R := by
    exact mul_le_mul_of_nonneg_left hx₀ hcoeff_nonneg
  -- Reassociate the scalar factor into the exact target normal form.
  have h_target_form :
      (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * R =
        (2 * γ₁ * R) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  calc
    f (S N R x₀) - f xStar
        ≤ (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * ‖x₀ - xStar‖ := h_method_bound
    _ ≤ (2 * γ₁ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * R := h_scaled_radius
    _ = (2 * γ₁ * R) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := h_target_form

end
