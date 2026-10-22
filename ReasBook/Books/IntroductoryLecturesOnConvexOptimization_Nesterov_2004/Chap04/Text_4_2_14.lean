/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConstrainedArgmin
open ModifiedAcceleratedCubicNewton

/- Text 4.2.14 lies in the Chapter 4 modified accelerated cubic-Newton step domain.

Sampled owner-style declarations:
* `argmin[{xk, step yk}] f` in `Algorithm_4_2_5`, the canonical accepted-point owner for
  `x̂_k`;
* `ModifiedAcceleratedCubicNewton.isMinOn` in `Algorithm_4_2_5`, the canonical source of the
  comparison `f x̂_k ≤ f x_k`;
* `ModifiedAcceleratedCubicNewton.xNext` in `Algorithm_4_2_5`, the owner-derived next
  iterate `x_{k+1}`;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the canonical owner of the cubic trial
  map `T_{2L₃}` used by the modified step.

Best owner abstraction:
* source-facing: the present item is a one-step objective-gap estimate;
* core/canonical: the accepted-point subtype `argmin[{xk, step yk}] f` together with
  `IsMinOn f Set.univ xStar`;
* bridge/view: the cubic decrease and step-length inequalities evaluated at the owner-derived
  points `xHat` and `xNext xHat`.

Primitive data:
* the objective `f`;
* the chapter-standard constant `L3 : NNReal`;
* the cubic step owner `step : CubicRegularizationMapping f (2 * (L3 : ℝ))`;
* the canonical accepted-point owner `xHat : argmin[{xk, step yk}] f`;
* the minimizer `xStar`;
* the strong-convexity scalar `σ₂`;
* the cubic decrease and step-length lower bounds for `xHat` and `xNext xHat`.

Derived API:
* the accepted-point comparison `f xHat ≤ f xk`, obtained canonically from `isMinOn xHat`;
* the first displayed drop comparison;
* the square-root next-gap lower bound.

The previous version duplicated the Chapter 4 owner layer by carrying raw sequences `x` and
`hatX` and by storing `f (x k) ≥ f (hatX k)` as primitive data, even though Algorithm 4.2.5
already records `x̂_k` through the canonical two-point `argmin` owner. This refinement keeps the
source-facing theorem but rewrites it directly on that canonical binder, so the accepted-point
comparison is derived from the owner abstraction instead of repeated as a parallel
hypothesis. It also restores the chapter-standard `L3 : NNReal` surface. -/

-- Proof sketch: apply `ModifiedAcceleratedCubicNewton.isMinOn xHat` to the competitor `xk` to
-- get `f xHat ≤ f xk`, then subtract the common term `f (xNext xHat)`.
/-- The accepted-point owner from Algorithm 4.2.5 immediately gives the comparison
`f x_k - f x_{k+1} ≥ f xHat - f x_{k+1}`. This is the bridge/view part of Text 4.2.14. -/
theorem modified_accelerated_cubic_drop_ge_hat_drop
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f) :
    f xk - f (xNext xHat) ≥ f xHat - f (xNext xHat) := by
  have hxHat_le_xk : f xHat ≤ f xk := by
    simpa using
      (ModifiedAcceleratedCubicNewton.isMinOn xHat)
        (by simp : xk ∈ ({xk, step yk} : Set E))
  linarith

-- Proof sketch: evaluate the global minimizer inequality at the comparison point `z`.
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Text 4 2 14: every function value lies above the global minimum value at
`xStar`, so the corresponding objective gap is nonnegative. -/
lemma modified_accelerated_cubic_next_gap_nonneg
    (f : E → ℝ) (xStar z : E)
    (hxStar : IsMinOn f Set.univ xStar) :
    0 ≤ f z - f xStar := by
  -- Global minimality compares `f z` directly to the minimum value `f xStar`.
  have hz : f xStar ≤ f z := hxStar (by simp : z ∈ Set.univ)
  linarith

-- Proof sketch: expand the cubic power into separate scalar factors, collapse each `rpow`
-- exponent using `3 * (1 / 6) = 1 / 2` and `3 * (1 / 3) = 1`, then rewrite the remaining
-- half-power as a square root.
/-- Helper for Text 4 2 14: cubing the step lower-bound coefficient produces the canonical
`sqrt`-gap factor. -/
lemma modified_accelerated_cubic_step_bound_cube_rewrite
    (L3 : NNReal) (σ₂ Δ : ℝ)
    (hσ₂ : 0 < σ₂)
    (hΔ : 0 ≤ Δ) :
    ((((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) / Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
        Real.rpow Δ (1 / 6 : ℝ)) ^ (3 : ℕ)) =
      (((2 : ℝ) * Real.sqrt 2 * Real.rpow σ₂ (1 / 2 : ℝ)) / (L3 : ℝ)) * Real.sqrt Δ := by
  have hsqrt_two_cube : (Real.sqrt 2) ^ (3 : ℕ) = (2 : ℝ) * Real.sqrt 2 := by
    -- The cubic power of `sqrt 2` reduces to `2 * sqrt 2`.
    calc
      (Real.sqrt 2) ^ (3 : ℕ) = (Real.sqrt 2) ^ (2 : ℕ) * Real.sqrt 2 := by
        simp [pow_succ]
      _ = (2 : ℝ) * Real.sqrt 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
  have hσ₂_rpow : (Real.rpow σ₂ (1 / 6 : ℝ)) ^ (3 : ℕ) = Real.rpow σ₂ (1 / 2 : ℝ) := by
    -- Cubing the sixth-root factor yields the expected half-power of `σ₂`.
    rw [show (1 / 2 : ℝ) = (1 / 6 : ℝ) * 3 by norm_num]
    symm
    simpa using (Real.rpow_mul_natCast hσ₂.le (1 / 6 : ℝ) 3)
  have hL3_rpow : (Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) ^ (3 : ℕ) = (L3 : ℝ) := by
    -- The cubic power cancels the one-third exponent on `L3`.
    rw [show (1 : ℝ) = (1 / 3 : ℝ) * 3 by norm_num]
    symm
    simpa using
      (Real.rpow_mul_natCast (show 0 ≤ (L3 : ℝ) by positivity) (1 / 3 : ℝ) 3)
  have hΔ_rpow : (Real.rpow Δ (1 / 6 : ℝ)) ^ (3 : ℕ) = Real.sqrt Δ := by
    -- The same exponent arithmetic turns the gap factor into `sqrt Δ`.
    rw [Real.sqrt_eq_rpow]
    rw [show (1 / 2 : ℝ) = (1 / 6 : ℝ) * 3 by norm_num]
    symm
    simpa using (Real.rpow_mul_natCast hΔ (1 / 6 : ℝ) 3)
  -- Expand the cube and rewrite each scalar contribution separately.
  rw [mul_pow, div_pow, mul_pow, hsqrt_two_cube, hσ₂_rpow, hL3_rpow, hΔ_rpow]

-- Proof sketch: rewrite `σ₂^(3/2)` as `σ₂ * σ₂^(1/2)` and then simplify the scalar prefactor.
/-- Helper for Text 4 2 14: the cubic-decrease prefactor matches the displayed
`σ₂^(3/2) / (3 L₃)` coefficient. -/
lemma modified_accelerated_cubic_hat_drop_coefficient
    (L3 : NNReal) (σ₂ : ℝ)
    (hσ₂ : 0 < σ₂) :
    (σ₂ / 6 : ℝ) * (((2 : ℝ) * Real.sqrt 2 * Real.rpow σ₂ (1 / 2 : ℝ)) / (L3 : ℝ)) =
      (Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ)) := by
  have hσ₂_pow : Real.rpow σ₂ (3 / 2 : ℝ) = σ₂ * Real.rpow σ₂ (1 / 2 : ℝ) := by
    -- Split the exponent `3 / 2` into `1 + 1 / 2` to isolate one factor of `σ₂`.
    calc
      Real.rpow σ₂ (3 / 2 : ℝ) = Real.rpow σ₂ ((1 : ℝ) + (1 / 2 : ℝ)) := by norm_num
      _ = Real.rpow σ₂ (1 : ℝ) * Real.rpow σ₂ (1 / 2 : ℝ) := by
        simpa using (Real.rpow_add hσ₂ (1 : ℝ) (1 / 2 : ℝ))
      _ = σ₂ * Real.rpow σ₂ (1 / 2 : ℝ) := by
        norm_num [Real.rpow_natCast]
  -- After the exponent rewrite, the remaining identity is a scalar rearrangement.
  rw [hσ₂_pow]
  ring

-- Proof sketch: combine the assumed cubic decrease estimate with the step-length lower bound and
-- simplify the constants.
/-- Text 4 2 14: let `xHat : argmin[{xk, step yk}] f` be the accepted point `x̂_k` chosen by
Algorithm 4.2.5 for the cubic owner `step : CubicRegularizationMapping f (2 L₃)`, and let
`xNext xHat` be the next iterate `x_{k+1}`. If `xStar` is a global minimizer of `f`,
`σ₂ > 0`, and the step satisfies
`f xHat - f (xNext xHat) ≥ (σ₂ / 6) ‖xNext xHat - xHat‖^3` together with
`‖xNext xHat - xHat‖ ≥
  (sqrt 2 * σ₂^(1/6) / L₃^(1/3))
  (f (xNext xHat) - f xStar)^(1/6)`,
then
`f xHat - f x_{k+1} ≥ (sqrt 2 * σ₂^(3/2) / (3 L₃)) (f x_{k+1} - f xStar)^(1/2)`. -/
theorem modified_accelerated_cubic_hat_drop_ge_sqrt_next_gap
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f)
    (xStar : E) (σ₂ : ℝ)
    (hxStar : IsMinOn f Set.univ xStar)
    (hσ₂ : 0 < σ₂)
    (hcubic :
      f xHat - f (xNext xHat) ≥
        (σ₂ / 6 : ℝ) * ‖xNext xHat - xHat‖ ^ (3 : ℕ))
    (hstep :
      ‖xNext xHat - xHat‖ ≥
        ((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
            Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow (f (xNext xHat) - f xStar) (1 / 6 : ℝ)) :
    f xHat - f (xNext xHat) ≥
      ((Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ))) *
        Real.sqrt (f (xNext xHat) - f xStar) := by
  let Δ : ℝ := f (xNext xHat) - f xStar
  let d : ℝ := ‖xNext xHat - xHat‖
  have hΔ_nonneg : 0 ≤ Δ := by
    -- The next gap is nonnegative because `xStar` is a global minimizer.
    simpa [Δ] using modified_accelerated_cubic_next_gap_nonneg f xStar (xNext xHat) hxStar
  have hstep_rhs_nonneg :
      0 ≤
        ((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
            Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow Δ (1 / 6 : ℝ) := by
    -- Every factor in the step lower bound is nonnegative, so cubing preserves the inequality.
    have hσ₂_root_nonneg : 0 ≤ Real.rpow σ₂ (1 / 6 : ℝ) := Real.rpow_nonneg hσ₂.le _
    have hL3_root_nonneg : 0 ≤ Real.rpow (L3 : ℝ) (1 / 3 : ℝ) := by
      exact Real.rpow_nonneg (by positivity : 0 ≤ (L3 : ℝ)) _
    have hΔ_root_nonneg : 0 ≤ Real.rpow Δ (1 / 6 : ℝ) := Real.rpow_nonneg hΔ_nonneg _
    exact
      mul_nonneg
        (div_nonneg (mul_nonneg (by positivity) hσ₂_root_nonneg) hL3_root_nonneg)
        hΔ_root_nonneg
  have hstep' :
      d ≥
        ((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
            Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow Δ (1 / 6 : ℝ) := by
    -- Rewrite the assumed step lower bound in terms of the local gap notation `Δ`.
    simpa [d, Δ] using hstep
  have hcube :
      ((((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) / Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow Δ (1 / 6 : ℝ)) ^ (3 : ℕ)) ≤ d ^ (3 : ℕ) := by
    -- Cube the whole step lower bound to match the cubic decrease hypothesis.
    exact pow_le_pow_left₀ hstep_rhs_nonneg hstep' 3
  -- Substitute the cubed step bound into the cubic decrease estimate and normalize the scalar.
  calc
    f xHat - f (xNext xHat)
        ≥ (σ₂ / 6 : ℝ) * d ^ (3 : ℕ) := by
          simpa [d] using hcubic
    _ ≥ (σ₂ / 6 : ℝ) *
          ((((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
                Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
              Real.rpow Δ (1 / 6 : ℝ)) ^ (3 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (σ₂ / 6 : ℝ) *
          ((((2 : ℝ) * Real.sqrt 2 * Real.rpow σ₂ (1 / 2 : ℝ)) / (L3 : ℝ)) *
            Real.sqrt Δ) := by
          rw [modified_accelerated_cubic_step_bound_cube_rewrite L3 σ₂ Δ hσ₂ hΔ_nonneg]
    _ = ((σ₂ / 6 : ℝ) *
          (((2 : ℝ) * Real.sqrt 2 * Real.rpow σ₂ (1 / 2 : ℝ)) / (L3 : ℝ))) *
          Real.sqrt Δ := by
          ring
    _ = ((Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ))) * Real.sqrt Δ := by
          rw [modified_accelerated_cubic_hat_drop_coefficient L3 σ₂ hσ₂]
    _ = ((Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ))) *
          Real.sqrt (f (xNext xHat) - f xStar) := by
          simp [Δ]

end
