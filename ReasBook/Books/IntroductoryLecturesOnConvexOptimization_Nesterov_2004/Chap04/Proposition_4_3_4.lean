/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.3.4 lies in the optimal cubic-Newton rate / scalar prefactor optimization
domain on a finite-dimensional real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` in `Theorem_4_3_2`, the chapter
  owner of the inverse-`7/2` objective-gap rate for general `σ ∈ (0, 1)`;
* `OptimalCubicNewtonMethod.accumulated_weight_lower_bound` in `Lemma_4_3_5`, the predecessor
  owner theorem underlying that rate;
* mathlib `IsMinOn`, the canonical owner for the scalar minimization statement on `Set.Ioo 0 1`.

Best owner abstractions:
* core/canonical for the algorithmic estimate: `OptimalCubicNewtonMethod B Mf f x0 sigma`
* core/canonical for the scalar optimization: `IsMinOn`

Primitive data:
* the method data already bundled by `OptimalCubicNewtonMethod`
* the comparison point `xStar` and the residual factor `γ`
* the scalar prefactor `σ ↦ 2 / (σ * sqrt (1 - σ^2))`

Derived API:
* the scalar minimization at `σ = 1 / √2`
* the sharp specialization of the general rate theorem at that parameter value

Source/core/bridge triage:
* source-facing: Proposition 4.3.4's optimal-`σ` claim and the resulting sharp inverse-`7/2` rate
* core/canonical: `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` and `IsMinOn`
* bridge/view: specialize the owner rate theorem to `σ = 1 / √2` and simplify the coefficient
-/

section

/-- Helper for Proposition 4.3.4: the candidate optimizer `1 / √2` lies in `(0, 1)`. -/
lemma one_div_sqrt_two_mem_Ioo : ((1 : ℝ) / Real.sqrt 2) ∈ Set.Ioo (0 : ℝ) 1 := by
  -- The optimizer is positive, and it is below `1` because `√2 > 1`.
  have htwo_nonneg : (0 : ℝ) ≤ 2
  · positivity
  have hsqrt_two_pos : 0 < Real.sqrt (2 : ℝ)
  · positivity
  have hsqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2
  · nlinarith [Real.sq_sqrt htwo_nonneg]
  constructor
  · positivity
  · have hlt : (1 : ℝ) / Real.sqrt 2 < 1
    · exact (div_lt_one hsqrt_two_pos).2 hsqrt_two_gt_one
    simpa using hlt

/-- Helper for Proposition 4.3.4: on `(0, 1)`, the factor `σ * √(1 - σ²)` is at most `1 / 2`. -/
lemma sigma_mul_sqrt_one_sub_sq_le_half {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) :
    σ * Real.sqrt (1 - σ ^ (2 : ℕ)) ≤ 1 / 2 := by
  -- Square the expression and reduce to the quadratic maximum at `σ² = 1 / 2`.
  have hσsq_lt : σ ^ (2 : ℕ) < 1
  · nlinarith [hσ.1, hσ.2]
  have hinside_nonneg : 0 ≤ 1 - σ ^ (2 : ℕ)
  · nlinarith [hσsq_lt]
  have hsquare :
      (σ * Real.sqrt (1 - σ ^ (2 : ℕ))) ^ (2 : ℕ) =
        σ ^ (2 : ℕ) * (1 - σ ^ (2 : ℕ))
  · calc
      (σ * Real.sqrt (1 - σ ^ (2 : ℕ))) ^ (2 : ℕ)
          = σ ^ (2 : ℕ) * (Real.sqrt (1 - σ ^ (2 : ℕ))) ^ (2 : ℕ) := by
              rw [mul_pow]
      _ = σ ^ (2 : ℕ) * (1 - σ ^ (2 : ℕ)) := by
            rw [Real.sq_sqrt hinside_nonneg]
  have hquad :
      σ ^ (2 : ℕ) * (1 - σ ^ (2 : ℕ)) ≤ (1 / 4 : ℝ)
  · nlinarith [sq_nonneg (σ ^ (2 : ℕ) - (1 / 2 : ℝ))]
  have hsq_le :
      (σ * Real.sqrt (1 - σ ^ (2 : ℕ))) ^ (2 : ℕ) ≤ ((1 / 2 : ℝ) ^ (2 : ℕ))
  · nlinarith [hsquare, hquad]
  have hnonneg : 0 ≤ σ * Real.sqrt (1 - σ ^ (2 : ℕ))
  · exact mul_nonneg (le_of_lt hσ.1) (Real.sqrt_nonneg _)
  nlinarith [hsq_le, hnonneg]

/-- Helper for Proposition 4.3.4: at `σ = 1 / √2`, the factor `σ * √(1 - σ²)` equals `1 / 2`. -/
lemma inv_sqrt_two_mul_sqrt_one_sub_sq_eq_half :
    ((1 : ℝ) / Real.sqrt 2) * Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)) = 1 / 2 := by
  -- Evaluate the optimizer exactly by first computing its square.
  have htwo_nonneg : (0 : ℝ) ≤ 2
  · positivity
  have hsq : ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ) = (1 / 2 : ℝ)
  · calc
      ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)
          = (1 : ℝ) ^ (2 : ℕ) / (Real.sqrt 2) ^ (2 : ℕ) := by
              rw [div_pow]
      _ = (1 / 2 : ℝ) := by
            rw [one_pow, Real.sq_sqrt htwo_nonneg]
  have hbase_nonneg : 0 ≤ (1 : ℝ) / Real.sqrt 2
  · exact le_of_lt one_div_sqrt_two_mem_Ioo.1
  have hsqrt_eq :
      Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)) = (1 : ℝ) / Real.sqrt 2
  · have hinner_eq :
        1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ) = ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)
    · rw [hsq]
      norm_num
    rw [hinner_eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hbase_nonneg]
  calc
    ((1 : ℝ) / Real.sqrt 2) * Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ))
        = ((1 : ℝ) / Real.sqrt 2) * ((1 : ℝ) / Real.sqrt 2) := by
            rw [hsqrt_eq]
    _ = 1 / 2 := by
          simpa [pow_two] using hsq

/-- Helper for Proposition 4.3.4: the reciprocal prefactor specializes to `4` at `σ = 1 / √2`. -/
lemma two_div_inv_sqrt_two_mul_sqrt_one_sub_sq_eq_four :
    (2 : ℝ) /
        (((1 : ℝ) / Real.sqrt 2) * Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ))) = 4 := by
  -- Substitute the exact optimizer value and evaluate the remaining reciprocal.
  rw [inv_sqrt_two_mul_sqrt_one_sub_sq_eq_half]
  norm_num

/-- Proposition 4.3.4, scalar part: the prefactor in Theorem 4.3.2 is minimized on `(0, 1)` at
`σ = 1 / √2`. -/
theorem inverse_seven_halves_prefactor_isMinOn :
    IsMinOn
      (fun σ : ℝ ↦
        (2 : ℝ) / (σ * Real.sqrt (1 - σ ^ (2 : ℕ))))
      (Set.Ioo (0 : ℝ) 1)
      ((1 : ℝ) / Real.sqrt 2) := by
  refine isMinOn_iff.mpr ?_
  intro σ hσ
  -- Compare reciprocals by showing the denominator is maximized at `σ = 1 / √2`.
  have hσsq_lt : σ ^ (2 : ℕ) < 1 := by
    nlinarith [hσ.1, hσ.2]
  have hinside_pos : 0 < 1 - σ ^ (2 : ℕ) := by
    nlinarith [hσsq_lt]
  have hden_pos : 0 < σ * Real.sqrt (1 - σ ^ (2 : ℕ)) := by
    exact mul_pos hσ.1 (Real.sqrt_pos.2 hinside_pos)
  have hopt_value :
      (2 : ℝ) /
          (((1 : ℝ) / Real.sqrt 2) *
            Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ))) = 4 := by
    rw [inv_sqrt_two_mul_sqrt_one_sub_sq_eq_half]
    norm_num
  rw [hopt_value]
  have hden_le : σ * Real.sqrt (1 - σ ^ (2 : ℕ)) ≤ 1 / 2 := by
    exact sigma_mul_sqrt_one_sub_sq_le_half hσ
  refine (le_div_iff₀ hden_pos).2 ?_
  nlinarith

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 xStar : PrimalSpace B} {γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 ((1 : ℝ) / Real.sqrt 2))

namespace OptimalCubicNewtonMethod

-- Proof sketch: the prefactor in Theorem 4.3.2 is the scalar function
-- `σ ↦ 2 / (σ * sqrt (1 - σ^2))` on `(0, 1)`. Differentiate this elementary function or,
-- equivalently, maximize `σ * sqrt (1 - σ^2)` on `(0, 1)` to obtain the optimizer
-- `σ = 1 / sqrt 2`. Then specialize
-- `method.gap_le_inverse_seven_halves_rate` to this value of `σ` and simplify
-- the coefficient
-- `2 / ((1 / sqrt 2) * sqrt (1 - (1 / sqrt 2)^2)) = 4`.
/-- Proposition 4.3.4, rate part: under the convexity assumptions of Theorem 4.3.2, the
right-hand-side
coefficient there is minimized at `σ = 1 / √2`; for an optimal cubic Newton method built with
this parameter, one obtains the sharp specialization
`f(x_k) - f(x^*) ≤ 4 γ^{3/2} M_f ‖x₀ - x^*‖^3 (3 / (2k + 1))^{3.5}` for every `k ≥ 1`. -/
theorem gap_le_inverse_seven_halves_rate_best_sigma
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    f (method k) - f xStar ≤
      (((4 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
          ‖Δ‖[B] ^ (3 : ℕ)) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := by
  -- Route correction: make the optimal-parameter specialization explicit instead of relying on a
  -- broad `simpa` to normalize the reciprocal coefficient.
  let Δ := x0 - xStar
  have hrate :
      f (method k) - f xStar ≤
        ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
              ‖Δ‖[B] ^ (3 : ℕ)) /
            (((1 : ℝ) / Real.sqrt 2) *
              Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)))) *
          Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := by
    -- First specialize Theorem 4.3.2 at the fixed parameter `σ = 1 / √2`.
    simpa [Δ] using
      method.gap_le_inverse_seven_halves_rate
        hf_conv hpsi_upper hresidual_lower hresidual_upper hk
  have hcoeff :
      (((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) * ‖Δ‖[B] ^ (3 : ℕ) /
          (((1 : ℝ) / Real.sqrt 2) * Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)))) =
        (((4 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) * ‖Δ‖[B] ^ (3 : ℕ)) := by
    -- Then rewrite the scalar reciprocal to `4` and regroup the remaining factors.
    rw [← two_div_inv_sqrt_two_mul_sqrt_one_sub_sq_eq_four]
    ring
  -- Substitute the exact coefficient computation into the specialized rate theorem.
  calc
    f (method k) - f xStar
        ≤ ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
              ‖Δ‖[B] ^ (3 : ℕ)) /
            (((1 : ℝ) / Real.sqrt 2) *
              Real.sqrt (1 - ((1 : ℝ) / Real.sqrt 2) ^ (2 : ℕ)))) *
          Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := hrate
    _ = (((4 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
            ‖Δ‖[B] ^ (3 : ℕ)) *
          Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := by
            rw [hcoeff]

end OptimalCubicNewtonMethod

end
