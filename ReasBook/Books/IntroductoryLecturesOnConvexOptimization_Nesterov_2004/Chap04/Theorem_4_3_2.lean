/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.3.2 lies in the optimal cubic-Newton estimating-sequence rate domain on a
finite-dimensional real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod` in `Algorithm_4_3_1`, the chapter owner for the iterate sequence,
  the cubic Newton step `T_M`, the estimating functions `ψ_k`, and the accumulated weights `A_k`;
* `OptimalCubicNewtonMethod.psi_isMin` in `Algorithm_4_3_1`, the derived owner theorem recording
  that each `v_k` minimizes `ψ_k`;
* `OptimalCubicNewtonMethod.accumulated_weight_lower_bound` in `Lemma_4_3_5`, the predecessor
  owner theorem producing the lower bound on `A_k` from the residual sandwich and the estimating
  majorization at `xStar`.

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`
* the comparison point `xStar`
* the scalar sandwich factor `γ`

Derived API:
* the estimating-function majorization at the comparison point `xStar`
* the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)`
* the lower bound on the accumulated weights `A_k`

Source/core/bridge triage:
* source-facing: Theorem 4.3.2's inverse-`7/2` objective-gap estimate
* core/canonical: the owner `OptimalCubicNewtonMethod`
* bridge/view: the passage from the accumulated-weight lower bound to the explicit rate
-/

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 xStar : PrimalSpace B} {sigma γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma)

namespace OptimalCubicNewtonMethod

/-- Helper for Theorem 4.3.2: the residual sandwich already forces the comparison factor
`γ` to be at least `1`. -/
private lemma gamma_one_le_of_residual_sandwich
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k)) :
    1 ≤ γ := by
  have hr_nonneg : 0 ≤ r[(method.step)] (method.y 0) := by
    -- The cubic-step residual is a norm, hence nonnegative.
    rw [CubicNewtonStep.residual_apply]
    positivity
  have hr_pos : 0 < r[(method.step)] (method.y 0) := by
    -- If the zeroth residual vanished, the upper sandwich would contradict `ρ₀ > 0`.
    by_contra hr_not_pos
    have hr_eq_zero : r[(method.step)] (method.y 0) = 0 := by
      exact le_antisymm (le_of_not_gt hr_not_pos) hr_nonneg
    have hρ_le_zero : method.rho 0 ≤ 0 := by
      have hupper := hresidual_upper 0
      rw [hr_eq_zero] at hupper
      simpa using hupper
    exact (not_le_of_gt (method.rho_pos 0)) hρ_le_zero
  have hone_mul_le :
      (1 : ℝ) * r[(method.step)] (method.y 0) ≤
        γ * r[(method.step)] (method.y 0) := by
    -- Chain the lower and upper sandwich bounds at the initial stage.
    exact le_trans (by simpa using hresidual_lower 0) (hresidual_upper 0)
  -- Cancel the positive residual factor from the right.
  nlinarith [hone_mul_le, hr_pos]

/-- Helper for Theorem 4.3.2: the correction term in Lemma 4.3.4 is nonnegative. -/
private lemma estimatingLowerBoundCorrection_nonneg
    (k : ℕ) :
    0 ≤ method.estimatingLowerBoundCorrection k := by
  rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
  have hσsq_lt : sigma ^ (2 : ℕ) < 1 := by
    nlinarith
  have hfactor_nonneg :
      0 ≤ (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * ((Mf : ℝ) / sigma)) := by
    -- The scalar prefactor is the product of two nonnegative terms.
    have hleft_nonneg : 0 ≤ (1 - sigma ^ (2 : ℕ)) / 4 := by
      nlinarith
    exact mul_nonneg hleft_nonneg method.M_pos.le
  -- Every summand in the correction term is nonnegative.
  unfold OptimalCubicNewtonMethod.estimatingLowerBoundCorrection
  refine mul_nonneg hfactor_nonneg ?_
  refine Finset.sum_nonneg ?_
  intro i hi
  refine mul_nonneg (method.A_nonneg (i + 1)) ?_
  rw [CubicNewtonStep.residual_apply]
  positivity

/-- Helper for Theorem 4.3.2: the estimating-sequence machinery yields the weighted objective-gap
bound `A_k (f(x_k) - f(xStar)) ≤ (1 / 2) ‖x₀ - xStar‖²`. -/
private lemma weighted_gap_mul_le_half_norm_sq
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    let Δ := x0 - xStar
    method.A k * (f (method k) - f xStar) ≤
      (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
  let Δ := x0 - xStar
  have hlower :=
    optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum
      (method := method) hf_conv hresidual_lower k
  have hmin : method.psi k (method.v k) ≤ method.psi k xStar := by
    -- Evaluate the minimizing property of `v_k` at the comparison point `xStar`.
    exact (isMinOn_univ_iff.mp (method.v_isMin k)) xStar
  have hvalue :
      method.A k * f (method k) + method.estimatingLowerBoundCorrection k ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Insert the lower estimating-sequence bound into the upper majorization at `xStar`.
    exact le_trans (le_trans hlower hmin) (by simpa [Δ] using hpsi_upper k)
  have hcorr_nonneg : 0 ≤ method.estimatingLowerBoundCorrection k := by
    exact method.estimatingLowerBoundCorrection_nonneg k
  have hplain :
      method.A k * f (method k) ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Drop the nonnegative correction term.
    linarith
  have hgap :
      method.A k * (f (method k) - f xStar) ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Rearrange the weighted value bound into the weighted gap form.
    linarith
  simpa [Δ] using hgap

/-- Helper for Theorem 4.3.2: every accumulated weight `A_k` with `k ≥ 1` is strictly positive. -/
private lemma accumulated_weight_pos_of_one_le
    {k : ℕ} (hk : 1 ≤ k) :
    0 < method.A k := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- The successor weight is the sum of a nonnegative previous weight and a positive increment.
      simpa using add_pos_of_nonneg_of_pos (method.A_nonneg n) (method.a_pos n)

/-- Helper for Theorem 4.3.2: the reciprocal `rpow` factors from Lemma 4.3.5 and the target rate
coefficient multiply to `1 / 2`. -/
private lemma inverse_seven_halves_scalar_product_eq_half
    (hσmem : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hγ : 1 ≤ γ) (k : ℕ) :
    ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ)) /
          Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) *
      ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ)) *
            Real.sqrt (1 - sigma ^ (2 : ℕ))) *
          Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) =
      (1 / 2 : ℝ) := by
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  have hγ_nonneg : 0 ≤ γ := hγ_pos.le
  rcases hσmem with ⟨hσ_pos, hσ_lt_one⟩
  have hinside_pos : 0 < 1 - sigma ^ (2 : ℕ) := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 - sigma ^ (2 : ℕ)) := Real.sqrt_pos.2 hinside_pos
  have hratio_pos : 0 < ((2 * k + 1 : ℝ) / 3) := by
    positivity
  set gpow : ℝ := Real.rpow γ (3 / 2 : ℝ)
  set tpow : ℝ := Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)
  have hgpow_pos : 0 < gpow := by
    -- The `γ^(3/2)` factor is strictly positive because `γ > 0`.
    dsimp [gpow]
    exact Real.rpow_pos_of_pos hγ_pos _
  have htpow_pos : 0 < tpow := by
    -- The `( (2k+1) / 3 )^(7/2)` factor is also strictly positive.
    dsimp [tpow]
    exact Real.rpow_pos_of_pos hratio_pos _
  have hinv_gamma : Real.rpow (1 / γ) (3 / 2 : ℝ) = gpow⁻¹ := by
    -- Rewrite the reciprocal power through `inv_rpow`.
    simpa [gpow, one_div] using (Real.inv_rpow hγ_nonneg (3 / 2 : ℝ))
  have hinv_ratio :
      Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) = tpow⁻¹ := by
    -- The reciprocal time factor is the inverse of `((2k+1)/3)^(7/2)`.
    have hratio_inv :
        (3 : ℝ) / (2 * k + 1 : ℝ) = (((2 * k + 1 : ℝ) / 3) : ℝ)⁻¹ := by
      field_simp
    rw [hratio_inv]
    simpa [tpow] using (Real.inv_rpow hratio_pos.le (7 / 2 : ℝ))
  -- After the reciprocal rewrites, the scalar identity is a field calculation.
  rw [hinv_gamma, hinv_ratio]
  dsimp [gpow, tpow]
  field_simp [hsqrt_pos.ne', hgpow_pos.ne', htpow_pos.ne']
  ring

/-- Helper for Theorem 4.3.2: Lemma 4.3.5's lower bound on `A_k` implies the displayed
right-hand side dominates `(1 / 2) ‖x₀ - xStar‖²` after multiplication by `A_k`. -/
private lemma half_norm_sq_le_accumulated_weight_mul_target_rhs
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) ≤
      method.A k *
        ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
              ‖Δ‖[B] ^ (3 : ℕ) /
            (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
          Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) := by
  let Δ := x0 - xStar
  let scalarCore : ℝ :=
    (((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ)) /
        Real.sqrt (1 - sigma ^ (2 : ℕ))) *
      Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)
  let scale : ℝ := ‖Δ‖[B] ^ (2 : ℕ) * scalarCore
  have hγ : 1 ≤ γ := by
    -- Recover the missing source-side hypothesis `γ ≥ 1` from the residual sandwich.
    exact method.gamma_one_le_of_residual_sandwich hresidual_lower hresidual_upper
  have hweight :
      (((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
          Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ≤
        ((Mf : ℝ) / sigma) * ‖Δ‖[B] * method.A k := by
    -- Import the predecessor lower bound in its denominator-free form.
    simpa [Δ] using
      method.accumulated_weight_lower_bound
        hγ hf_conv hpsi_upper hresidual_lower hresidual_upper hk
  have hscale_nonneg : 0 ≤ scale := by
    -- The scaling factor is nonnegative, so we may multiply the lower bound by it.
    have hγ_nonneg : 0 ≤ γ := le_trans (by norm_num) hγ
    have hγpow_nonneg : 0 ≤ Real.rpow γ (3 / 2 : ℝ) := Real.rpow_nonneg hγ_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - sigma ^ (2 : ℕ)) := Real.sqrt_nonneg _
    have hratio_nonneg :
        0 ≤ Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := by
      exact Real.rpow_nonneg (by positivity) _
    have hscalar_nonneg : 0 ≤ scalarCore := by
      dsimp [scalarCore]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by positivity) hγpow_nonneg) hsqrt_nonneg)
        hratio_nonneg
    dsimp [scale]
    exact mul_nonneg (by positivity) hscalar_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hweight hscale_nonneg
  have hleft :
      scale *
          ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) *
                Real.sqrt (1 - sigma ^ (2 : ℕ))) *
              Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ))) =
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- The scalar factors from the weight lower bound and the target coefficient cancel exactly.
    have hscalar :
        ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ)) /
              Real.sqrt (1 - sigma ^ (2 : ℕ))) *
            Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) *
          ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ)) *
                Real.sqrt (1 - sigma ^ (2 : ℕ))) *
              Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) =
          (1 / 2 : ℝ) := by
      exact inverse_seven_halves_scalar_product_eq_half method.sigma_mem hγ k
    have hscaled_scalar :=
      congrArg (fun t : ℝ ↦ ‖Δ‖[B] ^ (2 : ℕ) * t) hscalar
    simpa [scale, scalarCore, mul_assoc, mul_left_comm, mul_comm] using hscaled_scalar
  have hright :
      scale * (((Mf : ℝ) / sigma) * ‖Δ‖[B] * method.A k) =
        method.A k *
          ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
                ‖Δ‖[B] ^ (3 : ℕ) /
              (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
            Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) := by
    -- Rearrange the scaled lower-bound conclusion into the target right-hand side.
    have hσmem : sigma ∈ Set.Ioo (0 : ℝ) 1 := OptimalCubicNewtonMethod.sigma_mem method
    rcases hσmem with ⟨hσ_pos, hσ_lt_one⟩
    have hinside_pos : 0 < 1 - sigma ^ (2 : ℕ) := by
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt (1 - sigma ^ (2 : ℕ)) := Real.sqrt_pos.2 hinside_pos
    dsimp [scale, scalarCore]
    field_simp [hσ_pos.ne', hsqrt_pos.ne']
  -- Substitute the normalized left and right sides into the scaled lower bound.
  rw [hleft, hright] at hscaled
  simpa [Δ] using hscaled

-- Proof sketch: combine Lemma 4.3.4 with the upper majorization of `ψ_k` at the comparison point
-- `xStar` to get
-- `f (method k) - f xStar ≤ (1 / (2 * method.A k)) * ‖x₀ - xStar‖^2` for `k ≥ 1`. Then apply
-- `method.accumulated_weight_lower_bound` to bound `method.A k` from below and simplify the
-- resulting reciprocal estimate using `M = M_f / σ`.
/-- Theorem 4.3.2: if `f` is convex, the auxiliary parameters of Algorithm 4.3.1 satisfy
the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)` from Lemma 4.3.5, and the estimating
functions are majorized at a comparison point `xStar` by
`A_k f(xStar) + (1 / 2) ‖x₀ - xStar‖^2`, then Algorithm 4.3.1 with `M = M_f / σ` satisfies, for
every `k ≥ 1`,
`f(x_k) - f(xStar) ≤ (2 γ^(3/2) M_f ‖x₀ - xStar‖^3 / (σ * √(1 - σ^2))) * (3 / (2k + 1))^(7/2)`,
where the norm is the primal norm induced by `B`. -/
theorem gap_le_inverse_seven_halves_rate
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
      (((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
          ‖Δ‖[B] ^ (3 : ℕ) /
        (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := by
  let Δ := x0 - xStar
  have hgap_mul :
      method.A k * (f (method k) - f xStar) ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- First turn the estimating-sequence bounds into the standard weighted objective-gap estimate.
    simpa [Δ] using
      method.weighted_gap_mul_le_half_norm_sq
        hf_conv hpsi_upper hresidual_lower k
  have htarget_mul :
      (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) ≤
        method.A k *
          ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
                ‖Δ‖[B] ^ (3 : ℕ) /
              (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
            Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) := by
    -- Then use the lower bound on `A_k` to dominate the reciprocal target coefficient.
    simpa [Δ] using
      method.half_norm_sq_le_accumulated_weight_mul_target_rhs
        hf_conv hpsi_upper hresidual_lower hresidual_upper hk
  have hA_pos : 0 < method.A k := by
    -- The final cancellation step needs strict positivity of the accumulated weight.
    exact method.accumulated_weight_pos_of_one_le hk
  have hmul :
      method.A k * (f (method k) - f xStar) ≤
        method.A k *
          ((((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
                ‖Δ‖[B] ^ (3 : ℕ) /
              (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
            Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ)) := by
    -- Chain the weighted gap estimate with the scaled lower-bound conclusion.
    exact le_trans hgap_mul htarget_mul
  -- Cancel the positive factor `A_k` to finish with the displayed objective-gap estimate.
  nlinarith [hmul, hA_pos]

end OptimalCubicNewtonMethod

end
