/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.5 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`, the owner evaluation of the estimating
  sequence `ψ_k`;
* `OptimalCubicNewtonMethod.estimatingLowerBoundCorrection` in `Lemma_4_3_4`, the derived
  correction term `B_k` attached to a method;
* `optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum` in `Lemma_4_3_4`, the
  predecessor lemma bounding `A_k f(x_k) + B_k` by `ψ_k(v_k)`;
* `CubicNewtonStep.residual` in `Definition_4_3_6`, the owner residual `r_M`.

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`
* the chosen optimizer `xStar`
* the scalar sandwich factor `γ`

Derived API:
* the majorization of `ψ_k` at `xStar`
* the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)`
* the lower bound on the accumulated weights `A_k`

Source/core/bridge triage:
* source-facing: Lemma 4.3.5's quantitative lower bound on the accumulated weights `A_k`
* core/canonical: the owner `OptimalCubicNewtonMethod` and its derived correction term from
  Lemma 4.3.4
* bridge/view: the passage from the residual sandwich to a bound on the scalar recursion for
  `A_k`
-/

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma) {xStar : PrimalSpace B}

namespace OptimalCubicNewtonMethod

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: the accumulated lower-bound correction term is nonnegative because
each summand in its defining series is nonnegative. -/
private lemma estimatingLowerBoundCorrection_nonneg
    (k : ℕ) :
    0 ≤ method.estimatingLowerBoundCorrection k := by
  rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
  have hσsq_lt : sigma ^ (2 : ℕ) < 1 := by
    nlinarith
  have hfactor_nonneg :
      0 ≤ (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * ((Mf : ℝ) / sigma)) := by
    -- The scalar prefactor is the product of the positive `M = Mf / σ` and `((1 - σ²) / 4) ≥ 0`.
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

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: Lemma 4.3.4 and the comparison-point majorization bound the weighted
gap plus the accumulated correction by the initial quadratic distance budget. -/
private lemma weighted_gap_add_correction_le_half_norm_sq
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    let Δ := x0 - xStar
    method.A k * (f (method k) - f xStar) + method.estimatingLowerBoundCorrection k ≤
      (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
  let Δ := x0 - xStar
  have hlower :=
    optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum method
      hf hf_conv hresidual_lower k
  have hmin : method.psi k (method.v k) ≤ method.psi k xStar := by
    -- Evaluate the minimizing property of `v_k` at the comparison point `xStar`.
    exact (isMinOn_univ_iff.mp (method.v_isMin k)) xStar
  have hvalue :
      method.A k * f (method k) + method.estimatingLowerBoundCorrection k ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Chain Lemma 4.3.4 with the comparison-point majorization of `ψ_k`.
    exact le_trans (le_trans hlower hmin) (by simpa [Δ] using hpsi_upper k)
  have hgap :
      method.A k * (f (method k) - f xStar) + method.estimatingLowerBoundCorrection k ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Rearrange the value comparison into the weighted-gap-plus-correction form.
    linarith
  simpa [Δ] using hgap

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: once objective gaps above `xStar` are nonnegative, the estimating
lower-bound correction is controlled by the initial quadratic distance budget. -/
private lemma estimating_lower_bound_correction_le_half_norm_sq_of_gap_nonneg
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hgap_nonneg : ∀ j : ℕ, 0 ≤ f (method j) - f xStar)
    (k : ℕ) :
    let Δ := x0 - xStar
    method.estimatingLowerBoundCorrection k ≤
      (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
  let Δ := x0 - xStar
  have hbudget :
      method.A k * (f (method k) - f xStar) + method.estimatingLowerBoundCorrection k ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Start from the combined weighted-gap-plus-correction budget supplied by Lemma 4.3.4.
    simpa [Δ] using
      method.weighted_gap_add_correction_le_half_norm_sq
        hf hf_conv hpsi_upper hresidual_lower k
  have hweighted_gap_nonneg :
      0 ≤ method.A k * (f (method k) - f xStar) := by
    -- A nonnegative objective gap keeps the weighted contribution nonnegative as well.
    exact mul_nonneg (method.A_nonneg k) (hgap_nonneg k)
  have hcorr :
      method.estimatingLowerBoundCorrection k ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Drop the additional nonnegative weighted-gap term to isolate the correction budget.
    linarith
  simpa [Δ] using hcorr

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: dropping the nonnegative correction term yields the standard weighted
objective-gap estimate controlled by the initial quadratic distance. -/
private lemma weighted_gap_mul_le_half_norm_sq
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
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
  have hbudget :
      method.A k * (f (method k) - f xStar) + method.estimatingLowerBoundCorrection k ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    simpa [Δ] using
      method.weighted_gap_add_correction_le_half_norm_sq
        hf hf_conv hpsi_upper hresidual_lower k
  have hcorr_nonneg : 0 ≤ method.estimatingLowerBoundCorrection k := by
    exact method.estimatingLowerBoundCorrection_nonneg k
  have hgap :
      method.A k * (f (method k) - f xStar) ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Drop the nonnegative correction term from the combined budget.
    linarith
  simpa [Δ] using hgap

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: the residual upper sandwich turns the correction budget from
Lemma 4.3.4 into a budget on the weighted `ρ_i^3` sum. -/
private lemma rhoCubeBudget_le_halfNormSq
    (hγ : 1 ≤ γ)
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    (k : ℕ) :
    let Δ := x0 - xStar
    (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M / γ ^ (3 : ℕ)) *
        Finset.sum (Finset.range k) (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ)) ≤
      (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
  let Δ := x0 - xStar
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  have hsum_le :
      Finset.sum (Finset.range k) (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ)) ≤
        γ ^ (3 : ℕ) *
          Finset.sum (Finset.range k)
            (fun i ↦ method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ)) := by
    -- Compare each `ρ_i^3` against `γ^3 r_i^3` before summing.
    calc
      Finset.sum (Finset.range k) (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ))
          ≤ Finset.sum (Finset.range k)
              (fun i ↦
                method.A (i + 1) *
                  (γ ^ (3 : ℕ) * (r[(method.step)] (method.y i)) ^ (3 : ℕ))) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hρ_cube :
                    (method.rho i) ^ (3 : ℕ) ≤
                      γ ^ (3 : ℕ) * (r[(method.step)] (method.y i)) ^ (3 : ℕ) := by
                  have hρ_le :
                      method.rho i ≤ γ * r[(method.step)] (method.y i) := hresidual_upper i
                  have hpow :
                      (method.rho i) ^ (3 : ℕ) ≤
                        (γ * r[(method.step)] (method.y i)) ^ (3 : ℕ) := by
                    exact pow_le_pow_left₀ (method.rho_pos i).le hρ_le 3
                  calc
                    (method.rho i) ^ (3 : ℕ)
                        ≤ (γ * r[(method.step)] (method.y i)) ^ (3 : ℕ) := hpow
                    _ = γ ^ (3 : ℕ) * (r[(method.step)] (method.y i)) ^ (3 : ℕ) := by
                          rw [mul_pow]
                exact mul_le_mul_of_nonneg_left hρ_cube (method.A_nonneg (i + 1))
      _ = γ ^ (3 : ℕ) *
            Finset.sum (Finset.range k)
              (fun i ↦ method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hgap_nonneg : ∀ j : ℕ, 0 ≤ f (method j) - f xStar := by
    intro j
    -- Evaluate the minimizing property of `xStar` at the iterate `x_j`.
    exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) (method j))
  have hcorr_budget :
      method.estimatingLowerBoundCorrection k ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    -- Lemma 4.3.4 already controls the correction term once the objective gaps are nonnegative.
    simpa [Δ] using
      method.estimating_lower_bound_correction_le_half_norm_sq_of_gap_nonneg
        hf hf_conv hpsi_upper hresidual_lower hgap_nonneg k
  have hscale_nonneg :
      0 ≤ (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M / γ ^ (3 : ℕ)) := by
    have hinside_nonneg : 0 ≤ (1 - sigma ^ (2 : ℕ)) / 4 := by
      rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
      nlinarith
    exact div_nonneg (mul_nonneg hinside_nonneg method.M_pos.le) (by positivity)
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum_le hscale_nonneg
  have hrewrite :
      (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M / γ ^ (3 : ℕ)) *
          (γ ^ (3 : ℕ) *
            Finset.sum (Finset.range k)
              (fun i ↦ method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ))) =
        method.estimatingLowerBoundCorrection k := by
    -- Cancel the explicit `γ^3` factor and unfold the correction term.
    rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
    unfold OptimalCubicNewtonMethod.estimatingLowerBoundCorrection OptimalCubicNewtonMethod.M
    field_simp [hγ_pos.ne', hσ_pos.ne']
  rw [hrewrite] at hscaled
  exact le_trans hscaled hcorr_budget

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: the weight identity `a_{i+1}² = 2 A_{i+1} / (M ρ_i)` rewrites each
weighted `ρ_i^3` summand into the scalar quartic-over-sixth normal form. -/
private lemma rhoCubeSummand_eq_quarticDivIncrementSixth
    (i : ℕ) :
    method.A (i + 1) * (method.rho i) ^ (3 : ℕ) =
      (8 / method.M ^ (3 : ℕ)) *
        (method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) := by
  have ha_sq :
      (method.a (i + 1)) ^ (2 : ℕ) =
        (2 : ℝ) * method.A (i + 1) / (method.M * method.rho i) := by
    -- Rewrite the owner recursion so the successor weight `A_{i+1}` appears explicitly.
    simpa [method.A_succ i] using method.a_succ_sq i
  have hrho :
      method.rho i =
        (2 : ℝ) * method.A (i + 1) /
          (method.M * (method.a (i + 1)) ^ (2 : ℕ)) := by
    -- Solve the scalar weight identity for `ρ_i`.
    apply (eq_div_iff
      (mul_ne_zero method.M_pos.ne' ((pow_ne_zero 2) (method.a_pos i).ne'))).mpr
    have hmul :
        (method.a (i + 1)) ^ (2 : ℕ) * (method.M * method.rho i) =
          (2 : ℝ) * method.A (i + 1) := by
      exact (eq_div_iff (mul_ne_zero method.M_pos.ne' (method.rho_pos i).ne')).mp ha_sq
    calc
      method.rho i * (method.M * (method.a (i + 1)) ^ (2 : ℕ))
          = (method.a (i + 1)) ^ (2 : ℕ) * (method.M * method.rho i) := by ring
      _ = (2 : ℝ) * method.A (i + 1) := hmul
  -- Substitute the closed form for `ρ_i` and clear the positive denominators.
  rw [hrho]
  field_simp [method.M_pos.ne', (method.a_pos i).ne']
  ring

omit [CompleteSpace E] in
/-- Helper for Lemma 4.3.5: the correction budget becomes a pure scalar budget on
`∑ A_{i+1}^4 / a_{i+1}^6`. -/
private lemma quarticDivIncrementSixth_budget
    (hγ : 1 ≤ γ)
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    (k : ℕ) :
    let Δ := x0 - xStar
    Finset.sum (Finset.range k)
        (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) ≤
      (γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
        (4 * (1 - sigma ^ (2 : ℕ))) := by
  let Δ := x0 - xStar
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
  have hinside_pos : 0 < 1 - sigma ^ (2 : ℕ) := by
    nlinarith
  have hbudget :
      (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M / γ ^ (3 : ℕ)) *
          Finset.sum (Finset.range k)
            (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ)) ≤
        (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ) := by
    simpa [Δ] using
      method.rhoCubeBudget_le_halfNormSq
        hγ hf hf_conv hxStar hpsi_upper hresidual_lower hresidual_upper k
  have hsum_eq :
      Finset.sum (Finset.range k) (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ)) =
        (8 / method.M ^ (3 : ℕ)) *
          Finset.sum (Finset.range k)
            (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) := by
    -- Normalize each summand to the quartic-over-sixth scalar form.
    calc
      Finset.sum (Finset.range k) (fun i ↦ method.A (i + 1) * (method.rho i) ^ (3 : ℕ))
          = Finset.sum (Finset.range k)
              (fun i ↦ (8 / method.M ^ (3 : ℕ)) *
                (method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [method.rhoCubeSummand_eq_quarticDivIncrementSixth i]
      _ = (8 / method.M ^ (3 : ℕ)) *
            Finset.sum (Finset.range k)
              (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) := by
            rw [Finset.mul_sum]
  rw [hsum_eq] at hbudget
  have hscale_pos :
      0 < γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) / (2 * (1 - sigma ^ (2 : ℕ))) := by
    exact div_pos (mul_pos (pow_pos hγ_pos 3) (pow_pos method.M_pos 2)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hbudget hscale_pos.le
  have hleft :
      (γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) / (2 * (1 - sigma ^ (2 : ℕ)))) *
          ((((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M / γ ^ (3 : ℕ)) *
            ((8 / method.M ^ (3 : ℕ)) *
              Finset.sum (Finset.range k)
                (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)))) =
        Finset.sum (Finset.range k)
          (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) := by
    -- The scalar prefactors cancel exactly after the quartic normalization.
    field_simp [hinside_pos.ne', hγ_pos.ne', method.M_pos.ne']
    ring
  have hright :
      (γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) / (2 * (1 - sigma ^ (2 : ℕ)))) *
          ((1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ)) =
        (γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
          (4 * (1 - sigma ^ (2 : ℕ))) := by
    -- Rewrite the scaled right-hand side into the displayed budget constant.
    field_simp [hinside_pos.ne']
    ring
  rw [hleft, hright] at hscaled
  simpa [Δ] using hscaled

/-- Helper for Lemma 4.3.5: positive scalar increments force every successor accumulated weight
to be strictly positive. -/
private lemma accumulatedWeightSucc_pos
    {A a : ℕ → ℝ}
    (hA_zero : A 0 = 0)
    (hA_succ : ∀ n : ℕ, A (n + 1) = A n + a (n + 1))
    (ha_pos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ n : ℕ, 0 < A (n + 1)
  | 0 => by
      -- The first accumulated weight is exactly the first positive increment.
      rw [hA_succ 0, hA_zero, zero_add]
      simpa using ha_pos 0
  | n + 1 => by
      -- Each later accumulated weight adds another positive increment to a positive prefix weight.
      rw [hA_succ (n + 1)]
      exact add_pos_of_nonneg_of_pos
        (accumulatedWeightSucc_pos hA_zero hA_succ ha_pos n).le
        (ha_pos (n + 1))

/-- Helper for Lemma 4.3.5: the normalized quartic budget
`Q k = (∑_{i < k} A_{i+1}^4 / a_{i+1}^6) * A_k^2`
has an exact one-step recursion after dividing by `x = A_k / A_{k+1}`. -/
private lemma normalizedQuarticBudgetSucc
    {A a : ℕ → ℝ} {k : ℕ}
    (hAk_pos : 0 < A k)
    (hA_succ : A (k + 1) = A k + a (k + 1))
    (ha_pos : 0 < a (k + 1)) :
    let Q : ℕ → ℝ :=
      fun n ↦
        (Finset.sum (Finset.range n) (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ))) *
          A n ^ (2 : ℕ)
    let x : ℝ := A k / A (k + 1)
    Q (k + 1) = Q k / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
  let Q : ℕ → ℝ :=
    fun n ↦
      (Finset.sum (Finset.range n) (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ))) *
        A n ^ (2 : ℕ)
  let x : ℝ := A k / A (k + 1)
  have hAk_nonneg : 0 ≤ A k := hAk_pos.le
  have hAk1_pos : 0 < A (k + 1) := by
    -- The next accumulated weight adds a positive increment to a nonnegative previous weight.
    rw [hA_succ]
    exact add_pos_of_nonneg_of_pos hAk_nonneg ha_pos
  have hAk_ne : A k ≠ 0 := hAk_pos.ne'
  have hAk1_ne : A (k + 1) ≠ 0 := hAk1_pos.ne'
  have ha_ne : a (k + 1) ≠ 0 := ha_pos.ne'
  have hOneSub :
      1 - x = a (k + 1) / A (k + 1) := by
    -- Rewrite `1 - x` into the normalized increment ratio `a_{k+1} / A_{k+1}`.
    dsimp [x]
    rw [hA_succ]
    field_simp [hAk1_ne]
    ring
  calc
    Q (k + 1)
        = (Finset.sum (Finset.range k)
              (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ)) +
            A (k + 1) ^ (4 : ℕ) / a (k + 1) ^ (6 : ℕ)) *
            A (k + 1) ^ (2 : ℕ) := by
              simp [Q, Finset.sum_range_succ]
    _ = (Finset.sum (Finset.range k)
            (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ))) *
            A (k + 1) ^ (2 : ℕ) +
          (A (k + 1) ^ (4 : ℕ) / a (k + 1) ^ (6 : ℕ)) * A (k + 1) ^ (2 : ℕ) := by
            ring
    _ = Q k / x ^ (2 : ℕ) + A (k + 1) ^ (6 : ℕ) / a (k + 1) ^ (6 : ℕ) := by
          -- Convert the old prefix term and the fresh summand into the normalized `x`-form.
          dsimp [Q, x]
          congr 1
          · field_simp [hAk_ne, hAk1_ne]
          · ring
    _ = Q k / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
          -- The last term is exactly `(1 - x)⁻⁶` after substituting the increment ratio.
          rw [hOneSub]
          field_simp [ha_ne, hAk1_ne]

/-- Helper for Lemma 4.3.5: convexity of the seventh power gives the weighted estimate
`(a + t b)^7 ≤ (1 + t)^6 (a^7 + t b^7)` for nonnegative data. -/
private lemma addMulPowSeven_le
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    (a + t * b) ^ (7 : ℕ) ≤
      (1 + t) ^ (6 : ℕ) * (a ^ (7 : ℕ) + t * b ^ (7 : ℕ)) := by
  let p : ℝ :=
    a ^ (5 : ℕ) * t ^ (5 : ℕ) +
      6 * a ^ (5 : ℕ) * t ^ (4 : ℕ) +
      15 * a ^ (5 : ℕ) * t ^ (3 : ℕ) +
      20 * a ^ (5 : ℕ) * t ^ (2 : ℕ) +
      15 * a ^ (5 : ℕ) * t +
      6 * a ^ (5 : ℕ) +
      2 * a ^ (4 : ℕ) * b * t ^ (5 : ℕ) +
      12 * a ^ (4 : ℕ) * b * t ^ (4 : ℕ) +
      30 * a ^ (4 : ℕ) * b * t ^ (3 : ℕ) +
      40 * a ^ (4 : ℕ) * b * t ^ (2 : ℕ) +
      30 * a ^ (4 : ℕ) * b * t +
      5 * a ^ (4 : ℕ) * b +
      3 * a ^ (3 : ℕ) * b ^ (2 : ℕ) * t ^ (5 : ℕ) +
      18 * a ^ (3 : ℕ) * b ^ (2 : ℕ) * t ^ (4 : ℕ) +
      45 * a ^ (3 : ℕ) * b ^ (2 : ℕ) * t ^ (3 : ℕ) +
      60 * a ^ (3 : ℕ) * b ^ (2 : ℕ) * t ^ (2 : ℕ) +
      24 * a ^ (3 : ℕ) * b ^ (2 : ℕ) * t +
      4 * a ^ (3 : ℕ) * b ^ (2 : ℕ) +
      4 * a ^ (2 : ℕ) * b ^ (3 : ℕ) * t ^ (5 : ℕ) +
      24 * a ^ (2 : ℕ) * b ^ (3 : ℕ) * t ^ (4 : ℕ) +
      60 * a ^ (2 : ℕ) * b ^ (3 : ℕ) * t ^ (3 : ℕ) +
      45 * a ^ (2 : ℕ) * b ^ (3 : ℕ) * t ^ (2 : ℕ) +
      18 * a ^ (2 : ℕ) * b ^ (3 : ℕ) * t +
      3 * a ^ (2 : ℕ) * b ^ (3 : ℕ) +
      5 * a * b ^ (4 : ℕ) * t ^ (5 : ℕ) +
      30 * a * b ^ (4 : ℕ) * t ^ (4 : ℕ) +
      40 * a * b ^ (4 : ℕ) * t ^ (3 : ℕ) +
      30 * a * b ^ (4 : ℕ) * t ^ (2 : ℕ) +
      12 * a * b ^ (4 : ℕ) * t +
      2 * a * b ^ (4 : ℕ) +
      6 * b ^ (5 : ℕ) * t ^ (5 : ℕ) +
      15 * b ^ (5 : ℕ) * t ^ (4 : ℕ) +
      20 * b ^ (5 : ℕ) * t ^ (3 : ℕ) +
      15 * b ^ (5 : ℕ) * t ^ (2 : ℕ) +
      6 * b ^ (5 : ℕ) * t +
      b ^ (5 : ℕ)
  have hfactor :
      (1 + t) ^ (6 : ℕ) * (a ^ (7 : ℕ) + t * b ^ (7 : ℕ)) - (a + t * b) ^ (7 : ℕ) =
        t * (a - b) ^ (2 : ℕ) * p := by
    -- The difference factors as `t (a - b)^2` times a polynomial with nonnegative coefficients.
    dsimp [p]
    ring
  have hp_nonneg : 0 ≤ p := by
    -- Every monomial in the factored polynomial is nonnegative.
    dsimp [p]
    positivity
  have hdiff_nonneg :
      0 ≤ (1 + t) ^ (6 : ℕ) * (a ^ (7 : ℕ) + t * b ^ (7 : ℕ)) - (a + t * b) ^ (7 : ℕ) := by
    rw [hfactor]
    exact mul_nonneg (mul_nonneg ht (sq_nonneg (a - b))) hp_nonneg
  linarith

/-- Helper for Lemma 4.3.5: the scalar one-step kernel controlling the normalized quartic budget
from `k` to `k + 1`. -/
private lemma normalizedQuarticBudgetSuccKernel
    (s x : ℝ) (hs : 0 ≤ s) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 / 64 : ℝ) * (s + 2 / 3) ^ (7 : ℕ) ≤
      ((1 / 64 : ℝ) * s ^ (7 : ℕ)) / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
  -- Route correction: replace the stalled Hölder packaging by the smaller weighted-convexity
  -- estimate on `(a + t b)^7`, then choose `t = x^(-1/3) - 1`.
  set y : ℝ := Real.rpow x (1 / 3 : ℝ)
  have hy_pos : 0 < y := by
    -- The cubic-root normalization stays positive because `x > 0`.
    exact Real.rpow_pos_of_pos hx0 _
  have hy_lt_one : y < 1 := by
    -- Since `0 < x < 1`, its cubic root also lies in `(0, 1)`.
    dsimp [y]
    exact Real.rpow_lt_one hx0.le hx1 (by norm_num : (0 : ℝ) < 1 / 3)
  have hy_le_one : y ≤ 1 := hy_lt_one.le
  have hy_ne : y ≠ 0 := hy_pos.ne'
  have hy_cube : y ^ (3 : ℕ) = x := by
    -- Re-expand the cubic root back to `x`.
    simpa [y] using Real.rpow_inv_natCast_pow hx0.le (show (3 : ℕ) ≠ 0 by norm_num) (x := x)
  let t : ℝ := y⁻¹ - 1
  have ht_pos : 0 < t := by
    -- The weight parameter is positive because `y < 1`.
    dsimp [t]
    exact sub_pos.mpr ((one_lt_inv₀ hy_pos).2 hy_lt_one)
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hweighted :
      (s + t * ((2 / 3 : ℝ) / t)) ^ (7 : ℕ) ≤
        (1 + t) ^ (6 : ℕ) *
          (s ^ (7 : ℕ) + t * (((2 / 3 : ℝ) / t) ^ (7 : ℕ))) := by
    -- Apply the weighted seventh-power inequality with the rescaled second summand.
    exact addMulPowSeven_le hs (by positivity) ht_nonneg
  have hfirst :
      (1 + t) ^ (6 : ℕ) * s ^ (7 : ℕ) = s ^ (7 : ℕ) / x ^ (2 : ℕ) := by
    -- The first coefficient is exactly `x⁻²` because `1 + t = y⁻¹` and `y^3 = x`.
    dsimp [t]
    have hy_six : y ^ (6 : ℕ) = x ^ (2 : ℕ) := by
      calc
        y ^ (6 : ℕ) = (y ^ (3 : ℕ)) ^ (2 : ℕ) := by rw [← pow_mul]
        _ = x ^ (2 : ℕ) := by rw [hy_cube]
    field_simp [hy_ne, hx0.ne']
    rw [hy_six]
    ring
  have hone_sub_y :
      1 - y = (1 - x) / (1 + y + y ^ (2 : ℕ)) := by
    -- Factor `1 - x = (1 - y) (1 + y + y²)` using `y^3 = x`.
    apply (eq_div_iff (show (1 + y + y ^ (2 : ℕ)) ≠ 0 by positivity)).2
    calc
      (1 - y) * (1 + y + y ^ (2 : ℕ)) = 1 - y ^ (3 : ℕ) := by ring
      _ = 1 - x := by rw [hy_cube]
  have hsecond :
      (1 + t) ^ (6 : ℕ) * (t * (((2 / 3 : ℝ) / t) ^ (7 : ℕ))) ≤
        64 / (1 - x) ^ (6 : ℕ) := by
    -- Rewrite the second coefficient through `1 - y`, then bound the remaining numerator by
    -- using `0 < y ≤ 1`.
    have hy_sq_le : y ^ (2 : ℕ) ≤ 1 := by
      nlinarith
    have hsum_le : 1 + y + y ^ (2 : ℕ) ≤ 3 := by
      nlinarith
    have hpow_le :
        (1 + y + y ^ (2 : ℕ)) ^ (6 : ℕ) ≤ (3 : ℝ) ^ (6 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hsum_le 6
    have hnum_le :
        ((2 / 3 : ℝ) ^ (7 : ℕ)) * (1 + y + y ^ (2 : ℕ)) ^ (6 : ℕ) ≤ 64 := by
      have hscaled :=
        mul_le_mul_of_nonneg_left hpow_le (show 0 ≤ (2 / 3 : ℝ) ^ (7 : ℕ) by positivity)
      nlinarith
    have hdenom_pos : 0 < 1 - x := by
      nlinarith
    calc
      (1 + t) ^ (6 : ℕ) * (t * (((2 / 3 : ℝ) / t) ^ (7 : ℕ)))
          = ((2 / 3 : ℝ) ^ (7 : ℕ)) / (1 - y) ^ (6 : ℕ) := by
              dsimp [t]
              field_simp [hy_ne, sub_ne_zero.mpr hy_lt_one.ne]
              ring
      _ = (((2 / 3 : ℝ) ^ (7 : ℕ)) * (1 + y + y ^ (2 : ℕ)) ^ (6 : ℕ)) /
            (1 - x) ^ (6 : ℕ) := by
              rw [hone_sub_y]
              field_simp [hdenom_pos.ne', (show (1 + y + y ^ (2 : ℕ)) ≠ 0 by positivity)]
      _ ≤ 64 / (1 - x) ^ (6 : ℕ) := by
            exact div_le_div_of_nonneg_right hnum_le (by positivity)
  have hmain :
      (s + 2 / 3) ^ (7 : ℕ) ≤ s ^ (7 : ℕ) / x ^ (2 : ℕ) + 64 / (1 - x) ^ (6 : ℕ) := by
    -- Collapse the weighted inequality back to the displayed `x`-kernel.
    have hrewrite :
        s + t * ((2 / 3 : ℝ) / t) = s + 2 / 3 := by
      field_simp [ht_pos.ne']
    calc
      (s + 2 / 3) ^ (7 : ℕ) = (s + t * ((2 / 3 : ℝ) / t)) ^ (7 : ℕ) := by rw [hrewrite]
      _ ≤ (1 + t) ^ (6 : ℕ) *
            (s ^ (7 : ℕ) + t * (((2 / 3 : ℝ) / t) ^ (7 : ℕ))) := hweighted
      _ = (1 + t) ^ (6 : ℕ) * s ^ (7 : ℕ) +
            (1 + t) ^ (6 : ℕ) * (t * (((2 / 3 : ℝ) / t) ^ (7 : ℕ))) := by ring
      _ ≤ s ^ (7 : ℕ) / x ^ (2 : ℕ) + 64 / (1 - x) ^ (6 : ℕ) := by
            exact add_le_add (le_of_eq hfirst) hsecond
  -- Divide the already-normalized bound by `64`.
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain (show 0 ≤ (1 / 64 : ℝ) by norm_num)
  simpa [div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Lemma 4.3.5: a quartic budget on the scalar recursion forces the textbook
`((2 k + 1) / 3)^7` growth lower bound for the accumulated weights. -/
private lemma accumulatedWeightLowerBoundOfQuarticBudget
    {A a : ℕ → ℝ} (C : ℝ)
    (hA_zero : A 0 = 0)
    (hA_succ : ∀ n : ℕ, A (n + 1) = A n + a (n + 1))
    (ha_pos : ∀ n : ℕ, 0 < a (n + 1))
    {k : ℕ} (hk : 1 ≤ k)
    (hbudget :
      Finset.sum (Finset.range k)
          (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ)) ≤
        C) :
    (1 / 64 : ℝ) * (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
      C * A k ^ (2 : ℕ) := by
  let Q : ℕ → ℝ :=
    fun n ↦
      (Finset.sum (Finset.range n) (fun i ↦ A (i + 1) ^ (4 : ℕ) / a (i + 1) ^ (6 : ℕ))) *
        A n ^ (2 : ℕ)
  have hA_pos : ∀ n : ℕ, 0 < A (n + 1) := by
    -- Positive increments keep every successor accumulated weight positive.
    exact accumulatedWeightSucc_pos hA_zero hA_succ ha_pos
  have hQ :
      ∀ n : ℕ, (1 / 64 : ℝ) * (((2 * (n + 1) + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤ Q (n + 1) := by
    intro n
    induction n with
    | zero =>
        have hA1 : A 1 = a 1 := by
          simpa [hA_zero] using hA_succ 0
        have hQ1 : Q 1 = 1 := by
          -- The first normalized budget term is exactly `1`.
          dsimp [Q]
          rw [Finset.sum_singleton, hA1]
          field_simp [(ha_pos 0).ne']
        nlinarith [hQ1]
    | succ n ih =>
        let x : ℝ := A (n + 1) / A (n + 2)
        have hAk_pos : 0 < A (n + 1) := hA_pos n
        have hAk1_pos : 0 < A (n + 2) := hA_pos (n + 1)
        have hAk_lt : A (n + 1) < A (n + 2) := by
          -- The next accumulated weight is strictly larger because the new increment is positive.
          rw [hA_succ (n + 1)]
          linarith [ha_pos (n + 1)]
        have hx0 : 0 < x := by
          -- The normalized ratio `x = A_{n+1} / A_{n+2}` is positive.
          dsimp [x]
          exact div_pos hAk_pos hAk1_pos
        have hx1 : x < 1 := by
          -- The same ratio is strictly below `1` because `A_{n+1} < A_{n+2}`.
          dsimp [x]
          exact (div_lt_one hAk1_pos).2 hAk_lt
        have hnorm :
            Q (n + 2) = Q (n + 1) / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
          -- Rewrite the normalized budget by the exact one-step recursion.
          simpa [Q, x] using
            normalizedQuarticBudgetSucc
              (A := A) (a := a) (k := n + 1) hAk_pos (hA_succ (n + 1)) (ha_pos (n + 1))
        have hscaled_ih :
            ((1 / 64 : ℝ) * (((2 * (n + 1) + 1 : ℝ) / 3) ^ (7 : ℕ))) / x ^ (2 : ℕ) ≤
              Q (n + 1) / x ^ (2 : ℕ) := by
          -- Divide the induction hypothesis by the positive factor `x²`.
          exact div_le_div_of_nonneg_right ih (by positivity)
        have hkernel :=
          normalizedQuarticBudgetSuccKernel
            (((2 * (n + 1) + 1 : ℝ) / 3)) x (by positivity) hx0 hx1
        have hkernel' :
            (1 / 64 : ℝ) * (((2 * (n + 2) + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
              ((1 / 64 : ℝ) * (((2 * (n + 1) + 1 : ℝ) / 3) ^ (7 : ℕ))) / x ^ (2 : ℕ) +
                1 / (1 - x) ^ (6 : ℕ) := by
          have hrewrite :
              ((2 * (n + 2) + 1 : ℝ) / 3) =
                (((2 * (n + 1) + 1 : ℝ) / 3) + 2 / 3) := by
            ring
          rw [hrewrite]
          exact hkernel
        have hstep :
            (1 / 64 : ℝ) * (((2 * (n + 2) + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
              Q (n + 1) / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
          exact le_trans hkernel' (by exact add_le_add hscaled_ih le_rfl)
        have hstep' :
            (1 / 64 : ℝ) * (((2 * (n + 1 + 1) + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
              Q (n + 1) / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
          convert hstep using 1
          ring_nf
        have hnorm' :
            Q (n + 1 + 1) = Q (n + 1) / x ^ (2 : ℕ) + 1 / (1 - x) ^ (6 : ℕ) := by
          simpa [Nat.add_assoc] using hnorm
        simpa [hnorm'] using hstep'
  cases k with
  | zero =>
      cases hk
  | succ n =>
      have hbudget_mul :
          Q (n + 1) ≤ C * A (n + 1) ^ (2 : ℕ) := by
        -- Multiply the quartic budget by the nonnegative factor `A_{n+1}²`.
        have :=
          mul_le_mul_of_nonneg_right hbudget (sq_nonneg (A (n + 1)))
        simpa [Q] using this
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
        (le_trans (hQ n) hbudget_mul)

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.5: squaring the displayed `7 / 2` coefficient produces the natural
nat-power coefficient from the quartic-budget induction. -/
private lemma sevenHalvesCoefficient_sq
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma)
    (hγ : 1 ≤ γ) (k : ℕ) :
    ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) *
          Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ)) =
      ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
        (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
  have hinside_nonneg : 0 ≤ 1 - sigma ^ (2 : ℕ) := by
    nlinarith
  have hratio_nonneg : 0 ≤ ((2 * k + 1 : ℝ) / 3) := by
    positivity
  have hgamma_sq :
      (Real.rpow (1 / γ) (3 / 2 : ℝ)) ^ (2 : ℕ) = 1 / γ ^ (3 : ℕ) := by
    -- Rewrite `(γ⁻¹)^(3/2)` squared as `γ⁻³`.
    calc
      (Real.rpow (1 / γ) (3 / 2 : ℝ)) ^ (2 : ℕ)
          = (1 / γ) ^ ((3 / 2 : ℝ) * 2) := by
              exact (Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / γ) (3 / 2 : ℝ) 2).symm
      _ = (1 / γ) ^ (3 : ℝ) := by norm_num
      _ = 1 / γ ^ (3 : ℕ) := by
            simp
  have hratio_sq :
      (Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ) =
        (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
    -- The time factor squared becomes the natural seventh power.
    calc
      (Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ)
          = ((2 * k + 1 : ℝ) / 3) ^ ((7 / 2 : ℝ) * 2) := by
              exact (Real.rpow_mul_natCast hratio_nonneg (7 / 2 : ℝ) 2).symm
      _ = ((2 * k + 1 : ℝ) / 3) ^ (7 : ℝ) := by norm_num
      _ = (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
            simp
  calc
    ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) *
          Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ))
        =
      ((1 / 4 : ℝ) ^ (2 : ℕ)) *
        ((Real.rpow (1 / γ) (3 / 2 : ℝ)) ^ (2 : ℕ)) *
        ((Real.sqrt (1 - sigma ^ (2 : ℕ))) ^ (2 : ℕ)) *
        ((Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ)) := by
          ring
  _ = ((1 / 16 : ℝ) * (1 / γ ^ (3 : ℕ))) * (1 - sigma ^ (2 : ℕ)) *
        (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
          rw [show ((1 / 4 : ℝ) ^ (2 : ℕ)) = (1 / 16 : ℝ) by norm_num]
          rw [hgamma_sq, Real.sq_sqrt hinside_nonneg, hratio_sq]
  _ = ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
        (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
          field_simp [hγ_pos.ne']

-- Proof sketch: combine Lemma 4.3.4, under the contextual Chapter 4 regularity hypothesis
-- `hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)]`, with the upper majorization of the
-- estimating sequence at the global minimizer `xStar` to get the uniform correction bound
-- `method.estimatingLowerBoundCorrection k ≤ (1 / 2) ‖x₀ - xStar‖²`. Then use
-- the residual sandwich `r_M(y_i) ≤ ρ_i ≤ γ r_M(y_i)` to convert the correction bound into a
-- lower bound on `∑ i < k, ρ_i⁻¹ᐟ²`, optimize that sum under the correction constraint as in the
-- textbook Lagrange-multiplier argument, and finally bootstrap the resulting recursion in `A_k`.
-- Source alignment: `xStar` is the solution point, so the theorem keeps the minimizer hypothesis
-- `hxStar : IsMinOn f Set.univ xStar`; because the standalone method owner does not store
-- Definition 4.3.5's Hessian-Lipschitz regularity, the theorem also carries the contextual
-- hypothesis `hf`; and it keeps the nondegenerate-distance hypothesis
-- `hΔ : 0 < ‖x0 - xStar‖[B]`.
omit [CompleteSpace E] in
/-- Lemma 4.3.5: if `f ∈ C22[Mf]` is convex, `xStar` globally minimizes `f`, `γ ≥ 1`, the auxiliary
parameters of Algorithm 4.3.1 satisfy `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)` for every `k`, the
estimating functions are majorized at the solution point `xStar` by
`A_k f(xStar) + (1 / 2) ‖x₀ - xStar‖²`, and the initial `B`-distance to the solution is positive,
then every index `k ≥ 1` satisfies the denominator-free form of the textbook accumulated-weight
lower bound
`(1 / 4) (1 / γ)^(3/2) * sqrt (1 - σ^2) * ((2k + 1) / 3)^(7/2) ≤ M ‖x₀ - xStar‖ A_k`,
with `M = M_f / σ` and the norm induced by `B`. Under `0 < ‖x₀ - xStar‖[B]`, this is equivalent
to the source bound obtained by dividing through by `‖x₀ - xStar‖[B]`. -/
theorem accumulated_weight_lower_bound
    (hγ : 1 ≤ γ)
    (hf : (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (hΔ : 0 < ‖x0 - xStar‖[B])
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    let M : ℝ := (Mf : ℝ) / sigma
    ((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ) ≤
      M * ‖Δ‖[B] * method.A k := by
  let Δ := x0 - xStar
  let M : ℝ := (Mf : ℝ) / sigma
  have hquartic :
      Finset.sum (Finset.range k)
          (fun i ↦ method.A (i + 1) ^ (4 : ℕ) / method.a (i + 1) ^ (6 : ℕ)) ≤
        (γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
          (4 * (1 - sigma ^ (2 : ℕ))) := by
    -- First reduce the estimating-sequence argument to the pure scalar quartic budget.
    simpa [Δ] using
      method.quarticDivIncrementSixth_budget
        hγ hf hf_conv hxStar hpsi_upper hresidual_lower hresidual_upper k
  have hscalar :
      (1 / 64 : ℝ) * (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
        ((γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
          (4 * (1 - sigma ^ (2 : ℕ)))) * method.A k ^ (2 : ℕ) := by
    -- Instantiate the abstract scalar recursion lemma with the method weights.
    exact accumulatedWeightLowerBoundOfQuarticBudget
      (A := method.A) (a := method.a)
      ((γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
        (4 * (1 - sigma ^ (2 : ℕ))))
      method.A_zero method.A_succ method.a_pos hk hquartic
  rcases method.sigma_mem with ⟨hσ_pos, hσ_lt_one⟩
  have hinside_pos : 0 < 1 - sigma ^ (2 : ℕ) := by
    nlinarith
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  have hsquared :
      ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
          (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
        (method.M * ‖Δ‖[B] * method.A k) ^ (2 : ℕ) := by
    have hscale_pos : 0 < (4 * (1 - sigma ^ (2 : ℕ))) / γ ^ (3 : ℕ) := by
      exact div_pos (by positivity) (by positivity)
    have hscaled := mul_le_mul_of_nonneg_left hscalar hscale_pos.le
    have hleft :
        ((4 * (1 - sigma ^ (2 : ℕ))) / γ ^ (3 : ℕ)) *
            ((1 / 64 : ℝ) * (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ))) =
          ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
            (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := by
      -- The left scaling exposes the square of the target coefficient.
      field_simp [hγ_pos.ne']
      ring
    have hright :
        ((4 * (1 - sigma ^ (2 : ℕ))) / γ ^ (3 : ℕ)) *
            (((γ ^ (3 : ℕ) * method.M ^ (2 : ℕ) * ‖Δ‖[B] ^ (2 : ℕ)) /
                (4 * (1 - sigma ^ (2 : ℕ)))) * method.A k ^ (2 : ℕ)) =
          (method.M * ‖Δ‖[B] * method.A k) ^ (2 : ℕ) := by
      -- The quartic-budget constant collapses to the square of `M ‖Δ‖ A_k`.
      field_simp [hinside_pos.ne', hγ_pos.ne']
    rw [hleft, hright] at hscaled
    exact hscaled
  have hleft_nonneg :
      0 ≤
        (((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
          Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) := by
    -- Every scalar factor on the displayed left-hand side is nonnegative.
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ ?_
      · refine mul_nonneg (by positivity) ?_
        exact Real.rpow_nonneg (by positivity) _
      · exact Real.sqrt_nonneg _
    · exact Real.rpow_nonneg (by positivity) _
  have hright_nonneg : 0 ≤ M * ‖Δ‖[B] * method.A k := by
    -- The right-hand side is nonnegative because `M > 0`, `‖Δ‖ > 0`, and `A_k ≥ 0`.
    have hM_pos : 0 < M := by
      simpa [M, OptimalCubicNewtonMethod.M] using method.M_pos
    have hΔ_nonneg : 0 ≤ ‖Δ‖[B] := by
      exact hΔ.le
    refine mul_nonneg ?_ (method.A_nonneg k)
    exact mul_nonneg hM_pos.le hΔ_nonneg
  have htarget_sq :
      ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
          Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ)) ≤
        (M * ‖Δ‖[B] * method.A k) ^ (2 : ℕ) := by
    -- Rewrite the left square by the dedicated coefficient lemma and transport `method.M` to `M`.
    have hsquared' :
        ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
            (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) ≤
          (M * ‖Δ‖[B] * method.A k) ^ (2 : ℕ) := by
      simpa [M, OptimalCubicNewtonMethod.M] using hsquared
    calc
      ((((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
            Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ)) ^ (2 : ℕ))
          =
        ((1 - sigma ^ (2 : ℕ)) / (16 * γ ^ (3 : ℕ))) *
          (((2 * k + 1 : ℝ) / 3) ^ (7 : ℕ)) := method.sevenHalvesCoefficient_sq hγ k
      _ ≤ (M * ‖Δ‖[B] * method.A k) ^ (2 : ℕ) := hsquared'
  -- The desired estimate is the square-root form of the squared inequality above.
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp htarget_sq

end OptimalCubicNewtonMethod

end
