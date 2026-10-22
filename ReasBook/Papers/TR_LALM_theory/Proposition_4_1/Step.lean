/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

namespace LALM.Correction

open scoped InnerProductSpace

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The trial point obtained from a base-model step. -/
@[expose] def trialPoint (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x + p

/-- The trial point is the base point plus the base-model step. -/
theorem trialPoint_def (x p : EuclideanSpace ℝ (Fin n)) :
    trialPoint x p = x + p := rfl

/-- The constraint residual left by linearization at the base point. -/
@[expose] noncomputable def residual (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  c (trialPoint x p) - c x - fderiv ℝ c x p

/-- The residual has the nonlinear constraint-increment formula. -/
theorem residual_def (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    residual c x p = c (trialPoint x p) - c x - fderiv ℝ c x p := rfl

/-- The Gram endomorphism of the constraint gradient at a point. -/
@[expose] noncomputable def gram (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (ContinuousLinearMap.adjoint
      (EqualityConstrained.constraintGradient c z)).toLinearMap.comp
    (EqualityConstrained.constraintGradient c z).toLinearMap

/-- The Gram endomorphism is the adjoint of the constraint gradient composed with it. -/
theorem gram_def (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    gram c z =
      (ContinuousLinearMap.adjoint
          (EqualityConstrained.constraintGradient c z)).toLinearMap.comp
        (EqualityConstrained.constraintGradient c z).toLinearMap := rfl

/-- The canonical linear left inverse of the Gram endomorphism. -/
@[expose] noncomputable def gramInverse
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (gram c z).leftInverse

/-- On the regularity region, the Gram inverse is a left inverse. -/
theorem gramInverse_comp (h : EqualityConstrained.Regularity f c)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ h.region)
    (u : EuclideanSpace ℝ (Fin m)) :
    gramInverse c z (gram c z u) = u := by
  -- LICQ makes the Gram endomorphism injective, so its chosen left inverse applies.
  have gram_injective : Function.Injective (gram c z) := by
    rw [gram_def, ← ContinuousLinearMap.adjoint_toLinearMap]
    simpa only [LinearMap.coe_comp, Function.comp_apply] using
      (LinearMap.adjoint_comp_self_injective_iff
        (EqualityConstrained.constraintGradient c z).toLinearMap).mpr
          (h.constraintGradientInjective z hz)
  have gram_ker : LinearMap.ker (gram c z) = ⊥ :=
    LinearMap.ker_eq_bot.mpr gram_injective
  exact LinearMap.leftInverse_apply_of_inj gram_ker u

/-- On the regularity region, the Gram inverse is also a right inverse. -/
theorem comp_gramInverse (h : EqualityConstrained.Regularity f c)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ h.region)
    (u : EuclideanSpace ℝ (Fin m)) :
    gram c z (gramInverse c z u) = u := by
  -- In finite dimension the injective Gram endomorphism is also surjective.
  have gram_injective : Function.Injective (gram c z) := by
    rw [gram_def, ← ContinuousLinearMap.adjoint_toLinearMap]
    simpa only [LinearMap.coe_comp, Function.comp_apply] using
      (LinearMap.adjoint_comp_self_injective_iff
        (EqualityConstrained.constraintGradient c z).toLinearMap).mpr
          (h.constraintGradientInjective z hz)
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp gram_injective u
  rw [← hv, gramInverse_comp h z hz]

/-- The minimum-norm correction associated with a base-model step. -/
@[expose] noncomputable def step
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  -EqualityConstrained.constraintGradient c (trialPoint x p)
    (gramInverse c (trialPoint x p) (residual c x p))

/-- The correction has the adjoint-Gram inverse formula from the corrected update. -/
theorem step_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    step c x p = -EqualityConstrained.constraintGradient c (trialPoint x p)
      (gramInverse c (trialPoint x p) (residual c x p)) := rfl

/-- The corrected primal point obtained by adding the correction to the trial point. -/
@[expose] noncomputable def nextPoint
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  trialPoint x p + step c x p

/-- The corrected primal point has its defining update formula. -/
theorem nextPoint_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    nextPoint c x p = trialPoint x p + step c x p := rfl

/-- The classical multiplier update evaluated at the corrected primal point. -/
@[expose] noncomputable def nextMultiplier
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  multiplier + rho • c (nextPoint c x p)

/-- The corrected multiplier has the classical fixed-penalty update formula. -/
theorem nextMultiplier_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) :
    nextMultiplier c rho x multiplier p = multiplier + rho • c (nextPoint c x p) := rfl

/-- The constraint error remaining after the corrected primal update. -/
@[expose] noncomputable def error
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  c (nextPoint c x p) - c x - fderiv ℝ c x p

/-- The corrected constraint error has its defining formula. -/
theorem error_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    error c x p = c (nextPoint c x p) - c x - fderiv ℝ c x p := rfl

/-- The correction is the feasible solution of least norm for the adjoint equation. -/
theorem isMinimumNormSolution (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hz : trialPoint x p ∈ h.region) :
    ContinuousLinearMap.adjoint
        (EqualityConstrained.constraintGradient c (trialPoint x p)) (step c x p) =
      -residual c x p ∧
    ∀ q : EuclideanSpace ℝ (Fin n),
      ContinuousLinearMap.adjoint
          (EqualityConstrained.constraintGradient c (trialPoint x p)) q =
        -residual c x p →
      ‖step c x p‖ ≤ ‖q‖ := by
  constructor
  · -- The chosen Gram inverse makes the correction feasible.
    have hgram := comp_gramInverse h (trialPoint x p) hz (residual c x p)
    rw [step_def, map_neg, neg_inj]
    simpa only [gram_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using hgram
  · intro q hq
    have hfeasible :
        ContinuousLinearMap.adjoint
            (EqualityConstrained.constraintGradient c (trialPoint x p))
              (step c x p) = -residual c x p := by
      have hgram := comp_gramInverse h (trialPoint x p) hz (residual c x p)
      rw [step_def, map_neg, neg_inj]
      simpa only [gram_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using hgram
    have hkernel :
        ContinuousLinearMap.adjoint
            (EqualityConstrained.constraintGradient c (trialPoint x p))
              (q - step c x p) = 0 := by
      rw [map_sub, hq, hfeasible, sub_self]
    have horthogonal : ⟪step c x p, q - step c x p⟫_ℝ = 0 := by
      calc
        ⟪step c x p, q - step c x p⟫_ℝ =
            ⟪-EqualityConstrained.constraintGradient c (trialPoint x p)
                (gramInverse c (trialPoint x p) (residual c x p)),
              q - step c x p⟫_ℝ := by
          exact congrArg (fun v ↦ ⟪v, q - step c x p⟫_ℝ) (step_def c x p)
        _ = -⟪gramInverse c (trialPoint x p) (residual c x p),
              ContinuousLinearMap.adjoint
                (EqualityConstrained.constraintGradient c (trialPoint x p))
                  (q - step c x p)⟫_ℝ := by
          rw [inner_neg_left, ← ContinuousLinearMap.adjoint_inner_right]
        _ = 0 := by rw [hkernel, inner_zero_right, neg_zero]
    have hnormSq :
        ‖q‖ ^ 2 = ‖step c x p‖ ^ 2 + ‖q - step c x p‖ ^ 2 := by
      have hq_decomposition : q = step c x p + (q - step c x p) := by
        module
      calc
        ‖q‖ ^ 2 = ‖step c x p + (q - step c x p)‖ ^ 2 := by
          exact congrArg (fun v ↦ ‖v‖ ^ 2) hq_decomposition
        _ = ‖step c x p‖ ^ 2 + ‖q - step c x p‖ ^ 2 :=
          by simpa only [pow_two] using
            norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
    -- Orthogonal decomposition makes the correction the least-norm solution.
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
    nlinarith [sq_nonneg ‖q - step c x p‖]

/-- The correction satisfies the adjoint equation on the regularity region. -/
theorem step_feasible (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hz : trialPoint x p ∈ h.region) :
    ContinuousLinearMap.adjoint
        (EqualityConstrained.constraintGradient c (trialPoint x p)) (step c x p) =
      -residual c x p :=
  (isMinimumNormSolution h x p hz).1

/-- Every other solution of the adjoint equation has norm at least that of the correction. -/
theorem norm_step_minimal (h : EqualityConstrained.Regularity f c)
    (x p q : EuclideanSpace ℝ (Fin n)) (hz : trialPoint x p ∈ h.region)
    (hq : ContinuousLinearMap.adjoint
      (EqualityConstrained.constraintGradient c (trialPoint x p)) q =
        -residual c x p) :
    ‖step c x p‖ ≤ ‖q‖ :=
  (isMinimumNormSolution h x p hz).2 q hq

/-- A corrected step is admissible when both successive update segments stay in the
regularity region. -/
@[expose] noncomputable def IsAdmissible (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  segment ℝ x (trialPoint x p) ⊆ h.region ∧
    segment ℝ (trialPoint x p) (nextPoint c x p) ⊆ h.region

/-- Corrected-step admissibility is exactly the two required segment containments. -/
theorem isAdmissible_iff (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) :
    IsAdmissible h x p ↔
      segment ℝ x (trialPoint x p) ⊆ h.region ∧
        segment ℝ (trialPoint x p) (nextPoint c x p) ⊆ h.region := Iff.rfl

/-- Admissibility places the base point in the regularity region. -/
theorem base_mem_region (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    x ∈ h.region := by
  -- The base point is the left endpoint of the first admissible segment.
  exact hadm.1 (left_mem_segment ℝ x (trialPoint x p))

/-- Admissibility places the trial point in the regularity region. -/
theorem trialPoint_mem_region (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    trialPoint x p ∈ h.region := by
  -- The trial point is the right endpoint of the first admissible segment.
  exact hadm.1 (right_mem_segment ℝ x (trialPoint x p))

/-- Admissibility places the corrected point in the regularity region. -/
theorem nextPoint_mem_region (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    nextPoint c x p ∈ h.region := by
  -- The corrected point is the right endpoint of the second admissible segment.
  exact hadm.2 (right_mem_segment ℝ (trialPoint x p) (nextPoint c x p))

/-- The quadratic coefficient controlling the norm of the correction. -/
@[expose] noncomputable def stepConstant (h : EqualityConstrained.Regularity f c) : ℝ :=
  h.constraintGradientLipschitz / (2 * h.licqModulus)

/-- The correction coefficient is `L_c / (2 * sigma)`. -/
theorem stepConstant_def (h : EqualityConstrained.Regularity f c) :
    stepConstant h = h.constraintGradientLipschitz / (2 * h.licqModulus) := rfl

/-- The quartic coefficient controlling the corrected constraint error. -/
@[expose] noncomputable def errorConstant (h : EqualityConstrained.Regularity f c) : ℝ :=
  h.constraintGradientLipschitz ^ 3 / (8 * h.licqModulus ^ 2)

/-- The corrected-error coefficient is `L_c ^ 3 / (8 * sigma ^ 2)`. -/
theorem errorConstant_def (h : EqualityConstrained.Regularity f c) :
    errorConstant h =
      h.constraintGradientLipschitz ^ 3 / (8 * h.licqModulus ^ 2) := rfl

/-- The quadratic corrected-error factor at a chosen step radius. -/
@[expose] noncomputable def errorFactor (h : EqualityConstrained.Regularity f c)
    (delta : ℝ) : ℝ :=
  errorConstant h * delta ^ 2

/-- The corrected-error factor is the quartic coefficient times `delta ^ 2`. -/
theorem errorFactor_def (h : EqualityConstrained.Regularity f c) (delta : ℝ) :
    errorFactor h delta = errorConstant h * delta ^ 2 := rfl

/-- The linear displacement factor at a chosen step radius. -/
@[expose] noncomputable def displacementFactor (h : EqualityConstrained.Regularity f c)
    (delta : ℝ) : ℝ :=
  1 + stepConstant h * delta

/-- The displacement factor is `1 + stepConstant h * delta`. -/
theorem displacementFactor_def (h : EqualityConstrained.Regularity f c) (delta : ℝ) :
    displacementFactor h delta = 1 + stepConstant h * delta := rfl

/-- Admissibility gives the quadratic bound for the base linearization residual. -/
theorem residual_le (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    ‖residual c x p‖ ≤ LALM.linearizationConstant h * ‖p‖ ^ 2 := by
  -- Apply the segmentwise Taylor estimate to the base and trial points.
  have hremainder := LALM.norm_sub_sub_fderiv_le c
    h.constraintGradientLipschitz h.region x (trialPoint x p)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hadm.1
  simpa only [residual_def, trialPoint_def, add_sub_cancel_left,
    LALM.linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using hremainder

/-- Admissibility gives the quadratic bound for the correction. -/
theorem norm_step_le (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    ‖step c x p‖ ≤ stepConstant h * ‖p‖ ^ 2 := by
  -- Write the correction as the constraint gradient applied to the Gram preimage.
  let v := gramInverse c (trialPoint x p) (residual c x p)
  have hz := trialPoint_mem_region h x p hadm
  have hvLower :
      (h.licqModulus : ℝ) * ‖v‖ ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
    h.licqLowerBound (trialPoint x p) hz v
  have hgram := comp_gramInverse h (trialPoint x p) hz (residual c x p)
  have hnormSq :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
        ⟪v, residual c x p⟫_ℝ := by
    calc
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
          ⟪ContinuousLinearMap.adjoint
              (EqualityConstrained.constraintGradient c (trialPoint x p))
                (EqualityConstrained.constraintGradient c (trialPoint x p) v), v⟫_ℝ := by
        simpa only [ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
            (EqualityConstrained.constraintGradient c (trialPoint x p)) v
      _ = ⟪gram c (trialPoint x p) v, v⟫_ℝ := by
        rw [gram_def]
        rfl
      _ = ⟪residual c x p, v⟫_ℝ := by rw [hgram]
      _ = ⟪v, residual c x p⟫_ℝ := real_inner_comm _ _
  have hinnerUpper :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 ≤
        ‖v‖ * ‖residual c x p‖ := by
    rw [hnormSq]
    exact real_inner_le_norm v (residual c x p)
  have hscaledInner :
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ := by
    calc
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 ≤
          ((h.licqModulus : ℝ) * ‖v‖) * ‖residual c x p‖ := by
        calc
          (h.licqModulus : ℝ) *
              ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
              (h.licqModulus : ℝ) * ⟪v, residual c x p⟫_ℝ := by
            rw [hnormSq]
          _ ≤ (h.licqModulus : ℝ) * (‖v‖ * ‖residual c x p‖) := by
            gcongr
            exact real_inner_le_norm v (residual c x p)
          _ = ((h.licqModulus : ℝ) * ‖v‖) * ‖residual c x p‖ := by ring
      _ ≤ ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ :=
        mul_le_mul_of_nonneg_right hvLower (norm_nonneg _)
  have hgradientBound :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := by
    by_cases hzero :
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ = 0
    · rw [hzero]
      positivity
    · have hpositive :
          0 < ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      apply (le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mpr
      nlinarith
  have hresidual := residual_le h x p hadm
  rw [step_def]
  simp only [norm_neg]
  calc
    ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := hgradientBound
    _ ≤ (LALM.linearizationConstant h * ‖p‖ ^ 2) /
        (h.licqModulus : ℝ) := by
      gcongr
    _ = stepConstant h * ‖p‖ ^ 2 := by
      rw [stepConstant_def, LALM.linearizationConstant_def]
      norm_num [NNReal.coe_div]
      ring

/-- Admissibility gives the fourth-order bound for the corrected constraint error. -/
theorem norm_error_le (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p) :
    ‖error c x p‖ ≤ errorConstant h * ‖p‖ ^ 4 := by
  -- Feasibility converts the corrected error into a Taylor remainder at the trial point.
  have hlinearization :
      fderiv ℝ c (trialPoint x p) (step c x p) = -residual c x p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.adjoint_adjoint] using
        step_feasible h x p (trialPoint_mem_region h x p hadm)
  have herror :
      error c x p = c (nextPoint c x p) - c (trialPoint x p) -
        fderiv ℝ c (trialPoint x p) (step c x p) := by
    rw [error_def, hlinearization, residual_def]
    module
  have hremainder := LALM.norm_sub_sub_fderiv_le c
    h.constraintGradientLipschitz h.region (trialPoint x p) (nextPoint c x p)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hadm.2
  have hstep := norm_step_le h x p hadm
  have hstepNonneg : 0 ≤ stepConstant h * ‖p‖ ^ 2 := by
    rw [stepConstant_def]
    positivity
  have hstepSq : ‖step c x p‖ ^ 2 ≤ (stepConstant h * ‖p‖ ^ 2) ^ 2 := by
    nlinarith [norm_nonneg (step c x p)]
  rw [herror]
  calc
    ‖c (nextPoint c x p) - c (trialPoint x p) -
        fderiv ℝ c (trialPoint x p) (step c x p)‖ ≤
        (h.constraintGradientLipschitz : ℝ) / 2 * ‖step c x p‖ ^ 2 := by
      simpa only [nextPoint_def, add_sub_cancel_left] using hremainder
    _ ≤ (h.constraintGradientLipschitz : ℝ) / 2 *
        (stepConstant h * ‖p‖ ^ 2) ^ 2 := by
      gcongr
    _ = errorConstant h * ‖p‖ ^ 4 := by
      rw [stepConstant_def, errorConstant_def]
      field_simp [ne_of_gt (NNReal.coe_pos.2 h.licqModulus_pos)]
      ring

/-- Within a step radius, the corrected constraint error has a quadratic bound. -/
theorem norm_error_le_factor (h : EqualityConstrained.Regularity f c)
    (delta : ℝ) (x p : EuclideanSpace ℝ (Fin n))
    (hadm : IsAdmissible h x p) (hp : ‖p‖ ≤ delta) :
    ‖error c x p‖ ≤ errorFactor h delta * ‖p‖ ^ 2 := by
  -- Replace two powers of the step norm by the squared radius.
  have hdeltaNonneg : 0 ≤ delta := le_trans (norm_nonneg p) hp
  have hpSq : ‖p‖ ^ 2 ≤ delta ^ 2 := by nlinarith [norm_nonneg p]
  have hconstantNonneg : 0 ≤ errorConstant h := by
    rw [errorConstant_def]
    positivity
  calc
    ‖error c x p‖ ≤ errorConstant h * ‖p‖ ^ 4 := norm_error_le h x p hadm
    _ = (errorConstant h * ‖p‖ ^ 2) * ‖p‖ ^ 2 := by ring
    _ ≤ (errorConstant h * delta ^ 2) * ‖p‖ ^ 2 := by
      gcongr
    _ = errorFactor h delta * ‖p‖ ^ 2 := by rw [errorFactor_def]

/-- Within a step radius, the total corrected displacement is linear in the
base-step norm. -/
theorem displacement_le (h : EqualityConstrained.Regularity f c)
    (delta : ℝ) (x p : EuclideanSpace ℝ (Fin n))
    (hadm : IsAdmissible h x p) (hp : ‖p‖ ≤ delta) :
    ‖nextPoint c x p - x‖ ≤ displacementFactor h delta * ‖p‖ := by
  -- The corrected displacement is the sum of the base step and correction.
  have hstep := norm_step_le h x p hadm
  have hconstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  calc
    ‖nextPoint c x p - x‖ = ‖p + step c x p‖ := by
      rw [nextPoint_def, trialPoint_def]
      congr 1
      module
    _ ≤ ‖p‖ + ‖step c x p‖ := norm_add_le _ _
    _ ≤ ‖p‖ + stepConstant h * ‖p‖ ^ 2 := by linarith
    _ ≤ ‖p‖ + stepConstant h * delta * ‖p‖ := by
      have hproduct := mul_le_mul_of_nonneg_left hp hconstantNonneg
      nlinarith [norm_nonneg p]
    _ = displacementFactor h delta * ‖p‖ := by
      rw [displacementFactor_def]
      ring

/-- Helper for Proposition 4.1: a minimizer of the base quadratic model satisfies
its explicit first-order stationarity equation. -/
private lemma stepModelStationarity
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModel f c rho beta x multiplier) Set.univ p) :
    gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0 := by
  -- Differentiate the four explicit terms of the model at its minimizer.
  have haffine : HasFDerivAt
      (fun q ↦ c x + fderiv ℝ c x q) (fderiv ℝ c x) p := by
    fun_prop
  have hobjective : HasFDerivAt
      (fun q ↦ ⟪gradient f x, q⟫_ℝ) (innerSL ℝ (gradient f x)) p := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ (gradient f x)).hasFDerivAt
  have hmultiplier : HasFDerivAt
      (fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ)
      (innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) p := by
    simpa only [Function.comp_def, innerSL_apply_apply,
      EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        (innerSL ℝ multiplier).hasFDerivAt.comp p haffine
  have hpenalty : HasFDerivAt
      (fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((rho / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        haffine.norm_sq.const_mul (rho / 2)
  have hproximal : HasFDerivAt (fun q ↦ (beta / 2) * ‖q‖ ^ 2)
      ((beta / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id p).norm_sq.const_mul (beta / 2)
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ (gradient f x) +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((rho / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((beta / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪gradient f x, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative = innerSL ℝ
      (gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      modelDerivative]
    ring
  have hfunctions : LALM.stepModel f c rho beta x multiplier =ᶠ[nhds p]
      (((fun q ↦ ⟪gradient f x, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2 := by
    filter_upwards with q
    exact LALM.stepModel_def f c rho beta x multiplier q
  have hmodel : HasFDerivAt (LALM.stepModel f c rho beta x multiplier)
      modelDerivative p := hsum.congr_of_eventuallyEq hfunctions
  have hderivative : HasFDerivAt (LALM.stepModel f c rho beta x multiplier)
      (innerSL ℝ (gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) p :=
    hmodel.congr_fderiv hderivativeEq
  have hzero : innerSL ℝ
      (gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero hderivative
  have hnormSq :
      ‖gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, zero_apply] using
      congrArg
        (fun A ↦ A (gradient f x + EqualityConstrained.constraintGradient c x
          (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) hzero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Base-model minimization yields the perturbed multiplier identity for the corrected
update. -/
theorem perturbedMultiplierIdentity
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModel f c rho beta x multiplier) Set.univ p) :
    gradient f x + EqualityConstrained.constraintGradient c x
        (nextMultiplier c rho x multiplier p) + beta • p =
      rho • EqualityConstrained.constraintGradient c x (error c x p) := by
  -- Expand the corrected multiplier and error, then use model stationarity.
  rw [nextMultiplier_def, error_def]
  simp only [map_add, map_sub, map_smul]
  have hstationary := stepModelStationarity f c rho beta x multiplier p hp
  simp only [map_add, map_smul] at hstationary
  linear_combination (norm := module) hstationary

end LALM.Correction

end
