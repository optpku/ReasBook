/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Proposition_4_1.Step

public section

open scoped NNReal

/- legacy appendix remark C.1 (1): the NR-LALM+SOC correction is the minimum-norm solution of the
Newton equation and obeys the canonical admissible quadratic bound. -/

namespace LALM.Correction

namespace ScalarExample

/-- The zero objective in the scalar counterexample. -/
@[expose] def objective : EuclideanSpace ℝ (Fin 1) → ℝ :=
  fun _ ↦ 0

/-- The nonlinear constraint `y ↦ y + y² / 2` in the scalar counterexample. -/
@[expose] noncomputable def constraint :
    EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
  fun y ↦ EuclideanSpace.single 0 (y 0 + y 0 ^ 2 / 2)

/-- The base point `1 / 4` in the scalar counterexample. -/
@[expose] noncomputable def basePoint : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (1 / 4)

/-- The base-model step `-1 / 4` in the scalar counterexample. -/
@[expose] noncomputable def baseStep : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (-(1 / 4))

/-- The multiplier `β / 5 + ρ / 32` that makes `baseStep` minimize the scalar model. -/
@[expose] noncomputable def multiplier (β ρ : NNRealˣ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 (β / 5 + ρ / 32)

/-- The interval on which the scalar constraint gradient has uniform lower bound `1 / 2`. -/
@[expose] def region : Set (EuclideanSpace ℝ (Fin 1)) :=
  {y | y 0 ∈ Set.Ioo (-(1 / 2)) (1 / 2)}

/-- Helper for legacy appendix remark C.1: the derivative of the scalar constraint is multiplication by
`1 + y 0`. -/
private lemma fderiv_constraint (y : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ constraint y =
      (1 + y 0) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  -- Differentiate the scalar polynomial through the canonical one-coordinate equivalence.
  have hpoly_raw :=
    (hasDerivAt_id' (y 0)).add (((hasDerivAt_id' (y 0)).pow 2).div_const 2)
  have hpoly_derivative_eq :
      (1 : ℝ) + (2 * y 0 ^ (2 - 1) * 1) / 2 = 1 + y 0 := by
    norm_num
  have hpoly_deriv : HasDerivAt (fun t : ℝ ↦ t + t ^ 2 / 2)
      (1 + y 0) (y 0) := hpoly_raw.congr_deriv hpoly_derivative_eq
  have span_eq : ContinuousLinearMap.toSpanSingleton ℝ (1 + y 0) =
      (1 + y 0) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_apply,
      ContinuousLinearMap.id_apply]
    exact mul_comm t (1 + y 0)
  have hpoly : HasFDerivAt (fun t : ℝ ↦ t + t ^ 2 / 2)
      ((1 + y 0) • ContinuousLinearMap.id ℝ ℝ) (y 0) := by
    exact hpoly_deriv.hasFDerivAt.congr_fderiv span_eq
  have hcomp :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.hasFDerivAt.comp y
      (hpoly.comp y (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).hasFDerivAt)
  have constraint_eventually : constraint =ᶠ[nhds y]
      ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm ∘
        (fun t : ℝ ↦ t + t ^ 2 / 2) ∘
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) := by
    apply Filter.Eventually.of_forall
    intro z
    ext i
    fin_cases i
    simp [constraint, Function.comp_apply]
  have composed_derivative_eq :
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toContinuousLinearMap.comp
          (((1 + y 0) • ContinuousLinearMap.id ℝ ℝ).comp
            (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).toContinuousLinearMap) =
        (1 + y 0) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro u
    ext i
    fin_cases i
    simp
  exact (hcomp.congr_of_eventuallyEq constraint_eventually).congr_fderiv
    composed_derivative_eq |>.fderiv

/-- Helper for legacy appendix remark C.1: the scalar constraint gradient is multiplication by
`1 + y 0`. -/
private lemma constraintGradient_constraint (y : EuclideanSpace ℝ (Fin 1)) :
    EqualityConstrained.constraintGradient constraint y =
      (1 + y 0) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  -- Take the adjoint of the derivative formula; the scalar and identity are self-adjoint.
  rw [EqualityConstrained.constraintGradient_def, fderiv_constraint]
  ext u i
  fin_cases i
  simp

/-- Helper for legacy appendix remark C.1: the derivative of the constant scalar objective vanishes. -/
private lemma fderiv_objective (y : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ objective y = 0 := by
  -- Unfold the objective and use the derivative of a constant function.
  unfold objective
  exact fderiv_const_apply 0

/-- Helper for legacy appendix remark C.1: the squared norm of a one-dimensional Euclidean vector is the
square of its unique coordinate. -/
private lemma norm_sq_eq_coord_sq (u : EuclideanSpace ℝ (Fin 1)) :
    ‖u‖ ^ 2 = u 0 ^ 2 := by
  -- Replace the vector by its single-coordinate representation and evaluate its norm.
  have u_eq : u = EuclideanSpace.single 0 (u 0) := by
    ext i
    fin_cases i
    simp
  rw [u_eq, PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  simp

/-- The step `baseStep` minimizes the LALM base model for `multiplier β ρ`. -/
theorem baseStep_minimizes (β ρ : NNRealˣ) :
    IsMinOn (LALM.stepModel objective constraint (ρ : ℝ) (β : ℝ) basePoint
      (multiplier β ρ)) Set.univ baseStep := by
  -- Reduce every vector to its unique coordinate, then expose the scalar quadratic model.
  rw [isMinOn_univ_iff]
  intro q
  have q_eq : q = EuclideanSpace.single 0 (q 0) := by
    ext i
    fin_cases i
    simp
  have beta_nonneg : (0 : ℝ) ≤ β := NNReal.coe_nonneg β
  have rho_nonneg : (0 : ℝ) ≤ ρ := NNReal.coe_nonneg ρ
  rw [q_eq]
  simp [LALM.stepModel_def, constraint, basePoint, baseStep, multiplier,
    fderiv_constraint, fderiv_objective, norm_sq_eq_coord_sq,
    EuclideanSpace.inner_single_left]
  nlinarith [sq_nonneg (q 0 + 1 / 4)]

/-- The scalar base step sends `basePoint` to the trial point `0`. -/
theorem trialPoint_eq : trialPoint basePoint baseStep = 0 := by
  -- Add the two explicit single-coordinate vectors and cancel their coordinates.
  rw [trialPoint_def]
  ext i
  fin_cases i
  norm_num [basePoint, baseStep]

/-- The scalar linearization residual at the trial point equals `1 / 32`. -/
theorem residual_eq :
    residual constraint basePoint baseStep = EuclideanSpace.single 0 (1 / 32) := by
  -- Evaluate the nonlinear residual using the scalar derivative formula at `basePoint`.
  rw [residual_def, trialPoint_eq, fderiv_constraint]
  ext i
  fin_cases i
  norm_num [constraint, basePoint, baseStep]

/-- Helper for legacy appendix remark C.1: at the zero trial point the scalar Gram map is the identity. -/
private lemma gram_constraint_zero :
    gram constraint 0 = LinearMap.id := by
  -- The constraint gradient at zero is the identity, as is its adjoint composite.
  rw [gram_def, constraintGradient_constraint]
  ext u i
  fin_cases i
  simp

/-- Helper for legacy appendix remark C.1: the chosen inverse of the scalar Gram map fixes every vector at
the zero trial point. -/
private lemma gramInverse_constraint_zero (u : EuclideanSpace ℝ (Fin 1)) :
    gramInverse constraint 0 u = u := by
  -- Apply the canonical left-inverse computation after identifying the Gram kernel.
  have gram_ker : LinearMap.ker (gram constraint 0) = ⊥ := by
    rw [gram_constraint_zero]
    exact LinearMap.ker_id
  have gram_apply : gram constraint 0 u = u := by
    rw [gram_constraint_zero]
    rfl
  unfold gramInverse
  calc
    (gram constraint 0).leftInverse u =
        (gram constraint 0).leftInverse (gram constraint 0 u) :=
      congrArg (gram constraint 0).leftInverse gram_apply.symm
    _ = u := LinearMap.leftInverse_apply_of_inj gram_ker u

/-- The scalar minimum-norm correction equals `-1 / 32`. -/
theorem step_eq :
    step constraint basePoint baseStep = EuclideanSpace.single 0 (-(1 / 32)) := by
  -- At the zero trial point both the constraint gradient and its Gram inverse are identities.
  rw [step_def, trialPoint_eq, residual_eq, gramInverse_constraint_zero,
    constraintGradient_constraint]
  ext i
  fin_cases i
  norm_num

/-- The scalar corrected point has constraint value `-63 / 2048`. -/
theorem correctedConstraint_eq :
    constraint (nextPoint constraint basePoint baseStep) =
      EuclideanSpace.single 0 (-(63 / 2048)) := by
  -- Substitute the explicit correction and evaluate the scalar polynomial at `-1 / 32`.
  rw [nextPoint_def, trialPoint_eq, step_eq]
  ext i
  fin_cases i
  norm_num [constraint]

/-- Both scalar update segments stay in `region`. -/
theorem segments :
    segment ℝ basePoint (trialPoint basePoint baseStep) ⊆ region ∧
      segment ℝ (trialPoint basePoint baseStep)
        (nextPoint constraint basePoint baseStep) ⊆ region := by
  -- Parameterize both segments by nonnegative coefficients and bound their unique coordinate.
  constructor
  · rw [segment_subset_iff]
    intro a b ha hb hab
    rw [trialPoint_eq]
    simp only [smul_zero, add_zero, region, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · simp only [basePoint, PiLp.smul_apply, PiLp.single_apply, if_pos, smul_eq_mul]
      nlinarith
    · simp only [basePoint, PiLp.smul_apply, PiLp.single_apply, if_pos, smul_eq_mul]
      nlinarith
  · rw [segment_subset_iff]
    intro a b ha hb hab
    rw [trialPoint_eq, nextPoint_def, trialPoint_eq, step_eq]
    simp only [smul_zero, zero_add, region, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · simp only [PiLp.smul_apply, PiLp.single_apply, if_pos, smul_eq_mul]
      nlinarith
    · simp only [PiLp.smul_apply, PiLp.single_apply, if_pos, smul_eq_mul]
      nlinarith

/-- On `region`, the scalar constraint gradient has uniform lower norm bound `1 / 2`. -/
theorem licqLowerBound (y : EuclideanSpace ℝ (Fin 1)) (hy : y ∈ region)
    (u : EuclideanSpace ℝ (Fin 1)) :
    (1 / 2 : ℝ) * ‖u‖ ≤ ‖EqualityConstrained.constraintGradient constraint y u‖ := by
  -- The interval hypothesis bounds the positive scalar factor `1 + y 0` from below.
  have factor_lower : (1 / 2 : ℝ) ≤ 1 + y 0 := by
    unfold region at hy
    nlinarith [hy.1]
  have half_nonneg : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have factor_nonneg : (0 : ℝ) ≤ 1 + y 0 := le_trans half_nonneg factor_lower
  rw [constraintGradient_constraint, smul_apply,
    ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg factor_nonneg]
  exact mul_le_mul_of_nonneg_right factor_lower (norm_nonneg u)

/-- Any regularity certificate with `region` as its region makes `baseStep` admissible. -/
theorem isAdmissible (h : EqualityConstrained.Regularity objective constraint)
    (h_region : h.region = region) :
    IsAdmissible h basePoint baseStep := by
  -- Replace the regularity region by the explicit interval and use the segment certificate.
  rw [LALM.Correction.isAdmissible_iff, h_region]
  exact segments

/-- legacy appendix remark C.1 (2): in the explicit scalar example, applying the correction
strictly increases true constraint infeasibility from the feasible trial point. -/
theorem mayIncreaseTrueInfeasibility :
    ‖constraint (trialPoint basePoint baseStep)‖ <
      ‖constraint (nextPoint constraint basePoint baseStep)‖ := by
  -- The trial constraint is zero, while the corrected constraint is the nonzero scalar value.
  rw [trialPoint_eq, correctedConstraint_eq]
  simp [constraint, PiLp.norm_single]

end ScalarExample

end LALM.Correction

end

namespace LALM.Correction.ScalarExample


end LALM.Correction.ScalarExample
