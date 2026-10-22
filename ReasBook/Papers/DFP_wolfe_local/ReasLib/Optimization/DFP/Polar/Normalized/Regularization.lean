/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import ReasLib.Optimization.DFP.Polar.Recurrence

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.Normalized

/-- The exponential-logarithm branch representing `(1 + t ^ 3) ^ (1 / 3)` near zero. -/
def unitRoot (t : ℝ) : ℝ :=
  Real.exp (Real.log (1 + t ^ 3) / 3)

/-- The exponential-logarithm formula defining `unitRoot`. -/
theorem unitRoot_def (t : ℝ) :
    unitRoot t = Real.exp (Real.log (1 + t ^ 3) / 3) := by
  -- Unfold the named exp-log branch used throughout the regularization.
  rfl

/-- The exp-log cubic root is analytic at the origin. -/
private lemma unitRoot_analyticAt :
    AnalyticAt ℝ unitRoot 0 := by
  -- The logarithm input is positive at zero, so analytic composition applies.
  unfold unitRoot
  have hpoly : AnalyticAt ℝ (fun t : ℝ ↦ 1 + t ^ 3) 0 := by
    fun_prop
  have hquot : AnalyticAt ℝ (fun t : ℝ ↦ Real.log (1 + t ^ 3) / 3) 0 :=
    (hpoly.log (by norm_num)).div_const
  exact hquot.rexp'

/-- The exp-log cubic root admits exact cubic cancellation on its positive branch. -/
private lemma unitRoot_sub_one_eq_cube_div (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    unitRoot t - 1 = t ^ 3 / (unitRoot t ^ 2 + unitRoot t + 1) := by
  -- Cubing the exp-log formula recovers `1 + t ^ 3` exactly.
  have hcube : unitRoot t ^ 3 = 1 + t ^ 3 := by
    rw [unitRoot_def, ← Real.exp_nat_mul]
    calc
      Real.exp (3 * (Real.log (1 + t ^ 3) / 3)) = Real.exp (Real.log (1 + t ^ 3)) := by
        congr 1
        ring
      _ = 1 + t ^ 3 := Real.exp_log ht
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    have hroot : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  -- Factor the difference of cubes and cancel the positive denominator.
  apply (eq_div_iff hdenom).2
  calc
    (unitRoot t - 1) * (unitRoot t ^ 2 + unitRoot t + 1) = unitRoot t ^ 3 - 1 := by
      ring
    _ = t ^ 3 := by linarith

/-- The denominator in the exact cubic cancellation is analytic at the origin. -/
private lemma unitRootDenominator_analyticAt :
    AnalyticAt ℝ (fun t : ℝ ↦ unitRoot t ^ 2 + unitRoot t + 1) 0 := by
  -- Build the denominator from the analytic cubic root by ring operations.
  exact (unitRoot_analyticAt.pow 2).add unitRoot_analyticAt |>.add analyticAt_const

/-- The analytic continuation of the cubic next-scale map. -/
def nextScale (t : ℝ) : ℝ :=
  t / unitRoot t

/-- The quotient formula defining `nextScale`. -/
theorem nextScale_def (t : ℝ) :
    nextScale t = t / unitRoot t := by
  -- Expose the quotient defining the continued next scale.
  rfl

/-- The cubic-canceled coefficient in the total angular increment. -/
def angleFactor (t : ℝ) : ℝ :=
  9 * DFP.Polar.baseAngle / (unitRoot t ^ 2 + unitRoot t + 1)

/-- The cubic-cancellation formula defining `angleFactor`. -/
theorem angleFactor_def (t : ℝ) :
    angleFactor t =
      9 * DFP.Polar.baseAngle / (unitRoot t ^ 2 + unitRoot t + 1) := by
  -- Expose the denominator obtained by cubic cancellation.
  rfl

/-- The cubic-canceled angular coefficient is analytic at the origin. -/
private lemma angleFactor_analyticAt :
    AnalyticAt ℝ angleFactor 0 := by
  have hdenom_ne : unitRoot 0 ^ 2 + unitRoot 0 + 1 ≠ 0 := by
    norm_num [unitRoot]
  -- The canceled denominator has value three at the origin.
  unfold angleFactor
  exact analyticAt_const.div unitRootDenominator_analyticAt hdenom_ne

/-- The respective weights `2 / 3` and `1 / 3` of the two angular stages. -/
def stageWeight (i : Fin 2) : ℝ :=
  ![(2 : ℝ) / 3, (1 : ℝ) / 3] i

/-- Phase zero has angular weight `2 / 3`. -/
theorem stageWeight_zero :
    stageWeight 0 = (2 : ℝ) / 3 := by
  -- Evaluate the first entry of the two-stage weight vector.
  simp [stageWeight]

/-- Phase one has angular weight `1 / 3`. -/
theorem stageWeight_one :
    stageWeight 1 = (1 : ℝ) / 3 := by
  -- Evaluate the second entry of the two-stage weight vector.
  simp [stageWeight]

/-- The coefficient of `t ^ 2` in the angle of a normalized stage. -/
def limitAngle (i : Fin 2) : ℝ :=
  stageWeight i * (3 * DFP.Polar.baseAngle)

/-- The first limiting stage angle is `2 * baseAngle`. -/
theorem limitAngle_zero :
    limitAngle 0 = 2 * DFP.Polar.baseAngle := by
  -- Substitute the first stage weight and normalize its scalar coefficient.
  rw [limitAngle, stageWeight_zero]
  ring

/-- The second limiting stage angle is `baseAngle`. -/
theorem limitAngle_one :
    limitAngle 1 = DFP.Polar.baseAngle := by
  -- Substitute the second stage weight and normalize its scalar coefficient.
  rw [limitAngle, stageWeight_one]
  ring

/-- The analytic coefficient multiplying `t ^ 2` in a stage angle. -/
def stageAngleFactor (i : Fin 2) (t : ℝ) : ℝ :=
  stageWeight i * angleFactor t

/-- The phase-weighted formula defining `stageAngleFactor`. -/
theorem stageAngleFactor_def (i : Fin 2) (t : ℝ) :
    stageAngleFactor i t = stageWeight i * angleFactor t := by
  -- Expose the phase-weighted analytic angle coefficient.
  rfl

/-- Each phase-weighted angular coefficient is analytic at the origin. -/
private lemma stageAngleFactor_analyticAt (i : Fin 2) :
    AnalyticAt ℝ (stageAngleFactor i) 0 := by
  -- Multiplication by the fixed phase weight preserves analyticity.
  unfold stageAngleFactor
  exact analyticAt_const.mul angleFactor_analyticAt

/-- Each phase-weighted angular coefficient is strictly positive. -/
private lemma stageAngleFactor_pos (i : Fin 2) (t : ℝ) :
    0 < stageAngleFactor i t := by
  have hweight : 0 < stageWeight i := by
    fin_cases i
    · norm_num [stageWeight]
    · norm_num [stageWeight]
  have hangle : 0 < DFP.Polar.baseAngle := by
    rw [DFP.Polar.baseAngle_def]
    positivity
  have hroot : 0 < unitRoot t := Real.exp_pos _
  have hdenom : 0 < unitRoot t ^ 2 + unitRoot t + 1 := by
    nlinarith [sq_nonneg (unitRoot t)]
  -- Every factor in the canceled coefficient is positive.
  rw [stageAngleFactor_def, angleFactor_def]
  positivity

/-- The cubic-canceled analytic extension of a stage angle. -/
def stageAngle (i : Fin 2) (t : ℝ) : ℝ :=
  t ^ 2 * stageAngleFactor i t

/-- The canceled formula defining `stageAngle`. -/
theorem stageAngle_def (i : Fin 2) (t : ℝ) :
    stageAngle i t = t ^ 2 * stageAngleFactor i t := by
  -- Expose the canceled quadratic factor in the stage angle.
  rfl

/-- The canceled extension of `sin (stageAngle i t) / t ^ 2`. -/
def sinFactor (i : Fin 2) (t : ℝ) : ℝ :=
  stageAngleFactor i t * Real.sinc (stageAngle i t)

/-- The `sinc` formula defining `sinFactor`. -/
theorem sinFactor_def (i : Fin 2) (t : ℝ) :
    sinFactor i t = stageAngleFactor i t * Real.sinc (stageAngle i t) := by
  -- Expose the removable-singularity representation of the sine quotient.
  rfl

/-- The canceled extension of `t ^ 2 * cot (stageAngle i t)`. -/
def cotFactor (i : Fin 2) (t : ℝ) : ℝ :=
  Real.cos (stageAngle i t) / sinFactor i t

/-- The canceled formula defining `cotFactor`. -/
theorem cotFactor_def (i : Fin 2) (t : ℝ) :
    cotFactor i t = Real.cos (stageAngle i t) / sinFactor i t := by
  -- Expose the quotient by the regularized sine factor.
  rfl

/-- The analytic extension of `(nextScale t / t) ^ 2`. -/
def rescaleFactor (t : ℝ) : ℝ :=
  (unitRoot t)⁻¹ ^ 2

/-- The inverse-root formula defining `rescaleFactor`. -/
theorem rescaleFactor_def (t : ℝ) :
    rescaleFactor t = (unitRoot t)⁻¹ ^ 2 := by
  -- Expose the inverse-square root defining the boundary rescaling.
  rfl

/-- At positive scale, `nextScale` agrees with the real-power cubic scale formula. -/
theorem nextScale_eq_rpow (t : ℝ) (ht : 0 < t) :
    nextScale t = t * (1 + t ^ 3) ^ (-(1 : ℝ) / 3) := by
  have hbase : 0 < 1 + t ^ 3 := by
    nlinarith [pow_pos ht 3]
  have hroot : unitRoot t = (1 + t ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [unitRoot_def, Real.rpow_def_of_pos hbase]
    congr 1
    ring
  have hexponent : (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) := by
    ring
  -- Convert the inverse exp-log root to the negative real power.
  rw [nextScale_def, hroot, hexponent, Real.rpow_neg hbase.le]
  simp only [div_eq_mul_inv]

/-- At positive scale, a stage angle agrees with its weighted real-power increment. -/
theorem stageAngle_eq_rpow (i : Fin 2) (t : ℝ) (ht : 0 < t) :
    stageAngle i t =
      stageWeight i *
        ((9 * DFP.Polar.baseAngle / t) *
          ((1 + t ^ 3) ^ ((1 : ℝ) / 3) - 1)) := by
  have hbase : 0 < 1 + t ^ 3 := by
    nlinarith [pow_pos ht 3]
  have hroot : unitRoot t = (1 + t ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [unitRoot_def, Real.rpow_def_of_pos hbase]
    congr 1
    ring
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  -- Replace the real power by the named root, then use exact cubic cancellation.
  rw [stageAngle_def, stageAngleFactor_def, angleFactor_def, ← hroot,
    unitRoot_sub_one_eq_cube_div t hbase]
  field_simp [ht.ne', hdenom]

/-- The next-scale continuation is analytic at zero. -/
theorem nextScale_analyticAt :
    AnalyticAt ℝ nextScale 0 := by
  have hroot_ne : unitRoot 0 ≠ 0 := by
    norm_num [unitRoot]
  -- Divide the analytic identity map by the nonzero analytic root.
  unfold nextScale
  exact analyticAt_id.div unitRoot_analyticAt hroot_ne

/-- Each canceled stage angle is analytic at zero. -/
theorem stageAngle_analyticAt (i : Fin 2) :
    AnalyticAt ℝ (stageAngle i) 0 := by
  -- Retain the explicit quadratic factor in the analytic continuation.
  unfold stageAngle
  exact (analyticAt_id.pow 2).mul (stageAngleFactor_analyticAt i)

/-- The real sinc function is analytic at its removable singularity. -/
private lemma analyticAt_sinc_zero :
    AnalyticAt ℝ Real.sinc 0 := by
  obtain ⟨F, hF_analytic, hsin_factor⟩ :=
    (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0).exists_eq_sum_add_pow_mul 1
  have hsin_factor' : ∀ x : ℝ, Real.sin x = x * F x := by
    intro x
    simpa [iteratedDeriv_zero] using hsin_factor x
  have hderiv_eq :
      deriv Real.sin 0 = deriv (fun x : ℝ ↦ x * F x) 0 :=
    congrArg (fun f : ℝ → ℝ ↦ deriv f 0) (funext hsin_factor')
  have hF_zero : F 0 = 1 := by
    rw [Real.deriv_sin,
      deriv_fun_mul (c := fun x : ℝ ↦ x) (d := F) (by fun_prop)
        hF_analytic.differentiableAt] at hderiv_eq
    simpa using hderiv_eq.symm
  have hF_eq_sinc : F = Real.sinc := by
    funext x
    by_cases hx : x = 0
    · subst x
      simpa [Real.sinc_zero] using hF_zero
    · rw [Real.sinc_of_ne_zero hx]
      apply (eq_div_iff hx).2
      simpa [mul_comm] using (hsin_factor' x).symm
  -- The Taylor factor is exactly the continuous extension `Real.sinc`.
  rwa [hF_eq_sinc] at hF_analytic

/-- Away from zero, `sinFactor` recovers `sin (stageAngle i t) / t ^ 2`. -/
theorem sinFactor_eq_sin_div (i : Fin 2) (t : ℝ) (ht : 0 < t) :
    sinFactor i t = Real.sin (stageAngle i t) / t ^ 2 := by
  have hfactor : stageAngleFactor i t ≠ 0 := (stageAngleFactor_pos i t).ne'
  have hstage : stageAngle i t ≠ 0 := by
    rw [stageAngle_def]
    exact mul_ne_zero (pow_ne_zero 2 ht.ne') hfactor
  -- Expand `sinc` away from zero and cancel the explicit quadratic stage factor.
  rw [sinFactor_def, Real.sinc_of_ne_zero hstage, stageAngle_def]
  field_simp [ht.ne', hfactor]

/-- Away from zero, `cotFactor` recovers `t ^ 2 * cot (stageAngle i t)`. -/
theorem cotFactor_eq_mul_cot (i : Fin 2) (t : ℝ) (ht : 0 < t) :
    cotFactor i t = t ^ 2 * Real.cot (stageAngle i t) := by
  -- Inverting the regularized sine quotient requires only `t ≠ 0`.
  rw [cotFactor_def, sinFactor_eq_sin_div i t ht, Real.cot_eq_cos_div_sin]
  calc
    Real.cos (stageAngle i t) / (Real.sin (stageAngle i t) / t ^ 2) =
        Real.cos (stageAngle i t) * (Real.sin (stageAngle i t) / t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = Real.cos (stageAngle i t) * (t ^ 2 / Real.sin (stageAngle i t)) := by
      rw [inv_div]
    _ = t ^ 2 * (Real.cos (stageAngle i t) / Real.sin (stageAngle i t)) := by
      ring

/-- Away from zero, `rescaleFactor` is `(nextScale t / t) ^ 2`. -/
theorem rescaleFactor_eq_div_sq (t : ℝ) (ht : 0 < t) :
    rescaleFactor t = (nextScale t / t) ^ 2 := by
  have hroot : unitRoot t ≠ 0 := (Real.exp_pos _).ne'
  -- Cancel the positive scale in `nextScale t / t` before squaring.
  rw [rescaleFactor_def, nextScale_def]
  field_simp [ht.ne', hroot]

/-- The canceled sine quotient is analytic at zero for either stage. -/
theorem sinFactor_analyticAt (i : Fin 2) :
    AnalyticAt ℝ (sinFactor i) 0 := by
  have hstage_zero : stageAngle i 0 = 0 := by
    simp [stageAngle]
  have hsinc : AnalyticAt ℝ (fun t : ℝ ↦ Real.sinc (stageAngle i t)) 0 := by
    simpa [Function.comp_def] using
      analyticAt_sinc_zero.comp_of_eq (stageAngle_analyticAt i) hstage_zero
  -- Multiply the analytic angle coefficient by the analytic sinc extension.
  unfold sinFactor
  exact (stageAngleFactor_analyticAt i).mul hsinc

/-- The canceled cotangent factor is analytic at zero for either stage. -/
theorem cotFactor_analyticAt (i : Fin 2) :
    AnalyticAt ℝ (cotFactor i) 0 := by
  have hstage_zero : stageAngle i 0 = 0 := by
    simp [stageAngle]
  have hcos : AnalyticAt ℝ (fun t : ℝ ↦ Real.cos (stageAngle i t)) 0 := by
    simpa [Function.comp_def] using
      (Real.analyticAt_cos : AnalyticAt ℝ Real.cos 0).comp_of_eq
        (stageAngle_analyticAt i) hstage_zero
  have hsin_zero : sinFactor i 0 ≠ 0 := by
    have hfactor := (stageAngleFactor_pos i 0).ne'
    simpa [sinFactor, stageAngle, Real.sinc_zero] using hfactor
  -- The regularized sine denominator remains nonzero at the origin.
  unfold cotFactor
  exact hcos.div (sinFactor_analyticAt i) hsin_zero

/-- The next-scale quartic remainder factors through `t ^ 7` on the positive root branch. -/
private lemma nextScale_sub_quartic_eq (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    nextScale t - (t - (1 / 3 : ℝ) * t ^ 4) =
      t ^ 7 *
        ((unitRoot t ^ 2 + 2 * unitRoot t + 3) /
          (3 * unitRoot t * (unitRoot t ^ 2 + unitRoot t + 1) ^ 2)) := by
  have hroot : unitRoot t ≠ 0 := (Real.exp_pos _).ne'
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hdenom' : unitRoot t * (unitRoot t + 1) + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hcubic :
      (unitRoot t - 1) * (unitRoot t ^ 2 + unitRoot t + 1) = t ^ 3 :=
    (eq_div_iff hdenom).mp (unitRoot_sub_one_eq_cube_div t ht)
  have hfour : t ^ 4 = t * t ^ 3 := by
    ring
  have hseven : t ^ 7 = t * (t ^ 3) ^ 2 := by
    ring
  -- Express every higher power through the exact cubic factor before normalization.
  rw [nextScale_def, hfour, hseven, ← hcubic]
  field_simp [hroot, hdenom, hdenom']
  ring

/-- A stage-angle quadratic remainder factors through `t ^ 5` on the positive root branch. -/
private lemma stageAngle_sub_quadratic_eq (i : Fin 2) (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    stageAngle i t - limitAngle i * t ^ 2 =
      t ^ 5 *
        (-3 * DFP.Polar.baseAngle * stageWeight i * (unitRoot t + 2) /
          (unitRoot t ^ 2 + unitRoot t + 1) ^ 2) := by
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hdenom' : unitRoot t * (unitRoot t + 1) + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hcubic :
      (unitRoot t - 1) * (unitRoot t ^ 2 + unitRoot t + 1) = t ^ 3 :=
    (eq_div_iff hdenom).mp (unitRoot_sub_one_eq_cube_div t ht)
  have hfive : t ^ 5 = t ^ 2 * t ^ 3 := by
    ring
  -- Substitute the canceled cubic factor into the exact stage formula.
  rw [stageAngle_def, stageAngleFactor_def, angleFactor_def, limitAngle, hfive,
    ← hcubic]
  field_simp [hdenom, hdenom']
  ring

/-- The next-scale map has remainder of order seven after its quartic expansion. -/
theorem nextScale_expansion :
    (fun t : ℝ ↦ nextScale t - (t - (1 / 3 : ℝ) * t ^ 4)) =O[𝓝 0]
      fun t : ℝ ↦ t ^ 7 := by
  let qNext : ℝ → ℝ := fun t ↦
    (unitRoot t ^ 2 + 2 * unitRoot t + 3) /
      (3 * unitRoot t * (unitRoot t ^ 2 + unitRoot t + 1) ^ 2)
  have hnum :
      AnalyticAt ℝ (fun t : ℝ ↦ unitRoot t ^ 2 + 2 * unitRoot t + 3) 0 :=
    (unitRoot_analyticAt.pow 2).add (analyticAt_const.mul unitRoot_analyticAt) |>.add
      analyticAt_const
  have hdenom : AnalyticAt ℝ
      (fun t : ℝ ↦ 3 * unitRoot t * (unitRoot t ^ 2 + unitRoot t + 1) ^ 2) 0 :=
    (analyticAt_const.mul unitRoot_analyticAt).mul
      (unitRootDenominator_analyticAt.pow 2)
  have hdenom_ne :
      3 * unitRoot 0 * (unitRoot 0 ^ 2 + unitRoot 0 + 1) ^ 2 ≠ 0 := by
    norm_num [unitRoot]
  have hq_analytic : AnalyticAt ℝ qNext 0 := by
    dsimp only [qNext]
    exact hnum.div hdenom hdenom_ne
  have hq_order : qNext =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hq_analytic.continuousAt.isBigO_one ℝ
  have hmodel : (fun t : ℝ ↦ t ^ 7 * qNext t) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 7) := by
    simpa only [mul_one] using
      (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 7) (𝓝 0)).mul hq_order
  have hbase_eventually : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t ^ 3 := by
    have hcontinuous : ContinuousAt (fun t : ℝ ↦ 1 + t ^ 3) 0 := by
      fun_prop
    exact hcontinuous.eventually (Ioi_mem_nhds (by norm_num))
  have hfactor : (fun t : ℝ ↦ t ^ 7 * qNext t) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ nextScale t - (t - (1 / 3 : ℝ) * t ^ 4)) := by
    filter_upwards [hbase_eventually] with t ht
    exact (nextScale_sub_quartic_eq t ht).symm
  -- The analytic cofactor is bounded, so exact factorization gives the order-seven bound.
  exact hmodel.congr' hfactor Filter.EventuallyEq.rfl

/-- Each stage angle has an order-five remainder after its quadratic term. -/
theorem stageAngle_expansion (i : Fin 2) :
    (fun t : ℝ ↦ stageAngle i t - limitAngle i * t ^ 2) =O[𝓝 0]
      fun t : ℝ ↦ t ^ 5 := by
  let qAngle : ℝ → ℝ := fun t ↦
    -3 * DFP.Polar.baseAngle * stageWeight i * (unitRoot t + 2) /
      (unitRoot t ^ 2 + unitRoot t + 1) ^ 2
  have hnum : AnalyticAt ℝ
      (fun t : ℝ ↦ -3 * DFP.Polar.baseAngle * stageWeight i * (unitRoot t + 2)) 0 :=
    analyticAt_const.mul (unitRoot_analyticAt.add analyticAt_const)
  have hdenom :
      AnalyticAt ℝ (fun t : ℝ ↦ (unitRoot t ^ 2 + unitRoot t + 1) ^ 2) 0 :=
    unitRootDenominator_analyticAt.pow 2
  have hdenom_ne : (unitRoot 0 ^ 2 + unitRoot 0 + 1) ^ 2 ≠ 0 := by
    norm_num [unitRoot]
  have hq_analytic : AnalyticAt ℝ qAngle 0 := by
    dsimp only [qAngle]
    exact hnum.div hdenom hdenom_ne
  have hq_order : qAngle =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hq_analytic.continuousAt.isBigO_one ℝ
  have hmodel : (fun t : ℝ ↦ t ^ 5 * qAngle t) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 5) := by
    simpa only [mul_one] using
      (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 5) (𝓝 0)).mul hq_order
  have hbase_eventually : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t ^ 3 := by
    have hcontinuous : ContinuousAt (fun t : ℝ ↦ 1 + t ^ 3) 0 := by
      fun_prop
    exact hcontinuous.eventually (Ioi_mem_nhds (by norm_num))
  have hfactor : (fun t : ℝ ↦ t ^ 5 * qAngle t) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ stageAngle i t - limitAngle i * t ^ 2) := by
    filter_upwards [hbase_eventually] with t ht
    exact (stageAngle_sub_quadratic_eq i t ht).symm
  -- The analytic cofactor is bounded, so exact factorization gives the order-five bound.
  exact hmodel.congr' hfactor Filter.EventuallyEq.rfl

/-- The analytic boundary rescaling factor is analytic at zero. -/
theorem rescaleFactor_analyticAt :
    AnalyticAt ℝ rescaleFactor 0 := by
  have hroot_ne : unitRoot 0 ≠ 0 := by
    norm_num [unitRoot]
  -- Invert the nonzero analytic root and retain its square.
  unfold rescaleFactor
  exact (unitRoot_analyticAt.inv hroot_ne).pow 2

/-- The rescaling defect factors through `t ^ 3` on the positive root branch. -/
private lemma rescaleFactor_sub_one_eq (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    rescaleFactor t - 1 =
      t ^ 3 *
        (-(unitRoot t + 1) /
          (unitRoot t ^ 2 * (unitRoot t ^ 2 + unitRoot t + 1))) := by
  have hroot : unitRoot t ≠ 0 := (Real.exp_pos _).ne'
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hdenom' : unitRoot t * (unitRoot t + 1) + 1 ≠ 0 := by
    have hroot_pos : 0 < unitRoot t := Real.exp_pos _
    nlinarith [sq_nonneg (unitRoot t)]
  have hcubic :
      (unitRoot t - 1) * (unitRoot t ^ 2 + unitRoot t + 1) = t ^ 3 :=
    (eq_div_iff hdenom).mp (unitRoot_sub_one_eq_cube_div t ht)
  -- Replace `t ^ 3` by the exact difference-of-cubes factor before clearing denominators.
  rw [rescaleFactor_def, ← hcubic]
  field_simp [hroot, hdenom, hdenom']
  ring

/-- Every positive-order rescaling jet below cubic order vanishes at the origin. -/
private lemma rescaleFactor_iteratedFDeriv_eq_zero (n : ℕ) (hn_pos : 0 < n)
    (hn_lt : n < 3) :
    iteratedFDeriv ℝ n rescaleFactor 0 = 0 := by
  let qRes : ℝ → ℝ := fun t ↦
    -(unitRoot t + 1) /
      (unitRoot t ^ 2 * (unitRoot t ^ 2 + unitRoot t + 1))
  have hnum : AnalyticAt ℝ (fun t : ℝ ↦ -(unitRoot t + 1)) 0 :=
    (unitRoot_analyticAt.add analyticAt_const).neg
  have hdenom : AnalyticAt ℝ
      (fun t : ℝ ↦ unitRoot t ^ 2 * (unitRoot t ^ 2 + unitRoot t + 1)) 0 :=
    (unitRoot_analyticAt.pow 2).mul unitRootDenominator_analyticAt
  have hdenom_ne :
      unitRoot 0 ^ 2 * (unitRoot 0 ^ 2 + unitRoot 0 + 1) ≠ 0 := by
    norm_num [unitRoot]
  have hq_analytic : AnalyticAt ℝ qRes 0 := by
    dsimp only [qRes]
    exact hnum.div hdenom hdenom_ne
  have hsub_analytic :
      AnalyticAt ℝ (fun t : ℝ ↦ rescaleFactor t - 1) 0 :=
    rescaleFactor_analyticAt.sub analyticAt_const
  have hbase_eventually : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t ^ 3 := by
    have hcontinuous : ContinuousAt (fun t : ℝ ↦ 1 + t ^ 3) 0 := by
      fun_prop
    exact hcontinuous.eventually (Ioi_mem_nhds (by norm_num))
  have hfactor : ∀ᶠ t : ℝ in 𝓝 0,
      rescaleFactor t - 1 = (t - 0) ^ 3 • qRes t := by
    filter_upwards [hbase_eventually] with t ht
    simpa only [sub_zero, smul_eq_mul, qRes] using rescaleFactor_sub_one_eq t ht
  have horder :
      (3 : ℕ∞) ≤ analyticOrderAt (fun t : ℝ ↦ rescaleFactor t - 1) 0 :=
    (natCast_le_analyticOrderAt hsub_analytic).2 ⟨qRes, hq_analytic, hfactor⟩
  have hsub_deriv :
      iteratedDeriv n (fun t : ℝ ↦ rescaleFactor t - 1) 0 = 0 :=
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub_analytic).mp horder) n hn_lt
  have hscalar : iteratedDeriv n rescaleFactor 0 = 0 := by
    rw [iteratedDeriv_fun_sub rescaleFactor_analyticAt.contDiffAt contDiffAt_const,
      iteratedDeriv_const, if_neg hn_pos.ne'] at hsub_deriv
    simpa using hsub_deriv
  -- A real multilinear map is determined by its value on the all-ones vector.
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, zero_apply] using hscalar

/-- The boundary rescaling factor has zero first scale derivative at zero. -/
theorem rescaleFactor_firstIteratedFDeriv_eq_zero :
    iteratedFDeriv ℝ 1 rescaleFactor 0 = 0 := by
  -- Specialize the common cubic-order jet lemma to order one.
  exact rescaleFactor_iteratedFDeriv_eq_zero 1 (by norm_num) (by norm_num)

/-- The boundary rescaling factor has zero second scale derivative at zero. -/
theorem rescaleFactor_secondIteratedFDeriv_eq_zero :
    iteratedFDeriv ℝ 2 rescaleFactor 0 = 0 := by
  -- Specialize the common cubic-order jet lemma to order two.
  exact rescaleFactor_iteratedFDeriv_eq_zero 2 (by norm_num) (by norm_num)

end DFP.Polar.Normalized
