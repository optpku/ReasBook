/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.StageFeasibility
public import ReasLib.Optimization.DFP.Polar.SlowCoupling
public import ReasLib.Optimization.DFP.Polar.Continuation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

public section

noncomputable section

open Filter
open scoped Matrix Topology NNReal ContDiff

namespace DFP.Polar.RadiusExpansions

open Normalized StageFeasibility

/-- Helper for eq:polar-W-expansion: the fixed source angle is positive. -/
private theorem baseAngle_pos : 0 < baseAngle := by
  rw [baseAngle_def]
  positivity

/-- Helper for eq:polar-slope-estimates: the original even and odd limiting
slopes evaluated at the selected source parameter. -/
def referenceSlope (ν : ℝ) : Fin 2 → ℝ :=
  ![cycleZ ν + 2 * baseAngle, cycleW ν + baseAngle]

/-- Helper for eq:polar-slope-estimates: the two source slope formulas. -/
theorem referenceSlope_def (ν : ℝ) :
    referenceSlope ν = ![cycleZ ν + 2 * baseAngle, cycleW ν + baseAngle] := by
  rfl

/-- Helper for eq:polar-slope-estimates: the even source slope `Q_E`. -/
theorem referenceSlope_even (ν : ℝ) : referenceSlope ν 0 = cycleZ ν + 2 * baseAngle := by
  rfl

/-- Helper for eq:polar-slope-estimates: the odd source slope `Q_O`. -/
theorem referenceSlope_odd (ν : ℝ) : referenceSlope ν 1 = cycleW ν + baseAngle := by
  rfl

/-- Helper for eq:polar-W-expansion: the source fourth-order radius coefficient
`D_p = c_p Q_p - c_p²/2`. -/
def radiusCoefficient (ν : ℝ) (i : Fin 2) : ℝ :=
  limitAngle i * referenceSlope ν i - limitAngle i ^ 2 / 2

/-- Helper for eq:polar-W-expansion: the common coefficient formula. -/
theorem radiusCoefficient_def (ν : ℝ) (i : Fin 2) :
    radiusCoefficient ν i = limitAngle i * referenceSlope ν i - limitAngle i ^ 2 / 2 := by
  rfl

/-- Helper for eq:polar-W-expansion: the exact even coefficient `D₀`. -/
theorem radiusCoefficient_even (ν : ℝ) :
    radiusCoefficient ν 0 = 2 * baseAngle * referenceSlope ν 0 - 2 * baseAngle ^ 2 := by
  rw [radiusCoefficient_def, limitAngle_zero]
  ring

/-- Helper for eq:polar-W-expansion: the exact odd coefficient `D₁`. -/
theorem radiusCoefficient_odd (ν : ℝ) :
    radiusCoefficient ν 1 = baseAngle * referenceSlope ν 1 - baseAngle ^ 2 / 2 := by
  rw [radiusCoefficient_def, limitAngle_one]

/-- Helper for eq:polar-slope-estimates: the genuine source cycle slopes
exceed `2a` and `a` on the selected parameter interval. -/
theorem referenceSlopes_gt (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) :
    2 * baseAngle < referenceSlope ν 0 ∧ baseAngle < referenceSlope ν 1 := by
  have hfamily := TwoCycle.cycleFamily_mapsTo_positive hν
  have hZ : 0 < cycleZ ν := Set.mem_Ioi.mp hfamily.2.1
  have hW : 0 < cycleW ν := Set.mem_Ioi.mp hfamily.2.2
  rw [referenceSlope_even, referenceSlope_odd]
  exact ⟨lt_add_of_pos_left _ hZ, lt_add_of_pos_left _ hW⟩

/-- Helper for eq:polar-W-expansion: both original source radius coefficients
are strictly positive near `baseAngle`, in fact on the selected interval. -/
theorem radiusCoefficients_pos (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) :
    0 < radiusCoefficient ν 0 ∧ 0 < radiusCoefficient ν 1 := by
  have hQ := referenceSlopes_gt ν hν
  have hprodEven := mul_pos (mul_pos zero_lt_two baseAngle_pos) (sub_pos.mpr hQ.1)
  have hprodOdd := mul_pos baseAngle_pos (sub_pos.mpr hQ.2)
  rw [radiusCoefficient_even, radiusCoefficient_odd]
  constructor
  · nlinarith [sq_pos_of_pos baseAngle_pos]
  · nlinarith [sq_pos_of_pos baseAngle_pos]

/-- Helper for eq:polar-W-expansion: each phase's source radius coefficient
is positive on the original selected parameter interval. -/
theorem radiusCoefficient_pos (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    0 < radiusCoefficient ν i := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue] using (radiusCoefficients_pos ν hν).1
  · simpa only [Fin.mk_one, Fin.isValue] using (radiusCoefficients_pos ν hν).2

/-- Helper for eq:polar-W-expansion: the exact source radius formula at a
scalar normalized slope. -/
def radiusAtSlope (i : Fin 2) (t Q : ℝ) : ℝ :=
  Real.cos (stageAngle i t) + t ^ 2 * Q * Real.sin (stageAngle i t)

/-- Helper for eq:polar-W-expansion: the explicit scalar radius formula. -/
theorem radiusAtSlope_def (i : Fin 2) (t Q : ℝ) :
    radiusAtSlope i t Q = Real.cos (stageAngle i t) + t ^ 2 * Q * Real.sin (stageAngle i t) := by
  rfl

/-- Helper for eq:polar-W-expansion: the scalar formula is exactly the
accepted normalized radius factor at the state's actual slope. -/
theorem normalizedRadiusFactor_eq_radiusAtSlope (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    normalizedRadiusFactor i t x = radiusAtSlope i t (slope x) := by
  rw [normalizedRadiusFactor_def, radiusAtSlope_def]

/-- Helper for eq:polar-W-expansion: sine has an exact cubic remainder with
an analytic scalar cofactor at zero. -/
theorem sin_remainder_factor :
    ∃ q : ℝ → ℝ, AnalyticAt ℝ q 0 ∧ ∀ u : ℝ, Real.sin u - u = u ^ 3 * q u := by
  obtain ⟨q, hq, hformula⟩ :=
    (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0).exists_eq_sum_add_pow_mul 3
  refine ⟨q, hq, ?_⟩
  intro u
  have hsin : Real.sin u = u + u ^ 3 * q u := by
    simpa [Finset.sum_range_succ, iteratedDeriv_succ', iteratedDeriv_zero,
      Real.deriv_sin, Real.deriv_cos, smul_eq_mul] using hformula u
  rw [hsin]
  ring

/-- Helper for eq:polar-W-expansion: cosine has an exact quartic remainder
after `1-u²/2`, with an analytic scalar cofactor at zero. -/
theorem cos_remainder_factor :
    ∃ q : ℝ → ℝ, AnalyticAt ℝ q 0 ∧ ∀ u : ℝ,
      Real.cos u - 1 + u ^ 2 / 2 = u ^ 4 * q u := by
  obtain ⟨q, hq, hformula⟩ :=
    (Real.analyticAt_cos : AnalyticAt ℝ Real.cos 0).exists_eq_sum_add_pow_mul 4
  refine ⟨q, hq, ?_⟩
  intro u
  have hcos : Real.cos u = 1 - u ^ 2 / 2 + u ^ 4 * q u := by
    simpa [Finset.sum_range_succ, iteratedDeriv_succ', iteratedDeriv_zero,
      Real.deriv_cos, Real.deriv_sin, deriv.neg', Pi.neg_apply, smul_eq_mul, sub_eq_add_neg]
      using hformula u
  rw [hcos]
  ring

/-- Helper for eq:polar-W-expansion: the actual analytic stage angle tends
to zero with the scale. -/
theorem stageAngle_tendsto_zero (i : Fin 2) : Tendsto (stageAngle i) (𝓝 0) (𝓝 0) := by
  simpa [ContinuousAt, stageAngle_def] using
    (stageAngle_analyticAt i).continuousAt

/-- Helper for eq:polar-W-expansion: the actual stage angle has quadratic
scale order, following its proved fifth-order source remainder. -/
theorem stageAngle_isBigO_sq (i : Fin 2) :
    (stageAngle i) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
  have horder : (2 : ℕ) < 5 := by norm_num
  have hsmall : (fun t : ℝ ↦ t ^ 5) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) :=
    (Asymptotics.isLittleO_pow_pow horder).isBigO
  have hmain := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝 0)).const_mul_left
    (limitAngle i)
  simpa only [sub_add_cancel] using ((stageAngle_expansion i).trans hsmall).add hmain

/-- Helper for eq:polar-W-expansion: analytic trigonometric cofactors along
the actual quadratic angle give the corresponding doubled scale order. -/
theorem anglePowerFactor_isBigO (i : Fin 2) (n : ℕ) (q : ℝ → ℝ)
    (hq : AnalyticAt ℝ q 0) :
    (fun t : ℝ ↦ stageAngle i t ^ n * q (stageAngle i t)) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ (2 * n)) := by
  have hzero : stageAngle i 0 = 0 := by simp [stageAngle_def]
  have hcomp := hq.comp_of_eq (stageAngle_analyticAt i) hzero
  have hbounded := hcomp.continuousAt.isBigO_one ℝ
  simpa only [← pow_mul, mul_one, Function.comp_def] using
    ((stageAngle_isBigO_sq i).pow n).mul hbounded

/-- Helper for eq:polar-W-expansion: the sine of the original stage angle
has its source quadratic leading term and a fifth-order remainder. -/
theorem sin_stageAngle_expansion (i : Fin 2) :
    (fun t : ℝ ↦ Real.sin (stageAngle i t) - limitAngle i * t ^ 2) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 5) := by
  obtain ⟨q, hq, hfactor⟩ := sin_remainder_factor
  have hsin6 : (fun t : ℝ ↦ Real.sin (stageAngle i t) - stageAngle i t) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 6) := by
    simpa only [hfactor, Nat.reduceMul] using anglePowerFactor_isBigO i 3 q hq
  have horder : (5 : ℕ) < 6 := by norm_num
  have hsmall : (fun t : ℝ ↦ t ^ 6) =O[𝓝 0] (fun t : ℝ ↦ t ^ 5) :=
    (Asymptotics.isLittleO_pow_pow horder).isBigO
  simpa only [sub_add_sub_cancel] using (hsin6.trans hsmall).add (stageAngle_expansion i)

/-- Helper for eq:polar-W-expansion: the cosine of the original stage angle
has fourth-order leading defect and a seventh-order remainder. -/
theorem cos_stageAngle_expansion (i : Fin 2) :
    (fun t : ℝ ↦ Real.cos (stageAngle i t) - 1 + (limitAngle i) ^ 2 / 2 * t ^ 4)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 7) := by
  obtain ⟨q, hq, hfactor⟩ := cos_remainder_factor
  have hcos8 : (fun t : ℝ ↦ Real.cos (stageAngle i t) - 1 + stageAngle i t ^ 2 / 2)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 8) := by
    simpa only [hfactor, Nat.reduceMul] using anglePowerFactor_isBigO i 4 q hq
  have hmain := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝 0)).const_mul_left
    (limitAngle i)
  have hplus := (stageAngle_isBigO_sq i).add hmain
  have hproduct := (stageAngle_expansion i).mul hplus
  have hidentity (t : ℝ) :
      (stageAngle i t - limitAngle i * t ^ 2) * (stageAngle i t + limitAngle i * t ^ 2) =
        stageAngle i t ^ 2 - limitAngle i ^ 2 * t ^ 4 := by ring
  have hsquare7 : (fun t : ℝ ↦ stageAngle i t ^ 2 - limitAngle i ^ 2 * t ^ 4) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 7) := by
    simpa only [hidentity, ← pow_add, Nat.reduceAdd] using hproduct
  have horder : (7 : ℕ) < 8 := by norm_num
  have hsmall : (fun t : ℝ ↦ t ^ 8) =O[𝓝 0] (fun t : ℝ ↦ t ^ 7) :=
    (Asymptotics.isLittleO_pow_pow horder).isBigO
  have hmodel := (hcos8.trans hsmall).sub (hsquare7.const_mul_left (1 / 2 : ℝ))
  have hcombine (t : ℝ) :
      (Real.cos (stageAngle i t) - 1 + stageAngle i t ^ 2 / 2) -
          (1 / 2 : ℝ) * (stageAngle i t ^ 2 - limitAngle i ^ 2 * t ^ 4) =
        Real.cos (stageAngle i t) - 1 + limitAngle i ^ 2 / 2 * t ^ 4 := by ring
  simpa only [hcombine] using hmodel

/-- Helper for eq:polar-W-expansion: the exact source radius at a fixed
slope has fourth-order coefficient `cQ-c²/2` and seventh-order remainder. -/
theorem radiusAtSlope_expansion (i : Fin 2) (Q : ℝ) :
    (fun t : ℝ ↦ radiusAtSlope i t Q - 1 -
      (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4) =O[𝓝 0]
        (fun t : ℝ ↦ t ^ 7) := by
  have hcoef : (fun t : ℝ ↦ t ^ 2 * Q) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
    simpa only [mul_comm Q] using
      (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝 0)).const_mul_left Q
  have hproduct := hcoef.mul (sin_stageAngle_expansion i)
  have hproduct7 : (fun t : ℝ ↦ t ^ 2 * Q *
      (Real.sin (stageAngle i t) - limitAngle i * t ^ 2)) =O[𝓝 0]
        (fun t : ℝ ↦ t ^ 7) := by
    simpa only [← pow_add, Nat.reduceAdd] using hproduct
  have hidentity (t : ℝ) :
      (Real.cos (stageAngle i t) - 1 + limitAngle i ^ 2 / 2 * t ^ 4) +
          t ^ 2 * Q * (Real.sin (stageAngle i t) - limitAngle i * t ^ 2) =
        radiusAtSlope i t Q - 1 - (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4 := by
    rw [radiusAtSlope_def]
    ring
  simpa only [hidentity] using (cos_stageAngle_expansion i).add hproduct7

/-- Helper for eq:polar-W-expansion: the sine factor in the actual radius
map has quadratic scale order. -/
theorem sin_stageAngle_isBigO_sq (i : Fin 2) :
    (fun t : ℝ ↦ Real.sin (stageAngle i t)) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
  have hsin := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0).differentiableAt.isBigO_sub
  have hcomp : (fun t : ℝ ↦ Real.sin (stageAngle i t)) =O[𝓝 0] (stageAngle i) := by
    simpa only [Function.comp_def, Real.sin_zero, sub_zero] using
      hsin.comp_tendsto (stageAngle_tendsto_zero i)
  exact hcomp.trans (stageAngle_isBigO_sq i)

/-- Helper for eq:polar-W-expansion: the exact error in the source radius
splits into its fixed-slope Taylor remainder and one linear slope-error term. -/
theorem normalizedRadiusFactor_error_identity (i : Fin 2) (t Q : ℝ) (x : ℝ × ℝ × ℝ) :
    normalizedRadiusFactor i t x - 1 - (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4 =
      (radiusAtSlope i t Q - 1 - (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4) +
        t ^ 2 * (slope x - Q) * Real.sin (stageAngle i t) := by
  rw [normalizedRadiusFactor_def, radiusAtSlope_def]
  ring

/-- Helper for eq:polar-W-expansion: the exact trigonometric radius formula
turns a linear normalized slope error into one common fifth-order radius error. -/
theorem radiusEstimateOfSlopeBound (i : Fin 2) (Q B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      |slope x - Q| ≤ B * t →
        |normalizedRadiusFactor i t x - 1 -
          (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4| ≤ C * t ^ 5 := by
  have horder : (5 : ℕ) < 7 := by norm_num
  have hsmall : (fun t : ℝ ↦ t ^ 7) =O[𝓝 0] (fun t : ℝ ↦ t ^ 5) :=
    (Asymptotics.isLittleO_pow_pow horder).isBigO
  obtain ⟨A, hA, hfixed⟩ := ((radiusAtSlope_expansion i Q).trans hsmall).exists_pos
  obtain ⟨S, hS, hsin⟩ := (sin_stageAngle_isBigO_sq i).exists_pos
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (hfixed.bound.and hsin.bound)
  refine ⟨A + B * S, add_pos_of_pos_of_nonneg hA (mul_nonneg hB hS.le), δ, hδ, ?_⟩
  intro t ht htδ x hx
  have hdist : dist t 0 < δ := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht] using htδ
  rcases hbound hdist with ⟨hmodel, hsinBound⟩
  have hmodelAbs : |radiusAtSlope i t Q - 1 -
      (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4| ≤ A * t ^ 5 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 5)] using hmodel
  have hsinAbs : |Real.sin (stageAngle i t)| ≤ S * t ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 2)] using hsinBound
  have hbase : |t ^ 2 * (slope x - Q)| ≤ B * t ^ 3 := by
    calc
      |t ^ 2 * (slope x - Q)| = t ^ 2 * |slope x - Q| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      _ ≤ t ^ 2 * (B * t) := mul_le_mul_of_nonneg_left hx (sq_nonneg t)
      _ = B * t ^ 3 := by ring
  have hvariable : |t ^ 2 * (slope x - Q) * Real.sin (stageAngle i t)| ≤
      (B * S) * t ^ 5 := by
    calc
      |t ^ 2 * (slope x - Q) * Real.sin (stageAngle i t)| =
          |t ^ 2 * (slope x - Q)| * |Real.sin (stageAngle i t)| := abs_mul _ _
      _ ≤ (B * t ^ 3) * (S * t ^ 2) := mul_le_mul hbase hsinAbs
        (abs_nonneg _) (mul_nonneg hB (pow_nonneg ht 3))
      _ = (B * S) * t ^ 5 := by ring
  rw [normalizedRadiusFactor_error_identity]
  calc
    |(radiusAtSlope i t Q - 1 - (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4) +
        t ^ 2 * (slope x - Q) * Real.sin (stageAngle i t)| ≤
      |radiusAtSlope i t Q - 1 - (limitAngle i * Q - limitAngle i ^ 2 / 2) * t ^ 4| +
        |t ^ 2 * (slope x - Q) * Real.sin (stageAngle i t)| := abs_add_le _ _
    _ ≤ A * t ^ 5 + (B * S) * t ^ 5 := add_le_add hmodelAbs hvariable
    _ = (A + B * S) * t ^ 5 := by ring

/-- Helper for eq:polar-slope-estimates: slope preserves analytic state
germs with nonzero limiting off-diagonal entry. -/
theorem slopeAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : AnalyticAt ℝ X z) (hC : (X z).2.1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ slope (X y)) z := by
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z := analyticAt_snd.comp hX
  have hC' : AnalyticAt ℝ (fun y ↦ (X y).2.1) z := analyticAt_fst.comp hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z := analyticAt_snd.comp hCV
  simp only [slope_def]
  exact hV.div hC' hC

/-- Helper for eq:polar-slope-estimates: the actual normalized stage
preserves regular analytic scale, state, and multiplier germs. -/
theorem stageAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (hτ : AnalyticAt ℝ τ z) (hX : AnalyticAt ℝ X z)
    (hζ : AnalyticAt ℝ ζ z) (hη : AnalyticAt ℝ η z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z) (hτ0 : τ z = 0)
    (hσ : stageSigma i (τ z) (X z) (ζ z) (η z) ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stage i (τ y) (X y) (ζ y) (η y)) z := by
  have hA : AnalyticAt ℝ (fun y ↦ (X y).1) z := analyticAt_fst.comp hX
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z := analyticAt_snd.comp hX
  have hC : AnalyticAt ℝ (fun y ↦ (X y).2.1) z := analyticAt_fst.comp hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z := analyticAt_snd.comp hCV
  have hAngle := (stageAngle_analyticAt i).comp_of_eq hτ hτ0
  have hSin := (sinFactor_analyticAt i).comp_of_eq hτ hτ0
  have hCot := (cotFactor_analyticAt i).comp_of_eq hτ hτ0
  have hv0 : AnalyticAt ℝ (fun y ↦ stepV (X y) 0) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_zero]
    exact hSlope.neg
  have hv1 : AnalyticAt ℝ (fun y ↦ stepV (X y) 1) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact analyticAt_const
  have hw : AnalyticAt ℝ (fun y ↦ stepW i (τ y) (X y) (ζ y) (η y)) z := by
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases j
    · simp only [stepW_def, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simpa only [stepW_def, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hη
  have hR : AnalyticAt ℝ (fun y ↦ fun r c : Fin 2 ↦ rotation i (τ y) r c) z := by
    apply analyticAt_pi_iff.mpr
    intro r
    apply analyticAt_pi_iff.mpr
    intro c
    fin_cases r
    all_goals fin_cases c
    all_goals simp only [rotation_def, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  have hw0 := analyticAt_pi_iff.mp hw 0
  have hw1 := analyticAt_pi_iff.mp hw 1
  have hR0 := analyticAt_pi_iff.mp hR 0
  have hR1 := analyticAt_pi_iff.mp hR 1
  have hR00 := analyticAt_pi_iff.mp hR0 0
  have hR01 := analyticAt_pi_iff.mp hR0 1
  have hR10 := analyticAt_pi_iff.mp hR1 0
  have hR11 := analyticAt_pi_iff.mp hR1 1
  have hSecant : AnalyticAt ℝ
      (fun y ↦ stageSigma i (τ y) (X y) (ζ y) (η y)) z := by
    simp only [stageSigma_scalar]
    fun_prop
  have hInv := hSecant.inv hσ
  simp only [stage_apply, stageMatrix_def, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
    RealSymmetric2.matrix_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop

/-- Helper for eq:polar-slope-estimates: the computed first cycle stage is
jointly analytic in scale and its original boundary state. -/
theorem firstStage_joint_analyticAt (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleStage L κ 0 z.1 z.2 z.2) (0, x) := by
  have hτ : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.1) (0, x) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x) := analyticAt_snd
  have hAmp : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.1) (0, x) :=
    analyticAt_fst.comp hX
  have hfb : AnalyticAt ℝ
      (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ feedback L κ z.1 z.2) (0, x) := by
    simp only [feedback_def]
    fun_prop (disch := assumption)
  have hSlope := slopeAlong_analyticAt hX hC
  have hfb0 : feedback L κ 0 x = 1 := by simp [feedback_def]
  have hSecant : stageSigma 0 0 x 1 (feedback L κ 0 x) ≠ 0 := by
    rw [hfb0, stageSigma_zero_unit]
    exact one_ne_zero
  simpa only [cycleStage_even_apply] using
    stageAlong_analyticAt 0 hτ hX analyticAt_const hfb hSlope rfl hSecant

/-- Helper for eq:polar-slope-estimates: the normalized slope at each
actual phase input, including the computed odd stage. -/
def cycleSlope (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  slope (cycleInput L κ i t x)

/-- Helper for eq:polar-slope-estimates: the actual phase slope formula. -/
theorem cycleSlope_def (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleSlope L κ i t x = slope (cycleInput L κ i t x) := by
  rfl

/-- Helper for eq:polar-slope-estimates: both computed phase slopes are
jointly analytic in scale and state near a regular zero-scale cycle input. -/
theorem cycleSlope_joint_analyticAt (L κ : ℝ) (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleSlope L κ i z.1 z.2) (0, x) := by
  have hX : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x) := analyticAt_snd
  have hfirst := firstStage_joint_analyticAt L κ x hA hC
  have hfirstC : (cycleStage L κ 0 0 x x).2.1 ≠ 0 := by
    rw [cycleStage_zero]
    exact hCNext
  fin_cases i
  · simpa only [cycleSlope_def, Fin.zero_eta, Fin.isValue, cycleInput_zero] using
      slopeAlong_analyticAt hX hC
  · simpa only [cycleSlope_def, Fin.mk_one, Fin.isValue, cycleInput_one] using
      slopeAlong_analyticAt hfirst hfirstC

/-- Helper for eq:polar-slope-estimates: the exact limiting slopes of the
actual alternating cycle are the original `Q_E` and `Q_O`. -/
theorem cycleSlope_at_zero (L κ ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    cycleSlope L κ i 0 (TwoCycle.evenState (cycleK ν)) = referenceSlope ν i := by
  have hK := TwoCycle.cycleK_bijOn_parameterSet.mapsTo hν
  have hinv := TwoCycle.inverseParameter_invOn.1 hν
  fin_cases i
  · simp only [cycleSlope_def, Fin.zero_eta, Fin.isValue, cycleInput_zero,
      TwoCycle.slope_evenState _ hK, hinv, referenceSlope_even]
  · simp only [cycleSlope_def, Fin.mk_one, Fin.isValue, cycleInput_one,
      firstStage_zero_evenState L κ _ hK, TwoCycle.slope_oddState _ hK,
      hinv, referenceSlope_odd]

/-- Helper for eq:polar-slope-estimates: a common linear state deviation
gives common linear errors in both actual phase slopes, including the
computed odd stage, with parameters fixed before any starting index. -/
theorem cycleSlopeEstimateOfStateBound (L κ ν B : ℝ)
    (hν : ν ∈ TwoCycle.parameterSet) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      ‖x - TwoCycle.evenState (cycleK ν)‖ ≤ B * t →
        ∀ i : Fin 2, |cycleSlope L κ i t x - referenceSlope ν i| ≤ C * t := by
  have hK := TwoCycle.cycleK_bijOn_parameterSet.mapsTo hν
  have hE := (regularState_def _).mp (regularState_evenState (cycleK ν) hK)
  have hO := (regularState_def _).mp (regularState_oddState (cycleK ν) hK)
  have hCNext : (leadingStage (limitAngle 0) (TwoCycle.evenState (cycleK ν))).2.1 ≠ 0 := by
    rw [limitAngle_zero, TwoCycle.evenToOdd _ hK]
    exact hO.2.1.ne'
  let f : (ℝ × (ℝ × ℝ × ℝ)) → Fin 2 → ℝ := fun z i ↦ cycleSlope L κ i z.1 z.2
  have hf : AnalyticAt ℝ f (0, TwoCycle.evenState (cycleK ν)) := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact cycleSlope_joint_analyticAt L κ i _ hE.1.ne' hE.2.1.ne' hCNext
  obtain ⟨K, s, hs, hLip⟩ := hf.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hbase : (0, TwoCycle.evenState (cycleK ν)) ∈ s := mem_of_mem_nhds hs
  have hBOne : 0 < B + 1 := by linarith
  have hKOne : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨((K : ℝ) + 1) * (B + 1), mul_pos hKOne hBOne,
    ε / (B + 1), div_pos hε hBOne, ?_⟩
  intro t ht htδ x hx i
  have hdistBound : dist (t, x) (0, TwoCycle.evenState (cycleK ν)) ≤ (B + 1) * t := by
    rw [Prod.dist_eq]
    apply max_le
    · rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
      nlinarith [mul_nonneg hB ht]
    · rw [dist_eq_norm]
      have hBt : B * t ≤ (B + 1) * t := by nlinarith
      exact hx.trans hBt
  have hsmall : (B + 1) * t < ε := by
    nlinarith [(lt_div_iff₀ hBOne).mp htδ]
  have hin : (t, x) ∈ s := hball (Metric.mem_ball.mpr (hdistBound.trans_lt hsmall))
  have hfull := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hin hbase
  have hnormBound : ‖(t, x) - (0, TwoCycle.evenState (cycleK ν))‖ ≤ (B + 1) * t := by
    simpa only [dist_eq_norm] using hdistBound
  have htotal : ‖f (t, x) - f (0, TwoCycle.evenState (cycleK ν))‖ ≤
      (((K : ℝ) + 1) * (B + 1)) * t := by
    calc
      ‖f (t, x) - f (0, TwoCycle.evenState (cycleK ν))‖ ≤
          (K : ℝ) * ‖(t, x) - (0, TwoCycle.evenState (cycleK ν))‖ := hfull
      _ ≤ (K : ℝ) * ((B + 1) * t) := mul_le_mul_of_nonneg_left hnormBound K.coe_nonneg
      _ ≤ (((K : ℝ) + 1) * (B + 1)) * t := by
        nlinarith [mul_nonneg hBOne.le ht]
  have hcoordinate := (norm_le_pi_norm
    (f (t, x) - f (0, TwoCycle.evenState (cycleK ν))) i).trans htotal
  simpa only [f, Pi.sub_apply, cycleSlope_at_zero L κ ν hν, Real.norm_eq_abs] using hcoordinate

/-- Helper for eq:polar-W-expansion and eq:polar-slope-estimates: for the
actual two-stage inputs, a common linear state deviation gives both source
slope estimates and the fifth-order radius remainders with one constant. -/
theorem localSlopeAndRadiusBounds (L κ ν B : ℝ)
    (hν : ν ∈ TwoCycle.parameterSet) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      ‖x - TwoCycle.evenState (cycleK ν)‖ ≤ B * t →
        (∀ i : Fin 2, |cycleSlope L κ i t x - referenceSlope ν i| ≤ C * t) ∧
          ∀ i : Fin 2,
            |normalizedRadiusFactor i t (cycleInput L κ i t x) - 1 -
              radiusCoefficient ν i * t ^ 4| ≤ C * t ^ 5 := by
  obtain ⟨Cq, hCq, δq, hδq, hslope⟩ := cycleSlopeEstimateOfStateBound L κ ν B hν hB
  obtain ⟨C₀, hC₀, δ₀, hδ₀, hW₀⟩ := radiusEstimateOfSlopeBound 0 (referenceSlope ν 0) Cq hCq.le
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hW₁⟩ := radiusEstimateOfSlopeBound 1 (referenceSlope ν 1) Cq hCq.le
  have hC : 0 < Cq + C₀ + C₁ := by linarith
  refine ⟨Cq + C₀ + C₁, hC, min δq (min δ₀ δ₁), lt_min hδq (lt_min hδ₀ hδ₁), ?_⟩
  intro t ht htδ x hx
  have htq : t < δq := htδ.trans_le (min_le_left _ _)
  have ht₀ : t < δ₀ := (htδ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have ht₁ : t < δ₁ := (htδ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hq := hslope t ht htq x hx
  constructor
  · intro i
    have hCqLe : Cq ≤ Cq + C₀ + C₁ := by linarith
    exact (hq i).trans (mul_le_mul_of_nonneg_right hCqLe ht)
  · intro i
    have hq₀ : |slope (cycleInput L κ 0 t x) - referenceSlope ν 0| ≤ Cq * t := by
      simpa only [cycleSlope_def] using hq 0
    have hq₁ : |slope (cycleInput L κ 1 t x) - referenceSlope ν 1| ≤ Cq * t := by
      simpa only [cycleSlope_def] using hq 1
    have hbound₀ := hW₀ t ht ht₀ (cycleInput L κ 0 t x) hq₀
    have hbound₁ := hW₁ t ht ht₁ (cycleInput L κ 1 t x) hq₁
    have hC₀Le : C₀ ≤ Cq + C₀ + C₁ := by linarith
    have hC₁Le : C₁ ≤ Cq + C₀ + C₁ := by linarith
    have hresult₀ := hbound₀.trans (mul_le_mul_of_nonneg_right hC₀Le (pow_nonneg ht 5))
    have hresult₁ := hbound₁.trans (mul_le_mul_of_nonneg_right hC₁Le (pow_nonneg ht 5))
    fin_cases i
    · simpa only [radiusCoefficient_def, Fin.zero_eta, Fin.isValue] using hresult₀
    · simpa only [radiusCoefficient_def, Fin.mk_one, Fin.isValue] using hresult₁

/-- Helper for eq:polar-slope-estimates: the fixed fast norm controls the
ordinary displacement of a state from the source curve at its own amplitude. -/
theorem norm_state_sub_evenState_le (x : ℝ × ℝ × ℝ) :
    ‖x - TwoCycle.evenState x.1‖ ≤
      (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
        FastContraction.fixedNorm (FastContraction.fastError x) := by
  have hreconstruct : FastRemainder.perturbedState x.1 (FastContraction.fastError x) = x := by
    rw [FastRemainder.perturbedState_apply, FastContraction.fastError_def]
    simp only [FastContraction.fastCoordinates_apply, Pi.sub_apply, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp only
        ring
      · dsimp only
        ring
  have h := SlowCoupling.norm_perturbedState_sub_evenState_le x.1 (FastContraction.fastError x)
  rwa [hreconstruct] at h

/-- Helper for eq:polar-slope-estimates: the source slow and fast tube
deviations imply a common linear ordinary-state bound around the genuine
fixed even cycle, using the original inverse-parameter curve. -/
theorem stateBoundOfTube (ν M N : ℝ) (hν : ν ∈ TwoCycle.parameterSet)
    (hbranch : ContDiffAt ℝ ω TwoCycle.inverseParameter (cycleK ν))
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ B > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      |x.1 - cycleK ν| ≤ M * t →
        FastContraction.fixedNorm (FastContraction.fastError x) ≤ N * t ^ 3 →
          ‖x - TwoCycle.evenState (cycleK ν)‖ ≤ B * t := by
  have hK := TwoCycle.cycleK_bijOn_parameterSet.mapsTo hν
  have hcurve := TwoCycle.evenState_analyticAt (cycleK ν) hK hbranch
  obtain ⟨K, s, hs, hLip⟩ := hcurve.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hbase : cycleK ν ∈ s := mem_of_mem_nhds hs
  let P := ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hMOne : 0 < M + 1 := by linarith
  have hB : 0 < P * N + (K : ℝ) * M + 1 := by
    positivity
  refine ⟨P * N + (K : ℝ) * M + 1, hB,
    min 1 (ρ / (M + 1)), lt_min zero_lt_one (div_pos hρ hMOne), ?_⟩
  intro t ht htδ x hslow hfast
  have htOne : t ≤ 1 := (htδ.trans_le (min_le_left _ _)).le
  have htSquare : t ^ 2 ≤ 1 := pow_le_one₀ ht htOne
  have htCube : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr htSquare)]
  have hsmall : (M + 1) * t < ρ := by
    have htρ : t < ρ / (M + 1) := htδ.trans_le (min_le_right _ _)
    nlinarith [(lt_div_iff₀ hMOne).mp htρ]
  have hAin : x.1 ∈ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hMt : M * t ≤ (M + 1) * t := by nlinarith
    exact hslow.trans_lt (hMt.trans_lt hsmall)
  have hcurveBound := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hAin hbase
  have hslowNorm : ‖x.1 - cycleK ν‖ ≤ M * t := by
    simpa only [Real.norm_eq_abs] using hslow
  have hcurveLinear : ‖TwoCycle.evenState x.1 - TwoCycle.evenState (cycleK ν)‖ ≤
      ((K : ℝ) * M) * t := by
    calc
      ‖TwoCycle.evenState x.1 - TwoCycle.evenState (cycleK ν)‖ ≤
          (K : ℝ) * ‖x.1 - cycleK ν‖ := hcurveBound
      _ ≤ (K : ℝ) * (M * t) := mul_le_mul_of_nonneg_left hslowNorm K.coe_nonneg
      _ = ((K : ℝ) * M) * t := by ring
  have hfastLinear : ‖x - TwoCycle.evenState x.1‖ ≤ (P * N) * t := by
    calc
      ‖x - TwoCycle.evenState x.1‖ ≤
          P * FastContraction.fixedNorm (FastContraction.fastError x) :=
        norm_state_sub_evenState_le x
      _ ≤ P * (N * t ^ 3) := mul_le_mul_of_nonneg_left hfast hP.le
      _ ≤ P * (N * t) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htCube hN) hP.le
      _ = (P * N) * t := by ring
  calc
    ‖x - TwoCycle.evenState (cycleK ν)‖ =
        ‖(x - TwoCycle.evenState x.1) +
          (TwoCycle.evenState x.1 - TwoCycle.evenState (cycleK ν))‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖x - TwoCycle.evenState x.1‖ +
        ‖TwoCycle.evenState x.1 - TwoCycle.evenState (cycleK ν)‖ := norm_add_le _ _
    _ ≤ (P * N) * t + ((K : ℝ) * M) * t := add_le_add hfastLinear hcurveLinear
    _ ≤ (P * N + (K : ℝ) * M + 1) * t := by nlinarith

/-- Helper for eq:polar-W-expansion and eq:polar-slope-estimates: the source
slow `O(t)` and fast `O(t³)` tube deviations give the actual two-stage slope
and radius estimates, without assuming either desired expansion. -/
theorem localSlopeAndRadiusBoundsOfTube (L κ ν M N : ℝ)
    (hν : ν ∈ TwoCycle.parameterSet)
    (hbranch : ContDiffAt ℝ ω TwoCycle.inverseParameter (cycleK ν))
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ x : ℝ × ℝ × ℝ,
      |x.1 - cycleK ν| ≤ M * t →
        FastContraction.fixedNorm (FastContraction.fastError x) ≤ N * t ^ 3 →
          (∀ i : Fin 2, |cycleSlope L κ i t x - referenceSlope ν i| ≤ C * t) ∧
            ∀ i : Fin 2,
              |normalizedRadiusFactor i t (cycleInput L κ i t x) - 1 -
                radiusCoefficient ν i * t ^ 4| ≤ C * t ^ 5 := by
  obtain ⟨B, hB, δb, hδb, hstate⟩ := stateBoundOfTube ν M N hν hbranch hM hN
  obtain ⟨C, hC, δc, hδc, hlocal⟩ := localSlopeAndRadiusBounds L κ ν B hν hB.le
  refine ⟨C, hC, min δb δc, lt_min hδb hδc, ?_⟩
  intro t ht htδ x hslow hfast
  have hstateBound := hstate t ht (htδ.trans_le (min_le_left _ _)) x hslow hfast
  exact hlocal t ht (htδ.trans_le (min_le_right _ _)) x hstateBound

/-- Helper for eq:polar-slope-estimates: the exact prescribed even physical
slope is the squared scale times the actual normalized even slope. -/
theorem omega_even_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    p.omega (2 * j) = p.scale j ^ 2 *
      cycleSlope p.feedbackRate p.kStar 0 (p.scale j) (p.normalizedEvenState j) := by
  rw [Parameters.omega_def, Parameters.matrix_even, cycleSlope_def, cycleInput_zero,
    normalizedEvenState_eq_coordinates]
  exact (scale_sq_mul_slope_coordinates (p.scale j) (p.evenMatrix j)
    (ScaleTails.scale_pos p hstart j)).symm

/-- Helper for eq:polar-slope-estimates: the exact prescribed odd physical
slope is the squared scale times the slope of the computed normalized odd input. -/
theorem omega_odd_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    p.omega (2 * j + 1) = p.scale j ^ 2 *
      cycleSlope p.feedbackRate p.kStar 1 (p.scale j) (p.normalizedEvenState j) := by
  rw [Parameters.omega_def, Parameters.matrix_odd, cycleSlope_def,
    cycleInput_one_evenMatrix p j hstart]
  exact (scale_sq_mul_slope_coordinates (p.scale j) (p.oddMatrix j)
    (ScaleTails.scale_pos p hstart j)).symm

/-- Helper for eq:polar-slope-estimates: both actual physical phase slopes
are exactly the normalized cycle slopes times the original squared scale. -/
theorem omega_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) (i : Fin 2) :
    p.omega (2 * j + (i : ℕ)) = p.scale j ^ 2 *
      cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.add_zero] using
      omega_even_prescribed p j hstart
  · simpa only [Fin.mk_one, Fin.isValue, Fin.val_one] using omega_odd_prescribed p j hstart

/-- Helper for eq:polar-W-expansion: the normalized radius factor at the
actual phase input is exactly the prescribed physical radius-factor sequence. -/
theorem radiusFactor_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) (i : Fin 2) :
    normalizedRadiusFactor i (p.scale j)
        (cycleInput p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j)) =
      p.radiusRatio (2 * j + (i : ℕ)) := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.add_zero] using
      cycleRadius_even_prescribed p j hstart
  · simpa only [Fin.mk_one, Fin.isValue, Fin.val_one] using
      cycleRadius_odd_prescribed p j hstart

/-- Helper for eq:polar-slope-estimates: the exact physical normalization
transports a proved normalized slope error to a cubic physical slope error. -/
theorem omegaErrorOfCycleSlopeBound (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex)
    (i : Fin 2) (Q C : ℝ)
    (hq : |cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) - Q| ≤
      C * p.scale j) :
    |p.omega (2 * j + (i : ℕ)) - Q * p.scale j ^ 2| ≤ C * p.scale j ^ 3 := by
  rw [omega_prescribed p j hstart i]
  have hidentity : p.scale j ^ 2 *
      cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) -
        Q * p.scale j ^ 2 = p.scale j ^ 2 *
          (cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) - Q) := by
    ring
  rw [hidentity, abs_mul, abs_of_nonneg (sq_nonneg (p.scale j))]
  calc
    p.scale j ^ 2 *
        |cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) - Q| ≤
      p.scale j ^ 2 * (C * p.scale j) := mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    _ = C * p.scale j ^ 3 := by ring

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the actual
prescribed recurrence satisfies both phase expansions with one error constant
and one natural starting-index threshold, uniformly in every later `j₀`. -/
theorem actualSlopeAndRadiusEstimates :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ j : ℕ, ∀ i : Fin 2,
          let p := Parameters.of j₀ νStar
          |cycleSlope p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j) -
              referenceSlope νStar i| ≤ C * p.scale j ∧
            |p.omega (2 * j + (i : ℕ)) - referenceSlope νStar i * p.scale j ^ 2| ≤
              C * p.scale j ^ 3 ∧
              |p.radiusRatio (2 * j + (i : ℕ)) - 1 - radiusCoefficient νStar i * p.scale j ^ 4| ≤
                C * p.scale j ^ 5 := by
  obtain ⟨η, hη, hTube⟩ := Continuation.actualTube
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, hbranch, N, hN, M, hM, J₀, hJ₀, htube⟩ := hTube νStar hnear
  obtain ⟨C, hC, δ, hδ, hlocal⟩ := localSlopeAndRadiusBoundsOfTube
    (4 * baseAngle / (9 * νStar)) (cycleK νStar) νStar M N hparameter hbranch hM.le hN.le
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold δ hδ
  refine ⟨hparameter, C, hC, max J₀ J₁, lt_of_lt_of_le hJ₀ (le_max_left _ _), ?_⟩
  intro j₀ hj₀ j i
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using
      lt_of_lt_of_le hJ₀ ((le_max_left J₀ J₁).trans hj₀)
  have ht : 0 < p.scale j := ScaleTails.scale_pos p hstart j
  have hzeroScale : p.scale 0 < δ :=
    hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀)
  have hsmall : p.scale j < δ :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le j)).trans_lt hzeroScale
  have hactualTube := htube j₀ ((le_max_left J₀ J₁).trans hj₀) j
  have hfeedback : p.feedbackRate = 4 * baseAngle / (9 * νStar) := by
    simp only [p, Parameters.feedbackRate_def, Parameters.of_cycleParameter]
  have hkStar : p.kStar = cycleK νStar := by
    simp only [p, Parameters.kStar_def, Parameters.of_cycleParameter]
  have hslow : |(p.normalizedEvenState j).1 - cycleK νStar| ≤ M * p.scale j := by
    have h : |(p.normalizedEvenState j).1 - p.kStar| ≤ M * p.scale j := hactualTube.1
    rwa [hkStar] at h
  have hfast : FastContraction.fixedNorm (FastContraction.fastError (p.normalizedEvenState j)) ≤
      N * p.scale j ^ 3 := hactualTube.2.1
  have hresult := hlocal (p.scale j) ht.le hsmall (p.normalizedEvenState j) hslow hfast
  rw [← hfeedback, ← hkStar] at hresult
  have homega := omegaErrorOfCycleSlopeBound p j hstart i (referenceSlope νStar i) C (hresult.1 i)
  have hradius := hresult.2 i
  rw [radiusFactor_prescribed p j hstart i] at hradius
  exact ⟨hresult.1 i, homega, hradius⟩

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the
canonical even or odd phase of an actual iteration index. -/
def phaseIndex (k : ℕ) : Fin 2 := Fin.ofNat 2 k

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the finite
phase uses the standard reduction modulo two. -/
theorem phaseIndex_def (k : ℕ) : phaseIndex k = Fin.ofNat 2 k := by
  rfl

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the value
of the finite phase is the source parity `k % 2`. -/
theorem phaseIndex_val (k : ℕ) : (phaseIndex k : ℕ) = k % 2 := by
  rw [phaseIndex_def, Fin.ofNat_eq_cast]
  exact Fin.val_natCast k 2

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the
canonical finite phase satisfies the source cycle-index identity. -/
theorem phaseIndex_identity (k : ℕ) : 2 * (k / 2) + (phaseIndex k : ℕ) = k := by
  rw [phaseIndex_val]
  omega

/-- eq:polar-slope-estimates and eq:polar-W-expansion: the original actual
physical slope and radius-factor sequences have the source expansions at
every iteration, uniformly for all subsequently larger natural starting indices. -/
theorem polarRadiusExpansions :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ k : ℕ,
          let p := Parameters.of j₀ νStar
          |p.omega k - referenceSlope νStar (phaseIndex k) * p.scale (k / 2) ^ 2| ≤
              C * p.scale (k / 2) ^ 3 ∧
            |p.radiusRatio k - 1 - radiusCoefficient νStar (phaseIndex k) * p.scale (k / 2) ^ 4| ≤
              C * p.scale (k / 2) ^ 5 := by
  obtain ⟨η, hη, hbound⟩ := actualSlopeAndRadiusEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J, hJ, hactual⟩ := hbound νStar hnear
  refine ⟨hparameter, C, hC, J, hJ, ?_⟩
  intro j₀ hj₀ k
  have h := hactual j₀ hj₀ (k / 2) (phaseIndex k)
  rw [phaseIndex_identity] at h
  exact h.2

/-- Helper for eq:polar-W-expansion: a proved fifth-order remainder with
positive source coefficient gives quantitative fourth-order growth and `W>1`. -/
theorem radiusGrowthOfErrorBound (W D C t : ℝ) (hD : 0 < D)
    (ht : 0 < t) (hsmall : C * t ≤ D / 2)
    (herror : |W - 1 - D * t ^ 4| ≤ C * t ^ 5) :
    (D / 2) * t ^ 4 ≤ W - 1 ∧ W - 1 ≤ (3 * D / 2) * t ^ 4 ∧ 1 < W := by
  have hpower : C * t ^ 5 ≤ (D / 2) * t ^ 4 := by
    calc
      C * t ^ 5 = (C * t) * t ^ 4 := by ring
      _ ≤ (D / 2) * t ^ 4 := mul_le_mul_of_nonneg_right hsmall (pow_nonneg ht.le 4)
  have hbounds := abs_le.mp herror
  have hlower : (D / 2) * t ^ 4 ≤ W - 1 := by nlinarith
  have hupper : W - 1 ≤ (3 * D / 2) * t ^ 4 := by nlinarith
  have hpositive : 0 < (D / 2) * t ^ 4 := mul_pos (half_pos hD) (pow_pos ht 4)
  have hW : 1 < W := by linarith
  exact ⟨hlower, hupper, hW⟩

/-- Helper for eq:polar-W-expansion: after one common increase of the
natural starting-index threshold, every actual source radius factor exceeds
one and its defect has the source positive fourth-order size. -/
theorem polarRadiusGrowth :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ k : ℕ,
          let p := Parameters.of j₀ νStar
          (radiusCoefficient νStar (phaseIndex k) / 2) * p.scale (k / 2) ^ 4 ≤
              p.radiusRatio k - 1 ∧
            p.radiusRatio k - 1 ≤ (3 * radiusCoefficient νStar (phaseIndex k) / 2) *
                p.scale (k / 2) ^ 4 ∧
              1 < p.radiusRatio k := by
  obtain ⟨η, hη, hbound⟩ := polarRadiusExpansions
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J₀, hJ₀, hactual⟩ := hbound νStar hnear
  have hD := radiusCoefficients_pos νStar hparameter
  let d := min (radiusCoefficient νStar 0) (radiusCoefficient νStar 1)
  have hd : 0 < d := lt_min hD.1 hD.2
  have hdle : ∀ i : Fin 2, d ≤ radiusCoefficient νStar i := by
    intro i
    fin_cases i
    · simpa only [d, Fin.zero_eta, Fin.isValue] using
        min_le_left (radiusCoefficient νStar 0) (radiusCoefficient νStar 1)
    · simpa only [d, Fin.mk_one, Fin.isValue] using
        min_le_right (radiusCoefficient νStar 0) (radiusCoefficient νStar 1)
  have hcutoff : 0 < d / (2 * C) := div_pos hd (mul_pos zero_lt_two hC)
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold (d / (2 * C)) hcutoff
  refine ⟨hparameter, max J₀ J₁, lt_of_lt_of_le hJ₀ (le_max_left _ _), ?_⟩
  intro j₀ hj₀ k
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using
      lt_of_lt_of_le hJ₀ ((le_max_left J₀ J₁).trans hj₀)
  have ht : 0 < p.scale (k / 2) := ScaleTails.scale_pos p hstart _
  have hzeroScale : p.scale 0 < d / (2 * C) :=
    hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀)
  have hsmall : p.scale (k / 2) < d / (2 * C) :=
    (ScaleTails.scale_antitone p hstart (Nat.zero_le (k / 2))).trans_lt hzeroScale
  have htwoC : 0 < 2 * C := mul_pos zero_lt_two hC
  have hCt : C * p.scale (k / 2) ≤ radiusCoefficient νStar (phaseIndex k) / 2 := by
    nlinarith [(lt_div_iff₀ htwoC).mp hsmall, hdle (phaseIndex k)]
  have herror := (hactual j₀ ((le_max_left J₀ J₁).trans hj₀) k).2
  exact radiusGrowthOfErrorBound (p.radiusRatio k) (radiusCoefficient νStar (phaseIndex k)) C
    (p.scale (k / 2)) (radiusCoefficient_pos νStar hparameter (phaseIndex k)) ht hCt herror

end DFP.Polar.RadiusExpansions
