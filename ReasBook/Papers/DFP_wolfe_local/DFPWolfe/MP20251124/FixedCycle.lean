/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.Polar.General.Estimates
public import ReasLib.Optimization.DFP.Polar.General.FastContraction
public import ReasLib.Analysis.Analytic.Sqrt
import all ReasLib.Optimization.DFP.Polar.General.CycleFamily

public section
noncomputable section

namespace DFPWolfe.MP20251124.FixedCycle

open DFP.Polar.General

/-- Helper for `lem:fixed-cycle`: separation between the two roots of the fixed reference cycle. -/
def separation (γ : ℝ) : ℝ := Real.sqrt (1 - 2 / γ)

/-- Helper for `lem:fixed-cycle`: the prescribed gain at the start of each two-step cycle. -/
def gain (γ : ℝ) : ℝ := 3 / (4 * γ * separation γ)

/-- Helper for `eq:fixed-feedback`: the gain used by both the raw recurrence and its linearization. -/
theorem gain_formula (γ : ℝ) : gain γ = 3 / (4 * γ * Real.sqrt (1 - 2 / γ)) := by
  rfl

/-- Helper for `lem:fixed-cycle`: the positive distinct roots give a regular cycle for both unit angles. -/
theorem referenceDomain {γ : ℝ} (hγ : 2 < γ) : CycleDomain 1 1 (separation γ) := by
  have hpos : 0 < γ := lt_trans zero_lt_two hγ
  have hquot : 2 / γ < 1 := (div_lt_one hpos).2 hγ
  have hsep : 0 < separation γ := Real.sqrt_pos.2 (sub_pos.2 hquot)
  have hsq : separation γ ^ 2 = 1 - 2 / γ := Real.sq_sqrt (sub_nonneg.2 hquot.le)
  have hdiv : 0 < 2 / γ := div_pos zero_lt_two hpos
  constructor <;> nlinarith

/-- Helper for `lem:fixed-cycle`: the rational reference family recovers the manuscript's
prescribed diagonal and its two explicit coefficients at every γ > 2. -/
theorem referenceCoefficients {γ : ℝ} (hγ : 2 < γ) :
    cycleGamma 1 1 (separation γ) = γ ∧
    cycleLambdaEven 1 1 (separation γ) = (1 + separation γ) / 2 ∧
    cycleLambdaOdd 1 1 (separation γ) = (1 - separation γ) / 2 := by
  have hd := referenceDomain hγ
  have hpos : 0 < γ := lt_trans zero_lt_two hγ
  have hquot := (div_lt_one hpos).2 hγ
  have hsq : separation γ ^ 2 = 1 - 2 / γ := Real.sq_sqrt (sub_nonneg.2 hquot.le)
  field_simp [hpos.ne'] at hsq
  refine ⟨?_, ?_, ?_⟩
  · unfold cycleGamma
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero hd.nu_pos.ne' hd.even_gap_pos.ne')
      hd.odd_gap_pos.ne')).2
    linear_combination (separation γ) * hsq
  · unfold cycleLambdaEven
    field_simp [hd.nu_pos.ne']
    ring
  · unfold cycleLambdaOdd
    field_simp [hd.nu_pos.ne']
    ring

/-- Helper for `lem:fixed-cycle`: at γ = 9/4 the cycle starts at the given even matrix,
passes through the given odd matrix, and has unit feedback. -/
theorem initialReferences :
    evenState 1 1 (separation (9/4)) = (9/4, 3/2, 2) ∧
    oddState 1 1 (separation (9/4)) = (9/4, 3/4, 5/4) ∧ gain (9/4) = 1 := by
  have hsep : separation (9/4) = 1/3 := by
    have hs : separation (9 / 4) ^ 2 = 1 - 2 / (9 / 4 : ℝ) := by
      apply Real.sq_sqrt
      norm_num
    have hg : (2 : ℝ) < 9/4 := by norm_num
    nlinarith [(referenceDomain hg).nu_pos]
  norm_num [gain, hsep, evenState, oddState, cycleState, cycleGamma,
    cycleLambdaEven, cycleLambdaOdd]

/-- Helper for `lem:fixed-cycle`: the two equal-angle limiting stages exchange the
reference states for every γ > 2. -/
theorem referenceStages {γ : ℝ} (hγ : 2 < γ) :
    Normalized.leadingStage 1 (evenState 1 1 (separation γ)) = oddState 1 1 (separation γ) ∧
    Normalized.leadingStage 1 (oddState 1 1 (separation γ)) = evenState 1 1 (separation γ) := by
  have hd := referenceDomain hγ
  simpa only [Parameters.leadingStage_eq_original] using And.intro (evenToOdd hd) (oddToEven hd)

/-- Helper for `lem:fixed-cycle`: the actual two-step map with the fixed feedback has the
paper's restoring derivative in inverse index along the entire reference family. -/
theorem restoringDerivative {γ : ℝ} (hγ : 2 < γ) :
    HasDerivAt (fun t ↦ (Normalized.map (1/2) (fun _ ↦ 1) (fun _ ↦ 1) gain
      0 t (evenState 1 1 (separation γ))).1) (-(4/3) * (γ - 9/4)) 0 := by
  have hd := referenceDomain hγ
  have hdiag := (referenceCoefficients hγ).1
  have hpos : 0 < γ := lt_trans zero_lt_two hγ
  have h := Estimates.hasDerivAt_map_evenState_first (1/2) (fun _ ↦ 1) (fun _ ↦ 1)
    gain (separation γ) analyticAt_const analyticAt_const one_ne_zero one_ne_zero hd
  apply h.congr_deriv
  rw [hdiag, gain]
  field_simp [hpos.ne', hd.nu_pos.ne']
  ring

/-- Helper for `lem:fixed-cycle`: the fixed feedback is analytic throughout the open cycle branch. -/
theorem gain_analyticAt {γ : ℝ} (hγ : 2 < γ) : AnalyticAt ℝ gain γ := by
  have hpos : 0 < γ := lt_trans zero_lt_two hγ
  have hinside : 0 < 1 - 2 / γ := sub_pos.2 ((div_lt_one hpos).2 hγ)
  have hinner : AnalyticAt ℝ (fun x : ℝ ↦ 1 - 2 / x) γ :=
    analyticAt_const.sub (analyticAt_const.div analyticAt_id hpos.ne')
  have hsep : AnalyticAt ℝ separation γ := hinner.sqrt hinside.ne'
  have hfour : (4 : ℝ) ≠ 0 := by norm_num
  have hden := mul_ne_zero (mul_ne_zero hfour hpos.ne') (referenceDomain hγ).nu_pos.ne'
  exact analyticAt_const.div ((analyticAt_const.mul analyticAt_id).mul hsep) hden

/-- Helper for `lem:fixed-cycle`: joint analyticity in signed angular scale, inverse index,
and matrix entries at the manuscript's initial even state. -/
theorem map_analyticAt :
    AnalyticAt ℝ (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
      Normalized.map (1/2) (fun _ ↦ 1) (fun _ ↦ 1) gain z.1.1 z.1.2 z.2)
      ((0, 0), (9/4, 3/2, 2)) := by
  apply Normalized.map_analyticAt
  · exact analyticAt_const
  · exact analyticAt_const
  · apply gain_analyticAt
    norm_num
  · exact one_ne_zero
  · exact one_ne_zero
  · norm_num
  · norm_num [Normalized.leadingStage_apply]

/-- Helper for `lem:fixed-cycle`: the transverse Jacobian of the fixed limiting return map. -/
def jacobian : Matrix (Fin 2) (Fin 2) ℝ := !![6, -9/2; 8, -6]

/-- Helper for `lem:fixed-cycle`: differentiation of both stages gives the specified
matrix in the even transverse coordinates. -/
theorem transverseDerivative :
    HasFDerivAt (FastContraction.leadingCycle 1 1 (9/4))
      (DFP.Polar.FastContraction.matrixOperator jacobian) ![3/2, 2] := by
  have hc : (![3/2, 2] : Fin 2 → ℝ) 0 ≠ 0 := by norm_num
  have ho : DFP.Polar.FastContraction.leadingFast 1 (9/4) ![3/2, 2] 0 ≠ 0 := by
    norm_num [DFP.Polar.FastContraction.leadingFast_apply]
  have heq : FastContraction.cycleDerivative 1 1 (9/4) ![3/2, 2] = jacobian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [FastContraction.cycleDerivative_apply, jacobian, Matrix.mul_apply, Fin.sum_univ_two,
        DFP.Polar.FastContraction.stageDerivative_def, DFP.Polar.FastContraction.leadingFast_apply]
  rw [← heq]
  exact FastContraction.hasFDerivAt_leadingCycle 1 1 (9/4) _ hc ho

/-- Helper for `lem:fixed-cycle`: the product of the two stage Jacobians squares to zero. -/
theorem jacobian_sq_zero : jacobian * jacobian = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [jacobian, Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for `lem:fixed-cycle`: the reference derivative strictly contracts in the
Lyapunov norm defined by the paper's Gram matrix. -/
theorem referenceContraction :
    ∃ k ∈ Set.Ioo (0 : ℝ) 1, ∀ x : EuclideanSpace ℝ (Fin 2),
      FastContraction.lyapunovNorm jacobian 0 (FastContraction.euclideanOperator jacobian x) ≤
        k * FastContraction.lyapunovNorm jacobian 0 x := by
  have hκ : |(0 : ℝ)| < 1 := by norm_num
  have hJ : jacobian * jacobian = (0 : ℝ) • jacobian := by
    rw [jacobian_sq_zero, zero_smul]
  exact ⟨_, FastContraction.contractionFactor_bounds jacobian hκ,
    FastContraction.lyapunovNorm_contraction hJ hκ⟩

end DFPWolfe.MP20251124.FixedCycle
