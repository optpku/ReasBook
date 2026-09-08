module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

/-!
# Analyticity of the second-leg output coordinates

This file exposes the local real-analyticity interfaces needed to compose the canceled second-leg
formulas with parameter paths.  The distinguished point is `(ε, p, h) = (0, 2, 1)`.
-/

public section

noncomputable section

open Filter
open scoped Matrix Topology Nat ContDiff

namespace DFP.SecondLeg

/-- Helper for Infrastructure I.16a: the first spectral factors at the analytic base point. -/
private lemma firstSpectralFactors_base_analyticity :
    DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg Prod.fst DFP.FirstLeg.factorsBase

/-- Helper for Infrastructure I.16a: the first gradient factors at the analytic base point. -/
private lemma firstGradientFactors_base_analyticity :
    DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase

/-- Helper for Infrastructure I.16a: analyticity of the first spectral factor map. -/
private lemma firstSpectralFactors_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) :=
  analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic

/-- Helper for Infrastructure I.16a: analyticity of the first gradient factor map. -/
private lemma firstGradientFactors_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) :=
  (analyticAt_fst.comp analyticAt_snd).comp DFP.FirstLeg.factorsAnalytic

/-- Helper for Infrastructure I.16a: analyticity of the first low spectral coordinate. -/
private lemma firstLowSpectralFactor_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1)
    (0, 2, 1) :=
  analyticAt_fst.comp firstSpectralFactors_analyticAt

/-- Helper for Infrastructure I.16a: analyticity of the first high spectral coordinate. -/
private lemma firstHighSpectralFactor_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2)
    (0, 2, 1) :=
  analyticAt_snd.comp firstSpectralFactors_analyticAt

/-- Helper for Infrastructure I.16a: analyticity of the first low gradient coordinate. -/
private lemma firstLowGradientFactor_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1)
    (0, 2, 1) :=
  analyticAt_fst.comp firstGradientFactors_analyticAt

/-- Helper for Infrastructure I.16a: analyticity of the first high gradient coordinate. -/
private lemma firstHighGradientFactor_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2)
    (0, 2, 1) :=
  analyticAt_snd.comp firstGradientFactors_analyticAt

/-- Every entry of the canceled second-leg output metric is real analytic at the common base
point. -/
theorem outputMetricEntry_analyticAt (i j : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ outputMetric x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hL := firstLowSpectralFactor_analyticAt
  have hH := firstHighSpectralFactor_analyticAt
  have hQ := firstLowGradientFactor_analyticAt
  have hU := firstHighGradientFactor_analyticAt
  fin_cases i
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
        firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
        firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
        firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
        firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]

/-- Every coordinate of the canceled second-leg output gradient is real analytic at the common
base point. -/
theorem outputGradientEntry_analyticAt (i : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ outputGradient x.1 x.2.1 x.2.2 i) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hL := firstLowSpectralFactor_analyticAt
  have hH := firstHighSpectralFactor_analyticAt
  have hQ := firstLowGradientFactor_analyticAt
  have hU := firstHighGradientFactor_analyticAt
  fin_cases i
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
      firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num [firstSpectralFactors_base_analyticity,
      firstGradientFactors_base_analyticity]) [Prod.fst, Prod.snd]

/-- Helper for Infrastructure I.16a: the three metric entries used in analytic frame assembly. -/
private def metricEntriesForAnalyticity (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (outputMetric x.1 x.2.1 x.2.2 0 0,
    outputMetric x.1 x.2.1 x.2.2 0 1,
    outputMetric x.1 x.2.1 x.2.2 1 1)

/-- Helper for Infrastructure I.16a: analyticity of the assembled metric entries. -/
private lemma metricEntriesForAnalyticity_analyticAt :
    AnalyticAt ℝ metricEntriesForAnalyticity (0, 2, 1) := by
  exact (outputMetricEntry_analyticAt 0 0).prod
    ((outputMetricEntry_analyticAt 0 1).prod
      (outputMetricEntry_analyticAt 1 1))

/-- Helper for Infrastructure I.16a: the assembled metric entries at the analytic base. -/
private lemma metricEntriesForAnalyticity_base :
    metricEntriesForAnalyticity (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  norm_num [metricEntriesForAnalyticity, outputMetric,
    firstSpectralFactors_base_analyticity, firstGradientFactors_base_analyticity]

/-- Every entry of the canonical second-leg eigenframe is real analytic at the common base
point. -/
theorem frameEntry_analyticAt (i j : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ frame x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_frame i j
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntriesForAnalyticity_base] at houter
  have hcomp := houter.comp metricEntriesForAnalyticity_analyticAt
  apply hcomp.congr
  filter_upwards [] with x
  rfl

/-- The complete pair of second-leg gradient coordinates in the canonical frame is real analytic
at the common base point. -/
@[fun_prop]
theorem coordinates_analyticAt : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ coordinates x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hzero := ((frameEntry_analyticAt 0 0).mul
      (outputGradientEntry_analyticAt 0)).add
      ((frameEntry_analyticAt 1 0).mul (outputGradientEntry_analyticAt 1))
  have hone := ((frameEntry_analyticAt 0 1).mul
      (outputGradientEntry_analyticAt 0)).add
      ((frameEntry_analyticAt 1 1).mul (outputGradientEntry_analyticAt 1))
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦
      (frame x.1 x.2.1 x.2.2 0 0 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 0 * outputGradient x.1 x.2.1 x.2.2 1,
        frame x.1 x.2.1 x.2.2 0 1 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 1 * outputGradient x.1 x.2.1 x.2.2 1))
      (0, 2, 1) := hzero.prod hone
  apply hp.congr
  filter_upwards [] with x
  simp only [coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.transpose_apply]

/-- The second-leg coordinate pair is `C^k` at the common base point for every order `k`. -/
@[fun_prop]
theorem coordinates_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ coordinates x.1 x.2.1 x.2.2) (0, 2, 1) :=
  coordinates_analyticAt.contDiffAt

end DFP.SecondLeg
