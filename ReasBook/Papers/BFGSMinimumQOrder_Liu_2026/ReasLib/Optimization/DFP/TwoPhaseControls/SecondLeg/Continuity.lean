module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Continuity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.SecondLeg

/-- Helper for Infrastructure I.16a: the first spectral factors at the canceled base point. -/
private lemma firstSpectralFactors_base :
    DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg Prod.fst DFP.FirstLeg.factorsBase

/-- Helper for Infrastructure I.16a: the first gradient factors at the canceled base point. -/
private lemma firstGradientFactors_base :
    DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase

/-- Helper for Infrastructure I.16a: continuity of the first spectral factor map at the base. -/
private lemma firstSpectralFactors_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) :=
  (analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic).continuousAt

/-- Helper for Infrastructure I.16a: continuity of the first gradient factor map at the base. -/
private lemma firstGradientFactors_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) :=
  ((analyticAt_fst.comp analyticAt_snd).comp
    DFP.FirstLeg.factorsAnalytic).continuousAt

/-- Every entry of the canceled second-leg output metric is continuous at the
common zero-scale base point. -/
theorem outputMetricEntry_continuousAt (i j : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ outputMetric x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have hspectral := firstSpectralFactors_continuousAt
  have hgradient := firstGradientFactors_continuousAt
  fin_cases i
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base,
        firstGradientFactors_base])
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base,
        firstGradientFactors_base])
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base,
        firstGradientFactors_base])
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num [firstSpectralFactors_base,
        firstGradientFactors_base])

/-- Every coordinate of the canceled second-leg output gradient is continuous at
the common zero-scale base point. -/
theorem outputGradientEntry_continuousAt (i : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ outputGradient x.1 x.2.1 x.2.2 i) (0, 2, 1) := by
  have hspectral := firstSpectralFactors_continuousAt
  have hgradient := firstGradientFactors_continuousAt
  fin_cases i
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num [firstSpectralFactors_base,
      firstGradientFactors_base])
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num [firstSpectralFactors_base,
      firstGradientFactors_base])

/-- Helper for Infrastructure I.16a: the three metric entries used by the low frame. -/
private def metricEntries (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (outputMetric x.1 x.2.1 x.2.2 0 0,
    outputMetric x.1 x.2.1 x.2.2 0 1,
    outputMetric x.1 x.2.1 x.2.2 1 1)

/-- Helper for Infrastructure I.16a: continuity of the assembled metric entries. -/
private lemma metricEntries_continuousAt :
    ContinuousAt metricEntries (0, 2, 1) := by
  exact (outputMetricEntry_continuousAt 0 0).prodMk
    ((outputMetricEntry_continuousAt 0 1).prodMk
      (outputMetricEntry_continuousAt 1 1))

/-- Helper for Infrastructure I.16a: the assembled metric entries at the canceled base. -/
private lemma metricEntries_base :
    metricEntries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  norm_num [metricEntries, outputMetric, firstSpectralFactors_base,
    firstGradientFactors_base]

/-- Every entry of the canonical second-leg eigenframe is continuous at the
common zero-scale base point. -/
theorem frameEntry_continuousAt (i j : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ frame x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have houter := (RealSymmetric2.analyticOnNhd_frame i j
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart).continuousAt
  rw [← metricEntries_base] at houter
  have hcomp := houter.comp metricEntries_continuousAt
  apply hcomp.congr
  filter_upwards [] with x
  rfl

/-- The complete pair of second-leg gradient coordinates in the canonical frame
is continuous at the common zero-scale base point. -/
theorem coordinates_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ coordinates x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  rw [htop]
  have hzero := ((frameEntry_continuousAt 0 0).mul
      (outputGradientEntry_continuousAt 0)).add
      ((frameEntry_continuousAt 1 0).mul (outputGradientEntry_continuousAt 1))
  have hone := ((frameEntry_continuousAt 0 1).mul
      (outputGradientEntry_continuousAt 0)).add
      ((frameEntry_continuousAt 1 1).mul (outputGradientEntry_continuousAt 1))
  have hp : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (frame x.1 x.2.1 x.2.2 0 0 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 0 * outputGradient x.1 x.2.1 x.2.2 1,
        frame x.1 x.2.1 x.2.2 0 1 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 1 * outputGradient x.1 x.2.1 x.2.2 1))
      (0, 2, 1) := hzero.prodMk hone
  apply hp.congr
  filter_upwards [] with x
  simp only [coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.transpose_apply]

end DFP.SecondLeg
