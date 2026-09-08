module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.FirstLeg

/-- Every entry of the canceled first-leg output metric is continuous at the
common zero-scale base point. -/
theorem outputMetricEntry_continuousAt (i j : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ outputMetric x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  fin_cases i
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- Every coordinate of the canceled first-leg output gradient is continuous at
the common zero-scale base point. -/
theorem outputGradientEntry_continuousAt (i : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ outputGradient x.1 x.2.1 x.2.2 i) (0, 2, 1) := by
  fin_cases i
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- Every entry of the canonical first-leg eigenframe is continuous at the
common zero-scale base point. -/
theorem frameEntry_continuousAt (i j : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ frame x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  unfold frame outputMetric
  unfold RealSymmetric2.lowVector RealSymmetric2.lowRaw RealSymmetric2.lowDenom
  unfold RealSymmetric2.low RealSymmetric2.gap EuclideanPlane.frame
  dsimp
  fin_cases i
  · fin_cases j
    · fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
  · fin_cases j
    · fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The complete pair of first-leg gradient coordinates in the canonical frame
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

end DFP.FirstLeg
