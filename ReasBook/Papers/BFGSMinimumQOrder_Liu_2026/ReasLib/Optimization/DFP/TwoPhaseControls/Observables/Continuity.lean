module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Continuity
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Continuity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
public import ReasLib.Geometry.Euclidean.Angle.AbsToReal

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg

private def initialGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(1 : ℝ), x.2.1 * x.1 ^ 2]

private def intermediateGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)

private def finalGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
    DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)

private lemma initialGradientPath_continuousAt :
    ContinuousAt initialGradientPath (0, 2, 1) := by
  unfold initialGradientPath
  fun_prop

private lemma intermediateGradientPath_continuousAt :
    ContinuousAt intermediateGradientPath (0, 2, 1) := by
  have hpi : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)
      (0, 2, 1) := continuousAt_pi' DFP.FirstLeg.outputGradientEntry_continuousAt
  have hcomp := (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.comp hpi
  change ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ WithLp.toLp 2
      (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)) (0, 2, 1)
  simpa only [Function.comp_def] using hcomp

private lemma finalGradientPath_continuousAt :
    ContinuousAt finalGradientPath (0, 2, 1) := by
  have hpi : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) (0, 2, 1) := by
    apply continuousAt_pi'
    intro i
    fin_cases i
    · have hscalar := ((DFP.FirstLeg.frameEntry_continuousAt 0 0).mul
        (DFP.SecondLeg.outputGradientEntry_continuousAt 0)).add
        ((DFP.FirstLeg.frameEntry_continuousAt 0 1).mul
          (DFP.SecondLeg.outputGradientEntry_continuousAt 1))
      apply hscalar.congr
      filter_upwards [] with x
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · have hscalar := ((DFP.FirstLeg.frameEntry_continuousAt 1 0).mul
        (DFP.SecondLeg.outputGradientEntry_continuousAt 0)).add
        ((DFP.FirstLeg.frameEntry_continuousAt 1 1).mul
          (DFP.SecondLeg.outputGradientEntry_continuousAt 1))
      apply hscalar.congr
      filter_upwards [] with x
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcomp := (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.comp hpi
  change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ WithLp.toLp 2
    (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
      DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)) (0, 2, 1)
  simpa only [Function.comp_def] using hcomp

private lemma initialGradientPath_base_ne : initialGradientPath (0, 2, 1) ≠ 0 := by
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [initialGradientPath] at hzero

private lemma intermediateGradientPath_base_ne :
    intermediateGradientPath (0, 2, 1) ≠ 0 := by
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [intermediateGradientPath, DFP.FirstLeg.outputGradient] at hzero

private lemma finalGradientPath_base_ne : finalGradientPath (0, 2, 1) ≠ 0 := by
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [finalGradientPath, DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
    DFP.SecondLeg.outputGradient, hspectral, hgradient,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
    RealSymmetric2.low, RealSymmetric2.gap, EuclideanPlane.frame,
    EuclideanPlane.perp_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hzero

/-- The first endpoint oriented angle varies continuously through the common
zero-scale base state. -/
theorem firstEndpointAngleIncrement_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).firstEndpointAngleIncrement)
    (0, 2, 1) := by
  have houter : ContinuousAt
      (fun y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        EuclideanPlane.orientation.oangle y.1 y.2)
      (initialGradientPath (0, 2, 1), intermediateGradientPath (0, 2, 1)) :=
    EuclideanPlane.orientation.continuousAt_oangle
      initialGradientPath_base_ne intermediateGradientPath_base_ne
  have hpair := initialGradientPath_continuousAt.prodMk
    intermediateGradientPath_continuousAt
  have hcomp := ContinuousAt.comp
    (f := fun x : ℝ × ℝ × ℝ ↦
      (initialGradientPath x, intermediateGradientPath x))
    (g := fun y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      EuclideanPlane.orientation.oangle y.1 y.2)
    (x := ((0, 2, 1) : ℝ × ℝ × ℝ)) houter hpair
  change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
    EuclideanPlane.orientation.oangle (initialGradientPath x)
      (intermediateGradientPath x)) (0, 2, 1)
  simpa only [Function.comp_def] using hcomp

/-- The second endpoint oriented angle varies continuously through the common
zero-scale base state. -/
theorem secondEndpointAngleIncrement_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).secondEndpointAngleIncrement)
    (0, 2, 1) := by
  have houter : ContinuousAt
      (fun y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        EuclideanPlane.orientation.oangle y.1 y.2)
      (intermediateGradientPath (0, 2, 1), finalGradientPath (0, 2, 1)) :=
    EuclideanPlane.orientation.continuousAt_oangle
      intermediateGradientPath_base_ne finalGradientPath_base_ne
  have hpair := intermediateGradientPath_continuousAt.prodMk
    finalGradientPath_continuousAt
  have hcomp := ContinuousAt.comp
    (f := fun x : ℝ × ℝ × ℝ ↦
      (intermediateGradientPath x, finalGradientPath x))
    (g := fun y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      EuclideanPlane.orientation.oangle y.1 y.2)
    (x := ((0, 2, 1) : ℝ × ℝ × ℝ)) houter hpair
  change ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
    EuclideanPlane.orientation.oangle (intermediateGradientPath x)
      (finalGradientPath x)) (0, 2, 1)
  simpa only [Function.comp_def] using hcomp

/-- The absolute-value margin selecting the first endpoint-angle branch is
continuous at the common zero-scale base state. -/
theorem firstEndpointAngleMargin_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦
      Real.pi / 2 - |(observableMap x).firstEndpointAngleIncrement.toReal|)
    (0, 2, 1) := by
  have habs := Real.Angle.continuous_abs_toReal.continuousAt.comp
    firstEndpointAngleIncrement_continuousAt
  change ContinuousAt
    ((fun _ : ℝ × ℝ × ℝ ↦ Real.pi / 2) -
      fun x ↦ |(observableMap x).firstEndpointAngleIncrement.toReal|) (0, 2, 1)
  exact continuousAt_const.sub habs

/-- The absolute-value margin selecting the second endpoint-angle branch is
continuous at the common zero-scale base state. -/
theorem secondEndpointAngleMargin_continuousAt : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦
      Real.pi / 2 - |(observableMap x).secondEndpointAngleIncrement.toReal|)
    (0, 2, 1) := by
  have habs := Real.Angle.continuous_abs_toReal.continuousAt.comp
    secondEndpointAngleIncrement_continuousAt
  change ContinuousAt
    ((fun _ : ℝ × ℝ × ℝ ↦ Real.pi / 2) -
      fun x ↦ |(observableMap x).secondEndpointAngleIncrement.toReal|) (0, 2, 1)
  exact continuousAt_const.sub habs

/-- Every entry of the relative product of the two canonical eigenframes is
continuous at the common zero-scale base state. -/
theorem relativeFrameEntry_continuousAt (i j : Fin 2) : ContinuousAt
    (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) i j)
    (0, 2, 1) := by
  have hscalar := ((DFP.FirstLeg.frameEntry_continuousAt i 0).mul
    (DFP.SecondLeg.frameEntry_continuousAt 0 j)).add
    ((DFP.FirstLeg.frameEntry_continuousAt i 1).mul
      (DFP.SecondLeg.frameEntry_continuousAt 1 j))
  apply hscalar.congr
  filter_upwards [] with x
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end DFP.TwoLeg
