module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle

/-!
# Smooth scalar projections of the two-leg observable map

The amplitude and relative-frame angle are smooth to arbitrary order at the common canceled base
point `(ε, p, h) = (0, 2, 1)`.  The proof of the frame angle stays entrywise, avoiding any
dependence on a particular matrix norm instance.
-/

public section

noncomputable section

open scoped Matrix Nat ContDiff

namespace DFP.TwoLeg

/-- The observable amplitude ratio is `C^k` at the common base point for every order `k`. -/
@[fun_prop]
theorem amplitudeRatio_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).amplitudeRatio) (0, 2, 1) := by
  have h := contDiffAt_fst.comp (0, 2, 1) (DFP.SecondLeg.coordinates_contDiffAt k)
  change ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.SecondLeg.coordinates x.1 x.2.1 x.2.2).1) (0, 2, 1)
  simpa only [Function.comp_def] using h

/-- The observable relative-frame signed coordinate is `C^k` at the common base point for every
order `k`. -/
@[fun_prop]
theorem frameAngleIncrement_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).frameAngleIncrement) (0, 2, 1) := by
  have hf100 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 0 0)
      (0, 2, 1) := DFP.FirstLeg.frameEntry_analyticAt 0 0 |>.contDiffAt
  have hf101 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 0 1)
      (0, 2, 1) := DFP.FirstLeg.frameEntry_analyticAt 0 1 |>.contDiffAt
  have hf110 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 1 0)
      (0, 2, 1) := DFP.FirstLeg.frameEntry_analyticAt 1 0 |>.contDiffAt
  have hf111 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 1 1)
      (0, 2, 1) := DFP.FirstLeg.frameEntry_analyticAt 1 1 |>.contDiffAt
  have hf200 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.frame x.1 x.2.1 x.2.2 0 0)
      (0, 2, 1) := DFP.SecondLeg.frameEntry_analyticAt 0 0 |>.contDiffAt
  have hf210 : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.frame x.1 x.2.1 x.2.2 1 0)
      (0, 2, 1) := DFP.SecondLeg.frameEntry_analyticAt 1 0 |>.contDiffAt
  have h00 : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) 0 0) (0, 2, 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have h10 : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) 1 0) (0, 2, 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have hden :
      (DFP.FirstLeg.frame 0 2 1 * DFP.SecondLeg.frame 0 2 1) 0 0 ≠ 0 := by
    norm_num [DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
      DFP.SecondLeg.frame, DFP.SecondLeg.outputMetric,
      DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, RealSymmetric2.low, RealSymmetric2.high,
      RealSymmetric2.gap, RealSymmetric2.lowDenom, Matrix.mul_apply, Fin.sum_univ_two]
  change ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
    EuclideanPlane.SignedAngle.coordinate (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
      DFP.SecondLeg.frame x.1 x.2.1 x.2.2)) (0, 2, 1)
  unfold EuclideanPlane.SignedAngle.coordinate
  exact Real.contDiff_arctan.contDiffAt.comp (0, 2, 1) (h10.div h00 hden)

end DFP.TwoLeg
