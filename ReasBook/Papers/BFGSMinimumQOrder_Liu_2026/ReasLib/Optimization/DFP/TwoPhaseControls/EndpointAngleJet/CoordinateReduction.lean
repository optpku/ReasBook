module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Geometry.Euclidean.Plane.FrameOrientedAngle
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Geometry.Euclidean.Plane.FrameOrientedAngle

/-!
# Coordinate reduction for the second endpoint angle

The common first-leg eigenframe cancels from the intermediate and final gradients.
Consequently, the second endpoint angle can be expanded using only the two scalar
slopes in first-frame coordinates.
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg

/-- Reduce the second endpoint-gradient angle to the difference of its two first-frame
slope arctangents.  The hypotheses expose exactly the local chart, positivity, and
first-gradient factorization data needed by the reduction. -/
theorem secondEndpointAngleIncrement_toReal_eq_arctan_sub_of_localData
    (ε p h : ℝ)
    (hchart : DFP.FirstLeg.outputMetric ε p h 0 0 <
      DFP.FirstLeg.outputMetric ε p h 1 1)
    (hQ : 0 < (DFP.FirstLeg.gradientFactors ε p h).1)
    (hR : 0 < DFP.SecondLeg.outputGradient ε p h 0)
    (hgrad : (DFP.FirstLeg.frame ε p h).transpose *ᵥ
        DFP.FirstLeg.outputGradient ε p h =
      ![(DFP.FirstLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2]) :
    (observableMap (ε, p, h)).secondEndpointAngleIncrement.toReal =
      Real.arctan
          (DFP.SecondLeg.outputGradient ε p h 1 /
            DFP.SecondLeg.outputGradient ε p h 0) -
        Real.arctan
          (ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2 /
            (DFP.FirstLeg.gradientFactors ε p h).1) := by
  let e : EuclideanSpace ℝ (Fin 2) := RealSymmetric2.lowVector
    (DFP.FirstLeg.outputMetric ε p h 0 0)
    (DFP.FirstLeg.outputMetric ε p h 0 1)
    (DFP.FirstLeg.outputMetric ε p h 1 1)
  let F : Matrix (Fin 2) (Fin 2) ℝ := DFP.FirstLeg.frame ε p h
  have hframe : F = EuclideanPlane.frame e := by
    rfl
  have he : ‖e‖ = 1 := by
    exact RealSymmetric2.norm_lowVector _ _ _ hchart
  have hspecial : F ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    rw [hframe, EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
    exact he
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  have hreconstruct :
      F *ᵥ ![(DFP.FirstLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2] =
        DFP.FirstLeg.outputGradient ε p h := by
    rw [← hgrad]
    change F *ᵥ F.transpose *ᵥ DFP.FirstLeg.outputGradient ε p h = _
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  have hg1Lp :
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h) =
        WithLp.toLp 2
          (F *ᵥ ![(DFP.FirstLeg.gradientFactors ε p h).1,
            ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2]) :=
    congrArg (WithLp.toLp 2) hreconstruct.symm
  have hg2eta : DFP.SecondLeg.outputGradient ε p h =
      ![DFP.SecondLeg.outputGradient ε p h 0,
        DFP.SecondLeg.outputGradient ε p h 1] := by
    ext i
    fin_cases i <;> rfl
  have hangle := EuclideanPlane.oangle_frame_mulVec_toReal_eq_arctan_sub_of_pos
    e he
    (DFP.FirstLeg.gradientFactors ε p h).1
    (ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2)
    (DFP.SecondLeg.outputGradient ε p h 0)
    (DFP.SecondLeg.outputGradient ε p h 1) hQ hR
  have hprojection := congrArg (fun pair ↦ pair.2.toReal)
    (observableMap_endpointAngleIncrements ε p h)
  dsimp only at hprojection
  rw [hprojection, hg1Lp, hg2eta, hframe]
  exact hangle

end DFP.TwoLeg
