module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleError.Basic

public section

noncomputable section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-!
This companion is the endpoint-specific interface for the planar angle
perturbation estimate.  The orbit files naturally bound
`endpointCorrection C k`; the angle theorem is stated using the difference
between the endpoint displacement and the endpoint gradient.  The lemmas below
keep that sign transport in one place.
-/

/-- Helper for Infrastructure C: the endpoint correction has the norm of the
radial-minus-gradient perturbation used by the oriented-angle estimate. -/
theorem norm_endpointDisplacement_sub_gradient_eq_endpointCorrection
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    ‖orbit.endpoint k - C - orbit.endpointGradient k‖ =
      ‖orbit.endpointCorrection C k‖ := by
  rw [endpointCorrection_def]
  rw [norm_sub_rev]

/-- Infrastructure C: a positive common norm lower bound converts an endpoint
correction bound into a quantitative physical oriented-angle bound. -/
theorem abs_endpointCorrectionAngle_toReal_le
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (rho K : ℝ) (hrho : 0 < rho)
    (hgradient : rho ≤ ‖orbit.endpointGradient k‖)
    (hradial : rho ≤ ‖orbit.endpoint k - C‖)
    (hcorrection : ‖orbit.endpointCorrection C k‖ ≤ K) :
    |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal| ≤ Real.pi * K / rho := by
  apply abs_oangle_toReal_le_of_norm_perturbation
    EuclideanPlane.orientation (orbit.endpointGradient k)
      (orbit.endpoint k - C) rho K hrho hgradient hradial
  calc
    ‖(orbit.endpoint k - C) - orbit.endpointGradient k‖ =
        ‖orbit.endpointCorrection C k‖ :=
      norm_endpointDisplacement_sub_gradient_eq_endpointCorrection orbit C k
    _ ≤ K := hcorrection

/-- Infrastructure C: a fourth-order endpoint correction produces a cubic
physical oriented-angle error after division by the common radius. -/
theorem abs_endpointCorrectionAngle_toReal_le_of_cubic
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (rho K : ℝ) (hrho : 0 < rho)
    (hgradient : rho ≤ ‖orbit.endpointGradient k‖)
    (hradial : rho ≤ ‖orbit.endpoint k - C‖)
    (hcorrection : ‖orbit.endpointCorrection C k‖ ≤ K * rho ^ 4) :
    |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal| ≤ Real.pi * K * rho ^ 3 := by
  apply abs_oangle_toReal_le_of_cubic_perturbation
    EuclideanPlane.orientation (orbit.endpointGradient k)
      (orbit.endpoint k - C) rho K hrho hgradient hradial
  calc
    ‖(orbit.endpoint k - C) - orbit.endpointGradient k‖ =
        ‖orbit.endpointCorrection C k‖ :=
      norm_endpointDisplacement_sub_gradient_eq_endpointCorrection orbit C k
    _ ≤ K * rho ^ 4 := hcorrection

end DFP.TwoPhaseOrbit
