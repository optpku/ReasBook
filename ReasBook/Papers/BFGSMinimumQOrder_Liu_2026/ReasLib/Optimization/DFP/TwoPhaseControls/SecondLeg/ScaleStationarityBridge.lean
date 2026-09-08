module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.ScaleStationarity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.ScaleStationarity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet

public section

noncomputable section

namespace DFP.SecondLeg

/-!
# Scale stationarity of the low second-leg gradient factor

This module projects the scale-stationarity calculation for the complete tuple
of second-leg removable factors to its low gradient component.  Analyticity then
turns that first-order identity along the positive zero-scale slice into the
mixed second-order identities used by the transverse finite-jet argument.
-/

/-- Helper for Infrastructure I.16a and Lemma 4.15: the low second-leg gradient
factor is stationary in the signed scale at every positive transverse point. -/
theorem lowGradientFactor_scale_hasDerivAt (p h : ℝ)
    (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ lowGradientFactor (ε, p, h)) 0 0 := by
  have hgradientRaw :=
    (DFP.TwoLeg.secondLegFactors_scale_hasDerivAt p h hp hh).hasFDerivAt.snd.fst.hasDerivAt
  have hgradient :
      HasDerivAt (fun ε : ℝ ↦ (factors ε p h).2.1) (0, 0) 0 := by
    apply hgradientRaw.congr_deriv
    norm_num
  have hlowRaw := hgradient.hasFDerivAt.fst.hasDerivAt
  have hlow :
      HasDerivAt (fun ε : ℝ ↦ (factors ε p h).2.1.1) 0 0 := by
    apply hlowRaw.congr_deriv
    norm_num
  simpa only [lowGradientFactor, factors] using hlow

/-- Helper for Infrastructure I.16a and Lemma 4.15: every mixed Hessian of the
low second-leg gradient factor with one signed-scale direction and one
transverse direction vanishes at the canceled base point. -/
theorem lowGradientFactor_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2 lowGradientFactor (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  refine DFP.TwoLeg.iteratedFDeriv_scale_transverse_eq_zero_of_scaleStationarity
    lowGradientFactor lowGradientFactor_analyticAt ?_ v hv
  intro p h hp hh
  exact lowGradientFactor_scale_hasDerivAt p h hp hh

/-- Helper for Infrastructure I.16a and Lemma 4.15: the signed-scale/shape
mixed Hessian of the low second-leg gradient factor vanishes at the base. -/
theorem lowGradientFactor_scale_shape_cross_eq_zero :
    iteratedFDeriv ℝ 2 lowGradientFactor (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)] = 0 := by
  exact lowGradientFactor_scale_transverse_cross_eq_zero (0, 1, 0) rfl

/-- Helper for Infrastructure I.16a and Lemma 4.15: the signed-scale/high
mixed Hessian of the low second-leg gradient factor vanishes at the base. -/
theorem lowGradientFactor_scale_high_cross_eq_zero :
    iteratedFDeriv ℝ 2 lowGradientFactor (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 1)] = 0 := by
  exact lowGradientFactor_scale_transverse_cross_eq_zero (0, 0, 1) rfl

end DFP.SecondLeg
