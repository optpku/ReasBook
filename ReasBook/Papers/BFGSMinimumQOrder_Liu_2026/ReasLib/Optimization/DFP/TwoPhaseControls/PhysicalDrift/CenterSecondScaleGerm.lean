module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondDisplacementFactorGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondDisplacementFactorGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Helper for Infrastructure I.16a: the explicit linear coefficient of the canonical
second-leg common scale obtained from the four first-factor germs. -/
def centerSecondDisplacementScaleLinearCoeff (θ : ℝ × ℝ × ℝ) : ℝ :=
  WeightedCenterBracket.secondDisplacementScaleLinear θ.1
    (θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
    (-2 * θ.1) (-2 * θ.1) (θ.1 * (θ.2.1 - 6) / 3)

/-- Helper for Infrastructure I.16a: the explicit quadratic coefficient of the canonical
second-leg common scale obtained from the four first-factor germs. -/
def centerSecondDisplacementScaleQuadraticCoeff (θ : ℝ × ℝ × ℝ) : ℝ :=
  WeightedCenterBracket.secondDisplacementScaleQuadratic θ.1
    (θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
    (θ.2.2 * θ.2.1 * θ.1 ^ 2 + 4 * θ.2.2 * θ.1 ^ 2 +
      2 * θ.2.1 * θ.1 ^ 2 - 10 * θ.1 ^ 2 + 2)
    (-2 * θ.1) (6 * θ.1 ^ 2)
    (-2 * θ.1)
    (-2 * θ.2.1 * θ.1 ^ 2 / 3 + 4 * θ.1 ^ 2 - 5 / 2)
    (θ.1 * (θ.2.1 - 6) / 3)
    (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2)

/-- Infrastructure I.16a: the public first-factor quadratic germs determine the canonical
second-leg common quotient scale germ. -/
theorem centerSecondDisplacementScale_quadraticGerm (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm (centerSecondDisplacementScale θ) (-1)
      (centerSecondDisplacementScaleLinearCoeff θ)
      (centerSecondDisplacementScaleQuadraticCoeff θ) := by
  obtain ⟨hL, hH, hQ, hU⟩ := independentRadiusFirstFactorQuadraticGerms θ
  have hN := WeightedCenterBracket.secondDisplacementNumerator_quadraticGerm
    hL hH hQ hU
  have hD := WeightedCenterBracket.secondDisplacementDenominator_quadraticGerm
    (b := θ.1)
    hL hH hQ hU
  have hS := WeightedCenterBracket.secondDisplacementScale_quadraticGerm
    (b := θ.1)
    (L := centerSecondDisplacementLow θ)
    (H := centerSecondDisplacementHigh θ)
    (Q := centerSecondDisplacementGradientLow θ)
    (U := centerSecondDisplacementGradientHigh θ)
    hN hD
  have hpath : ∀ r : ℝ,
      centerSecondDisplacementScale θ r =
        WeightedCenterBracket.secondDisplacementScale θ.1
          (centerSecondDisplacementLow θ) (centerSecondDisplacementHigh θ)
          (centerSecondDisplacementGradientLow θ)
          (centerSecondDisplacementGradientHigh θ) r := by
    intro r
    rfl
  have hS' := hS.congrFunction hpath
  apply hS'.congrCoefficients
  · rfl
  · rfl
  · dsimp [centerSecondDisplacementScaleQuadraticCoeff,
      WeightedCenterBracket.secondDisplacementScaleQuadratic]
    ring

/-- Helper for Infrastructure I.16a: the explicit second-leg scale germ feeds directly into the
canonical weighted center-bracket quadratic germ. -/
theorem canonicalCenterBracket_quadraticGerm_of_explicitScale (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm (canonicalCenterBracket θ) 0
      (canonicalCenterBracketLinearCoeff θ (centerSecondDisplacementScaleLinearCoeff θ))
      (canonicalCenterBracketQuadraticCoeff θ
        (centerSecondDisplacementScaleLinearCoeff θ)
        (centerSecondDisplacementScaleQuadraticCoeff θ)) := by
  exact canonicalCenterBracket_quadraticGerm_of_scaleCertificate θ
    (centerSecondDisplacementScale_quadraticGerm θ)

end DFP.TwoLeg.Mixed
