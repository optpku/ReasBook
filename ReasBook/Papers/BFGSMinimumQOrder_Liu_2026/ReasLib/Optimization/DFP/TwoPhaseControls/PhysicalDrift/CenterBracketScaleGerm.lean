module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFirstBracketQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondDisplacementFactorGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFirstBracketQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondDisplacementFactorGerm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Helper for Infrastructure I.16a: the canonical second normalized displacement vector
assembled from the four independent-radius first factors. -/
def canonicalSecondNormalizedDisplacement
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : Fin 2 → ℝ :=
  ![
    (CenterRaw.secondNormalizedDisplacement θ.1 r
      (centerSecondDisplacementLow θ r)
      (centerSecondDisplacementHigh θ r)
      (centerSecondDisplacementGradientLow θ r)
      (centerSecondDisplacementGradientHigh θ r)) 0,
    (CenterRaw.secondNormalizedDisplacement θ.1 r
      (centerSecondDisplacementLow θ r)
      (centerSecondDisplacementHigh θ r)
      (centerSecondDisplacementGradientLow θ r)
      (centerSecondDisplacementGradientHigh θ r)) 1
  ]

/-- Helper for Infrastructure I.16a: the scalar canonical weighted center bracket before
transport to the physical evaluator. -/
def canonicalCenterBracket (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦
    (weightedCenterBracket
      (canonicalFirstFrame θ r)
      (canonicalFirstNormalizedDisplacement θ r)
      (canonicalSecondNormalizedDisplacement θ r)) 0

/-- Helper for Infrastructure I.16a: the linear coefficient of the canonical center bracket
after a common second-leg scale germ is supplied. -/
def canonicalCenterBracketLinearCoeff
    (θ : ℝ × ℝ × ℝ) (s₁ : ℝ) : ℝ :=
  -(4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) +
    2 * centerSecondDisplacementCoordinateLinearCoeff θ s₁

/-- Helper for Infrastructure I.16a: the quadratic coefficient of the canonical center bracket
after a common second-leg scale germ is supplied. -/
def canonicalCenterBracketQuadraticCoeff
    (θ : ℝ × ℝ × ℝ) (s₁ s₂ : ℝ) : ℝ :=
  -(2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) +
    2 * (centerSecondDisplacementCoordinateQuadraticCoeff θ s₁ s₂ +
      1 / 2 - 2)

/-- Infrastructure I.16a: a common-scale germ certificate determines the quadratic germ of
the canonical weighted center bracket, leaving only the source scale quotient to be proved. -/
theorem canonicalCenterBracket_quadraticGerm_of_scaleCertificate
    (θ : ℝ × ℝ × ℝ) {s₁ s₂ : ℝ}
    (hscale : HasQuadraticGerm (centerSecondDisplacementScale θ) (-1) s₁ s₂) :
    HasQuadraticGerm (canonicalCenterBracket θ) 0
      (canonicalCenterBracketLinearCoeff θ s₁)
      (canonicalCenterBracketQuadraticCoeff θ s₁ s₂) := by
  have hsecond :=
    centerRaw_secondNormalizedDisplacement_coordinate_quadraticGerms_of_scaleCertificate
      θ hscale
  let uSecond : ℝ → Fin 2 → ℝ := canonicalSecondNormalizedDisplacement θ
  have hu0 : HasQuadraticGerm (fun r ↦ uSecond r 0) 0 (-2)
      (centerSecondDisplacementTransverseCoeff θ s₁) := by
    simpa [uSecond, canonicalSecondNormalizedDisplacement] using hsecond.1
  have hu1 : HasQuadraticGerm (fun r ↦ uSecond r 1) (-1)
      (centerSecondDisplacementCoordinateLinearCoeff θ s₁)
      (centerSecondDisplacementCoordinateQuadraticCoeff θ s₁ s₂) := by
    simpa [uSecond, canonicalSecondNormalizedDisplacement] using hsecond.2
  have hbracket := canonicalFirstBracket_quadraticGerm θ hu0 hu1
  have hlinear :
      -(4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) +
          2 * centerSecondDisplacementCoordinateLinearCoeff θ s₁ =
        canonicalCenterBracketLinearCoeff θ s₁ := by
    rfl
  have hquadratic :
      -(2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) +
          2 * (centerSecondDisplacementCoordinateQuadraticCoeff θ s₁ s₂ +
            1 / 2 - 2) =
        canonicalCenterBracketQuadraticCoeff θ s₁ s₂ := by
    rfl
  have hcoeff := hbracket.congrCoefficients rfl hlinear hquadratic
  apply hcoeff.congrFunction
  intro r
  rfl

end DFP.TwoLeg.Mixed
