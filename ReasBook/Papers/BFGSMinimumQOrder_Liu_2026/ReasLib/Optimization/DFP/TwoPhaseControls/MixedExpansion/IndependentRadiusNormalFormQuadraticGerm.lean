module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusRecoveryGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusRecoveryGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/- The shape coordinate is a quotient of the high spectral/gradient factors
   by the low spectral/gradient factors.  These coefficient functions keep the
   quotient algebra available without exposing the normal-form construction. -/

/-- Helper for Appendix Lemma A.6: the linear coefficient of the recovered shape
    quotient determined by four component quadratic germs. -/
def shapeQuadraticLinearCoefficient
    (s₁ t₁ g₁ u₁ : ℝ) : ℝ :=
  2 * u₁ + 2 * t₁ - 4 * g₁ - s₁

/-- Helper for Appendix Lemma A.6: the quadratic coefficient of the recovered shape
    quotient determined by four component quadratic germs. -/
def shapeQuadraticCoefficient
    (s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ) : ℝ :=
  (4 * g₁ + s₁) ^ 2 / 2 -
      (4 * g₂ + 2 * g₁ ^ 2 + 2 * s₁ * g₁ + s₂) -
      (u₁ + t₁) * (4 * g₁ + s₁) +
      2 * u₂ + u₁ ^ 2 / 2 + 2 * t₁ * u₁ + 2 * t₂

/-- Helper for Appendix Lemma A.6: four component quadratic germs determine the
    recovered shape germ through order two. -/
theorem shapeQuadraticGerm_of_componentGerms
    {sLow sHigh gLow gHigh : ℝ → ℝ}
    {s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ}
    (hsLow : HasQuadraticGerm sLow 2 s₁ s₂)
    (hsHigh : HasQuadraticGerm sHigh 1 t₁ t₂)
    (hgLow : HasQuadraticGerm gLow 1 g₁ g₂)
    (hgHigh : HasQuadraticGerm gHigh 2 u₁ u₂) :
    HasQuadraticGerm
      (fun r ↦ sHigh r * gHigh r ^ 2 / (sLow r * gLow r ^ 2))
      2 (shapeQuadraticLinearCoefficient s₁ t₁ g₁ u₁)
        (shapeQuadraticCoefficient s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂) := by
  have hhighSquare := hgHigh.mul hgHigh
  have hlowSquare := hgLow.mul hgLow
  have hhighSquareConstant : (2 * 2 : ℝ) = 4 := by
    norm_num
  have hhighSquareLinear : (2 * u₁ + u₁ * 2 : ℝ) = 4 * u₁ := by
    ring
  have hhighSquareQuadratic :
      (2 * u₂ + u₁ * u₁ + u₂ * 2 : ℝ) = 4 * u₂ + u₁ ^ 2 := by
    ring
  have hhighSquare' := hhighSquare.congrCoefficients hhighSquareConstant
    hhighSquareLinear hhighSquareQuadratic
  have hnumerator := hsHigh.mul hhighSquare'
  have hnumeratorConstant : (1 * 4 : ℝ) = 4 := by
    norm_num
  have hnumeratorLinear :
      (1 * (4 * u₁) + t₁ * 4 : ℝ) = 4 * u₁ + 4 * t₁ := by
    ring
  have hnumeratorQuadratic :
      (1 * (4 * u₂ + u₁ ^ 2) + t₁ * (4 * u₁) + t₂ * 4 : ℝ) =
        4 * u₂ + u₁ ^ 2 + 4 * t₁ * u₁ + 4 * t₂ := by
    ring
  have hnumerator' := hnumerator.congrCoefficients hnumeratorConstant
    hnumeratorLinear hnumeratorQuadratic
  have hlowSquareConstant : (1 * 1 : ℝ) = 1 := by
    norm_num
  have hlowSquareLinear : (1 * g₁ + g₁ * 1 : ℝ) = 2 * g₁ := by
    ring
  have hlowSquareQuadratic :
      (1 * g₂ + g₁ * g₁ + g₂ * 1 : ℝ) = 2 * g₂ + g₁ ^ 2 := by
    ring
  have hlowSquare' := hlowSquare.congrCoefficients hlowSquareConstant
    hlowSquareLinear hlowSquareQuadratic
  have hdenominator := hsLow.mul hlowSquare'
  have hdenominatorConstant : (2 * 1 : ℝ) = 2 := by
    norm_num
  have hdenominatorLinear :
      (2 * (2 * g₁) + s₁ * 1 : ℝ) = 4 * g₁ + s₁ := by
    ring
  have hdenominatorQuadratic :
      (2 * (2 * g₂ + g₁ ^ 2) + s₁ * (2 * g₁) + s₂ * 1 : ℝ) =
        4 * g₂ + 2 * g₁ ^ 2 + 2 * s₁ * g₁ + s₂ := by
    ring
  have hdenominator' := hdenominator.congrCoefficients hdenominatorConstant
    hdenominatorLinear hdenominatorQuadratic
  have hdenominatorBase : (2 : ℝ) ≠ 0 := by
    norm_num
  have hquotient := hnumerator'.div hdenominator' hdenominatorBase
  have hlinear :
      (4 : ℝ) * (-(4 * g₁ + s₁) / 2 ^ 2) +
          (4 * u₁ + 4 * t₁) * (2 : ℝ)⁻¹ =
        shapeQuadraticLinearCoefficient s₁ t₁ g₁ u₁ := by
    simp [shapeQuadraticLinearCoefficient]
    ring
  have hquadratic :
      (4 : ℝ) * ((4 * g₁ + s₁) ^ 2 / 2 ^ 3 -
            (4 * g₂ + 2 * g₁ ^ 2 + 2 * s₁ * g₁ + s₂) / 2 ^ 2) +
          (4 * u₁ + 4 * t₁) * (-(4 * g₁ + s₁) / 2 ^ 2) +
          (4 * u₂ + u₁ ^ 2 + 4 * t₁ * u₁ + 4 * t₂) * (2 : ℝ)⁻¹ =
        shapeQuadraticCoefficient s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ := by
    simp [shapeQuadraticCoefficient]
    ring
  have hconstant : (4 : ℝ) * (2 : ℝ)⁻¹ = 2 := by
    norm_num
  have hcoeff := hquotient.congrCoefficients hconstant hlinear hquadratic
  apply hcoeff.congrFunction
  intro r
  simp only [pow_two]

/-- Helper for Appendix Lemma A.6: the mixed parameter specialization of the
    recovered shape quadratic coefficient. -/
def independentRadiusShapeQuadraticCoefficient (θ : ℝ × ℝ × ℝ) : ℝ :=
  let b := θ.1
  let P := θ.2.1
  let J := θ.2.2
  shapeQuadraticCoefficient
    (b * (2 * J + P - 12))
    ((3 * P * J * b ^ 2 - 84 * J * b ^ 2 - 26 * P * b ^ 2 -
      510 * b ^ 2 + 30) / 3)
    (8 * b)
    (4 * b ^ 2 * (6 * J + P + 78) / 3)
    0
    ((24 * J * b ^ 2 - 4 * P * b ^ 2 + 384 * b ^ 2 - 117) / 18)
    (4 * b * (3 * J + P + 12) / 9)
    ((6 * P * J * b ^ 2 + 216 * J * b ^ 2 - 2 * P ^ 2 * b ^ 2 +
      12 * P * b ^ 2 - 756 * b ^ 2 - 243) / 27)

/-- Appendix Lemma A.6: the independent-radius normal form has the explicit
    radius, shape, and high-scale quadratic germs. -/
theorem independentRadiusNormalFormQuadraticGerm
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦ (independentRadiusNormalForm θ r).1)
        0 1 (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusNormalForm θ r).2.1)
        2 (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9)
          (independentRadiusShapeQuadraticCoefficient θ) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusNormalForm θ r).2.2)
        1 (8 * θ.1)
          (4 * θ.1 ^ 2 * (6 * θ.2.2 + θ.2.1 + 78) / 3) := by
  obtain ⟨hsLow, hsHigh, hgLow, hgHigh⟩ :=
    independentRadiusSecondFactorQuadraticGerms θ
  have hshape := shapeQuadraticGerm_of_componentGerms
    hsLow hsHigh hgLow hgHigh
  have hshapeLinear :
      shapeQuadraticLinearCoefficient
          (θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
          (8 * θ.1) 0
          (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) =
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9 := by
    simp [shapeQuadraticLinearCoefficient]
    ring
  have hshapeConstant : (2 : ℝ) = 2 := by
    rfl
  have hshapeQuadratic :
      shapeQuadraticCoefficient
          (θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
          ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 - 84 * θ.2.2 * θ.1 ^ 2 -
            26 * θ.2.1 * θ.1 ^ 2 - 510 * θ.1 ^ 2 + 30) / 3)
          (8 * θ.1)
          (4 * θ.1 ^ 2 * (6 * θ.2.2 + θ.2.1 + 78) / 3)
          0
          ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
            384 * θ.1 ^ 2 - 117) / 18)
          (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9)
          ((6 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 216 * θ.2.2 * θ.1 ^ 2 -
            2 * θ.2.1 ^ 2 * θ.1 ^ 2 + 12 * θ.2.1 * θ.1 ^ 2 -
            756 * θ.1 ^ 2 - 243) / 27) =
        independentRadiusShapeQuadraticCoefficient θ := by
    rfl
  have hshapeCoeff := hshape.congrCoefficients hshapeConstant hshapeLinear
    hshapeQuadratic
  have hshapeNormalFunction : ∀ r : ℝ,
      (independentRadiusNormalForm θ r).2.1 =
        (independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2 ^ 2 /
          ((independentRadiusSecondSpectral (θ, r)).1 *
            (independentRadiusSecondGradient (θ, r)).1 ^ 2) := by
    intro r
    rw [independentRadiusNormalForm_eq_recoveryFactors]
    rfl
  have hshapeNormal := hshapeCoeff.congrFunction hshapeNormalFunction
  have hrho := independentRadiusRecoveryFactorQuadraticGerm θ
  have hid : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [quadraticModel]
  have hradiusRaw := hid.mul hrho
  have hradiusConstant : (0 * 1 : ℝ) = 0 := by
    ring
  have hradiusLinear : (0 *
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) + 1 * 1 : ℝ) = 1 := by
    ring
  have hradiusQuadratic :
      (0 * (-(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
          1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162) +
        1 * (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) + 0 * 1 : ℝ) =
      θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18 := by
    ring
  have hradiusCoeff := hradiusRaw.congrCoefficients hradiusConstant
    hradiusLinear hradiusQuadratic
  have hradiusNormalFunction : ∀ r : ℝ,
      (independentRadiusNormalForm θ r).1 =
        r * ((independentRadiusSecondSpectral (θ, r)).1 *
          (independentRadiusSecondGradient (θ, r)).1 /
          ((independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2)) := by
    intro r
    rw [independentRadiusNormalForm_eq_recoveryFactors]
    rfl
  have hradiusNormal := hradiusCoeff.congrFunction hradiusNormalFunction
  have hhighNormalFunction : ∀ r : ℝ,
      (independentRadiusNormalForm θ r).2.2 =
        (independentRadiusSecondSpectral (θ, r)).2 := by
    intro r
    rw [independentRadiusNormalForm_eq_recoveryFactors]
    rfl
  have hhighNormal := hsHigh.congrFunction hhighNormalFunction
  exact ⟨hradiusNormal, hshapeNormal, hhighNormal⟩

end DFP.TwoLeg.Mixed
