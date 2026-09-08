module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJetCertificates
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFrameQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFrameQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg.Mixed

namespace WeightedCenterBracket

/-! The following path definitions are the source-facing normal forms for the two
normalized displacements.  Keeping them separate from `mixedCenterBracket` lets
the physical evaluator provide only a pointwise compatibility theorem. -/

/-- Infrastructure I.16a: the first-leg normalized displacement coordinate at index `1`. -/
def firstDisplacementCoordinate
    (b : ℝ) (p : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ -(2 / 3 : ℝ) * (p r + 1) / (1 + 2 * b * r + r ^ 2)

/-- Infrastructure I.16a: the first-leg normalized displacement coordinate at index `0`. -/
def firstDisplacementTransverse
    (b : ℝ) (p : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ r * firstDisplacementCoordinate b p r

/-- Infrastructure I.16a: the denominator of the second-leg normalized displacement. -/
def secondDisplacementDenominator
    (b : ℝ) (L H Q U : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦
    r * L r * Q r * (r * L r * Q r - 2 * b * H r * U r) +
      H r * U r * (H r * U r - 2 * b * r * L r * Q r)

/-- Infrastructure I.16a: the common numerator of the two second-leg normalized
displacement coordinates. -/
def secondDisplacementNumerator
    (L H Q U : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2

/-- Infrastructure I.16a: the common scalar multiplying the canonical second-leg
displacement direction. -/
def secondDisplacementScale
    (b : ℝ) (L H Q U : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ -(1 / 3 : ℝ) * secondDisplacementNumerator L H Q U r /
    secondDisplacementDenominator b L H Q U r

/-- Infrastructure I.16a: the linear coefficient of the second-leg common scale
in terms of the four component germs. -/
def secondDisplacementScaleLinear
    (b l₁ h₁ q₁ u₁ : ℝ) : ℝ :=
  -((h₁ + l₁ + 4 * q₁ + 2 * u₁) -
      3 * (2 * (-4 * b + h₁ + u₁))) / 3

/-- Infrastructure I.16a: the quadratic coefficient of the second-leg common scale
in terms of the four component germs. -/
def secondDisplacementScaleQuadratic
    (b l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ) : ℝ :=
  -((2 * h₁ * u₁ + h₂ + 2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 +
        4 * q₂ + u₁ ^ 2 + 2 * u₂) -
      (h₁ + l₁ + 4 * q₁ + 2 * u₁) * (2 * (-4 * b + h₁ + u₁)) +
      3 * ((2 * (-4 * b + h₁ + u₁)) ^ 2 -
        (-8 * b * h₁ - 4 * b * l₁ - 8 * b * q₁ - 8 * b * u₁ +
          h₁ ^ 2 + 4 * h₁ * u₁ + 2 * h₂ + u₁ ^ 2 + 2 * u₂ + 4))) / 3

/-- Infrastructure I.16a: the second-leg normalized displacement coordinate at index `0`. -/
def secondDisplacementTransverse
    (b : ℝ) (L H Q U : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ secondDisplacementScale b L H Q U r * (r * L r * Q r)

/-- Infrastructure I.16a: the second-leg normalized displacement coordinate at index `1`. -/
def secondDisplacementCoordinate
    (b : ℝ) (L H Q U : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ secondDisplacementScale b L H Q U r * (H r * U r)

/-- Infrastructure I.16a: the raw first normalized displacement is the pair of the
transverse and coordinate scalar paths. -/
theorem firstNormalizedDisplacement_coordinatePair
    (b r : ℝ) (p : ℝ → ℝ) :
    CenterRaw.firstNormalizedDisplacement b r (p r) =
      ![firstDisplacementTransverse b p r, firstDisplacementCoordinate b p r] := by
  ext i
  fin_cases i
  · change
      (-(2 / 3 : ℝ) * (p r + 1) / (1 + 2 * b * r + r ^ 2)) * r =
        r * (-(2 / 3 : ℝ) * (p r + 1) / (1 + 2 * b * r + r ^ 2))
    ring
  · simp [CenterRaw.firstNormalizedDisplacement, firstDisplacementTransverse,
      firstDisplacementCoordinate]

/-- Infrastructure I.16a: the raw second normalized displacement is the pair of the
transverse and coordinate scalar paths. -/
theorem secondNormalizedDisplacement_coordinatePair
    (b r : ℝ) (L H Q U : ℝ → ℝ) :
    CenterRaw.secondNormalizedDisplacement b r (L r) (H r) (Q r) (U r) =
      ![secondDisplacementTransverse b L H Q U r,
        secondDisplacementCoordinate b L H Q U r] := by
  ext i
  fin_cases i
  · simp [CenterRaw.secondNormalizedDisplacement, secondDisplacementTransverse,
      secondDisplacementCoordinate, secondDisplacementScale,
      secondDisplacementNumerator, secondDisplacementDenominator]
  · simp [CenterRaw.secondNormalizedDisplacement, secondDisplacementTransverse,
      secondDisplacementCoordinate, secondDisplacementScale,
      secondDisplacementNumerator, secondDisplacementDenominator]

/-- Infrastructure I.16a: a quadratic germ for the input scalar produces both
first-leg normalized displacement coordinate germs. -/
theorem firstDisplacement_quadraticGerms
    {b : ℝ} {p : ℝ → ℝ} {p₁ p₂ : ℝ}
    (hp : HasQuadraticGerm p 2 p₁ p₂) :
    HasQuadraticGerm (firstDisplacementCoordinate b p) (-2)
        (4 * b - (2 / 3 : ℝ) * p₁)
        (2 - 8 * b ^ 2 + (4 / 3 : ℝ) * b * p₁ - (2 / 3 : ℝ) * p₂) ∧
      HasQuadraticGerm (firstDisplacementTransverse b p) 0 (-2)
        (4 * b - (2 / 3 : ℝ) * p₁) := by
  have hden : HasQuadraticGerm
      (fun r : ℝ ↦ 1 + 2 * b * r + r ^ 2) 1 (2 * b) 1 := by
    apply (HasQuadraticGerm.model 1 (2 * b) 1).congrFunction
    intro r
    simp only [quadraticModel]
    ring
  have hnum := hp.add (HasQuadraticGerm.model 1 0 0)
  have hquot := hnum.div hden one_ne_zero
  have hscaled := hquot.constMul (-(2 / 3 : ℝ))
  have hcoordinate : HasQuadraticGerm
      (firstDisplacementCoordinate b p) (-2)
        (4 * b - (2 / 3 : ℝ) * p₁)
        (2 - 8 * b ^ 2 + (4 / 3 : ℝ) * b * p₁ - (2 / 3 : ℝ) * p₂) := by
    have hconstant : (-(2 / 3 : ℝ)) * ((2 + 1) * 1⁻¹) = -2 := by
      ring
    have hlinear :
        (-(2 / 3 : ℝ)) * ((2 + 1) * (-(2 * b) / 1 ^ 2) +
          (p₁ + 0) * 1⁻¹) = 4 * b - (2 / 3 : ℝ) * p₁ := by
      ring
    have hquadratic :
        (-(2 / 3 : ℝ)) *
            ((2 + 1) * ((2 * b) ^ 2 / 1 ^ 3 - 1 / 1 ^ 2) +
              (p₁ + 0) * (-(2 * b) / 1 ^ 2) +
              (p₂ + 0) * 1⁻¹) =
          2 - 8 * b ^ 2 + (4 / 3 : ℝ) * b * p₁ - (2 / 3 : ℝ) * p₂ := by
      ring
    have hcoeff := hscaled.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    simp only [firstDisplacementCoordinate, quadraticModel, zero_mul, add_zero]
    ring
  have hradius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp only [quadraticModel]
    ring
  have htransRaw := hradius.mul hcoordinate
  have htransConstant : (0 : ℝ) * (-2) = 0 := by
    ring
  have htransLinear : 0 * (4 * b - (2 / 3 : ℝ) * p₁) + 1 * (-2) = -2 := by
    ring
  have htransQuadratic :
      0 * (2 - 8 * b ^ 2 + (4 / 3 : ℝ) * b * p₁ - (2 / 3 : ℝ) * p₂) +
          1 * (4 * b - (2 / 3 : ℝ) * p₁) + 0 * (-2) =
        4 * b - (2 / 3 : ℝ) * p₁ := by
    ring
  have htransCoeff := htransRaw.congrCoefficients
    htransConstant htransLinear htransQuadratic
  have htrans : HasQuadraticGerm (firstDisplacementTransverse b p) 0 (-2)
      (4 * b - (2 / 3 : ℝ) * p₁) := by
    apply htransCoeff.congrFunction
    intro r
    simp only [firstDisplacementTransverse]
  exact ⟨hcoordinate, htrans⟩

/-- Infrastructure I.16a: a numerator germ at `3` and a denominator germ at `1`
determine the quadratic germ of the normalized second-leg scale. -/
theorem secondDisplacementScale_quadraticGerm_of_factorGerms
    {N D : ℝ → ℝ} {n₁ n₂ d₁ d₂ : ℝ}
    (hN : HasQuadraticGerm N 3 n₁ n₂)
    (hD : HasQuadraticGerm D 1 d₁ d₂) :
    HasQuadraticGerm (fun r ↦ -(1 / 3 : ℝ) * N r / D r) (-1)
      (-(n₁ - 3 * d₁) / 3)
      (-(3 * (d₁ ^ 2 - d₂) - n₁ * d₁ + n₂) / 3) := by
  have hquot := hN.div hD one_ne_zero
  have hscaled := hquot.constMul (-(1 / 3 : ℝ))
  have hconstant : (-(1 / 3 : ℝ)) * (3 * 1⁻¹) = -1 := by
    ring
  have hlinear :
      (-(1 / 3 : ℝ)) * (3 * (-(d₁) / 1 ^ 2) + n₁ * 1⁻¹) =
        -(n₁ - 3 * d₁) / 3 := by
    ring
  have hquadratic :
      (-(1 / 3 : ℝ)) *
          (3 * (d₁ ^ 2 / 1 ^ 3 - d₂ / 1 ^ 2) +
            n₁ * (-(d₁) / 1 ^ 2) + n₂ * 1⁻¹) =
        -(3 * (d₁ ^ 2 - d₂) - n₁ * d₁ + n₂) / 3 := by
    ring
  have hcoeff := hscaled.congrCoefficients hconstant hlinear hquadratic
  apply hcoeff.congrFunction
  intro r
  rw [div_eq_mul_inv]
  ring

/-- Infrastructure I.16a: the factor-germ scale adapter specializes to the named
second-leg displacement scale without exposing its quotient implementation. -/
theorem secondDisplacementScale_quadraticGerm
    {b : ℝ} {L H Q U : ℝ → ℝ} {n₁ n₂ d₁ d₂ : ℝ}
    (hN : HasQuadraticGerm (secondDisplacementNumerator L H Q U) 3 n₁ n₂)
    (hD : HasQuadraticGerm (secondDisplacementDenominator b L H Q U) 1 d₁ d₂) :
    HasQuadraticGerm (secondDisplacementScale b L H Q U) (-1)
      (-(n₁ - 3 * d₁) / 3)
      (-(3 * (d₁ ^ 2 - d₂) - n₁ * d₁ + n₂) / 3) := by
  have hscale := secondDisplacementScale_quadraticGerm_of_factorGerms hN hD
  apply hscale.congrFunction
  intro r
  simp only [secondDisplacementScale, secondDisplacementNumerator,
    secondDisplacementDenominator]

/-- Infrastructure I.16a: the four factor germs determine the numerator germ of
the second-leg normalized displacement scale. -/
theorem secondDisplacementNumerator_quadraticGerm
    {L H Q U : ℝ → ℝ} {l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ}
    (hL : HasQuadraticGerm L 2 l₁ l₂)
    (hH : HasQuadraticGerm H 1 h₁ h₂)
    (hQ : HasQuadraticGerm Q 1 q₁ q₂)
    (hU : HasQuadraticGerm U 1 u₁ u₂) :
    HasQuadraticGerm (secondDisplacementNumerator L H Q U) 3
      (h₁ + l₁ + 4 * q₁ + 2 * u₁)
      (2 * h₁ * u₁ + h₂ + 2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 +
        4 * q₂ + u₁ ^ 2 + 2 * u₂) := by
  have hQSquareRaw := hQ.mul hQ
  have hQSquare : HasQuadraticGerm (fun r ↦ Q r ^ 2) 1 (2 * q₁)
      (q₁ ^ 2 + 2 * q₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ Q r * Q r) 1 (2 * q₁)
        (q₁ ^ 2 + 2 * q₂) := by
      apply hQSquareRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hcoeff.congrFunction
    intro r
    ring
  have hUSquareRaw := hU.mul hU
  have hUSquare : HasQuadraticGerm (fun r ↦ U r ^ 2) 1 (2 * u₁)
      (u₁ ^ 2 + 2 * u₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ U r * U r) 1 (2 * u₁)
        (u₁ ^ 2 + 2 * u₂) := by
      apply hUSquareRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hcoeff.congrFunction
    intro r
    ring
  have hLQSquareRaw := hL.mul hQSquare
  have hLQSquare : HasQuadraticGerm (fun r ↦ L r * Q r ^ 2) 2
      (l₁ + 4 * q₁)
      (2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 + 4 * q₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ L r * Q r ^ 2) 2
        (l₁ + 4 * q₁)
        (2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 + 4 * q₂) := by
      apply hLQSquareRaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  have hHUSquareRaw := hH.mul hUSquare
  have hHUSquare : HasQuadraticGerm (fun r ↦ H r * U r ^ 2) 1
      (h₁ + 2 * u₁) (2 * h₁ * u₁ + h₂ + u₁ ^ 2 + 2 * u₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ H r * U r ^ 2) 1
        (h₁ + 2 * u₁) (2 * h₁ * u₁ + h₂ + u₁ ^ 2 + 2 * u₂) := by
      apply hHUSquareRaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  have hsumRaw := hLQSquare.add hHUSquare
  have hsum : HasQuadraticGerm
      (fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2) 3
      (h₁ + l₁ + 4 * q₁ + 2 * u₁)
      (2 * h₁ * u₁ + h₂ + 2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 +
        4 * q₂ + u₁ ^ 2 + 2 * u₂) := by
    have hcoeff : HasQuadraticGerm
        (fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2) 3
        (h₁ + l₁ + 4 * q₁ + 2 * u₁)
        (2 * h₁ * u₁ + h₂ + 2 * l₁ * q₁ + l₂ + 2 * q₁ ^ 2 +
          4 * q₂ + u₁ ^ 2 + 2 * u₂) := by
      apply hsumRaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  apply hsum.congrFunction
  intro r
  rfl

/-- Infrastructure I.16a: the four factor germs determine the denominator germ
of the second-leg normalized displacement scale. -/
theorem secondDisplacementDenominator_quadraticGerm
    {b : ℝ} {L H Q U : ℝ → ℝ} {l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ}
    (hL : HasQuadraticGerm L 2 l₁ l₂)
    (hH : HasQuadraticGerm H 1 h₁ h₂)
    (hQ : HasQuadraticGerm Q 1 q₁ q₂)
    (hU : HasQuadraticGerm U 1 u₁ u₂) :
    HasQuadraticGerm (secondDisplacementDenominator b L H Q U) 1
      (2 * (-4 * b + h₁ + u₁))
      (-8 * b * h₁ - 4 * b * l₁ - 8 * b * q₁ - 8 * b * u₁ +
        h₁ ^ 2 + 4 * h₁ * u₁ + 2 * h₂ + u₁ ^ 2 + 2 * u₂ + 4) := by
  have hLQRaw := hL.mul hQ
  have hLQ : HasQuadraticGerm (fun r ↦ L r * Q r) 2
      (2 * q₁ + l₁) (2 * q₂ + l₁ * q₁ + l₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ L r * Q r) 2
        (2 * q₁ + l₁) (2 * q₂ + l₁ * q₁ + l₂) := by
      apply hLQRaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  have hradius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp only [quadraticModel]
    ring
  have hXRaw := hradius.mul hLQ
  have hX : HasQuadraticGerm (fun r ↦ r * L r * Q r) 0 2
      (l₁ + 2 * q₁) := by
    have hconstant : (0 : ℝ) * 2 = 0 := by ring
    have hlinear : 0 * (2 * q₁ + l₁) + 1 * 2 = 2 := by ring
    have hquadratic :
        0 * (2 * q₂ + l₁ * q₁ + l₂) + 1 * (2 * q₁ + l₁) + 0 * 2 =
          l₁ + 2 * q₁ := by ring
    have hcoeff : HasQuadraticGerm (fun r ↦ r * (L r * Q r)) 0 2
        (l₁ + 2 * q₁) := by
      exact hXRaw.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    ring
  have hHURaw := hH.mul hU
  have hHU : HasQuadraticGerm (fun r ↦ H r * U r) 1
      (h₁ + u₁) (h₂ + h₁ * u₁ + u₂) := by
    have hcoeff : HasQuadraticGerm (fun r ↦ H r * U r) 1
        (h₁ + u₁) (h₂ + h₁ * u₁ + u₂) := by
      apply hHURaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  have hleftRaw := hX.sub (hHU.constMul (2 * b))
  have hleft : HasQuadraticGerm
      (fun r ↦ r * L r * Q r - 2 * b * (H r * U r)) (-2 * b)
      (2 - 2 * b * (h₁ + u₁))
      (l₁ + 2 * q₁ - 2 * b * (h₂ + h₁ * u₁ + u₂)) := by
    have hcoeff : HasQuadraticGerm
        (fun r ↦ r * L r * Q r - 2 * b * (H r * U r)) (-2 * b)
        (2 - 2 * b * (h₁ + u₁))
        (l₁ + 2 * q₁ - 2 * b * (h₂ + h₁ * u₁ + u₂)) := by
      apply hleftRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hcoeff.congrFunction
    intro r
    ring
  have hrightRaw := hHU.sub (hX.constMul (2 * b))
  have hright : HasQuadraticGerm
      (fun r ↦ H r * U r - 2 * b * (r * L r * Q r)) 1
      (h₁ + u₁ - 4 * b)
      (h₂ + h₁ * u₁ + u₂ - 2 * b * (l₁ + 2 * q₁)) := by
    have hcoeff : HasQuadraticGerm
        (fun r ↦ H r * U r - 2 * b * (r * L r * Q r)) 1
        (h₁ + u₁ - 4 * b)
        (h₂ + h₁ * u₁ + u₂ - 2 * b * (l₁ + 2 * q₁)) := by
      apply hrightRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hcoeff.congrFunction
    intro r
    ring
  have hsumRaw := hX.mul hleft |>.add (hHU.mul hright)
  have hsum : HasQuadraticGerm
      (fun r ↦
        (r * L r * Q r) * (r * L r * Q r - 2 * b * (H r * U r)) +
          (H r * U r) * (H r * U r - 2 * b * (r * L r * Q r))) 1
      (2 * (-4 * b + h₁ + u₁))
      (-8 * b * h₁ - 4 * b * l₁ - 8 * b * q₁ - 8 * b * u₁ +
        h₁ ^ 2 + 4 * h₁ * u₁ + 2 * h₂ + u₁ ^ 2 + 2 * u₂ + 4) := by
    have hcoeff : HasQuadraticGerm
        (fun r ↦
          (r * L r * Q r) * (r * L r * Q r - 2 * b * (H r * U r)) +
            (H r * U r) * (H r * U r - 2 * b * (r * L r * Q r))) 1
        (2 * (-4 * b + h₁ + u₁))
        (-8 * b * h₁ - 4 * b * l₁ - 8 * b * q₁ - 8 * b * u₁ +
          h₁ ^ 2 + 4 * h₁ * u₁ + 2 * h₂ + u₁ ^ 2 + 2 * u₂ + 4) := by
      apply hsumRaw.congrCoefficients
      · ring
      · ring
      · ring
    exact hcoeff
  apply hsum.congrFunction
  intro r
  simp only [secondDisplacementDenominator]
  ring

/-- Infrastructure I.16a: a scale germ and the four factor germs determine both
second-leg normalized displacement coordinate germs. -/
theorem secondDisplacementCoordinates_quadraticGerms_of_scaleGerm
    {S L H Q U : ℝ → ℝ}
    {s₁ s₂ l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ}
    (hS : HasQuadraticGerm S (-1) s₁ s₂)
    (hL : HasQuadraticGerm L 2 l₁ l₂)
    (hH : HasQuadraticGerm H 1 h₁ h₂)
    (hQ : HasQuadraticGerm Q 1 q₁ q₂)
    (hU : HasQuadraticGerm U 1 u₁ u₂) :
    HasQuadraticGerm (fun r ↦ S r * (r * L r * Q r)) 0 (-2)
        (-(l₁ + 2 * q₁) + 2 * s₁) ∧
      HasQuadraticGerm (fun r ↦ S r * (H r * U r)) (-1)
        (s₁ - h₁ - u₁)
        (s₂ - h₂ - h₁ * u₁ - u₂ + s₁ * (h₁ + u₁)) := by
  have hLQ := hL.mul hQ
  have hradius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp only [quadraticModel]
    ring
  have hdirectionRaw := hradius.mul hLQ
  have hdirection : HasQuadraticGerm
      (fun r ↦ r * L r * Q r) 0 2 (l₁ + 2 * q₁) := by
    have hconstant : (0 : ℝ) * (2 * 1) = 0 := by ring
    have hlinear : 0 * (2 * q₁ + l₁ * 1) + 1 * (2 * 1) = 2 := by ring
    have hquadratic :
        0 * (2 * q₂ + l₁ * q₁ + l₂ * 1) +
            1 * (2 * q₁ + l₁ * 1) + 0 * (2 * 1) = l₁ + 2 * q₁ := by
      ring
    have hcoeff := hdirectionRaw.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    ring
  have htransverseRaw := hS.mul hdirection
  have htransverse : HasQuadraticGerm
      (fun r ↦ S r * (r * L r * Q r)) 0 (-2)
        (-(l₁ + 2 * q₁) + 2 * s₁) := by
    have hconstant : (-1 : ℝ) * 0 = 0 := by ring
    have hlinear : (-1 : ℝ) * 2 + s₁ * 0 = -2 := by ring
    have hquadratic :
        (-1 : ℝ) * (l₁ + 2 * q₁) + s₁ * 2 + s₂ * 0 =
          -(l₁ + 2 * q₁) + 2 * s₁ := by
      ring
    have hcoeff := htransverseRaw.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    rfl
  have hHU := hH.mul hU
  have hproduct : HasQuadraticGerm (fun r ↦ H r * U r) 1
      (h₁ + u₁) (h₂ + h₁ * u₁ + u₂) := by
    have hconstant : (1 : ℝ) * 1 = 1 := by ring
    have hlinear : 1 * u₁ + h₁ * 1 = h₁ + u₁ := by ring
    have hquadratic :
        1 * u₂ + h₁ * u₁ + h₂ * 1 = h₂ + h₁ * u₁ + u₂ := by
      ring
    have hcoeff := hHU.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    rfl
  have hcoordinateRaw := hS.mul hproduct
  have hcoordinate : HasQuadraticGerm (fun r ↦ S r * (H r * U r)) (-1)
      (s₁ - h₁ - u₁)
      (s₂ - h₂ - h₁ * u₁ - u₂ + s₁ * (h₁ + u₁)) := by
    have hconstant : (-1 : ℝ) * 1 = -1 := by ring
    have hlinear : (-1 : ℝ) * (h₁ + u₁) + s₁ * 1 =
        s₁ - h₁ - u₁ := by ring
    have hquadratic :
        (-1 : ℝ) * (h₂ + h₁ * u₁ + u₂) + s₁ * (h₁ + u₁) + s₂ * 1 =
          s₂ - h₂ - h₁ * u₁ - u₂ + s₁ * (h₁ + u₁) := by
      ring
    have hcoeff := hcoordinateRaw.congrCoefficients hconstant hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    rfl
  exact ⟨htransverse, hcoordinate⟩

/-- Infrastructure I.16a: the named second-leg displacement paths consume the
factor-germ coordinate adapter after the common scale has been established. -/
theorem secondDisplacementCoordinates_quadraticGerms
    {b : ℝ} {L H Q U : ℝ → ℝ}
    {s₁ s₂ l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ}
    (hS : HasQuadraticGerm (secondDisplacementScale b L H Q U) (-1) s₁ s₂)
    (hL : HasQuadraticGerm L 2 l₁ l₂)
    (hH : HasQuadraticGerm H 1 h₁ h₂)
    (hQ : HasQuadraticGerm Q 1 q₁ q₂)
    (hU : HasQuadraticGerm U 1 u₁ u₂) :
    HasQuadraticGerm (secondDisplacementTransverse b L H Q U) 0 (-2)
        (-(l₁ + 2 * q₁) + 2 * s₁) ∧
      HasQuadraticGerm (secondDisplacementCoordinate b L H Q U) (-1)
        (s₁ - h₁ - u₁)
        (s₂ - h₂ - h₁ * u₁ - u₂ + s₁ * (h₁ + u₁)) := by
  have hpaths := secondDisplacementCoordinates_quadraticGerms_of_scaleGerm
    hS hL hH hQ hU
  apply hpaths.imp
  · intro h
    apply h.congrFunction
    intro r
    rfl
  · intro h
    apply h.congrFunction
    intro r
    rfl

/-- Infrastructure I.16a: the canonical factor certificates directly produce the
two second-leg normalized displacement coordinate germs. -/
theorem secondDisplacementCoordinates_quadraticGerms_of_factorGerms
    {b : ℝ} {L H Q U : ℝ → ℝ}
    {l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ : ℝ}
    (hL : HasQuadraticGerm L 2 l₁ l₂)
    (hH : HasQuadraticGerm H 1 h₁ h₂)
    (hQ : HasQuadraticGerm Q 1 q₁ q₂)
    (hU : HasQuadraticGerm U 1 u₁ u₂) :
    HasQuadraticGerm (secondDisplacementTransverse b L H Q U) 0 (-2)
        (-(l₁ + 2 * q₁) +
          2 * secondDisplacementScaleLinear b l₁ h₁ q₁ u₁) ∧
      HasQuadraticGerm (secondDisplacementCoordinate b L H Q U) (-1)
        (secondDisplacementScaleLinear b l₁ h₁ q₁ u₁ - h₁ - u₁)
        (secondDisplacementScaleQuadratic b l₁ l₂ h₁ h₂ q₁ q₂ u₁ u₂ -
          h₂ - h₁ * u₁ - u₂ +
          secondDisplacementScaleLinear b l₁ h₁ q₁ u₁ * (h₁ + u₁)) := by
  have hN := secondDisplacementNumerator_quadraticGerm
    (L := L) (H := H) (Q := Q) (U := U) hL hH hQ hU
  have hD := secondDisplacementDenominator_quadraticGerm
    (b := b) (L := L) (H := H) (Q := Q) (U := U) hL hH hQ hU
  have hS := secondDisplacementScale_quadraticGerm
    (b := b) hN hD
  have hcoordinates := secondDisplacementCoordinates_quadraticGerms_of_scaleGerm
    hS hL hH hQ hU
  rcases hcoordinates with ⟨htrans, hcoord⟩
  constructor
  · apply htrans.congrCoefficients
    · rfl
    · rfl
    · rfl
  · apply hcoord.congrCoefficients
    · rfl
    · rfl
    · dsimp only [secondDisplacementScaleQuadratic,
        secondDisplacementScaleLinear]
      ring


/-!
This companion isolates the scalar coordinate of the weighted center bracket and
provides its quadratic-germ calculus.  Source files can prove entry germs for a
frame and two normalized displacements independently, then consume the theorem
below without unfolding the vector-valued transport construction.
-/

/-- Infrastructure I.16a: the zero-coordinate scalar normal form of a weighted center
bracket built from a radius-dependent frame and two displacement paths. -/
def coordZero
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u₀ u₁ : ℝ → Fin 2 → ℝ) : ℝ → ℝ :=
  fun r ↦ -(u₀ r 1) +
    2 * (F r 0 0 * u₁ r 1 + F r 0 1 * u₁ r 0)

/-- Infrastructure I.16a: projecting a weighted center bracket to coordinate zero gives
the scalar normal form `coordZero`, with no assumptions on the frame or paths. -/
theorem coord_zero_apply
    (F : Matrix (Fin 2) (Fin 2) ℝ)
    (u₀ u₁ : Fin 2 → ℝ) :
    (weightedCenterBracket F u₀ u₁) 0 =
      -(u₀ 1) + 2 * (F 0 0 * u₁ 1 + F 0 1 * u₁ 0) := by
  simp [weightedCenterBracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Infrastructure I.16a: a raw bracket certificate transports its zero coordinate to
the scalar `coordZero` normal form after frame and displacement projections are identified. -/
theorem bracketCertificate_bracket_zero_eq_coordZero
    {b r : ℝ} {state : ℝ × ℝ × ℝ}
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : ℝ → Fin 2 → ℝ}
    (certificate : CenterRaw.BracketCertificate b r state)
    (hF : CenterRaw.firstFrame b state = F r)
    (h₀ : certificate.firstNormalized = u₀ r)
    (h₁ : certificate.secondNormalized = u₁ r) :
    certificate.bracket 0 = coordZero F u₀ u₁ r := by
  calc
    certificate.bracket 0 =
        weightedCenterBracket (CenterRaw.firstFrame b state)
          certificate.firstNormalized certificate.secondNormalized 0 := rfl
    _ = weightedCenterBracket (F r) (u₀ r) (u₁ r) 0 := by
      rw [hF, h₀, h₁]
    _ = coordZero F u₀ u₁ r := by
      simpa only [coordZero] using
        coord_zero_apply (F r) (u₀ r) (u₁ r)

/-- Infrastructure I.16a: entry-wise quadratic germs of the frame and normalized
displacements combine into a quadratic germ for the scalar weighted bracket. -/
theorem coordZero_quadraticGerm
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : ℝ → Fin 2 → ℝ}
    {f₁ f₂ g₁ g₂ a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ : ℝ}
    (hF00 : HasQuadraticGerm (fun r ↦ F r 0 0) 1 f₁ f₂)
    (hF01 : HasQuadraticGerm (fun r ↦ F r 0 1) 0 g₁ g₂)
    (hu₀ : HasQuadraticGerm (fun r ↦ u₀ r 1) a₀ a₁ a₂)
    (hu₁₀ : HasQuadraticGerm (fun r ↦ u₁ r 0) b₀ b₁ b₂)
    (hu₁₁ : HasQuadraticGerm (fun r ↦ u₁ r 1) c₀ c₁ c₂)
    (hbase : -a₀ + 2 * (1 * c₀ + 0 * b₀) = 0) :
    HasQuadraticGerm (coordZero F u₀ u₁) 0
      (-a₁ + 2 * (f₁ * c₀ + c₁ + g₁ * b₀))
      (-a₂ + 2 * (c₂ + f₁ * c₁ + f₂ * c₀ + g₁ * b₁ + g₂ * b₀)) := by
  have hfirstProduct := hF00.mul hu₁₁
  have hsecondProduct := hF01.mul hu₁₀
  have hproducts := hfirstProduct.add hsecondProduct
  have hscaled := hproducts.constMul 2
  have hnegative := hu₀.neg
  have hsum := hnegative.add hscaled
  have hconstant : -a₀ + 2 * (1 * c₀ + 0 * b₀) = 0 := by
    exact hbase
  have hlinear :
      (-a₁) + 2 * (1 * c₁ + f₁ * c₀ + (0 * b₁ + g₁ * b₀)) =
        -a₁ + 2 * (f₁ * c₀ + c₁ + g₁ * b₀) := by
    ring
  have hquadratic :
      (-a₂) + 2 *
          ((1 * c₂ + f₁ * c₁ + f₂ * c₀) +
            (0 * b₂ + g₁ * b₁ + g₂ * b₀)) =
        -a₂ + 2 * (c₂ + f₁ * c₁ + f₂ * c₀ + g₁ * b₁ + g₂ * b₀) := by
    ring
  have hcoeff := hsum.congrCoefficients hconstant hlinear hquadratic
  apply hcoeff.congrFunction
  intro r
  simp only [coordZero]

/-- Infrastructure I.16a: a quadratic germ for the scalar normal form transfers to the
actual zero-coordinate weighted bracket through the projection identity. -/
theorem weighted_coord_zero_quadraticGerm
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : ℝ → Fin 2 → ℝ}
    {f₁ f₂ g₁ g₂ a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ : ℝ}
    (hF00 : HasQuadraticGerm (fun r ↦ F r 0 0) 1 f₁ f₂)
    (hF01 : HasQuadraticGerm (fun r ↦ F r 0 1) 0 g₁ g₂)
    (hu₀ : HasQuadraticGerm (fun r ↦ u₀ r 1) a₀ a₁ a₂)
    (hu₁₀ : HasQuadraticGerm (fun r ↦ u₁ r 0) b₀ b₁ b₂)
    (hu₁₁ : HasQuadraticGerm (fun r ↦ u₁ r 1) c₀ c₁ c₂)
    (hbase : -a₀ + 2 * (1 * c₀ + 0 * b₀) = 0) :
    HasQuadraticGerm
      (fun r ↦ (weightedCenterBracket (F r) (u₀ r) (u₁ r)) 0) 0
      (-a₁ + 2 * (f₁ * c₀ + c₁ + g₁ * b₀))
      (-a₂ + 2 * (c₂ + f₁ * c₁ + f₂ * c₀ + g₁ * b₁ + g₂ * b₀)) := by
  have hscalar := coordZero_quadraticGerm hF00 hF01 hu₀ hu₁₀ hu₁₁ hbase
  apply hscalar.congrFunction
  intro r
  exact coord_zero_apply (F r) (u₀ r) (u₁ r)

/-- Infrastructure I.16a: joint radius regularity restricts to the corresponding scalar
slice at a fixed parameter, preserving the order of differentiability. -/
theorem radiusSlice_contDiffAt
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (θ : ℝ × ℝ × ℝ)
    (hW : ContDiffAt ℝ 3 (Function.uncurry W) (θ, 0)) :
    ContDiffAt ℝ 3 (W θ) 0 := by
  have hpath : ContDiffAt ℝ 3 (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  have hcomp := hW.comp 0 hpath
  have hfun : Function.uncurry W ∘ Prod.mk θ = W θ := by
    funext r
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- Infrastructure I.16a: a cubic-regular scalar bracket germ with zero base value
and linear coefficient `κ` yields the two-term radius germ `[0, κ]` used by the
compact quotient transport. -/
theorem truncatedGerm_of_coordZero_quadraticGerm
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)}
    {κ c : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry W) (θ, 0))
    (hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm (W θ) 0 (κ θ) (c θ)) :
    IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, κ θ] : Fin 2 → ℝ) n) := by
  have horder : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have hregular₂ : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 2 (Function.uncurry W) (θ, 0) := by
    intro θ hθ
    exact (hregular θ hθ).of_le horder
  have hzero : ∀ θ, θ ∈ K → W θ 0 = 0 := by
    intro θ hθ
    have hslice := radiusSlice_contDiffAt θ (hregular θ hθ)
    have hcoeff :=
      (hgerm θ hθ).iteratedDeriv_coefficients_of_contDiffAt hslice
    have hvalue : iteratedDeriv 0 (W θ) 0 = 0 := hcoeff.1
    simpa only [iteratedDeriv_zero] using hvalue
  have hlinear : ∀ θ, θ ∈ K → iteratedDeriv 1 (W θ) 0 = κ θ := by
    intro θ hθ
    have hslice := radiusSlice_contDiffAt θ (hregular θ hθ)
    have hcoeff :=
      (hgerm θ hθ).iteratedDeriv_coefficients_of_contDiffAt hslice
    exact hcoeff.2.1
  have htruncated := independentRadiusTruncatedGerm_of_twoDerivativeData
    (f := W) (K := K) (c₀ := fun _ ↦ 0) (c₁ := κ)
    hregular₂ hzero hlinear
  simpa only using htruncated

end WeightedCenterBracket

end DFP.TwoLeg.Mixed
