module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterDisplacementQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterDisplacementQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion exposes the second normalized displacement through a small
certificate boundary.  The common scalar scale is intentionally supplied as a
germ certificate; this keeps the file independent of the physical-drift parent
and lets the weighted-bracket owner provide the quotient certificate.
-/

/-- Helper for Infrastructure I.16a: the first spectral low factor along the
independent-radius slice used by the raw second displacement. -/
def centerSecondDisplacementLow (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦ (independentRadiusFirstSpectral (θ, r)).1

/-- Helper for Infrastructure I.16a: the first spectral high factor along the
independent-radius slice used by the raw second displacement. -/
def centerSecondDisplacementHigh (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦ (independentRadiusFirstSpectral (θ, r)).2

/-- Helper for Infrastructure I.16a: the first gradient low factor along the
independent-radius slice used by the raw second displacement. -/
def centerSecondDisplacementGradientLow (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦ (independentRadiusFirstGradient (θ, r)).1

/-- Helper for Infrastructure I.16a: the first gradient high factor along the
independent-radius slice used by the raw second displacement. -/
def centerSecondDisplacementGradientHigh (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦ (independentRadiusFirstGradient (θ, r)).2

/-- Helper for Infrastructure I.16a: the common scalar in the raw second
displacement, isolated as the scale certificate's source-facing path. -/
def centerSecondDisplacementScale (θ : ℝ × ℝ × ℝ) : ℝ → ℝ :=
  fun r ↦
    -(1 / 3 : ℝ) *
      (centerSecondDisplacementLow θ r *
          centerSecondDisplacementGradientLow θ r ^ 2 +
        centerSecondDisplacementHigh θ r *
          centerSecondDisplacementGradientHigh θ r ^ 2) /
      (r * centerSecondDisplacementLow θ r *
          centerSecondDisplacementGradientLow θ r *
          (r * centerSecondDisplacementLow θ r *
              centerSecondDisplacementGradientLow θ r -
            2 * θ.1 * centerSecondDisplacementHigh θ r *
              centerSecondDisplacementGradientHigh θ r) +
        centerSecondDisplacementHigh θ r *
          centerSecondDisplacementGradientHigh θ r *
          (centerSecondDisplacementHigh θ r *
              centerSecondDisplacementGradientHigh θ r -
            2 * θ.1 * r * centerSecondDisplacementLow θ r *
              centerSecondDisplacementGradientLow θ r))

/-- Helper for Infrastructure I.16a: the transverse quadratic coefficient obtained
from a supplied common-scale germ. -/
def centerSecondDisplacementTransverseCoeff
    (θ : ℝ × ℝ × ℝ) (s₁ : ℝ) : ℝ :=
  -(θ.1 * (2 * θ.2.2 + θ.2.1 + 4) + 2 * (-2 * θ.1)) + 2 * s₁

/-- Helper for Infrastructure I.16a: the coordinate linear coefficient obtained
from a supplied common-scale germ. -/
def centerSecondDisplacementCoordinateLinearCoeff
    (θ : ℝ × ℝ × ℝ) (s₁ : ℝ) : ℝ :=
  s₁ - (-2 * θ.1) - θ.1 * (θ.2.1 - 6) / 3

/-- Helper for Infrastructure I.16a: the coordinate quadratic coefficient obtained
from a supplied common-scale germ. -/
def centerSecondDisplacementCoordinateQuadraticCoeff
    (θ : ℝ × ℝ × ℝ) (s₁ s₂ : ℝ) : ℝ :=
  s₂ - 6 * θ.1 ^ 2 - (-2 * θ.1) * (θ.1 * (θ.2.1 - 6) / 3) -
      (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2) +
    s₁ * (-2 * θ.1 + θ.1 * (θ.2.1 - 6) / 3)

/-- Infrastructure I.16a: a common-scale quadratic germ certificate and the public
first-factor germs determine both coordinates of `CenterRaw.secondNormalizedDisplacement`. -/
theorem centerRaw_secondNormalizedDisplacement_coordinate_quadraticGerms_of_scaleCertificate
    (θ : ℝ × ℝ × ℝ) {s₁ s₂ : ℝ}
    (hscale : HasQuadraticGerm (centerSecondDisplacementScale θ) (-1) s₁ s₂) :
    HasQuadraticGerm
        (fun r ↦
          (CenterRaw.secondNormalizedDisplacement θ.1 r
            (centerSecondDisplacementLow θ r)
            (centerSecondDisplacementHigh θ r)
            (centerSecondDisplacementGradientLow θ r)
            (centerSecondDisplacementGradientHigh θ r)) 0)
        0 (-2) (centerSecondDisplacementTransverseCoeff θ s₁) ∧
      HasQuadraticGerm
        (fun r ↦
          (CenterRaw.secondNormalizedDisplacement θ.1 r
            (centerSecondDisplacementLow θ r)
            (centerSecondDisplacementHigh θ r)
            (centerSecondDisplacementGradientLow θ r)
            (centerSecondDisplacementGradientHigh θ r)) 1)
        (-1) (centerSecondDisplacementCoordinateLinearCoeff θ s₁)
          (centerSecondDisplacementCoordinateQuadraticCoeff θ s₁ s₂) := by
  obtain ⟨hL, hH, hQ, hU⟩ := independentRadiusFirstFactorQuadraticGerms θ
  have hRadius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [quadraticModel]
  have hXRaw := (hRadius.mul hL).mul hQ
  have hX : HasQuadraticGerm
      (fun r ↦ r * centerSecondDisplacementLow θ r *
        centerSecondDisplacementGradientLow θ r)
      0 2 (θ.1 * (2 * θ.2.2 + θ.2.1 + 4) - 4 * θ.1) := by
    have hconst : (0 : ℝ) * 2 * 1 = 0 := by norm_num
    have hlinear :
        0 * 2 * (-2 * θ.1) +
            (0 * (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) + 1 * 2) * 1 = 2 := by ring
    have hquadratic :
        0 * 2 * (-2 * θ.2.1 * θ.1 ^ 2 / 3 + 4 * θ.1 ^ 2 - 5 / 2) +
            (0 * (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) + 1 * 2) *
              (-2 * θ.1) +
            (0 * (θ.2.1 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.2 * θ.1 ^ 2 +
              2 * θ.2.1 * θ.1 ^ 2 - 10 * θ.1 ^ 2 + 2) +
              1 * (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) + 0 * 2) * 1 =
          θ.1 * (2 * θ.2.2 + θ.2.1 + 4) - 4 * θ.1 := by ring
    have hcoeff := hXRaw.congrCoefficients hconst hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    rfl
  have hYRaw := hH.mul hU
  have hY : HasQuadraticGerm
      (fun r ↦ centerSecondDisplacementHigh θ r *
        centerSecondDisplacementGradientHigh θ r)
      1 (θ.1 * (θ.2.1 - 6) / 3 - 2 * θ.1)
      (6 * θ.1 ^ 2 + (-2 * θ.1) *
        (θ.1 * (θ.2.1 - 6) / 3) +
        (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2)) := by
    have hconst : (1 : ℝ) * 1 = 1 := by norm_num
    have hlinear :
        1 * (θ.1 * (θ.2.1 - 6) / 3) + (-2 * θ.1) * 1 =
          θ.1 * (θ.2.1 - 6) / 3 - 2 * θ.1 := by ring
    have hquadratic :
        1 * (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2) +
            (-2 * θ.1) * (θ.1 * (θ.2.1 - 6) / 3) +
            6 * θ.1 ^ 2 * 1 =
          6 * θ.1 ^ 2 + (-2 * θ.1) *
            (θ.1 * (θ.2.1 - 6) / 3) +
            (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2) := by ring
    have hcoeff := hYRaw.congrCoefficients hconst hlinear hquadratic
    apply hcoeff.congrFunction
    intro r
    rfl
  have hcoord0 : ∀ r : ℝ,
      (CenterRaw.secondNormalizedDisplacement θ.1 r
        (centerSecondDisplacementLow θ r)
        (centerSecondDisplacementHigh θ r)
        (centerSecondDisplacementGradientLow θ r)
        (centerSecondDisplacementGradientHigh θ r)) 0 =
      centerSecondDisplacementScale θ r *
        (r * centerSecondDisplacementLow θ r *
          centerSecondDisplacementGradientLow θ r) := by
    intro r
    rfl
  have hcoord1 : ∀ r : ℝ,
      (CenterRaw.secondNormalizedDisplacement θ.1 r
        (centerSecondDisplacementLow θ r)
        (centerSecondDisplacementHigh θ r)
        (centerSecondDisplacementGradientLow θ r)
        (centerSecondDisplacementGradientHigh θ r)) 1 =
      centerSecondDisplacementScale θ r *
        (centerSecondDisplacementHigh θ r *
          centerSecondDisplacementGradientHigh θ r) := by
    intro r
    rfl
  have hgeneric :=
    secondNormalizedDisplacement_coordinate_quadraticGerms_of_factorCertificate
      (b := θ.1)
      (L := centerSecondDisplacementLow θ)
      (H := centerSecondDisplacementHigh θ)
      (Q := centerSecondDisplacementGradientLow θ)
      (U := centerSecondDisplacementGradientHigh θ)
      (alpha := centerSecondDisplacementScale θ)
      (x := fun r ↦ r * centerSecondDisplacementLow θ r *
        centerSecondDisplacementGradientLow θ r)
      (y := fun r ↦ centerSecondDisplacementHigh θ r *
        centerSecondDisplacementGradientHigh θ r)
      hscale hX hY hcoord0 hcoord1
  have htransverse := hgeneric.1
  have hcoordinate := hgeneric.2
  have htransverseConstant : (-1 : ℝ) * 0 = 0 := by norm_num
  have htransverseLinear : (-1 : ℝ) * 2 + s₁ * 0 = -2 := by norm_num
  have htransverseQuadratic :
      (-1 : ℝ) *
          (θ.1 * (2 * θ.2.2 + θ.2.1 + 4) - 4 * θ.1) +
        s₁ * 2 + s₂ * 0 = centerSecondDisplacementTransverseCoeff θ s₁ := by
    dsimp [centerSecondDisplacementTransverseCoeff]
    ring
  have htransverseCoeff := htransverse.congrCoefficients
    htransverseConstant htransverseLinear htransverseQuadratic
  have hcoordinateConstant : (-1 : ℝ) * 1 = -1 := by norm_num
  have hcoordinateLinear :
      (-1 : ℝ) *
          (θ.1 * (θ.2.1 - 6) / 3 - 2 * θ.1) + s₁ * 1 =
        centerSecondDisplacementCoordinateLinearCoeff θ s₁ := by
    dsimp [centerSecondDisplacementCoordinateLinearCoeff]
    ring
  have hcoordinateQuadratic :
      (-1 : ℝ) *
          (6 * θ.1 ^ 2 + (-2 * θ.1) *
            (θ.1 * (θ.2.1 - 6) / 3) +
            (-2 * θ.2.2 * θ.1 ^ 2 - θ.2.1 * θ.1 ^ 2 - 1 / 2)) +
        s₁ * (θ.1 * (θ.2.1 - 6) / 3 - 2 * θ.1) + s₂ * 1 =
      centerSecondDisplacementCoordinateQuadraticCoeff θ s₁ s₂ := by
    dsimp [centerSecondDisplacementCoordinateQuadraticCoeff]
    ring
  have hcoordinateCoeff := hcoordinate.congrCoefficients
    hcoordinateConstant hcoordinateLinear hcoordinateQuadratic
  exact ⟨htransverseCoeff, hcoordinateCoeff⟩

end DFP.TwoLeg.Mixed
