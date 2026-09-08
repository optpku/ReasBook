module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFrameQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterFrameQuadraticGerm

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion isolates the radius-normalized displacement germs used by the
weighted center bracket.  It proves the first-leg chart calculation and keeps
the second-leg raw factorization as an explicit, reusable certificate boundary.
-/

/-- Helper for Infrastructure I.16a: the canonical first normalized displacement has explicit
quadratic germs in both coordinate directions. -/
theorem firstNormalizedDisplacement_coordinate_quadraticGerms
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦
          (CenterRaw.firstNormalizedDisplacement θ.1 r
            (2 + θ.2.1 * θ.1 * r)) 0)
        0 (-2) (4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) ∧
      HasQuadraticGerm
        (fun r ↦
          (CenterRaw.firstNormalizedDisplacement θ.1 r
            (2 + θ.2.1 * θ.1 * r)) 1)
        (-2) (4 * θ.1 - 2 * θ.2.1 * θ.1 / 3)
          (2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) := by
  let b : ℝ := θ.1
  let P : ℝ := θ.2.1
  let radius : ℝ → ℝ := fun r ↦ r
  let p : ℝ → ℝ := fun r ↦ 2 + P * b * r
  let numerator : ℝ → ℝ := fun r ↦ -(2 / 3 : ℝ) * (p r + 1)
  let denominator : ℝ → ℝ := fun r ↦ 1 + 2 * b * r + r ^ 2
  let alpha : ℝ → ℝ := fun r ↦ numerator r / denominator r
  have hradius : HasQuadraticGerm radius 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [radius, quadraticModel]
  have hp : HasQuadraticGerm p 2 (P * b) 0 := by
    have hmodel := HasQuadraticGerm.model 2 (P * b) 0
    apply hmodel.congrFunction
    intro r
    simp [p, quadraticModel]
  have hpPlus : HasQuadraticGerm (fun r ↦ p r + 1) 3 (P * b) 0 := by
    have hone := HasQuadraticGerm.model 1 0 0
    have hsum := hp.add hone
    have hsumConstant : 2 + 1 = (3 : ℝ) := by ring
    have hsumLinear : P * b + 0 = P * b := by ring
    have hsumQuadratic : 0 + 0 = (0 : ℝ) := by ring
    have hsumCoeff := hsum.congrCoefficients
      hsumConstant hsumLinear hsumQuadratic
    have hsumPath : ∀ r : ℝ,
        p r + 1 = p r + quadraticModel 1 0 0 r := by
      intro r
      simp [quadraticModel]
    exact hsumCoeff.congrFunction hsumPath
  have hnumRaw := hpPlus.constMul (-(2 / 3 : ℝ))
  have hnumConstant : (-(2 / 3 : ℝ) * 3) = (-2 : ℝ) := by ring
  have hnumLinear : -(2 / 3 : ℝ) * (P * b) = -(2 / 3 : ℝ) * (P * b) := rfl
  have hnumQuadratic : -(2 / 3 : ℝ) * 0 = (0 : ℝ) := by ring
  have hnumCoeff := hnumRaw.congrCoefficients
    hnumConstant hnumLinear hnumQuadratic
  have hnumPath : ∀ r : ℝ,
      numerator r = -(2 / 3 : ℝ) * (p r + 1) := by
    intro r
    rfl
  have hnum : HasQuadraticGerm numerator (-2) (-(2 / 3 : ℝ) * (P * b)) 0 :=
    hnumCoeff.congrFunction hnumPath
  have hradiusSquareRaw := hradius.mul hradius
  have hradiusSquarePath : ∀ r : ℝ, radius r * radius r = r ^ 2 := by
    intro r
    simp [radius]
    ring
  have hradiusSquare := hradiusSquareRaw.congrFunction
    (fun r ↦ (hradiusSquarePath r).symm)
  have hdenBase := HasQuadraticGerm.model 1 0 0
  have hdenLinear := hradius.constMul (2 * b)
  have hdenRaw := hdenBase.add hdenLinear
  have hdenRaw' := hdenRaw.add hradiusSquare
  have hdenConstantCoeff : 1 + 2 * b * 0 + 0 * 0 = (1 : ℝ) := by ring
  have hdenLinearCoeff : 0 + 2 * b * 1 + (0 * 1 + 1 * 0) = 2 * b := by ring
  have hdenQuadraticCoeff :
      0 + 2 * b * 0 + (0 * 0 + 1 * 1 + 0 * 0) = (1 : ℝ) := by ring
  have hdenCoeff := hdenRaw'.congrCoefficients
    hdenConstantCoeff hdenLinearCoeff hdenQuadraticCoeff
  have hdenRawPath : ∀ r : ℝ,
      denominator r = quadraticModel 1 0 0 r + 2 * b * radius r + r ^ 2 := by
    intro r
    simp [denominator, radius, quadraticModel]
  have hden : HasQuadraticGerm denominator 1 (2 * b) 1 :=
    hdenCoeff.congrFunction hdenRawPath
  have hdenPath : ∀ r : ℝ, denominator r =
      1 + 2 * b * r + r ^ 2 := by
    intro r
    rfl
  have hden' := hden.congrFunction hdenPath
  have hden0 : (1 : ℝ) ≠ 0 := by norm_num
  have halphaRaw := hnum.div hden' hden0
  have halpha : HasQuadraticGerm alpha (-2)
      (4 * b - 2 * P * b / 3)
      (2 + b ^ 2 * (4 * P / 3 - 8)) := by
    apply halphaRaw.congrCoefficients
    · norm_num
    · ring
    · ring
  have halphaPath : ∀ r : ℝ,
      alpha r = (-(2 / 3 : ℝ) *
        (2 + P * b * r + 1)) / (1 + 2 * b * r + r ^ 2) := by
    intro r
    rfl
  have hcoord0Raw := halpha.mul hradius
  let coordinate0 : ℝ → ℝ := fun r ↦
    (CenterRaw.firstNormalizedDisplacement b r (2 + P * b * r)) 0
  have hcoord0Path : ∀ r : ℝ, coordinate0 r = alpha r * radius r := by
    intro r
    simp [coordinate0, alpha, numerator, denominator, p, radius,
      CenterRaw.firstNormalizedDisplacement]
  have hcoord0Raw' := hcoord0Raw.congrFunction hcoord0Path
  have hcoord0 : HasQuadraticGerm coordinate0 0 (-2)
      (4 * b - 2 * P * b / 3) := by
    apply hcoord0Raw'.congrCoefficients
    · ring
    · ring
    · ring
  let coordinate1 : ℝ → ℝ := fun r ↦
    (CenterRaw.firstNormalizedDisplacement b r (2 + P * b * r)) 1
  have hcoord1Path : ∀ r : ℝ, coordinate1 r = alpha r := by
    intro r
    simp [coordinate1, alpha, numerator, denominator, p,
      CenterRaw.firstNormalizedDisplacement]
  have hcoord1 := halpha.congrFunction hcoord1Path
  have hcoord0' : HasQuadraticGerm
      (fun r ↦
        (CenterRaw.firstNormalizedDisplacement θ.1 r
          (2 + θ.2.1 * θ.1 * r)) 0)
      0 (-2) (4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) := by
    have hzero : (0 : ℝ) = 0 := rfl
    have hlinear : (-2 : ℝ) = -2 := rfl
    have hquadratic : 4 * b - 2 * P * b / 3 =
        4 * θ.1 - 2 * θ.2.1 * θ.1 / 3 := by
      dsimp [b, P]
    exact hcoord0.congrCoefficients hzero hlinear hquadratic
  have hcoord1' : HasQuadraticGerm
      (fun r ↦
        (CenterRaw.firstNormalizedDisplacement θ.1 r
          (2 + θ.2.1 * θ.1 * r)) 1)
      (-2) (4 * θ.1 - 2 * θ.2.1 * θ.1 / 3)
        (2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) := by
    have hzero : -2 = (-2 : ℝ) := rfl
    have hlinear : 4 * b - 2 * P * b / 3 =
        4 * θ.1 - 2 * θ.2.1 * θ.1 / 3 := by
      dsimp [b, P]
    have hquadratic : 2 + b ^ 2 * (4 * P / 3 - 8) =
        2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8) := by
      dsimp [b, P]
    exact hcoord1.congrCoefficients hzero hlinear hquadratic
  exact ⟨hcoord0', hcoord1'⟩

/-- Helper for Infrastructure I.16a: a scalar second-leg factor germ and two coordinate
factor germs produce the quadratic germs of the normalized second displacement. -/
theorem secondNormalizedDisplacement_coordinate_quadraticGerms_of_factorCertificate
    {b : ℝ} {L H Q U alpha x y : ℝ → ℝ}
    {a₀ a₁ a₂ x₀ x₁ x₂ y₀ y₁ y₂ : ℝ}
    (halpha : HasQuadraticGerm alpha a₀ a₁ a₂)
    (hx : HasQuadraticGerm x x₀ x₁ x₂)
    (hy : HasQuadraticGerm y y₀ y₁ y₂)
    (hcoord0 : ∀ r : ℝ,
      (CenterRaw.secondNormalizedDisplacement b r (L r) (H r) (Q r) (U r)) 0 =
        alpha r * x r)
    (hcoord1 : ∀ r : ℝ,
      (CenterRaw.secondNormalizedDisplacement b r (L r) (H r) (Q r) (U r)) 1 =
        alpha r * y r) :
    HasQuadraticGerm
        (fun r ↦
          (CenterRaw.secondNormalizedDisplacement b r (L r) (H r) (Q r) (U r)) 0)
        (a₀ * x₀) (a₀ * x₁ + a₁ * x₀)
          (a₀ * x₂ + a₁ * x₁ + a₂ * x₀) ∧
      HasQuadraticGerm
        (fun r ↦
          (CenterRaw.secondNormalizedDisplacement b r (L r) (H r) (Q r) (U r)) 1)
        (a₀ * y₀) (a₀ * y₁ + a₁ * y₀)
          (a₀ * y₂ + a₁ * y₁ + a₂ * y₀) := by
  have hprod0 := halpha.mul hx
  have hprod1 := halpha.mul hy
  have hcoord0' := hprod0.congrFunction hcoord0
  have hcoord1' := hprod1.congrFunction hcoord1
  exact ⟨hcoord0', hcoord1'⟩

end DFP.TwoLeg.Mixed
