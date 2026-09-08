module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion gives the quadratic interface for the canonical low eigenframe at the
diagonal base.  It is deliberately independent of the physical evaluator: downstream
center and angle proofs can consume the two first-column entries without unfolding the
normalization construction.
-/

/-- Helper for Infrastructure I.16a: the first two coordinates of a symmetric-matrix
path are assembled into a quadratic germ for its low eigenvector. -/
theorem lowVector_coordinate_quadraticGerms
    {a b d : ℝ → ℝ}
    {a₁ a₂ b₁ b₂ d₁ d₂ : ℝ}
    (ha : HasQuadraticGerm a 0 a₁ a₂)
    (hb : HasQuadraticGerm b 0 b₁ b₂)
    (hd : HasQuadraticGerm d 1 d₁ d₂) :
    HasQuadraticGerm
        (fun r ↦ RealSymmetric2.lowVector (a r) (b r) (d r) 0)
        1 0 (-b₁ ^ 2 / 2) ∧
      HasQuadraticGerm
        (fun r ↦ RealSymmetric2.lowVector (a r) (b r) (d r) 1)
        0 (-b₁) (-b₂ + (d₁ - a₁) * b₁) := by
  let delta : ℝ → ℝ := fun r ↦ d r - a r
  have hdeltaRaw := hd.sub ha
  have hdeltaPath : ∀ r : ℝ, delta r = d r - a r := by
    intro r
    rfl
  have hdelta := hdeltaRaw.congrFunction hdeltaPath
  have hdelta' : HasQuadraticGerm delta (1 - 0) (d₁ - a₁) (d₂ - a₂) := by
    have hzero : (1 - 0 : ℝ) = 1 - 0 := rfl
    have hlinear : (d₁ - a₁ : ℝ) = d₁ - a₁ := rfl
    have hquadratic : (d₂ - a₂ : ℝ) = d₂ - a₂ := rfl
    exact hdelta.congrCoefficients hzero hlinear hquadratic
  have hbSquareRaw := hb.mul hb
  have hbSquarePath : ∀ r : ℝ, b r * b r = b r ^ 2 := by
    intro r
    ring
  have hbSquare := hbSquareRaw.congrFunction (fun r ↦ (hbSquarePath r).symm)
  have hbSquare' : HasQuadraticGerm (fun r ↦ b r ^ 2) 0 0 (b₁ ^ 2) := by
    have hzero : (0 * 0 : ℝ) = 0 := by ring
    have hlinear : (0 * b₁ + b₁ * 0 : ℝ) = 0 := by ring
    have hquadratic : (0 * b₂ + b₁ * b₁ + b₂ * 0 : ℝ) = b₁ ^ 2 := by ring
    exact hbSquare.congrCoefficients hzero hlinear hquadratic
  let discriminant : ℝ → ℝ := fun r ↦ delta r ^ 2 + 4 * b r ^ 2
  have hdeltaSquareRaw := hdelta'.mul hdelta'
  have hdeltaSquarePath : ∀ r : ℝ, delta r * delta r = delta r ^ 2 := by
    intro r
    ring
  have hdeltaSquare := hdeltaSquareRaw.congrFunction (fun r ↦ (hdeltaSquarePath r).symm)
  have hdiscRaw := hdeltaSquare.add (hbSquare'.constMul 4)
  have hdiscPath : ∀ r : ℝ,
      discriminant r = delta r ^ 2 + 4 * b r ^ 2 := by
    intro r
    rfl
  have hdiscCoeff := hdiscRaw.congrFunction hdiscPath
  have hdisc : HasQuadraticGerm discriminant 1
      (2 * (d₁ - a₁))
      (2 * (d₂ - a₂) + (d₁ - a₁) ^ 2 + 4 * b₁ ^ 2) := by
    apply hdiscCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let gapPath : ℝ → ℝ := fun r ↦ Real.sqrt (discriminant r)
  have hgapRaw := hdisc.sqrtOne
  have hgapPathEq : ∀ r : ℝ, gapPath r = Real.sqrt (discriminant r) := by
    intro r
    rfl
  have hgapCoeff := hgapRaw.congrFunction hgapPathEq
  have hgap : HasQuadraticGerm gapPath 1
      (d₁ - a₁)
      (d₂ - a₂ + 2 * b₁ ^ 2) := by
    apply hgapCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let lowPath : ℝ → ℝ := fun r ↦
    (a r + d r - gapPath r) / 2
  have hsum := ha.add hd
  have hsumPath : ∀ r : ℝ, a r + d r = a r + d r := by
    intro r
    rfl
  have hsum' := hsum.congrFunction hsumPath
  have hlowRaw := (hsum'.sub hgap).constMul (1 / 2 : ℝ)
  have hlowPathEq : ∀ r : ℝ,
      lowPath r = (1 / 2 : ℝ) * (a r + d r - gapPath r) := by
    intro r
    simp [lowPath]
    ring
  have hlowCoeff := hlowRaw.congrFunction hlowPathEq
  have hlow : HasQuadraticGerm lowPath 0 a₁ (a₂ - b₁ ^ 2) := by
    apply hlowCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let firstCoordinate : ℝ → ℝ := fun r ↦ d r - lowPath r
  have hfirstRaw := hd.sub hlow
  have hfirstPath : ∀ r : ℝ, firstCoordinate r = d r - lowPath r := by
    intro r
    rfl
  have hfirstCoeff := hfirstRaw.congrFunction hfirstPath
  have hfirst : HasQuadraticGerm firstCoordinate 1
      (d₁ - a₁) (d₂ - a₂ + b₁ ^ 2) := by
    apply hfirstCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let denominatorRad : ℝ → ℝ := fun r ↦ firstCoordinate r ^ 2 + b r ^ 2
  have hfirstSquareRaw := hfirst.mul hfirst
  have hfirstSquarePath : ∀ r : ℝ,
      firstCoordinate r * firstCoordinate r = firstCoordinate r ^ 2 := by
    intro r
    ring
  have hfirstSquare := hfirstSquareRaw.congrFunction (fun r ↦ (hfirstSquarePath r).symm)
  have hdenomRadRaw := hfirstSquare.add hbSquare'
  have hdenomRadPath : ∀ r : ℝ,
      denominatorRad r = firstCoordinate r ^ 2 + b r ^ 2 := by
    intro r
    rfl
  have hdenomRadCoeff := hdenomRadRaw.congrFunction hdenomRadPath
  have hdenomRad : HasQuadraticGerm denominatorRad 1
      (2 * (d₁ - a₁))
      (2 * (d₂ - a₂) + (d₁ - a₁) ^ 2 + 3 * b₁ ^ 2) := by
    apply hdenomRadCoeff.congrCoefficients
    · ring
    · ring
    · ring
  let denominator : ℝ → ℝ := fun r ↦ Real.sqrt (denominatorRad r)
  have hdenomRaw := hdenomRad.sqrtOne
  have hdenomPathEq : ∀ r : ℝ, denominator r = Real.sqrt (denominatorRad r) := by
    intro r
    rfl
  have hdenomCoeff := hdenomRaw.congrFunction hdenomPathEq
  have hdenom : HasQuadraticGerm denominator 1
      (d₁ - a₁) (d₂ - a₂ + (3 / 2 : ℝ) * b₁ ^ 2) := by
    apply hdenomCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hdenomNonzero : (1 : ℝ) ≠ 0 := by norm_num
  have hdenomInvRaw := hdenom.inv hdenomNonzero
  have hdenomInv : HasQuadraticGerm (fun r ↦ (denominator r)⁻¹) 1
      (-(d₁ - a₁))
      ((d₁ - a₁) ^ 2 - (d₂ - a₂ + (3 / 2 : ℝ) * b₁ ^ 2)) := by
    apply hdenomInvRaw.congrCoefficients
    · ring
    · ring
    · ring
  let rawFirst : ℝ → ℝ := firstCoordinate
  let rawSecond : ℝ → ℝ := fun r ↦ -b r
  have hrawFirst : HasQuadraticGerm rawFirst 1
      (d₁ - a₁) (d₂ - a₂ + b₁ ^ 2) := by
    simpa only [rawFirst] using hfirst
  have hrawSecond : HasQuadraticGerm rawSecond 0 (-b₁) (-b₂) := by
    have hneg := hb.neg
    have hzero : (-0 : ℝ) = 0 := by ring
    have hlinear : (-b₁ : ℝ) = -b₁ := rfl
    have hquadratic : (-b₂ : ℝ) = -b₂ := rfl
    exact hneg.congrCoefficients hzero hlinear hquadratic
  have hcoordFirstRaw := hdenomInv.mul hrawFirst
  have hcoordSecondRaw := hdenomInv.mul hrawSecond
  let coordinateFirst : ℝ → ℝ := fun r ↦ (denominator r)⁻¹ * rawFirst r
  let coordinateSecond : ℝ → ℝ := fun r ↦ (denominator r)⁻¹ * rawSecond r
  have hcoordFirstPath : ∀ r : ℝ,
      coordinateFirst r = (denominator r)⁻¹ * rawFirst r := by
    intro r
    rfl
  have hcoordSecondPath : ∀ r : ℝ,
      coordinateSecond r = (denominator r)⁻¹ * rawSecond r := by
    intro r
    rfl
  have hcoordFirstCoeff := hcoordFirstRaw.congrFunction hcoordFirstPath
  have hcoordSecondCoeff := hcoordSecondRaw.congrFunction hcoordSecondPath
  have hcoordFirst : HasQuadraticGerm coordinateFirst 1 0 (-b₁ ^ 2 / 2) := by
    apply hcoordFirstCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hcoordSecond : HasQuadraticGerm coordinateSecond 0 (-b₁)
      (-b₂ + (d₁ - a₁) * b₁) := by
    apply hcoordSecondCoeff.congrCoefficients
    · ring
    · ring
    · ring
  have hlowPointwise : ∀ r : ℝ,
      RealSymmetric2.low (a r) (b r) (d r) = lowPath r := by
    intro r
    simp [RealSymmetric2.low, RealSymmetric2.gap, lowPath, gapPath,
      discriminant, delta]
  have hdenominatorPointwise : ∀ r : ℝ,
      RealSymmetric2.lowDenom (a r) (b r) (d r) = denominator r := by
    intro r
    rw [RealSymmetric2.lowDenom_apply]
    rw [hlowPointwise r]
  constructor
  · apply hcoordFirst.congrFunction
    intro r
    change (RealSymmetric2.lowDenom (a r) (b r) (d r))⁻¹ *
      (d r - RealSymmetric2.low (a r) (b r) (d r)) = coordinateFirst r
    rw [hlowPointwise r]
    rw [hdenominatorPointwise r]
  · apply hcoordSecond.congrFunction
    intro r
    change (RealSymmetric2.lowDenom (a r) (b r) (d r))⁻¹ *
      (-b r) = coordinateSecond r
    rw [hdenominatorPointwise r]

/-- Helper for Infrastructure I.16a: quadratic germs for a symmetric-matrix path determine all
four entries of its canonical low eigenframe at the diagonal base. -/
theorem lowFrame_entry_quadraticGerms
    {a b d : ℝ → ℝ}
    {a₁ a₂ b₁ b₂ d₁ d₂ : ℝ}
    (ha : HasQuadraticGerm a 0 a₁ a₂)
    (hb : HasQuadraticGerm b 0 b₁ b₂)
    (hd : HasQuadraticGerm d 1 d₁ d₂) :
    HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector (a r) (b r) (d r)) 0 0)
        1 0 (-b₁ ^ 2 / 2) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector (a r) (b r) (d r)) 0 1)
        0 b₁ (b₂ - (d₁ - a₁) * b₁) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector (a r) (b r) (d r)) 1 0)
        0 (-b₁) (-b₂ + (d₁ - a₁) * b₁) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector (a r) (b r) (d r)) 1 1)
        1 0 (-b₁ ^ 2 / 2) := by
  obtain ⟨hfirst, hsecond⟩ := lowVector_coordinate_quadraticGerms ha hb hd
  have h00 : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector (a r) (b r) (d r)) 0 0)
      1 0 (-b₁ ^ 2 / 2) := by
    apply hfirst.congrFunction
    intro r
    simp [EuclideanPlane.frame]
  have h10 : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector (a r) (b r) (d r)) 1 0)
      0 (-b₁) (-b₂ + (d₁ - a₁) * b₁) := by
    apply hsecond.congrFunction
    intro r
    simp [EuclideanPlane.frame]
  have h01Raw := hsecond.neg
  have h01Coeff : HasQuadraticGerm
      (fun r ↦ -RealSymmetric2.lowVector (a r) (b r) (d r) 1)
      0 b₁ (b₂ - (d₁ - a₁) * b₁) := by
    apply h01Raw.congrCoefficients
    · ring
    · ring
    · ring
  have h01 : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector (a r) (b r) (d r)) 0 1)
      0 b₁ (b₂ - (d₁ - a₁) * b₁) := by
    apply h01Coeff.congrFunction
    intro r
    simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
  have h11 : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector (a r) (b r) (d r)) 1 1)
      1 0 (-b₁ ^ 2 / 2) := by
    apply hfirst.congrFunction
    intro r
    simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
  exact ⟨h00, h01, h10, h11⟩

/-- Helper for Infrastructure I.16a: the independent-radius first metric triple
inherits a concrete quadratic germ for every canonical low-frame entry. -/
theorem independentRadiusFirstFrameQuadraticGerms (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple (θ, r)).1
            (independentRadiusFirstMetricTriple (θ, r)).2.1
            (independentRadiusFirstMetricTriple (θ, r)).2.2) 0 0)
        1 0 (-1 / 2) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple (θ, r)).1
            (independentRadiusFirstMetricTriple (θ, r)).2.1
            (independentRadiusFirstMetricTriple (θ, r)).2.2) 0 1)
        0 1 (-2 * θ.1) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple (θ, r)).1
            (independentRadiusFirstMetricTriple (θ, r)).2.1
            (independentRadiusFirstMetricTriple (θ, r)).2.2) 1 0)
        0 (-1) (2 * θ.1) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple (θ, r)).1
            (independentRadiusFirstMetricTriple (θ, r)).2.1
            (independentRadiusFirstMetricTriple (θ, r)).2.2) 1 1)
        1 0 (-1 / 2) := by
  obtain ⟨hA, hC, hD, _, _⟩ :=
    independentFirstResidualQuadraticGerms θ.1 θ.2.1 θ.2.2
  have hRadius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [quadraticModel]
  have hRadiusSquareRaw := hRadius.mul hRadius
  have hRadiusSquarePath : ∀ r : ℝ, r * r = r ^ 2 := by
    intro r
    ring
  have hRadiusSquare := hRadiusSquareRaw.congrFunction
    (fun r ↦ (hRadiusSquarePath r).symm)
  have hRadiusSquare' : HasQuadraticGerm (fun r : ℝ ↦ r ^ 2) 0 0 1 := by
    have hzero : (0 * 0 : ℝ) = 0 := by ring
    have hlinear : (0 * 1 + 1 * 0 : ℝ) = 0 := by ring
    have hquadratic : (0 * 0 + 1 * 1 + 0 * 0 : ℝ) = 1 := by ring
    exact hRadiusSquare.congrCoefficients hzero hlinear hquadratic
  have hmetricARaw := hRadiusSquare'.mul hA
  have hmetricAPath : ∀ r : ℝ,
      (fun s : ℝ ↦ s ^ 2 *
        (independentFirstResiduals θ.1 s
          (2 + θ.2.1 * θ.1 * s) (1 + θ.2.2 * θ.1 * s)).1) r =
        (independentRadiusFirstMetricTriple (θ, r)).1 := by
    intro r
    rfl
  have hmetricA := hmetricARaw.congrFunction hmetricAPath
  have hmetricA' : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstMetricTriple (θ, r)).1) 0 0 3 := by
    apply hmetricA.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricCRaw := hRadius.mul hC
  have hmetricCPath : ∀ r : ℝ,
      (fun s : ℝ ↦ s *
        (independentFirstResiduals θ.1 s
          (2 + θ.2.1 * θ.1 * s) (1 + θ.2.2 * θ.1 * s)).2.1) r =
        (independentRadiusFirstMetricTriple (θ, r)).2.1 := by
    intro r
    rfl
  have hmetricC := hmetricCRaw.congrFunction hmetricCPath
  have hmetricC' : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstMetricTriple (θ, r)).2.1)
      0 1 (-4 * θ.1) := by
    apply hmetricC.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricDPath : ∀ r : ℝ,
      (independentFirstResiduals θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)).2.2 =
        (independentRadiusFirstMetricTriple (θ, r)).2.2 := by
    intro r
    rfl
  have hmetricD := hD.congrFunction hmetricDPath
  have hmetricD' : HasQuadraticGerm
      (fun r ↦ (independentRadiusFirstMetricTriple (θ, r)).2.2)
      1 (-2 * θ.1) (6 * θ.1 ^ 2 - 1) := by
    apply hmetricD.congrCoefficients
    · ring
    · ring
    · ring
  have hframe := lowFrame_entry_quadraticGerms hmetricA' hmetricC' hmetricD'
  rcases hframe with ⟨h00, h01, h10, h11⟩
  have h00' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusFirstMetricTriple (θ, r)).1
          (independentRadiusFirstMetricTriple (θ, r)).2.1
          (independentRadiusFirstMetricTriple (θ, r)).2.2) 0 0)
      1 0 (-1 / 2) := by
    apply h00.congrCoefficients
    · ring
    · ring
    · ring
  have h01' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusFirstMetricTriple (θ, r)).1
          (independentRadiusFirstMetricTriple (θ, r)).2.1
          (independentRadiusFirstMetricTriple (θ, r)).2.2) 0 1)
      0 1 (-2 * θ.1) := by
    apply h01.congrCoefficients
    · ring
    · ring
    · ring
  have h10' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusFirstMetricTriple (θ, r)).1
          (independentRadiusFirstMetricTriple (θ, r)).2.1
          (independentRadiusFirstMetricTriple (θ, r)).2.2) 1 0)
      0 (-1) (2 * θ.1) := by
    apply h10.congrCoefficients
    · ring
    · ring
    · ring
  have h11' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusFirstMetricTriple (θ, r)).1
          (independentRadiusFirstMetricTriple (θ, r)).2.1
          (independentRadiusFirstMetricTriple (θ, r)).2.2) 1 1)
      1 0 (-1 / 2) := by
    apply h11.congrCoefficients
    · ring
    · ring
    · ring
  exact ⟨h00', h01', h10', h11'⟩

/-! The second-leg metric triple has the same low-frame interface, with the
second residual coefficients supplying the explicit linear and quadratic frame
terms needed by the center transport. -/

/-- Helper for Infrastructure I.16a: the independent-radius second metric triple
inherits a concrete quadratic germ for every canonical low-frame entry. -/
theorem independentRadiusSecondFrameQuadraticGerms (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusSecondMetricTriple (θ, r)).1
            (independentRadiusSecondMetricTriple (θ, r)).2.1
            (independentRadiusSecondMetricTriple (θ, r)).2.2) 0 0)
        1 0 (-2) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusSecondMetricTriple (θ, r)).1
            (independentRadiusSecondMetricTriple (θ, r)).2.1
            (independentRadiusSecondMetricTriple (θ, r)).2.2) 0 1)
        0 2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 36) / 3) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusSecondMetricTriple (θ, r)).1
            (independentRadiusSecondMetricTriple (θ, r)).2.1
            (independentRadiusSecondMetricTriple (θ, r)).2.2) 1 0)
        0 (-2) (-θ.1 * (6 * θ.2.2 + θ.2.1 + 36) / 3) ∧
      HasQuadraticGerm
        (fun r ↦ EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusSecondMetricTriple (θ, r)).1
            (independentRadiusSecondMetricTriple (θ, r)).2.1
            (independentRadiusSecondMetricTriple (θ, r)).2.2) 1 1)
        1 0 (-2) := by
  obtain ⟨hA, hC, hD, _, _⟩ := independentRadiusSecondComponentQuadraticGerms θ
  have hRadius : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [quadraticModel]
  have hRadiusSquareRaw := hRadius.mul hRadius
  have hRadiusSquarePath : ∀ r : ℝ, r * r = r ^ 2 := by
    intro r
    ring
  have hRadiusSquare := hRadiusSquareRaw.congrFunction
    (fun r ↦ (hRadiusSquarePath r).symm)
  have hRadiusSquare' : HasQuadraticGerm (fun r : ℝ ↦ r ^ 2) 0 0 1 := by
    have hzero : (0 * 0 : ℝ) = 0 := by ring
    have hlinear : (0 * 1 + 1 * 0 : ℝ) = 0 := by ring
    have hquadratic : (0 * 0 + 1 * 1 + 0 * 0 : ℝ) = 1 := by ring
    exact hRadiusSquare.congrCoefficients hzero hlinear hquadratic
  have hmetricARaw := hRadiusSquare'.mul hA
  have hmetricAPath : ∀ r : ℝ,
      (fun s : ℝ ↦ s ^ 2 *
        (independentSecondResiduals θ.1 s
          (independentRadiusFirstSpectral (θ, s)).1
          (independentRadiusFirstSpectral (θ, s)).2
          (independentRadiusFirstGradient (θ, s)).1
          (independentRadiusFirstGradient (θ, s)).2).1) r =
        (independentRadiusSecondMetricTriple (θ, r)).1 := by
    intro r
    rfl
  have hmetricA := hmetricARaw.congrFunction hmetricAPath
  have hmetricA' : HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondMetricTriple (θ, r)).1) 0 0 6 := by
    apply hmetricA.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricCRaw := hRadius.mul hC
  have hmetricCPath : ∀ r : ℝ,
      (fun s : ℝ ↦ s *
        (independentSecondResiduals θ.1 s
          (independentRadiusFirstSpectral (θ, s)).1
          (independentRadiusFirstSpectral (θ, s)).2
          (independentRadiusFirstGradient (θ, s)).1
          (independentRadiusFirstGradient (θ, s)).2).2.1) r =
        (independentRadiusSecondMetricTriple (θ, r)).2.1 := by
    intro r
    rfl
  have hmetricC := hmetricCRaw.congrFunction hmetricCPath
  have hmetricC' : HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondMetricTriple (θ, r)).2.1)
      0 2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
    apply hmetricC.congrCoefficients
    · ring
    · ring
    · ring
  have hmetricDPath : ∀ r : ℝ,
      (independentSecondResiduals θ.1 r
        (independentRadiusFirstSpectral (θ, r)).1
        (independentRadiusFirstSpectral (θ, r)).2
        (independentRadiusFirstGradient (θ, r)).1
        (independentRadiusFirstGradient (θ, r)).2).2.2 =
        (independentRadiusSecondMetricTriple (θ, r)).2.2 := by
    intro r
    rfl
  have hmetricD := hD.congrFunction hmetricDPath
  have hmetricD' : HasQuadraticGerm
      (fun r ↦ (independentRadiusSecondMetricTriple (θ, r)).2.2)
      1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    apply hmetricD.congrCoefficients
    · ring
    · ring
    · ring
  have hframe := lowFrame_entry_quadraticGerms hmetricA' hmetricC' hmetricD'
  rcases hframe with ⟨h00, h01, h10, h11⟩
  have h00' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusSecondMetricTriple (θ, r)).1
          (independentRadiusSecondMetricTriple (θ, r)).2.1
          (independentRadiusSecondMetricTriple (θ, r)).2.2) 0 0)
      1 0 (-2) := by
    apply h00.congrCoefficients
    · ring
    · ring
    · ring
  have h01' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusSecondMetricTriple (θ, r)).1
          (independentRadiusSecondMetricTriple (θ, r)).2.1
          (independentRadiusSecondMetricTriple (θ, r)).2.2) 0 1)
      0 2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 36) / 3) := by
    apply h01.congrCoefficients
    · ring
    · ring
    · ring
  have h10' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusSecondMetricTriple (θ, r)).1
          (independentRadiusSecondMetricTriple (θ, r)).2.1
          (independentRadiusSecondMetricTriple (θ, r)).2.2) 1 0)
      0 (-2) (-θ.1 * (6 * θ.2.2 + θ.2.1 + 36) / 3) := by
    apply h10.congrCoefficients
    · ring
    · ring
    · ring
  have h11' : HasQuadraticGerm
      (fun r ↦ EuclideanPlane.frame
        (RealSymmetric2.lowVector
          (independentRadiusSecondMetricTriple (θ, r)).1
          (independentRadiusSecondMetricTriple (θ, r)).2.1
          (independentRadiusSecondMetricTriple (θ, r)).2.2) 1 1)
      1 0 (-2) := by
    apply h11.congrCoefficients
    · ring
    · ring
    · ring
  exact ⟨h00', h01', h10', h11'⟩

end DFP.TwoLeg.Mixed
