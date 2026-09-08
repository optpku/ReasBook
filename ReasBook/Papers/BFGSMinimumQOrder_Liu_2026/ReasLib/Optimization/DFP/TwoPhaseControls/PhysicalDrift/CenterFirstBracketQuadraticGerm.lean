module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterDisplacementQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterDisplacementQuadraticGerm

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-- Helper for Infrastructure I.16a: the canonical first-leg low frame along a mixed
parameter-radius path. -/
def canonicalFirstFrame (θ : ℝ × ℝ × ℝ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  EuclideanPlane.frame
    (RealSymmetric2.lowVector
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2)

/-- Helper for Infrastructure I.16a: the canonical first-leg normalized displacement
along a mixed parameter-radius path. -/
def canonicalFirstNormalizedDisplacement (θ : ℝ × ℝ × ℝ) (r : ℝ) : Fin 2 → ℝ :=
  CenterRaw.firstNormalizedDisplacement θ.1 r
    (2 + θ.2.1 * θ.1 * r)

/-- Infrastructure I.16a: concrete first-frame and first-displacement germs combine with
any second-displacement coordinate germs into the scalar weighted center-bracket germ. -/
theorem canonicalFirstBracket_quadraticGerm
    (θ : ℝ × ℝ × ℝ)
    {uSecond : ℝ → Fin 2 → ℝ}
    {b₁ b₂ c₁ c₂ : ℝ}
    (hb : HasQuadraticGerm (fun r ↦ uSecond r 0) 0 b₁ b₂)
    (hc : HasQuadraticGerm (fun r ↦ uSecond r 1) (-1) c₁ c₂) :
    HasQuadraticGerm
      (fun r ↦
        (weightedCenterBracket
          (canonicalFirstFrame θ r)
          (canonicalFirstNormalizedDisplacement θ r)
          (uSecond r)) 0)
      0
      (-(4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) + 2 * c₁)
      (-(2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) +
        2 * (c₂ + 1 / 2 + b₁)) := by
  obtain ⟨hF00, hF01, _, _⟩ := independentRadiusFirstFrameQuadraticGerms θ
  obtain ⟨hu0, hu1⟩ := firstNormalizedDisplacement_coordinate_quadraticGerms θ
  have hF00' : HasQuadraticGerm
      (fun r ↦ (canonicalFirstFrame θ r) 0 0) 1 0 (-1 / 2) := by
    simpa only [canonicalFirstFrame] using hF00
  have hF01' : HasQuadraticGerm
      (fun r ↦ (canonicalFirstFrame θ r) 0 1) 0 1 (-2 * θ.1) := by
    simpa only [canonicalFirstFrame] using hF01
  have hu0' : HasQuadraticGerm
      (fun r ↦ (canonicalFirstNormalizedDisplacement θ r) 1) (-2)
        (4 * θ.1 - 2 * θ.2.1 * θ.1 / 3)
        (2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) := by
    simpa only [canonicalFirstNormalizedDisplacement] using hu1
  have hfirstRaw := hF00'.mul hc
  have hsecondRaw := hF01'.mul hb
  have hproductsRaw := hfirstRaw.add hsecondRaw
  have hscaledRaw := hproductsRaw.constMul 2
  have hnegative := hu0'.neg
  have hsumRaw := hnegative.add hscaledRaw
  have hconstant : -(-2 : ℝ) + 2 * (1 * (-1) + 0 * 0) = 0 := by
    ring
  have hlinear :
      -(4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) +
          2 * (1 * c₁ + 0 * (-1) + (0 * b₁ + 1 * 0)) =
        -(4 * θ.1 - 2 * θ.2.1 * θ.1 / 3) + 2 * c₁ := by
    ring
  have hquadratic :
      -(2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) +
          2 * (1 * c₂ + 0 * c₁ + (-1 / 2 : ℝ) * (-1) +
            (0 * b₂ + 1 * b₁ + (-2 * θ.1) * 0)) =
        -(2 + θ.1 ^ 2 * (4 * θ.2.1 / 3 - 8)) +
          2 * (c₂ + 1 / 2 + b₁) := by
    ring
  have hcoeff := hsumRaw.congrCoefficients hconstant hlinear hquadratic
  apply hcoeff.congrFunction
  intro r
  have hprojection :
      (weightedCenterBracket
          (canonicalFirstFrame θ r)
          (canonicalFirstNormalizedDisplacement θ r)
          (uSecond r)) 0 =
        -(canonicalFirstNormalizedDisplacement θ r 1) +
          2 * ((canonicalFirstFrame θ r) 0 0 * uSecond r 1 +
            (canonicalFirstFrame θ r) 0 1 * uSecond r 0) := by
    simp [weightedCenterBracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hprojection]

end DFP.TwoLeg.Mixed
