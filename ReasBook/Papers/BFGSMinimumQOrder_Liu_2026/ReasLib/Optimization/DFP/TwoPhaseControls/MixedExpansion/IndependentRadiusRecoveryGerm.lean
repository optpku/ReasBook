module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondFactorGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondFactorGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Appendix Lemma A.6: the recovered radius factor has the explicit quadratic
germ obtained from the four second-leg factor germs. -/
theorem independentRadiusRecoveryFactorQuadraticGerm
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
      (fun r ↦
        (independentRadiusSecondSpectral (θ, r)).1 *
          (independentRadiusSecondGradient (θ, r)).1 /
          ((independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2))
      1 (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18)
      (-(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
          1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162) := by
  obtain ⟨hsLow, hsHigh, hgLow, hgHigh⟩ :=
    independentRadiusSecondFactorQuadraticGerms θ
  have hfactor := recoveryRadiusQuadraticGerm_of_componentGerms
    hsLow hsHigh hgLow hgHigh
  have hconstant : (1 : ℝ) = 1 := by
    rfl
  have hlinear :
      (2 * 0 + θ.1 * (2 * θ.2.2 + θ.2.1 - 12) -
        (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 + 2 * (8 * θ.1))) / 2 =
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18 := by
    ring
  have hquadratic :
      (2 * (2 * ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
          384 * θ.1 ^ 2 - 117) / 18) +
          θ.1 * (2 * θ.2.2 + θ.2.1 - 12) * 0 +
          (3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 - 84 * θ.2.2 * θ.1 ^ 2 -
            26 * θ.2.1 * θ.1 ^ 2 - 510 * θ.1 ^ 2 + 30) / 3) -
        (2 * 0 + θ.1 * (2 * θ.2.2 + θ.2.1 - 12)) *
          (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 + 2 * (8 * θ.1)) +
        (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 + 2 * (8 * θ.1)) ^ 2 -
        2 * ((6 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 216 * θ.2.2 * θ.1 ^ 2 -
            2 * θ.2.1 ^ 2 * θ.1 ^ 2 + 12 * θ.2.1 * θ.1 ^ 2 -
            756 * θ.1 ^ 2 - 243) / 27 +
          (8 * θ.1) * (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) +
          2 * (4 * θ.1 ^ 2 * (6 * θ.2.2 + θ.2.1 + 78) / 3))) / 4 =
      -(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
          1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162 := by
    ring
  exact hfactor.congrCoefficients hconstant hlinear hquadratic

/-- Appendix Lemma A.6: multiplying the recovered radius factor by the
independent radius yields the quadratic germ of the recovered radius path. -/
theorem independentRadiusRecoveredRadiusQuadraticGerm
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
      (fun r ↦ r *
        ((independentRadiusSecondSpectral (θ, r)).1 *
          (independentRadiusSecondGradient (θ, r)).1 /
          ((independentRadiusSecondSpectral (θ, r)).2 *
            (independentRadiusSecondGradient (θ, r)).2)))
      0 1 (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) := by
  obtain ⟨hsLow, hsHigh, hgLow, hgHigh⟩ :=
    independentRadiusSecondFactorQuadraticGerms θ
  have hpath := recoveryRadiusPathQuadraticGerm_of_componentGerms
    hsLow hsHigh hgLow hgHigh
  have hconstant : (0 : ℝ) = 0 := by
    rfl
  have hlinear : (1 : ℝ) = 1 := by
    rfl
  have hquadratic :
      (2 * 0 + θ.1 * (2 * θ.2.2 + θ.2.1 - 12) -
        (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 + 2 * (8 * θ.1))) / 2 =
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18 := by
    ring
  exact hpath.congrCoefficients hconstant hlinear hquadratic

end DFP.TwoLeg.Mixed
