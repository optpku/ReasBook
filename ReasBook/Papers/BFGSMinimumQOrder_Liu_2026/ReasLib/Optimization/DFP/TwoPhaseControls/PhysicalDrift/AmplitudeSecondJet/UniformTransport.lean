module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.RecoveredRadius
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.RecoveredRadius
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: the linear coefficient of the recovered-radius
    physical amplitude germ. -/
def physicalAmplitudeLinearCoefficient (θ : ℝ × ℝ × ℝ) : ℝ :=
  θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18

/-- Helper for Appendix Lemma A.6: the quadratic coefficient of the recovered-radius
    physical amplitude germ. -/
def physicalAmplitudeQuadraticCoefficient (θ : ℝ × ℝ × ℝ) : ℝ :=
  -(36 * θ.2.2 ^ 2 * θ.1 ^ 2 - 21 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
      3636 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.1 ^ 2 * θ.1 ^ 2 +
      1158 * θ.2.1 * θ.1 ^ 2 - 450 * θ.1 ^ 2 - 486) / 162

/-- Appendix Lemma A.6: eventual equality with the recovered-radius projection and joint
    `C³` regularity produce the three-term physical-amplitude germ needed for a cubic
    uniform remainder. -/
theorem physicalAmplitudeTruncatedGerm_of_recoveredRadius
    {amplitude : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry amplitude) (θ, 0))
    (hphysical : ∀ θ, θ ∈ K →
      amplitude θ =ᶠ[𝓝 0]
        (fun r ↦
          (independentRadiusSecondSpectral (θ, r)).1 *
              (independentRadiusSecondGradient (θ, r)).1 /
            ((independentRadiusSecondSpectral (θ, r)).2 *
              (independentRadiusSecondGradient (θ, r)).2))) :
    IndependentRadiusTruncatedGerm amplitude K 3
      (fun n θ ↦
        (![1, physicalAmplitudeLinearCoefficient θ,
          physicalAmplitudeQuadraticCoefficient θ] : Fin 3 → ℝ) n) := by
  have hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm (amplitude θ) 1
        (physicalAmplitudeLinearCoefficient θ)
        (physicalAmplitudeQuadraticCoefficient θ) := by
    intro θ hθ
    have hsliceMap : ContDiffAt ℝ 3 (fun r : ℝ ↦ (θ, r)) 0 := by
      fun_prop
    have hslice : ContDiffAt ℝ 3 (amplitude θ) 0 := by
      have hcomp := (hregular θ hθ).comp 0 hsliceMap
      have hfun : (Function.uncurry amplitude ∘ Prod.mk θ) = amplitude θ := by
        funext r
        rfl
      rw [hfun] at hcomp
      exact hcomp
    have hquadratic := physicalAmplitudeQuadraticGerm_of_recoveredRadius
      θ (hphysical θ hθ) hslice.continuousAt
    simpa only [physicalAmplitudeLinearCoefficient,
      physicalAmplitudeQuadraticCoefficient] using hquadratic
  exact independentRadiusTruncatedGerm_of_quadraticGerms hregular hgerm

/-- Helper for Appendix Lemma A.6: the physical-amplitude truncated germ yields the
    explicit compact-uniform cubic remainder used by the amplitude expansion. -/
theorem physicalAmplitudeRemainderOn_of_recoveredRadius
    {amplitude : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K)
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry amplitude) (θ, 0))
    (hphysical : ∀ θ, θ ∈ K →
      amplitude θ =ᶠ[𝓝 0]
        (fun r ↦
          (independentRadiusSecondSpectral (θ, r)).1 *
              (independentRadiusSecondGradient (θ, r)).1 /
            ((independentRadiusSecondSpectral (θ, r)).2 *
              (independentRadiusSecondGradient (θ, r)).2))) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ amplitude θ r - 1 -
        physicalAmplitudeLinearCoefficient θ * r -
        physicalAmplitudeQuadraticCoefficient θ * r ^ 2) K C 3 := by
  have hGerm := physicalAmplitudeTruncatedGerm_of_recoveredRadius
    hregular hphysical
  have hthreePos : 0 < (3 : ℕ) := by
    norm_num
  obtain ⟨C, hC, hraw⟩ := uniformRemainderOn_of_independentRadiusTruncatedGerm
    hthreePos hK hGerm
  refine ⟨C, hC, ?_⟩
  convert hraw using 1
  · funext θ r
    simp [Fin.sum_univ_succ, physicalAmplitudeLinearCoefficient,
      physicalAmplitudeQuadraticCoefficient]
    ring
  · norm_num

end DFP.TwoLeg.Mixed
