module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.UniformTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.UniformTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryAdapter

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: the first recovery-factor coordinate is jointly
    finite-smooth along every compact parameter fiber. -/
theorem recoveredAmplitude_contDiffAt
    (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ 3
      (Function.uncurry
        (fun η r ↦ (independentRadiusRecoveryFactors (η, r)).1)) (θ, 0) := by
  have hrec := independentRadiusRecoveryFactors_analyticAt_of_secondFactors θ
  have hfirst := analyticAt_fst.comp hrec
  have hfun :
      Function.uncurry
          (fun η r ↦ (independentRadiusRecoveryFactors (η, r)).1) =
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusRecoveryFactors z).1) := by
    funext z
    rfl
  rw [hfun]
  exact hfirst.contDiffAt

/-- Appendix Lemma A.6: a physical amplitude projection with the recovered-radius
    eventual equality inherits the explicit three-term amplitude germ, while a paired
    frame-angle equality transports its supplied two-term germ at the same time. -/
theorem pairedObservableGerms_of_recoveredRadius_projection
    {K : Set (ℝ × ℝ × ℝ)}
    {angleNormalForm : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {angleCoeff : Fin 2 → (ℝ × ℝ × ℝ) → ℝ}
    (hamplitude : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry
          (fun η r ↦ (independentRadiusRecoveryFactors (η, r)).1)))
    (hangle : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).frameAngleIncrement) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry angleNormalForm))
    (hangleGerm : IndependentRadiusTruncatedGerm angleNormalForm K 2 angleCoeff) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) K 3
        (fun n θ ↦
          (![1, physicalAmplitudeLinearCoefficient θ,
            physicalAmplitudeQuadraticCoefficient θ] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement) K 2 angleCoeff := by
  have hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3
        (Function.uncurry
          (fun η r ↦ (independentRadiusRecoveryFactors (η, r)).1)) (θ, 0) := by
    intro θ hθ
    exact recoveredAmplitude_contDiffAt θ
  have hquadratic : ∀ θ, θ ∈ K →
      HasQuadraticGerm
        (fun r ↦ (independentRadiusRecoveryFactors (θ, r)).1) 1
        (physicalAmplitudeLinearCoefficient θ)
        (physicalAmplitudeQuadraticCoefficient θ) := by
    intro θ hθ
    have hfactor := independentRadiusRecoveryFactorQuadraticGerm θ
    simpa only [independentRadiusRecoveryFactors,
      physicalAmplitudeLinearCoefficient, physicalAmplitudeQuadraticCoefficient] using hfactor
  have hamplitudeGerm := independentRadiusTruncatedGerm_of_quadraticGerms
    hregular hquadratic
  exact pairedObservableGerms_of_uncurry_eventuallyEq
    hamplitude hangle hamplitudeGerm hangleGerm

end DFP.TwoLeg.Mixed
