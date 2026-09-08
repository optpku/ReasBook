module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Analysis.Calculus.Analytic.RecoveryFactors
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Analysis.Calculus.Analytic.RecoveryFactors

public section

namespace DFP.TwoLeg.Mixed

/-! A small interface for the final algebraic recovery stage of the independent-radius
normal form.  The analytic construction of the two-leg factors remains upstream; this
module isolates the harmless quotient/product transport used after that construction. -/

/-- An analytic recovered-factor map gives an analytic
normal-form map after multiplying the radius coordinate into its first factor. -/
theorem independentRadiusNormalForm_analyticAt_of_recoveryFactors
    (θ : ℝ × ℝ × ℝ)
    (hrec : AnalyticAt ℝ independentRadiusRecoveryFactors (θ, 0)) :
    AnalyticAt ℝ (Function.uncurry independentRadiusNormalForm) (θ, 0) := by
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) :=
    analyticAt_snd
  have hρ : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        z.2 * (independentRadiusRecoveryFactors z).1) (θ, 0) := by
    exact hr.mul (analyticAt_fst.comp hrec)
  have hp : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusRecoveryFactors z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hrec)
  have hhigh : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusRecoveryFactors z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hrec)
  have htriple := hρ.prod (hp.prod hhigh)
  have hEq : (Function.uncurry independentRadiusNormalForm) =
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (z.2 * (independentRadiusRecoveryFactors z).1,
          (independentRadiusRecoveryFactors z).2.1,
          (independentRadiusRecoveryFactors z).2.2)) := by
    funext z
    exact independentRadiusNormalForm_eq_recoveryFactors z.1 z.2
  rw [hEq]
  exact htriple

/-- The analytic recovery interface yields finite smoothness
of the normal form at every order. -/
theorem independentRadiusNormalForm_contDiffAt_of_analyticRecovery
    (m : ℕ) (θ : ℝ × ℝ × ℝ)
    (hrec : AnalyticAt ℝ independentRadiusRecoveryFactors (θ, 0)) :
    ContDiffAt ℝ m (Function.uncurry independentRadiusNormalForm) (θ, 0) := by
  exact (independentRadiusNormalForm_analyticAt_of_recoveryFactors θ hrec).contDiffAt

/-- The parent second-factor analytic declarations
assemble into an analytic recovery package without unfolding the raw DFP map. -/
theorem independentRadiusRecoveryFactors_analyticAt_of_secondFactors
    (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusRecoveryFactors (θ, 0) := by
  have hS := independentRadiusSecondSpectral_analyticAt θ
  have hG := independentRadiusSecondGradient_analyticAt θ
  have hS0 := independentRadiusSecondSpectral_zero θ
  have hG0 := independentRadiusSecondGradient_zero θ
  have hRadius :
      (independentRadiusSecondSpectral (θ, 0)).2 *
          (independentRadiusSecondGradient (θ, 0)).2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hShape :
      (independentRadiusSecondSpectral (θ, 0)).1 *
          (independentRadiusSecondGradient (θ, 0)).1 ^ 2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hGeneric := AnalyticRecovery.analyticAt_recoveryFactors
    hS hG hRadius hShape
  have hEq : independentRadiusRecoveryFactors =
      AnalyticRecovery.recoveryFactors independentRadiusSecondSpectral
        independentRadiusSecondGradient := by
    funext z
    unfold independentRadiusRecoveryFactors AnalyticRecovery.recoveryFactors
    rfl
  rw [hEq]
  exact hGeneric

/-- Appendix Lemma A.5: the independent-radius normal form is finite-smooth after
the second-factor analytic declarations have been established. -/
theorem independentRadiusNormalForm_contDiffAt_of_secondFactors
    (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m (Function.uncurry independentRadiusNormalForm) (θ, 0) := by
  exact independentRadiusNormalForm_contDiffAt_of_analyticRecovery m θ
    (independentRadiusRecoveryFactors_analyticAt_of_secondFactors θ)

end DFP.TwoLeg.Mixed
