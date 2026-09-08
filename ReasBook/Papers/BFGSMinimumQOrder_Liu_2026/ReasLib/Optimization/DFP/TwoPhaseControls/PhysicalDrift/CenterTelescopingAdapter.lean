module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
This companion records the algebraic telescoping interface for a two-leg center
displacement.  It assumes only identity-control gradient increments and an orthogonal
intermediate frame; all evaluator-specific side conditions remain explicit at the call site.
-/

/-- Helper for Appendix Lemma A.6: identity-control gradient increments telescope after
    transport through an orthogonal intermediate frame. -/
theorem centerDisplacement_zero_of_identityGradientIncrements
    (F : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ g₁ g₂ s₀ s₁ : Fin 2 → ℝ)
    (horth : F * F.transpose = 1)
    (hfirst : g₁ = g₀ + s₀)
    (hsecond : g₂ = F.transpose *ᵥ g₁ + s₁) :
    WithLp.toLp 2 s₀ + WithLp.toLp 2 (F *ᵥ s₁) -
        (WithLp.toLp 2 (F *ᵥ g₂) - WithLp.toLp 2 g₀) = 0 := by
  have htransport : F *ᵥ g₂ = g₀ + s₀ + F *ᵥ s₁ := by
    rw [hsecond, hfirst, Matrix.mulVec_add, Matrix.mulVec_mulVec, horth,
      Matrix.one_mulVec]
  rw [htransport]
  simp only [WithLp.toLp_add]
  module

end DFP.TwoLeg.Mixed
