module

public import ReasLib.Analysis.Calculus.Analytic.RecoveryFactors
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
import all ReasLib.Analysis.Calculus.Analytic.RecoveryFactors

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion isolates the one-dimensional quotient differentiation used by the independent
radius normal form.  The target coefficients are expressed as component derivatives, so the
downstream proof never has to unfold the recovery record or manipulate product derivatives.
-/

/-- Component derivative data at `(S 0, G 0) = ((2,1),(1,2))`
    determine the first derivative of the recovered radius, shape, and high-scale factors.  The
    squared denominator in the shape quotient contributes the coefficient `4 * g₁`. -/
theorem recoveryFactors_hasDerivAt_of_componentJets
    (S G : ℝ → ℝ × ℝ) (s₁ s₂ g₁ g₂ : ℝ)
    (hS₁ : HasDerivAt (fun t ↦ (S t).1) s₁ 0)
    (hS₂ : HasDerivAt (fun t ↦ (S t).2) s₂ 0)
    (hG₁ : HasDerivAt (fun t ↦ (G t).1) g₁ 0)
    (hG₂ : HasDerivAt (fun t ↦ (G t).2) g₂ 0)
    (hS0 : S 0 = (2, 1)) (hG0 : G 0 = (1, 2)) :
    HasDerivAt (fun t ↦ AnalyticRecovery.recoveryFactors S G t)
      ((s₁ + 2 * g₁ - 2 * s₂ - g₂) / 2,
        (2 * s₂ + 2 * g₂ - s₁ - 4 * g₁, s₂)) 0 := by
  have hnumRadius := hS₁.mul hG₁
  have hdenRadius := hS₂.mul hG₂
  have hnumShape := hS₂.mul (hG₂.pow 2)
  have hdenShape := hS₁.mul (hG₁.pow 2)
  have hdenRadius0 : (S 0).2 * (G 0).2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hdenShape0 : (S 0).1 * (G 0).1 ^ 2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hρraw := hnumRadius.div hdenRadius hdenRadius0
  have hρ : HasDerivAt
      (fun t ↦ (S t).1 * (G t).1 / ((S t).2 * (G t).2))
      ((s₁ + 2 * g₁ - 2 * s₂ - g₂) / 2) 0 := by
    apply hρraw.congr_deriv
    simp [hS0, hG0]
    ring
  have hpraw := hnumShape.div hdenShape hdenShape0
  have hp : HasDerivAt
      (fun t ↦ (S t).2 * (G t).2 ^ 2 / ((S t).1 * (G t).1 ^ 2))
      (2 * s₂ + 2 * g₂ - s₁ - 4 * g₁) 0 := by
    apply hpraw.congr_deriv
    simp [hS0, hG0]
    ring
  have htriple := hρ.prodMk (hp.prodMk hS₂)
  simpa only [AnalyticRecovery.recoveryFactors] using htriple

end DFP.TwoLeg.Mixed
