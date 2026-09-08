module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RecoveryDerivative

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion packages the component-jet interface for the independent-radius
recovery factors.  It leaves the raw mixed-map identification separate, so it can
be consumed while that transport proof is still under construction.
-/

/-- First-radius jets of the second spectral and gradient
factor pairs transport to the derivative of the recovered factor triple. -/
theorem independentRadiusRecoveryFactors_hasDerivAt_of_componentJets
    (θ : ℝ × ℝ × ℝ) (s₁ s₂ g₁ g₂ : ℝ)
    (hS : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) (s₁, s₂) 0)
    (hG : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) (g₁, g₂) 0)
    (hrepresentation :
      (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) =
        AnalyticRecovery.recoveryFactors
          (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
          (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))) :
    HasDerivAt
      (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r))
      ((s₁ + 2 * g₁ - 2 * s₂ - g₂) / 2,
        (2 * s₂ + 2 * g₂ - s₁ - 4 * g₁, s₂)) 0 := by
  have hS0 : (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) 0 =
      (2, 1) := independentRadiusSecondSpectral_zero θ
  have hG0 : (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) 0 =
      (1, 2) := independentRadiusSecondGradient_zero θ
  have hrec := recoveryFactors_hasDerivAt_of_componentJets
    (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
    (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))
    s₁ s₂ g₁ g₂ hS.fst hS.snd hG.fst hG.snd hS0 hG0
  rw [hrepresentation]
  exact hrec

/-- The same component jets give the first-radius jet of
the full independent-radius normal form, with unit derivative in its first coordinate. -/
theorem independentRadiusNormalForm_hasDerivAt_of_componentJets
    (θ : ℝ × ℝ × ℝ) (s₁ s₂ g₁ g₂ : ℝ)
    (hS : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r)) (s₁, s₂) 0)
    (hG : HasDerivAt
      (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r)) (g₁, g₂) 0)
    (hrepresentation :
      (fun r : ℝ ↦ independentRadiusRecoveryFactors (θ, r)) =
        AnalyticRecovery.recoveryFactors
          (fun r : ℝ ↦ independentRadiusSecondSpectral (θ, r))
          (fun r : ℝ ↦ independentRadiusSecondGradient (θ, r))) :
    HasDerivAt
      (fun r : ℝ ↦ independentRadiusNormalForm θ r)
      (1, (2 * s₂ + 2 * g₂ - s₁ - 4 * g₁, s₂)) 0 := by
  have hrec := independentRadiusRecoveryFactors_hasDerivAt_of_componentJets
    θ s₁ s₂ g₁ g₂ hS hG hrepresentation
  have hρ := hrec.fst
  have hshape := hrec.snd.fst
  have hscale := hrec.snd.snd
  have hprod : (fun r : ℝ ↦ r) *
      (fun r : ℝ ↦ (independentRadiusRecoveryFactors (θ, r)).1) =
      (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) := by
    funext r
    rfl
  have hfirst : HasDerivAt
      (fun r : ℝ ↦ r * (independentRadiusRecoveryFactors (θ, r)).1) 1 0 := by
    rw [← hprod]
    have hraw := (hasDerivAt_id' (0 : ℝ)).mul hρ
    simpa only [independentRadiusRecoveryFactors_zero θ, Prod.fst,
      zero_mul, one_mul, add_zero] using hraw
  have htriple := hfirst.prodMk (hshape.prodMk hscale)
  have hnormal : (fun r : ℝ ↦ independentRadiusNormalForm θ r) =
      (fun r : ℝ ↦
        (r * (independentRadiusRecoveryFactors (θ, r)).1,
          (independentRadiusRecoveryFactors (θ, r)).2.1,
          (independentRadiusRecoveryFactors (θ, r)).2.2)) := by
    funext r
    exact independentRadiusNormalForm_eq_recoveryFactors θ r
  rw [hnormal]
  exact htriple

/-- Once the independent normal form is identified with
the raw two-leg evaluator, the public-map equality follows from the nonzero-radius raw
map bridge. -/
theorem independentRadiusNormalForm_eq_map_of_raw_transport
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hr : r ≠ 0)
    (hraw : independentRadiusNormalForm θ r =
      independentMapRaw θ.1 r (input θ r).2.1 (input θ r).2.2) :
    independentRadiusNormalForm θ r = map θ.1 (input θ r) := by
  have hmap : independentMapRaw θ.1 r (input θ r).2.1 (input θ r).2.2 =
      map θ.1 (input θ r) := by
    rw [input_apply]
    exact independentMapRaw_eq_map θ.1 r
      (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) hr
  exact hraw.trans hmap

end DFP.TwoLeg.Mixed
