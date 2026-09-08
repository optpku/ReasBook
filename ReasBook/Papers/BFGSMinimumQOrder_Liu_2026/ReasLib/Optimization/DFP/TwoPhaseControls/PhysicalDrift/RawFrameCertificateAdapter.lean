module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondScaleGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

namespace CenterRaw

/-!
This companion is the source-facing boundary for the oriented-frame branch.  It does
not assert a particular evaluator identity: source lemmas provide the frame and
displacement data, while this file packages those data into the raw certificate used
by the denominator-cleared center residual.
-/

/-- Helper for Infrastructure I.16a: simultaneous negation of the frame and second normalized
displacement leaves the weighted center bracket unchanged. -/
theorem weightedCenterBracket_neg_frame_neg_displacement
    (F : Matrix (Fin 2) (Fin 2) ℝ) (u₀ u₁ : Fin 2 → ℝ) :
    weightedCenterBracket (-F) u₀ (-u₁) = weightedCenterBracket F u₀ u₁ := by
  ext i
  fin_cases i
  · simp [weightedCenterBracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [weightedCenterBracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- Helper for Infrastructure I.16a: a signed frame/second-displacement branch is packaged as a
raw `BracketCertificate`, with its scalar bracket identified with a supplied kernel. -/
theorem bracketCertificate_of_signedFrameData
    {b r : ℝ} {state : ℝ × ℝ × ℝ}
    {F : Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : Fin 2 → ℝ} {W : ℝ}
    (horth : F * F.transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame b state = F ∧
        (CenterRaw.secondStep b state).2.2 = r • u₁) ∨
      (CenterRaw.firstFrame b state = -F ∧
        (CenterRaw.secondStep b state).2.2 = r • (-u₁)))
    (hfirst : (CenterRaw.firstStep b state).2.2 = r • u₀)
    (hbracket : (weightedCenterBracket F u₀ u₁) 0 = W) :
    ∃ certificate : CenterRaw.BracketCertificate b r state,
      certificate.bracket 0 = W := by
  rcases hbranch with ⟨hframe, hsecond⟩ | ⟨hframe, hsecond⟩
  · have horthActual :
        CenterRaw.firstFrame b state * (CenterRaw.firstFrame b state).transpose = 1 := by
      rw [hframe]
      exact horth
    let certificate : CenterRaw.BracketCertificate b r state :=
      { firstNormalized := u₀
        secondNormalized := u₁
        frame_orthogonal := horthActual
        first_displacement := hfirst
        second_displacement := hsecond }
    have hcertificate : certificate.bracket 0 = W := by
      calc
        certificate.bracket 0 =
            (weightedCenterBracket (CenterRaw.firstFrame b state) u₀ u₁) 0 := by
          rfl
        _ = (weightedCenterBracket F u₀ u₁) 0 := by rw [hframe]
        _ = W := hbracket
    exact ⟨certificate, hcertificate⟩
  · have horthActual :
        CenterRaw.firstFrame b state * (CenterRaw.firstFrame b state).transpose = 1 := by
      rw [hframe]
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using horth
    let certificate : CenterRaw.BracketCertificate b r state :=
      { firstNormalized := u₀
        secondNormalized := -u₁
        frame_orthogonal := horthActual
        first_displacement := hfirst
        second_displacement := hsecond }
    have hcertificate : certificate.bracket 0 = W := by
      calc
        certificate.bracket 0 =
            (weightedCenterBracket (CenterRaw.firstFrame b state) u₀ (-u₁)) 0 := by
          rfl
        _ = (weightedCenterBracket (-F) u₀ (-u₁)) 0 := by rw [hframe]
        _ = (weightedCenterBracket F u₀ u₁) 0 := by
          rw [weightedCenterBracket_neg_frame_neg_displacement]
        _ = W := hbracket
    exact ⟨certificate, hcertificate⟩

end CenterRaw

/-- Helper for Infrastructure I.16a: the canonical weighted center bracket has the prescribed
linear coefficient after the public second-scale germ is specialized. -/
theorem canonicalCenterBracket_quadraticGerm_of_centerScale
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm (canonicalCenterBracket θ) 0
      (centerBracketCoefficient θ)
      (canonicalCenterBracketQuadraticCoeff θ
        (centerSecondDisplacementScaleLinearCoeff θ)
        (centerSecondDisplacementScaleQuadraticCoeff θ)) := by
  have hscale := centerSecondDisplacementScale_quadraticGerm θ
  have hcanonical := canonicalCenterBracket_quadraticGerm_of_scaleCertificate θ hscale
  apply hcanonical.congrCoefficients
  · rfl
  · dsimp only [canonicalCenterBracketLinearCoeff,
      centerSecondDisplacementCoordinateLinearCoeff,
      centerSecondDisplacementScaleLinearCoeff,
      WeightedCenterBracket.secondDisplacementScaleLinear,
      centerBracketCoefficient]
    ring
  · rfl

/-- Helper for Infrastructure I.16a: joint `C³` regularity of the canonical bracket
    upgrades its public quadratic germ to the truncated-germ interface consumed by compact
    quotient transport. -/
theorem canonicalCenterBracket_truncatedGerm_of_regular
    {K : Set (ℝ × ℝ × ℝ)}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry canonicalCenterBracket) (θ, 0)) :
    IndependentRadiusTruncatedGerm canonicalCenterBracket K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n) := by
  refine WeightedCenterBracket.truncatedGerm_of_coordZero_quadraticGerm
    (c := fun θ ↦ canonicalCenterBracketQuadraticCoeff θ
      (centerSecondDisplacementScaleLinearCoeff θ)
      (centerSecondDisplacementScaleQuadraticCoeff θ)) hregular ?_
  intro θ hθ
  exact canonicalCenterBracket_quadraticGerm_of_centerScale θ

/-- Helper for Infrastructure I.16a: a signed raw-frame branch transports the physical center
    residual directly to the canonical frame-coordinate bracket. -/
theorem centerResidual_eq_controlRadius_mul_canonicalBracketResidual_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) *
        (canonicalCenterBracket θ r - centerBracketCoefficient θ * r) := by
  have hbracket :
      (weightedCenterBracket (canonicalFirstFrame θ r)
        (canonicalFirstNormalizedDisplacement θ r)
        (canonicalSecondNormalizedDisplacement θ r)) 0 =
        canonicalCenterBracket θ r := by
    rfl
  obtain ⟨certificate, hcertificate⟩ :=
    CenterRaw.bracketCertificate_of_signedFrameData
      (F := canonicalFirstFrame θ r)
      (u₀ := canonicalFirstNormalizedDisplacement θ r)
      (u₁ := canonicalSecondNormalizedDisplacement θ r)
      (W := canonicalCenterBracket θ r)
      horth hbranch hfirst hbracket
  have hres := certificate.centerResidual_eq_controlRadius_mul_bracketResidual
  rw [hcertificate] at hres
  simpa only [physicalCenterResidual] using hres

/-- Infrastructure I.16a: compact bracket-germ bounds consume signed-frame data through the
raw certificate adapter, leaving the source-specific frame identities as explicit hypotheses. -/
theorem centerResidual_zeroFilledQuotient_uniformBound_of_signedFrameData
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {F : (ℝ × ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ}
    (hK : IsCompact K)
    (hW : IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (horth : ∀ θ, θ ∈ K → F θ * (F θ).transpose = 1)
    (hbranch : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstFrame θ.1 (input θ r) = F θ ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F θ ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-(u₁ θ r))))
    (hfirst : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ θ r)
    (hbracket : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (weightedCenterBracket (F θ) (u₀ θ r) (u₁ θ r)) 0 = W θ r) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have hcertificate : ∀ θ ∈ K, ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = W θ r := by
    intro θ hθ r hr
    exact CenterRaw.bracketCertificate_of_signedFrameData
      (horth θ hθ) (hbranch θ hθ r hr) (hfirst θ hθ r hr)
      (hbracket θ hθ r hr)
  exact centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
    hK hW δ₀ hδ₀ hcertificate

/-- Helper for Infrastructure I.16a: the quotient bound remains valid when the oriented
    frame itself varies with the radius, which is the natural shape of the canonical
    eigenframe along a mixed parameter path. -/
theorem centerResidual_zeroFilledQuotient_uniformBound_of_radiusDependentFrameData
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {F : (ℝ × ℝ × ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ}
    (hK : IsCompact K)
    (hW : IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (horth : ∀ θ, θ ∈ K → ∀ r : ℝ,
      F θ r * (F θ r).transpose = 1)
    (hbranch : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstFrame θ.1 (input θ r) = F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-(u₁ θ r))))
    (hfirst : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ θ r)
    (hbracket : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (weightedCenterBracket (F θ r) (u₀ θ r) (u₁ θ r)) 0 = W θ r) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have hcertificate : ∀ θ ∈ K, ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = W θ r := by
    intro θ hθ r hr
    exact CenterRaw.bracketCertificate_of_signedFrameData
      (horth θ hθ r) (hbranch θ hθ r hr) (hfirst θ hθ r hr)
      (hbracket θ hθ r hr)
  exact centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
    hK hW δ₀ hδ₀ hcertificate

/-- Helper for Infrastructure I.16a: joint regularity and a quadratic germ
automatically provide the truncated germ required by a radius-dependent frame
quotient bound. -/
theorem centerResidual_zeroFilledQuotient_uniformBound_of_radiusFrameGerm
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {F : (ℝ × ℝ × ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : (ℝ × ℝ × ℝ) → ℝ → Fin 2 → ℝ}
    {c : (ℝ × ℝ × ℝ) → ℝ}
    (hK : IsCompact K)
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry W) (θ, 0))
    (hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm (W θ) 0 (centerBracketCoefficient θ)
        (c θ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (horth : ∀ θ, θ ∈ K → ∀ r : ℝ,
      F θ r * (F θ r).transpose = 1)
    (hbranch : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstFrame θ.1 (input θ r) = F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-(u₁ θ r))))
    (hfirst : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ θ r)
    (hbracket : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      (weightedCenterBracket (F θ r) (u₀ θ r) (u₁ θ r)) 0 = W θ r) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have hW : IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n) := by
    apply WeightedCenterBracket.truncatedGerm_of_coordZero_quadraticGerm hregular
    exact hgerm
  exact centerResidual_zeroFilledQuotient_uniformBound_of_radiusDependentFrameData
    hK hW δ₀ hδ₀ horth hbranch hfirst hbracket

end DFP.TwoLeg.Mixed
