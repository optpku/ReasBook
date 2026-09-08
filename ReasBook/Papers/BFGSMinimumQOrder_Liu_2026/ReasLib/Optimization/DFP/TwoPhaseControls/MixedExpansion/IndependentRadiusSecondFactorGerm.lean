module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion transports second-leg residual germs through the eigenframe and gradient
quotients.  It stops before raw-map identification, so the algebraic certificate can be
used by both the mixed expansion and physical-drift owners.
-/

/-- Helper for Appendix Lemma A.6: second-leg residual and gradient quadratic germs determine
the four normalized spectral/gradient factor germs through order two. -/
theorem independentSecondFactorQuadraticGerms_of_residualGerms
    {A C D q u : ℝ → ℝ}
    {a₁ a₂ c₁ c₂ d₁ d₂ q₂ u₁ u₂ : ℝ}
    (hA : HasQuadraticGerm A 6 a₁ a₂)
    (hC : HasQuadraticGerm C 2 c₁ c₂)
    (hD : HasQuadraticGerm D 1 d₁ d₂)
    (hq : HasQuadraticGerm q 1 0 q₂)
    (hu : HasQuadraticGerm u 0 u₁ u₂) :
    HasQuadraticGerm
        (fun r ↦
          let t := (A r, C r, D r)
          let high := RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2
          (t.1 * t.2.2 - t.2.1 ^ 2) / high)
        2 (a₁ + 4 * d₁ - 4 * c₁)
          (a₂ + 4 * d₂ - 4 * d₁ ^ 2 - c₁ ^ 2 - 4 * c₂ + 4 * c₁ * d₁ - 8) ∧
      HasQuadraticGerm
        (fun r ↦
          let t := (A r, C r, D r)
          RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2)
        1 d₁ (4 + d₂) ∧
      HasQuadraticGerm
        (fun r ↦
          let t := (A r, C r, D r)
          let qv := q r
          let uv := u r
          let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
          let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
          ((t.2.2 - low) * qv - r ^ 2 * t.2.1 * uv) / denom)
        1 0 (q₂ - 2) ∧
      HasQuadraticGerm
        (fun r ↦
          let t := (A r, C r, D r)
          let qv := q r
          let uv := u r
          let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
          let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
          (t.2.1 * qv + (t.2.2 - low) * uv) / denom)
        2 (c₁ + u₁ - 2 * d₁)
          (2 * q₂ + c₂ + u₂ + d₁ * u₁ + 2 * d₁ ^ 2 - 2 * d₂ -
            d₁ * (c₁ + u₁)) := by
  let X : ℝ → ℝ := fun r ↦ r
  have hX : HasQuadraticGerm X 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [X, quadraticModel]
  have hX2 := hX.mul hX
  let mA : ℝ → ℝ := fun r ↦ X r * X r * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmARaw := hX2.mul hA
  have hmAPath : ∀ r : ℝ, mA r = X r * X r * A r := by
    intro r
    rfl
  have hmA := hmARaw.congrFunction hmAPath
  have hmA' : HasQuadraticGerm mA 0 0 6 := by
    apply hmA.congrCoefficients
    · ring
    · ring
    · ring
  have hmCRaw := hX.mul hC
  have hmCPath : ∀ r : ℝ, mC r = X r * C r := by
    intro r
    rfl
  have hmC := hmCRaw.congrFunction hmCPath
  have hmC' : HasQuadraticGerm mC 0 2 c₁ := by
    apply hmC.congrCoefficients
    · ring
    · ring
    · ring
  have hmD : HasQuadraticGerm mD 1 d₁ d₂ := by
    simpa only [mD] using hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hradRaw := ((hmA'.sub hmD).mul (hmA'.sub hmD)).add
    ((hmC'.mul hmC').constMul 4)
  have hradPath : ∀ r : ℝ,
      rad r = (mA r - mD r) * (mA r - mD r) +
        4 * (mC r * mC r) := by
    intro r
    simp [rad, pow_two]
  have hrad := hradRaw.congrFunction hradPath
  have hrad' : HasQuadraticGerm rad 1 (2 * d₁) (d₁ ^ 2 + 2 * d₂ + 4) := by
    apply hrad.congrCoefficients
    · ring
    · ring
    · ring
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap := hrad'.sqrtOne
  have hgap' : HasQuadraticGerm gap 1 d₁ (d₂ + 2) := by
    apply hgap.congrCoefficients
    · rfl
    · ring
    · ring
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hhalf := HasQuadraticGerm.model (1 / 2 : ℝ) 0 0
  have hhighRaw := ((hmA'.add hmD).add hgap').mul hhalf
  have hhighPath : ∀ r : ℝ,
      high r = (mA r + mD r + gap r) * quadraticModel (1 / 2) 0 0 r := by
    intro r
    simp [high, quadraticModel]
    ring
  have hhigh := hhighRaw.congrFunction hhighPath
  have hhigh' : HasQuadraticGerm high 1 d₁ (4 + d₂) := by
    apply hhigh.congrCoefficients
    · ring
    · ring
    · ring
  have hlowRaw := ((hmA'.add hmD).sub hgap').mul hhalf
  have hlowPath : ∀ r : ℝ,
      low r = (mA r + mD r - gap r) * quadraticModel (1 / 2) 0 0 r := by
    intro r
    simp [low, quadraticModel]
    ring
  have hlow := hlowRaw.congrFunction hlowPath
  have hlow' : HasQuadraticGerm low 0 0 2 := by
    apply hlow.congrCoefficients
    · ring
    · ring
    · ring
  let spectralNumerator : ℝ → ℝ := fun r ↦ A r * D r - C r * C r
  have hnumRaw := (hA.mul hD).sub (hC.mul hC)
  have hnumPath : ∀ r : ℝ,
      spectralNumerator r = A r * D r - C r * C r := by
    intro r
    simp [spectralNumerator, pow_two]
  have hnum := hnumRaw.congrFunction hnumPath
  have hnum' : HasQuadraticGerm spectralNumerator 2
      (a₁ + 6 * d₁ - 4 * c₁)
      (a₂ + 6 * d₂ + a₁ * d₁ - c₁ ^ 2 - 4 * c₂) := by
    apply hnum.congrCoefficients
    · ring
    · ring
    · ring
  have hhighBase : (1 : ℝ) ≠ 0 := by norm_num
  let spectralLow : ℝ → ℝ := fun r ↦ spectralNumerator r / high r
  have hlowSpectralRaw := hnum'.div hhigh' hhighBase
  have hlowSpectralPath : ∀ r : ℝ,
      spectralLow r = spectralNumerator r / high r := by
    intro r
    rfl
  have hlowSpectral := hlowSpectralRaw.congrFunction hlowSpectralPath
  have hlowSpectral' : HasQuadraticGerm spectralLow 2
      (a₁ + 4 * d₁ - 4 * c₁)
      (a₂ + 4 * d₂ - 4 * d₁ ^ 2 - c₁ ^ 2 - 4 * c₂ + 4 * c₁ * d₁ - 8) := by
    apply hlowSpectral.congrCoefficients
    · ring
    · ring
    · ring
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenRadRaw := ((hmD.sub hlow').mul (hmD.sub hlow')).add (hmC'.mul hmC')
  have hdenRadPath : ∀ r : ℝ,
      denomRad r = (mD r - low r) * (mD r - low r) + mC r * mC r := by
    intro r
    simp [denomRad, pow_two]
  have hdenRad := hdenRadRaw.congrFunction hdenRadPath
  have hdenRad' : HasQuadraticGerm denomRad 1 (2 * d₁) (d₁ ^ 2 + 2 * d₂) := by
    apply hdenRad.congrCoefficients
    · ring
    · ring
    · ring
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom := hdenRad'.sqrtOne
  have hdenom' : HasQuadraticGerm denom 1 d₁ d₂ := by
    apply hdenom.congrCoefficients
    · rfl
    · ring
    · ring
  have hdenBase : (1 : ℝ) ≠ 0 := by norm_num
  let lowNumerator : ℝ → ℝ := fun r ↦
    (mD r - low r) * q r - X r * X r * C r * u r
  have hlowNumRaw := (hmD.sub hlow').mul hq
  have hvanishing := (((hX2.mul hC).mul hu))
  have hlowNumCombined := hlowNumRaw.sub hvanishing
  have hlowNumPath : ∀ r : ℝ,
      lowNumerator r = (mD r - low r) * q r - X r * X r * C r * u r := by
    intro r
    simp [lowNumerator, pow_two]
  have hlowNum := hlowNumCombined.congrFunction hlowNumPath
  have hlowNum' : HasQuadraticGerm lowNumerator 1 d₁ (q₂ + d₂ - 2) := by
    apply hlowNum.congrCoefficients
    · ring
    · ring
    · ring
  let lowGradient : ℝ → ℝ := fun r ↦ lowNumerator r / denom r
  have hlowGradientRaw := hlowNum'.div hdenom' hdenBase
  have hlowGradientPath : ∀ r : ℝ,
      lowGradient r = lowNumerator r / denom r := by
    intro r
    rfl
  have hlowGradient := hlowGradientRaw.congrFunction hlowGradientPath
  have hlowGradient' : HasQuadraticGerm lowGradient 1 0 (q₂ - 2) := by
    apply hlowGradient.congrCoefficients
    · ring
    · ring
    · ring
  let highNumerator : ℝ → ℝ := fun r ↦ C r * q r + (mD r - low r) * u r
  have hhighNumRaw := (hC.mul hq).add ((hmD.sub hlow').mul hu)
  have hhighNumPath : ∀ r : ℝ,
      highNumerator r = C r * q r + (mD r - low r) * u r := by
    intro r
    simp [highNumerator]
  have hhighNum := hhighNumRaw.congrFunction hhighNumPath
  have hhighNum' : HasQuadraticGerm highNumerator 2 (c₁ + u₁)
      (2 * q₂ + c₂ + u₂ + d₁ * u₁) := by
    apply hhighNum.congrCoefficients
    · ring
    · ring
    · ring
  let highGradient : ℝ → ℝ := fun r ↦ highNumerator r / denom r
  have hhighGradientRaw := hhighNum'.div hdenom' hdenBase
  have hhighGradientPath : ∀ r : ℝ,
      highGradient r = highNumerator r / denom r := by
    intro r
    rfl
  have hhighGradient := hhighGradientRaw.congrFunction hhighGradientPath
  have hhighGradient' : HasQuadraticGerm highGradient 2 (c₁ + u₁ - 2 * d₁)
      (2 * q₂ + c₂ + u₂ + d₁ * u₁ + 2 * d₁ ^ 2 - 2 * d₂ -
        d₁ * (c₁ + u₁)) := by
    apply hhighGradient.congrCoefficients
    · ring
    · ring
    · ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hlowSpectral'.congrFunction
    intro r
    simp [spectralLow, independentSecondSpectralFactors, low, high,
      rad, gap, denomRad, denom, mA, mC, mD, X, spectralNumerator,
      RealSymmetric2.high_apply, RealSymmetric2.gap_apply, pow_two]
    ring_nf
  · apply hhigh'.congrFunction
    intro r
    simp [high, independentSecondSpectralFactors, low, rad, gap, mA, mC, mD, X,
      RealSymmetric2.high_apply, RealSymmetric2.gap_apply, pow_two]
    ring_nf
  · apply hlowGradient'.congrFunction
    intro r
    simp [lowGradient, independentSecondGradientFactors, low, denom,
      denomRad, rad, gap, mA, mC, mD, X, lowNumerator,
      RealSymmetric2.low_apply, RealSymmetric2.lowDenom_apply,
      RealSymmetric2.gap_apply, pow_two]
    ring_nf
  · apply hhighGradient'.congrFunction
    intro r
    simp [highGradient, independentSecondGradientFactors, low, denom,
      denomRad, rad, gap, mA, mC, mD, X, highNumerator,
      RealSymmetric2.low_apply, RealSymmetric2.lowDenom_apply,
      RealSymmetric2.gap_apply, pow_two]
    ring_nf

/-- Appendix Lemma A.6: the second-leg factor paths on the independent-radius
path carry the explicit quadratic coefficients used by the recovery map. -/
theorem independentRadiusSecondFactorQuadraticGerms
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm
        (fun r ↦ (independentRadiusSecondSpectral (θ, r)).1)
        2 (θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
        ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 - 84 * θ.2.2 * θ.1 ^ 2 -
            26 * θ.2.1 * θ.1 ^ 2 - 510 * θ.1 ^ 2 + 30) / 3) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusSecondSpectral (θ, r)).2)
        1 (8 * θ.1)
        (4 * θ.1 ^ 2 * (6 * θ.2.2 + θ.2.1 + 78) / 3) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusSecondGradient (θ, r)).1)
        1 0 ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
          384 * θ.1 ^ 2 - 117) / 18) ∧
      HasQuadraticGerm
        (fun r ↦ (independentRadiusSecondGradient (θ, r)).2)
        2 (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9)
        ((6 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 216 * θ.2.2 * θ.1 ^ 2 -
            2 * θ.2.1 ^ 2 * θ.1 ^ 2 + 12 * θ.2.1 * θ.1 ^ 2 -
            756 * θ.1 ^ 2 - 243) / 27) := by
  let residualA : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let residualC : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.1
  let residualD : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.2
  let residualQ : ℝ → ℝ := fun r ↦
    (independentSecondGradientResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let residualU : ℝ → ℝ := fun r ↦
    (independentSecondGradientResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2
  let lowFactorModel : ℝ → ℝ := fun r ↦
    let t := (residualA r, residualC r, residualD r)
    let high := RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2
    (t.1 * t.2.2 - t.2.1 ^ 2) / high
  let highFactorModel : ℝ → ℝ := fun r ↦
    let t := (residualA r, residualC r, residualD r)
    RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2
  let lowGradientModel : ℝ → ℝ := fun r ↦
    let t := (residualA r, residualC r, residualD r)
    let qv := residualQ r
    let uv := residualU r
    let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
    let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
    ((t.2.2 - low) * qv - r ^ 2 * t.2.1 * uv) / denom
  let highGradientModel : ℝ → ℝ := fun r ↦
    let t := (residualA r, residualC r, residualD r)
    let qv := residualQ r
    let uv := residualU r
    let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
    let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
    (t.2.1 * qv + (t.2.2 - low) * uv) / denom
  obtain ⟨hA, hC, hD, hq, hu⟩ := independentRadiusSecondComponentQuadraticGerms θ
  have hA' : HasQuadraticGerm residualA 6
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3)
      ((12 * θ.2.2 ^ 2 * θ.1 ^ 2 + 11 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          540 * θ.2.2 * θ.1 ^ 2 - θ.2.1 ^ 2 * θ.1 ^ 2 +
          78 * θ.2.1 * θ.1 ^ 2 + 2058 * θ.1 ^ 2 - 66) / 3) := by
    simpa only [residualA] using hA
  have hC' : HasQuadraticGerm residualC 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)
      ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
          θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
          2538 * θ.1 ^ 2 - 126) / 9) := by
    simpa only [residualC] using hC
  have hD' : HasQuadraticGerm residualD 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    simpa only [residualD] using hD
  have hq' : HasQuadraticGerm residualQ 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18) := by
    simpa only [residualQ] using hq
  have hu' : HasQuadraticGerm residualU 0
      (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)
      (-(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
        θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
        1314 * θ.1 ^ 2 - 162) / 27) := by
    simpa only [residualU] using hu
  obtain ⟨hLow, hHigh, hGLow, hGHigh⟩ :=
    independentSecondFactorQuadraticGerms_of_residualGerms hA' hC' hD' hq' hu'
  have hLowModel : HasQuadraticGerm lowFactorModel 2
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3 + 4 * (8 * θ.1) -
        4 * (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3))
      (((12 * θ.2.2 ^ 2 * θ.1 ^ 2 + 11 * θ.2.2 * θ.2.1 * θ.1 ^ 2 +
          540 * θ.2.2 * θ.1 ^ 2 - θ.2.1 ^ 2 * θ.1 ^ 2 +
          78 * θ.2.1 * θ.1 ^ 2 + 2058 * θ.1 ^ 2 - 66) / 3 +
        4 * (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
          78 * θ.1 ^ 2 - 3) / 3) -
        4 * (8 * θ.1) ^ 2 -
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) ^ 2 -
        4 * ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
          θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
          2538 * θ.1 ^ 2 - 126) / 9) +
        4 * (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) * (8 * θ.1) -
        8)) := by
    simpa only [lowFactorModel] using hLow
  have hHighModel : HasQuadraticGerm highFactorModel 1 (8 * θ.1)
      (4 + 4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    simpa only [highFactorModel] using hHigh
  have hGLowModel : HasQuadraticGerm lowGradientModel 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 81) / 18 - 2) := by
    simpa only [lowGradientModel] using hGLow
  have hGHighModel : HasQuadraticGerm highGradientModel 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3 +
        -θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9 - 2 * (8 * θ.1))
      (2 * ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
          384 * θ.1 ^ 2 - 81) / 18) +
        (3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
          θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
          2538 * θ.1 ^ 2 - 126) / 9 +
        -(3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 288 * θ.2.2 * θ.1 ^ 2 -
          θ.2.1 ^ 2 * θ.1 ^ 2 + 48 * θ.2.1 * θ.1 ^ 2 +
          1314 * θ.1 ^ 2 - 162) / 27 +
        8 * θ.1 * (-θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9) +
        2 * (8 * θ.1) ^ 2 -
        2 * (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
          78 * θ.1 ^ 2 - 3) / 3) -
        8 * θ.1 * (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3 +
          -θ.1 * (6 * θ.2.2 - θ.2.1 + 60) / 9)) := by
    simpa only [highGradientModel] using hGHigh
  have hLowCoeff : HasQuadraticGerm lowFactorModel 2
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
      ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 - 84 * θ.2.2 * θ.1 ^ 2 -
        26 * θ.2.1 * θ.1 ^ 2 - 510 * θ.1 ^ 2 + 30) / 3) := by
    apply hLowModel.congrCoefficients
    · ring
    · ring
    · ring
  have hHighCoeff : HasQuadraticGerm highFactorModel 1 (8 * θ.1)
      (4 * θ.1 ^ 2 * (6 * θ.2.2 + θ.2.1 + 78) / 3) := by
    apply hHighModel.congrCoefficients
    · rfl
    · rfl
    · ring
  have hGLowCoeff : HasQuadraticGerm lowGradientModel 1 0
      ((24 * θ.2.2 * θ.1 ^ 2 - 4 * θ.2.1 * θ.1 ^ 2 +
        384 * θ.1 ^ 2 - 117) / 18) := by
    apply hGLowModel.congrCoefficients
    · rfl
    · rfl
    · ring
  have hGHighCoeff : HasQuadraticGerm highGradientModel 2
      (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9)
      ((6 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 216 * θ.2.2 * θ.1 ^ 2 -
        2 * θ.2.1 ^ 2 * θ.1 ^ 2 + 12 * θ.2.1 * θ.1 ^ 2 -
        756 * θ.1 ^ 2 - 243) / 27) := by
    apply hGHighModel.congrCoefficients
    · ring
    · ring
    · ring
  have hLowPath : ∀ r : ℝ,
      (independentRadiusSecondSpectral (θ, r)).1 =
        lowFactorModel r := by
    intro r
    simp [independentRadiusSecondSpectral, independentSecondSpectralFactors,
      lowFactorModel, residualA, residualC, residualD, RealSymmetric2.high_apply,
      RealSymmetric2.gap_apply, pow_two]
  have hHighPath : ∀ r : ℝ,
      (independentRadiusSecondSpectral (θ, r)).2 =
        highFactorModel r := by
    intro r
    simp [independentRadiusSecondSpectral, independentSecondSpectralFactors,
      highFactorModel, residualA, residualC, residualD, RealSymmetric2.high_apply,
      RealSymmetric2.gap_apply, pow_two]
  have hGLowPath : ∀ r : ℝ,
      (independentRadiusSecondGradient (θ, r)).1 =
        lowGradientModel r := by
    intro r
    simp [independentRadiusSecondGradient, independentSecondGradientFactors,
      lowGradientModel, residualA, residualC, residualD, residualQ, residualU,
      RealSymmetric2.low_apply, RealSymmetric2.lowDenom_apply,
      RealSymmetric2.gap_apply, pow_two]
  have hGHighPath : ∀ r : ℝ,
      (independentRadiusSecondGradient (θ, r)).2 =
        highGradientModel r := by
    intro r
    simp [independentRadiusSecondGradient, independentSecondGradientFactors,
      highGradientModel, residualA, residualC, residualD, residualQ, residualU,
      RealSymmetric2.low_apply, RealSymmetric2.lowDenom_apply,
      RealSymmetric2.gap_apply, pow_two]
  refine ⟨hLowCoeff.congrFunction hLowPath,
    hHighCoeff.congrFunction hHighPath,
    hGLowCoeff.congrFunction hGLowPath,
    hGHighCoeff.congrFunction hGHighPath⟩

end DFP.TwoLeg.Mixed
