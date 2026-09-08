module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusDerivatives
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJets
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RawSignInvariance
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusDerivatives
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJets
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.RawSignInvariance

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion computes the one-dimensional component jets needed by the independent-radius
normal form without importing the paper-facing mixed-expansion module.  The first-leg gradient
residual has derivative `b * (P + 6) / 3`; rotation into the eigenframe changes the corresponding
high factor derivative to `b * (P - 6) / 3`.
-/

/-- The first normalized spectral and gradient factors have
    their first-radius jets at the canonical zero-radius base point. -/
lemma independentRadiusFirstFactorJets (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusFirstSpectral (θ, r))
        (θ.1 * (2 * θ.2.2 + θ.2.1 + 4), -2 * θ.1) 0 ∧
      HasDerivAt (fun r ↦ independentRadiusFirstGradient (θ, r))
        (-2 * θ.1, θ.1 * (θ.2.1 - 6) / 3) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let A : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).1
  let C : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).2.1
  let D : ℝ → ℝ := fun r ↦ (independentRadiusFirstResiduals (θ, r)).2.2
  let q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradientResiduals (θ, r)).1
  let u : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradientResiduals (θ, r)).2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hResidual := independentRadiusFirstResiduals_hasDerivAt θ
  have hA : HasDerivAt A (θ.1 * (2 * θ.2.2 + θ.2.1 - 2)) 0 := by
    simpa only [A] using hasDerivAt_fst_of_prod hResidual
  have hC : HasDerivAt C (-4 * θ.1) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hResidual
    simpa only [C] using hasDerivAt_fst_of_prod hsecond
  have hD : HasDerivAt D (-2 * θ.1) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hResidual
    simpa only [D] using hasDerivAt_snd_of_prod hsecond
  have hGradientResidual := independentRadiusFirstGradientResiduals_hasDerivAt θ
  have hq : HasDerivAt q (-2 * θ.1) 0 := by
    simpa only [q] using hasDerivAt_fst_of_prod hGradientResidual
  have hu : HasDerivAt u (θ.1 * (θ.2.1 + 6) / 3) 0 := by
    simpa only [u] using hasDerivAt_snd_of_prod hGradientResidual
  have hA0 : A 0 = 3 := by
    norm_num [A, independentRadiusFirstResiduals, independentFirstResiduals]
  have hC0 : C 0 = 1 := by
    norm_num [C, independentRadiusFirstResiduals, independentFirstResiduals]
  have hD0 : D 0 = 1 := by
    norm_num [D, independentRadiusFirstResiduals, independentFirstResiduals]
  have hq0 : q 0 = 1 := by
    norm_num [q, independentRadiusFirstGradientResiduals,
      independentFirstGradientResiduals]
  have hu0 : u 0 = 0 := by
    norm_num [u, independentRadiusFirstGradientResiduals,
      independentFirstGradientResiduals]
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    have hraw := (hX.pow 2).mul hA
    have hcoefficient :
        2 * X 0 ^ (2 - 1) * 1 * A 0 + X 0 ^ 2 *
          (θ.1 * (2 * θ.2.2 + θ.2.1 - 2)) = 0 := by
      simp [X]
    exact hraw.congr_deriv hcoefficient
  have hmC : HasDerivAt mC 1 0 := by
    have hraw := hX.mul hC
    have hcoefficient : 1 * C 0 + X 0 * (-4 * θ.1) = 1 := by
      simp [X, hC0]
    exact hraw.congr_deriv hcoefficient
  have hmD : HasDerivAt mD (-2 * θ.1) 0 := by
    exact hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hradRaw := ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4)
  have hradCoefficient :
      2 * (mA - mD) 0 ^ (2 - 1) * (0 - (-2 * θ.1)) +
          4 * (2 * mC 0 ^ (2 - 1) * 1) = -4 * θ.1 := by
    simp [mA, mC, mD, X, hD0]
    ring
  have hrad : HasDerivAt rad (-4 * θ.1) 0 := hradRaw.congr_deriv hradCoefficient
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgapRaw := hrad.sqrt hrad0
  have hgapCoefficient : -4 * θ.1 / (2 * Real.sqrt (rad 0)) = -2 * θ.1 := by
    simp [rad, mA, mC, mD, X, hD0]
    ring_nf
  have hgap : HasDerivAt gap (-2 * θ.1) 0 := hgapRaw.congr_deriv hgapCoefficient
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have htwo : (2 : ℝ) ≠ 0 := by
    norm_num
  have hhighRaw := ((hmA.add hmD).add hgap).div (hasDerivAt_const 0 (2 : ℝ)) htwo
  have hhighCoefficient :
      ((0 + (-2 * θ.1) + (-2 * θ.1)) * 2 -
          (mA + mD + gap) 0 * 0) / 2 ^ 2 = -2 * θ.1 := by
    simp
    ring
  have hhigh : HasDerivAt high (-2 * θ.1) 0 :=
    hhighRaw.congr_deriv hhighCoefficient
  have hlowRaw := ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) htwo
  have hlowCoefficient :
      ((0 + (-2 * θ.1) - (-2 * θ.1)) * 2 -
          (mA + mD - gap) 0 * 0) / 2 ^ 2 = 0 := by
    simp
  have hlow : HasDerivAt low 0 0 := hlowRaw.congr_deriv hlowCoefficient
  have hhigh0 : high 0 ≠ 0 := by
    norm_num [high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]
  let spectralLow : ℝ → ℝ := fun r ↦ (A r * D r - C r ^ 2) / high r
  have hSpectralLowRaw := ((hA.mul hD).sub (hC.pow 2)).div hhigh hhigh0
  have hSpectralLowCoefficient :
      (((θ.1 * (2 * θ.2.2 + θ.2.1 - 2)) * D 0 + A 0 * (-2 * θ.1) -
          2 * C 0 ^ (2 - 1) * (-4 * θ.1)) * high 0 -
        (A * D - C ^ 2) 0 * (-2 * θ.1)) / high 0 ^ 2 =
        θ.1 * (2 * θ.2.2 + θ.2.1 + 4) := by
    simp [high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]
    ring
  have hSpectralLow : HasDerivAt spectralLow
      (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 :=
    hSpectralLowRaw.congr_deriv hSpectralLowCoefficient
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRadRaw := ((hmD.sub hlow).pow 2).add (hmC.pow 2)
  have hdenomRadCoefficient :
      2 * (mD - low) 0 ^ (2 - 1) * (-2 * θ.1 - 0) +
          2 * mC 0 ^ (2 - 1) * 1 = -4 * θ.1 := by
    simp [mD, low, mC, X, gap, rad, mA, hD0]
    ring
  have hdenomRad : HasDerivAt denomRad (-4 * θ.1) 0 :=
    hdenomRadRaw.congr_deriv hdenomRadCoefficient
  have hdenomRad0 : denomRad 0 ≠ 0 := by
    simp [denomRad, mD, low, mC, X, hC0, hD0, gap, rad, mA, hA0]
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenomRaw := hdenomRad.sqrt hdenomRad0
  have hdenomCoefficient :
      -4 * θ.1 / (2 * Real.sqrt (denomRad 0)) = -2 * θ.1 := by
    simp [denomRad, mD, low, mC, X, gap, rad, mA, hD0]
    ring_nf
  have hdenom : HasDerivAt denom (-2 * θ.1) 0 :=
    hdenomRaw.congr_deriv hdenomCoefficient
  have hdenom0 : denom 0 ≠ 0 := by
    norm_num [denom, denomRad, mD, low, mC, X, hC0, hD0, gap, rad, mA, hA0]
  let gradientLow : ℝ → ℝ := fun r ↦
    ((D r - low r) * q r - X r ^ 2 * C r * u r) / denom r
  let gradientHigh : ℝ → ℝ := fun r ↦
    (C r * q r + (D r - low r) * u r) / denom r
  have hGradientLowRaw :=
    (((hD.sub hlow).mul hq).sub (((hX.pow 2).mul hC).mul hu)).div hdenom hdenom0
  have hGradientLowCoefficient :
      (((-2 * θ.1 - 0) * q 0 + (D - low) 0 * (-2 * θ.1) -
          ((2 * X 0 ^ (2 - 1) * 1 * C 0 + X 0 ^ 2 * (-4 * θ.1)) * u 0 +
            (X ^ 2 * C) 0 * (θ.1 * (θ.2.1 + 6) / 3))) * denom 0 -
        ((D - low) * q - X ^ 2 * C * u) 0 * (-2 * θ.1)) / denom 0 ^ 2 =
        -2 * θ.1 := by
    simp [denom, denomRad, low, gap, rad, mA, mC, mD, X,
      hC0, hD0, hq0, hu0]
  have hGradientLow : HasDerivAt gradientLow (-2 * θ.1) 0 :=
    hGradientLowRaw.congr_deriv hGradientLowCoefficient
  have hGradientHighRaw := ((hC.mul hq).add ((hD.sub hlow).mul hu)).div hdenom hdenom0
  have hGradientHighCoefficient :
      (((-4 * θ.1) * q 0 + C 0 * (-2 * θ.1) +
          ((-2 * θ.1 - 0) * u 0 + (D - low) 0 *
            (θ.1 * (θ.2.1 + 6) / 3))) * denom 0 -
        (C * q + (D - low) * u) 0 * (-2 * θ.1)) / denom 0 ^ 2 =
        θ.1 * (θ.2.1 - 6) / 3 := by
    simp [denom, denomRad, low, gap, rad, mA, mC, mD, X,
      hC0, hD0, hq0, hu0]
    ring_nf
  have hGradientHigh : HasDerivAt gradientHigh (θ.1 * (θ.2.1 - 6) / 3) 0 :=
    hGradientHighRaw.congr_deriv hGradientHighCoefficient
  have hgapEq : ∀ r : ℝ,
      gap r = RealSymmetric2.gap (mA r) (mC r) (mD r) := by
    intro r
    simp only [gap, RealSymmetric2.gap_apply]
    congr 1
    ring
  have hhighEq : ∀ r : ℝ,
      high r = RealSymmetric2.high (mA r) (mC r) (mD r) := by
    intro r
    dsimp [high]
    rw [RealSymmetric2.high_apply, hgapEq r]
  have hlowEq : ∀ r : ℝ,
      low r = RealSymmetric2.low (mA r) (mC r) (mD r) := by
    intro r
    dsimp [low]
    rw [RealSymmetric2.low_apply, hgapEq r]
  have hdenomEq : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom (mA r) (mC r) (mD r) := by
    intro r
    simp [denom, denomRad, RealSymmetric2.lowDenom_apply, hlowEq r]
  have hhighEqConcrete : ∀ r : ℝ,
      high r = RealSymmetric2.high
        (r ^ 2 * (independentRadiusFirstResiduals (θ, r)).1)
        (r * (independentRadiusFirstResiduals (θ, r)).2.1)
        (independentRadiusFirstResiduals (θ, r)).2.2 := by
    intro r
    simpa [mA, mC, mD, X] using hhighEq r
  have hlowEqConcrete : ∀ r : ℝ,
      low r = RealSymmetric2.low
        (r ^ 2 * (independentRadiusFirstResiduals (θ, r)).1)
        (r * (independentRadiusFirstResiduals (θ, r)).2.1)
        (independentRadiusFirstResiduals (θ, r)).2.2 := by
    intro r
    simpa [mA, mC, mD, X] using hlowEq r
  have hdenomEqConcrete : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom
        (r ^ 2 * (independentRadiusFirstResiduals (θ, r)).1)
        (r * (independentRadiusFirstResiduals (θ, r)).2.1)
        (independentRadiusFirstResiduals (θ, r)).2.2 := by
    intro r
    simpa [mA, mC, mD, X] using hdenomEq r
  have hmetricConcrete : ∀ r : ℝ,
      independentRadiusFirstMetricTriple (θ, r) =
        (r ^ 2 * (independentRadiusFirstResiduals (θ, r)).1,
          r * (independentRadiusFirstResiduals (θ, r)).2.1,
          (independentRadiusFirstResiduals (θ, r)).2.2) := by
    intro r
    rfl
  have hSpectralPair := hSpectralLow.prodMk hhigh
  have hSpectralEq : ∀ r : ℝ,
      (spectralLow r, high r) = independentRadiusFirstSpectral (θ, r) := by
    intro r
    unfold independentRadiusFirstSpectral
    rw [hmetricConcrete r]
    apply Prod.ext
    · change (A r * D r - C r ^ 2) / high r =
        ((independentRadiusFirstResiduals (θ, r)).1 *
          (independentRadiusFirstResiduals (θ, r)).2.2 -
          (independentRadiusFirstResiduals (θ, r)).2.1 ^ 2) /
          RealSymmetric2.high
            (r ^ 2 * (independentRadiusFirstResiduals (θ, r)).1)
            (r * (independentRadiusFirstResiduals (θ, r)).2.1)
            (independentRadiusFirstResiduals (θ, r)).2.2
      rw [hhighEqConcrete r]
    · exact hhighEqConcrete r
  have hSpectral := hSpectralPair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hSpectralEq r).symm))
  have hGradientPair := hGradientLow.prodMk hGradientHigh
  have hGradientEq : ∀ r : ℝ,
      (gradientLow r, gradientHigh r) = independentRadiusFirstGradient (θ, r) := by
    intro r
    unfold independentRadiusFirstGradient
    rw [hmetricConcrete r]
    apply Prod.ext
    · dsimp [gradientLow, A, C, D, q, u, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r]
    · dsimp [gradientHigh, A, C, D, q, u, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r]
  have hGradient := hGradientPair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hGradientEq r).symm))
  exact ⟨hSpectral, hGradient⟩

/-- The normalized second-leg residual triple has its explicit
    first derivative at zero. -/
lemma independentRadiusSecondResiduals_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt
      (fun r ↦ independentSecondResiduals θ.1 r
        (independentRadiusFirstSpectral (θ, r)).1
        (independentRadiusFirstSpectral (θ, r)).2
        (independentRadiusFirstGradient (θ, r)).1
        (independentRadiusFirstGradient (θ, r)).2)
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3,
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3, 8 * θ.1)) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hX0 : X 0 = 0 := by
    simp [X]
  -- Project the four scalar first-factor jets before forming rational residuals.
  have hfirst := independentRadiusFirstFactorJets θ
  have hL : HasDerivAt L (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 := by
    simpa only [L] using hasDerivAt_fst_of_prod hfirst.1
  have hH : HasDerivAt H (-2 * θ.1) 0 := by
    simpa only [H] using hasDerivAt_snd_of_prod hfirst.1
  have hQ : HasDerivAt Q (-2 * θ.1) 0 := by
    simpa only [Q] using hasDerivAt_fst_of_prod hfirst.2
  have hU : HasDerivAt U (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    simpa only [U] using hasDerivAt_snd_of_prod hfirst.2
  have hL0 : L 0 = 2 := by
    simpa only [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa only [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa only [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa only [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  let w₁ : ℝ → ℝ := X * L * Q - fun r ↦ 2 * θ.1 * (H * U) r
  let w₂ : ℝ → ℝ := H * U - fun r ↦ 2 * θ.1 * (X * L * Q) r
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₁, X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂ (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0, hU0, hX0]
    ring
  let β : ℝ → ℝ := X * L * Q * w₁ + H * U * w₂
  let γ : ℝ → ℝ := X ^ 2 * L * w₁ ^ 2 + H * w₂ ^ 2
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hγ : HasDerivAt γ (2 * θ.1 * (θ.2.1 - 27) / 3) 0 := by
    have h := (((hX.pow 2).mul hL).mul (hw₁.pow 2)).add (hH.mul (hw₂.pow 2))
    apply h.congr_deriv
    simp [γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0, hX0]
  have hγ0 : γ 0 ≠ 0 := by
    simp [γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0, hX0]
  let A : ℝ → ℝ := L - X ^ 2 * L ^ 2 * w₁ ^ 2 / γ + L ^ 2 * Q ^ 2 / β
  let C : ℝ → ℝ := -(X * L * H * w₁ * w₂ / γ) + L * Q * H * U / β
  let D : ℝ → ℝ := H - H ^ 2 * w₂ ^ 2 / γ + H ^ 2 * U ^ 2 / β
  -- Quotient differentiation now sees only scalar paths and named nonzero bases.
  have hA : HasDerivAt A
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    have h := (hL.sub
      ((((hX.pow 2).mul (hL.pow 2)).mul (hw₁.pow 2)).div hγ hγ0)).add
      (((hL.pow 2).mul (hQ.pow 2)).div hβ hβ0)
    apply h.congr_deriv
    simp [A, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hC : HasDerivAt C
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have h :=
      (((((hX.mul hL).mul hH).mul hw₁).mul hw₂).div hγ hγ0).neg.add
        (((hL.mul hQ).mul hH).mul hU |>.div hβ hβ0)
    apply h.congr_deriv
    simp [C, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hD : HasDerivAt D (8 * θ.1) 0 := by
    have h := (hH.sub (((hH.pow 2).mul (hw₂.pow 2)).div hγ hγ0)).add
      (((hH.pow 2).mul (hU.pow 2)).div hβ hβ0)
    apply h.congr_deriv
    simp [D, β, γ, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have htriple := hA.prodMk (hC.prodMk hD)
  -- Repackage the scalar model as the canonical residual definition pointwise.
  have hresidualEq : ∀ r : ℝ,
      (A r, C r, D r) =
        independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2 := by
    intro r
    simp [independentSecondResiduals, A, C, D, β, γ, w₁, w₂, X, L, H, Q, U]
    constructor
    · ring
    · constructor
      · ring
      · ring
  apply htriple.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ (hresidualEq r).symm)

/-- The normalized second-leg spectral pair has derivative
    `(b (2 J + P - 12), 8 b)` at zero radius. -/
lemma independentRadiusSecondSpectralJet (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusSecondSpectral (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA : HasDerivAt A
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    simpa only [A] using hasDerivAt_fst_of_prod hres
  have hC : HasDerivAt C
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [C] using hasDerivAt_fst_of_prod hsecond
  have hD : HasDerivAt D (8 * θ.1) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [D] using hasDerivAt_snd_of_prod hsecond
  have hA0 : A 0 = 6 := by
    simp only [A, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg Prod.fst (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simp only [C, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simp only [D, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    have hraw := (hX.pow 2).mul hA
    apply hraw.congr_deriv
    simp [mA, X]
  have hmC : HasDerivAt mC 2 0 := by
    have hraw := hX.mul hC
    apply hraw.congr_deriv
    simp [mC, X, hC0]
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    have hraw := ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4)
    apply hraw.congr_deriv
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
    ring
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    have hraw := hrad.sqrt hrad0
    apply hraw.congr_deriv
    simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0]
    ring_nf
  let high : ℝ → ℝ := fun r ↦ (mA r + mD r + gap r) / 2
  have hhigh : HasDerivAt high (8 * θ.1) 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hraw := ((hmA.add hmD).add hgap).div (hasDerivAt_const 0 (2 : ℝ)) htwo
    apply hraw.congr_deriv
    simp [high]
    ring
  have hhigh0 : high 0 ≠ 0 := by
    simp [high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]
  let spectralLow : ℝ → ℝ := fun r ↦ (A r * D r - C r ^ 2) / high r
  have hSL : HasDerivAt spectralLow
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12)) 0 := by
    have hraw := ((hA.mul hD).sub (hC.pow 2)).div hhigh hhigh0
    apply hraw.congr_deriv
    simp [spectralLow, high, mA, mC, mD, gap, rad, X, hA0, hC0, hD0]
    ring
  have hgapEq : ∀ r : ℝ,
      gap r = RealSymmetric2.gap (mA r) (mC r) (mD r) := by
    intro r
    simp only [gap, RealSymmetric2.gap_apply]
    congr 1
    ring
  have hhighEq : ∀ r : ℝ,
      high r = RealSymmetric2.high (mA r) (mC r) (mD r) := by
    intro r
    dsimp [high]
    rw [RealSymmetric2.high_apply, hgapEq r]
  have hhighEqConcrete : ∀ r : ℝ,
      high r = RealSymmetric2.high (r ^ 2 * A r) (r * C r) (D r) := by
    intro r
    simpa [mA, mC, mD, X] using hhighEq r
  have hpair := hSL.prodMk hhigh
  have hpairEq : ∀ r : ℝ,
      (spectralLow r, high r) = independentRadiusSecondSpectral (θ, r) := by
    intro r
    unfold independentRadiusSecondSpectral independentSecondSpectralFactors
    apply Prod.ext
    · change (A r * D r - C r ^ 2) / high r =
        (A r * D r - C r ^ 2) /
          RealSymmetric2.high (r ^ 2 * A r) (r * C r) (D r)
      rw [hhighEqConcrete r]
    · exact hhighEqConcrete r
  exact hpair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hpairEq r).symm))

/-
/-! The gradient counterpart uses the same residual jet, but keeps the low-factor
    denominator visible so that the quotient differentiation is independent of the
    spectral transport above. -/

/-- The normalized second-leg gradient pair has derivative
    `(0, 4 b (3 J + P + 12) / 9)` at zero radius. -/
lemma independentRadiusSecondGradientJet (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hfirst := independentRadiusFirstFactorJets θ
  have hL : HasDerivAt L (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 := by
    simpa only [L] using hasDerivAt_fst_of_prod hfirst.1
  have hH : HasDerivAt H (-2 * θ.1) 0 := by
    simpa only [H] using hasDerivAt_snd_of_prod hfirst.1
  have hQ : HasDerivAt Q (-2 * θ.1) 0 := by
    simpa only [Q] using hasDerivAt_fst_of_prod hfirst.2
  have hU : HasDerivAt U (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    simpa only [U] using hasDerivAt_snd_of_prod hfirst.2
  have hL0 : L 0 = 2 := by
    simpa only [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa only [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa only [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa only [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA : HasDerivAt A
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    simpa only [A] using hasDerivAt_fst_of_prod hres
  have hC : HasDerivAt C
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have hs := hasDerivAt_snd_of_prod hres
    simpa only [C] using hasDerivAt_fst_of_prod hs
  have hD : HasDerivAt D (8 * θ.1) 0 := by
    have hs := hasDerivAt_snd_of_prod hres
    simpa only [D] using hasDerivAt_snd_of_prod hs
  have hA0 : A 0 = 6 := by
    simpa only [A, L, H, Q, U] using congrArg Prod.fst
      (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simpa only [C, L, H, Q, U] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simpa only [D, L, H, Q, U] using congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let w₁ : ℝ → ℝ := fun r ↦ r * L r * Q r - 2 * θ.1 * H r * U r
  let w₂ : ℝ → ℝ := fun r ↦ H r * U r - 2 * θ.1 * r * L r * Q r
  let β : ℝ → ℝ := fun r ↦ r * L r * Q r * w₁ r + H r * U r * w₂ r
  let δ : ℝ → ℝ := fun r ↦ L r * Q r ^ 2 + H r * U r ^ 2
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₁, X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂ (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
  have hδ : HasDerivAt δ
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 30) / 3) 0 := by
    have h := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
    apply h.congr_deriv
    simp [δ, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hδ0 : δ 0 = 3 := by
    simp [δ, hL0, hH0, hQ0, hU0]
  let threeβ : ℝ → ℝ := fun r ↦ 3 * β r
  have hthreeβ : HasDerivAt threeβ (2 * θ.1 * (θ.2.1 - 24)) 0 := by
    have h := hβ.const_mul 3
    apply h.congr_deriv
    simp [threeβ]
    ring
  have hthreeβ0 : threeβ 0 ≠ 0 := by
    simp [threeβ, hβ0]
  let q : ℝ → ℝ := fun r ↦ Q r - X r * δ r * w₁ r / threeβ r
  let u : ℝ → ℝ := fun r ↦ U r - δ r * w₂ r / threeβ r
  have hq : HasDerivAt q 0 0 := by
    have h := hQ.sub (((hX.mul hδ).mul hw₁).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [q, threeβ, X, L, H, Q, U, δ, w₁, w₂, β, hL0, hH0, hQ0, hU0,
      hδ0]
    ring
  have hu : HasDerivAt u
      (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9) 0 := by
    have h := hU.sub ((hδ.mul hw₂).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [u, threeβ, X, L, H, Q, U, δ, w₁, w₂, β, hL0, hH0, hQ0, hU0,
      hδ0]
    ring
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    have h := (hX.pow 2).mul hA
    apply h.congr_deriv
    simp [mA, X]
  have hmC : HasDerivAt mC 2 0 := by
    have h := hX.mul hC
    apply h.congr_deriv
    simp [mC, X, hC0]
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    have h := ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4)
    apply h.congr_deriv
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
    ring
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    have h := hrad.sqrt hrad0
    apply h.congr_deriv
    simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0]
    ring_nf
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hlow : HasDerivAt low 0 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have h := ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) htwo
    apply h.congr_deriv
    simp [low]
    ring
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRad : HasDerivAt denomRad (16 * θ.1) 0 := by
    have h := ((hmD.sub hlow).pow 2).add (hmC.pow 2)
    apply h.congr_deriv
    simp [denomRad, mD, low, mC, X, hA0, hC0, hD0]
    ring
  have hdenomRad0 : denomRad 0 ≠ 0 := by
    simp [denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad]
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom : HasDerivAt denom (8 * θ.1) 0 := by
    have h := hdenomRad.sqrt hdenomRad0
    apply h.congr_deriv
    simp [denom, denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad]
    ring_nf
  have hdenom0 : denom 0 ≠ 0 := by
    simp [denom, denomRad, mD, low, mC, X, hA0, hC0, hD0, gap, rad]
  let gradientLow : ℝ → ℝ := fun r ↦
    ((mD r - low r) * q r - X r ^ 2 * C r * u r) / denom r
  let gradientHigh : ℝ → ℝ := fun r ↦
    (C r * q r + (mD r - low r) * u r) / denom r
  have hGL : HasDerivAt gradientLow 0 0 := by
    have h := ((((hmD.sub hlow).mul hq).sub (((hX.pow 2).mul hC).mul hu)).div
      hdenom hdenom0)
    apply h.congr_deriv
    simp [gradientLow, denom, denomRad, low, gap, rad, mA, mC, mD, X,
      A, C, D, q, u, hA0, hC0, hD0]
    ring
  have hGH : HasDerivAt gradientHigh
      (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
    have h := ((hC.mul hq).add ((hmD.sub hlow).mul hu)).div hdenom hdenom0
    apply h.congr_deriv
    simp [gradientHigh, denom, denomRad, low, gap, rad, mA, mC, mD, X,
      A, C, D, q, u, hA0, hC0, hD0]
    ring
  have hpair := hGL.prodMk hGH
  have hpairEq : ∀ r : ℝ,
      (gradientLow r, gradientHigh r) = independentRadiusSecondGradient (θ, r) := by
    intro r
    unfold independentRadiusSecondGradient independentSecondGradientFactors
    apply Prod.ext
    · change ((mD r - low r) * q r - r ^ 2 * C r * u r) / denom r = _
      simp [gradientLow]
    · change (C r * q r + (mD r - low r) * u r) / denom r = _
      simp [gradientHigh]
  exact hpair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hpairEq r).symm))
-/

/-- The normalized second-leg gradient pair has derivative
`(0, 4 b (3 J + P + 12) / 9)` at zero radius. -/
lemma independentRadiusSecondGradientJet (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let L : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).1
  let H : ℝ → ℝ := fun r ↦ (independentRadiusFirstSpectral (θ, r)).2
  let Q : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).1
  let U : ℝ → ℝ := fun r ↦ (independentRadiusFirstGradient (θ, r)).2
  let A : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).1
  let C : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.1
  let D : ℝ → ℝ := fun r ↦
    (independentSecondResiduals θ.1 r (L r) (H r) (Q r) (U r)).2.2
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hX0 : X 0 = 0 := by
    simp [X]
  -- Reuse the established first-factor and residual jets coordinatewise.
  have hfirst := independentRadiusFirstFactorJets θ
  have hL : HasDerivAt L (θ.1 * (2 * θ.2.2 + θ.2.1 + 4)) 0 := by
    simpa only [L] using hasDerivAt_fst_of_prod hfirst.1
  have hH : HasDerivAt H (-2 * θ.1) 0 := by
    simpa only [H] using hasDerivAt_snd_of_prod hfirst.1
  have hQ : HasDerivAt Q (-2 * θ.1) 0 := by
    simpa only [Q] using hasDerivAt_fst_of_prod hfirst.2
  have hU : HasDerivAt U (θ.1 * (θ.2.1 - 6) / 3) 0 := by
    simpa only [U] using hasDerivAt_snd_of_prod hfirst.2
  have hL0 : L 0 = 2 := by
    simpa only [L] using congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
  have hH0 : H 0 = 1 := by
    simpa only [H] using congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
  have hQ0 : Q 0 = 1 := by
    simpa only [Q] using congrArg Prod.fst (independentRadiusFirstGradient_zero θ)
  have hU0 : U 0 = 1 := by
    simpa only [U] using congrArg Prod.snd (independentRadiusFirstGradient_zero θ)
  have hres := independentRadiusSecondResiduals_hasDerivAt θ
  have hA : HasDerivAt A
      (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) 0 := by
    simpa only [A, L, H, Q, U] using hasDerivAt_fst_of_prod hres
  have hC : HasDerivAt C
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [C, L, H, Q, U] using hasDerivAt_fst_of_prod hsecond
  have hD : HasDerivAt D (8 * θ.1) 0 := by
    have hsecond := hasDerivAt_snd_of_prod hres
    simpa only [D, L, H, Q, U] using hasDerivAt_snd_of_prod hsecond
  have hA0 : A 0 = 6 := by
    simp only [A, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg Prod.fst (independentRadiusSecondResiduals_zero θ)
  have hC0 : C 0 = 2 := by
    simp only [C, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.1)
      (independentRadiusSecondResiduals_zero θ)
  have hD0 : D 0 = 1 := by
    simp only [D, L, H, Q, U, independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
    exact congrArg (fun t : ℝ × ℝ × ℝ ↦ t.2.2)
      (independentRadiusSecondResiduals_zero θ)
  let w₁ : ℝ → ℝ := X * L * Q - fun r ↦ 2 * θ.1 * (H * U) r
  let w₂ : ℝ → ℝ := H * U - fun r ↦ 2 * θ.1 * (X * L * Q) r
  let β : ℝ → ℝ := X * L * Q * w₁ + H * U * w₂
  let δ : ℝ → ℝ := L * Q ^ 2 + H * U ^ 2
  have hw₁ : HasDerivAt w₁
      (2 + 2 * θ.1 ^ 2 * (12 - θ.2.1) / 3) 0 := by
    have h := ((hX.mul hL).mul hQ).sub ((hH.mul hU).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₁, X, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hw₂ : HasDerivAt w₂ (θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (hH.mul hU).sub (((hX.mul hL).mul hQ).const_mul (2 * θ.1))
    apply h.congr_deriv
    simp [w₂, X, L, H, Q, U, hL0, hH0, hQ0, hU0, hX0]
    ring
  have hβ : HasDerivAt β (2 * θ.1 * (θ.2.1 - 24) / 3) 0 := by
    have h := (((hX.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
    apply h.congr_deriv
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0]
    ring
  have hβ0 : β 0 ≠ 0 := by
    simp [β, X, L, H, Q, U, w₁, w₂, hL0, hH0, hQ0, hU0, hX0]
  have hδ : HasDerivAt δ
      (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 30) / 3) 0 := by
    have h := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
    apply h.congr_deriv
    simp [δ, L, H, Q, U, hL0, hH0, hQ0, hU0]
    ring
  have hδ0 : δ 0 = 3 := by
    norm_num [δ, hL0, hH0, hQ0, hU0]
  let threeβ : ℝ → ℝ := fun r ↦ 3 * β r
  have hthreeβ : HasDerivAt threeβ (2 * θ.1 * (θ.2.1 - 24)) 0 := by
    have hcoefficient : 3 * (2 * θ.1 * (θ.2.1 - 24) / 3) =
        2 * θ.1 * (θ.2.1 - 24) := by
      ring
    exact hβ.const_mul 3 |>.congr_deriv hcoefficient
  have hthreeβ0 : threeβ 0 ≠ 0 := by
    simp [threeβ, hβ0]
  let q : ℝ → ℝ := Q - X * δ * w₁ / threeβ
  let u : ℝ → ℝ := U - δ * w₂ / threeβ
  have hq : HasDerivAt q 0 0 := by
    have h := hQ.sub (((hX.mul hδ).mul hw₁).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [q, threeβ, X, L, H, Q, U, δ, w₁, w₂, β,
      hL0, hH0, hQ0, hU0, hδ0]
    ring
  have hq0 : q 0 = 1 := by
    norm_num [q, threeβ, X, δ, w₁, β, hX0, hL0, hH0, hQ0, hU0, hδ0]
  have hu0 : u 0 = 0 := by
    norm_num [u, threeβ, X, δ, w₂, β, hX0, hL0, hH0, hQ0, hU0, hδ0]
  have hu : HasDerivAt u
      (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9) 0 := by
    have h := hU.sub ((hδ.mul hw₂).div hthreeβ hthreeβ0)
    apply h.congr_deriv
    simp [u, threeβ, X, L, H, Q, U, δ, w₁, w₂, β,
      hL0, hH0, hQ0, hU0, hδ0]
    ring
  let mA : ℝ → ℝ := fun r ↦ X r ^ 2 * A r
  let mC : ℝ → ℝ := fun r ↦ X r * C r
  let mD : ℝ → ℝ := D
  have hmA : HasDerivAt mA 0 0 := by
    have hcoefficient :
        2 * X 0 ^ (2 - 1) * 1 * A 0 + X 0 ^ 2 *
            (θ.1 * (30 * θ.2.2 + 7 * θ.2.1 + 204) / 3) = 0 := by
      simp [X]
    exact (hX.pow 2).mul hA |>.congr_deriv hcoefficient
  have hmC : HasDerivAt mC 2 0 := by
    have hcoefficient : 1 * C 0 + X 0 *
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) = 2 := by
      simp [X, hC0]
    exact hX.mul hC |>.congr_deriv hcoefficient
  have hmD : HasDerivAt mD (8 * θ.1) 0 := hD
  have hmA0 : mA 0 = 0 := by
    simp [mA, X]
  have hmC0 : mC 0 = 0 := by
    simp [mC, X]
  have hmD0 : mD 0 = 1 := hD0
  let rad : ℝ → ℝ := fun r ↦ (mA r - mD r) ^ 2 + 4 * (mC r) ^ 2
  have hrad : HasDerivAt rad (16 * θ.1) 0 := by
    have hcoefficient :
        (2 : ℝ) * (mA - mD) 0 ^ (2 - 1) * (0 - 8 * θ.1) +
            4 * ((2 : ℝ) * mC 0 ^ (2 - 1) * 2) = 16 * θ.1 := by
      simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
      ring
    exact ((hmA.sub hmD).pow 2).add ((hmC.pow 2).const_mul 4) |>.congr_deriv
      hcoefficient
  have hrad0 : rad 0 ≠ 0 := by
    simp [rad, mA, mC, mD, X, hA0, hC0, hD0]
  let gap : ℝ → ℝ := fun r ↦ Real.sqrt (rad r)
  have hgap : HasDerivAt gap (8 * θ.1) 0 := by
    have hcoefficient : 16 * θ.1 / (2 * Real.sqrt (rad 0)) = 8 * θ.1 := by
      simp [gap, rad, mA, mC, mD, X, hA0, hC0, hD0]
      ring_nf
    exact (hrad.sqrt hrad0).congr_deriv hcoefficient
  have hgap0 : gap 0 = 1 := by
    norm_num [gap, rad, hmA0, hmC0, hmD0]
  let low : ℝ → ℝ := fun r ↦ (mA r + mD r - gap r) / 2
  have hlow : HasDerivAt low 0 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by
      norm_num
    have hcoefficient :
        ((0 + 8 * θ.1 - 8 * θ.1) * 2 - (mA + mD - gap) 0 * 0) / 2 ^ 2 = 0 := by
      simp [low]
    exact ((hmA.add hmD).sub hgap).div (hasDerivAt_const 0 (2 : ℝ)) htwo
      |>.congr_deriv hcoefficient
  have hlow0 : low 0 = 0 := by
    norm_num [low, hmA0, hmD0, hgap0]
  let denomRad : ℝ → ℝ := fun r ↦ (mD r - low r) ^ 2 + (mC r) ^ 2
  have hdenomRad : HasDerivAt denomRad (16 * θ.1) 0 := by
    have hcoefficient :
        2 * (mD - low) 0 ^ (2 - 1) * (8 * θ.1 - 0) +
            2 * mC 0 ^ (2 - 1) * 2 = 16 * θ.1 := by
      simp [denomRad, hmD0, hlow0, hmC0]
      ring
    exact ((hmD.sub hlow).pow 2).add (hmC.pow 2) |>.congr_deriv hcoefficient
  have hdenomRadValue : denomRad 0 = 1 := by
    norm_num [denomRad, hmD0, hlow0, hmC0]
  have hdenomRad0 : denomRad 0 ≠ 0 := by
    rw [hdenomRadValue]
    norm_num
  let denom : ℝ → ℝ := fun r ↦ Real.sqrt (denomRad r)
  have hdenom : HasDerivAt denom (8 * θ.1) 0 := by
    have hcoefficient : 16 * θ.1 / (2 * Real.sqrt (denomRad 0)) = 8 * θ.1 := by
      rw [hdenomRadValue]
      norm_num
      ring
    exact (hdenomRad.sqrt hdenomRad0).congr_deriv hcoefficient
  have hdenomValue : denom 0 = 1 := by
    norm_num [denom, hdenomRadValue]
  have hdenom0 : denom 0 ≠ 0 := by
    rw [hdenomValue]
    norm_num
  let gradientLow : ℝ → ℝ := ((mD - low) * q - X ^ 2 * C * u) / denom
  let gradientHigh : ℝ → ℝ := (C * q + (mD - low) * u) / denom
  have hGL : HasDerivAt gradientLow 0 0 := by
    have hcoefficient :
        (((8 * θ.1 - 0) * q 0 + (mD - low) 0 * 0 -
            ((2 * X 0 ^ (2 - 1) * 1 * C 0 + X 0 ^ 2 *
                (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)) * u 0 +
              (X ^ 2 * C) 0 * (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9))) *
          denom 0 - ((mD - low) * q - X ^ 2 * C * u) 0 * (8 * θ.1)) /
          denom 0 ^ 2 = 0 := by
      simp [gradientLow, hmD0, hlow0, hq0, hX0, hC0, hu0, hdenomValue]
    exact ((((hmD.sub hlow).mul hq).sub (((hX.pow 2).mul hC).mul hu)).div
      hdenom hdenom0).congr_deriv hcoefficient
  have hGH : HasDerivAt gradientHigh
      (4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
    have hcoefficient :
        (((θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) * q 0 + C 0 * 0 +
            ((8 * θ.1 - 0) * u 0 + (mD - low) 0 *
              (θ.1 * (θ.2.1 - 6 * θ.2.2 - 60) / 9))) * denom 0 -
          (C * q + (mD - low) * u) 0 * (8 * θ.1)) / denom 0 ^ 2 =
          4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9 := by
      simp [gradientHigh, hC0, hq0, hmD0, hlow0, hu0, hdenomValue]
      ring
    exact ((hC.mul hq).add ((hmD.sub hlow).mul hu)).div hdenom hdenom0
      |>.congr_deriv hcoefficient
  -- Identify the scalar square-root model with the fixed low-eigenvector chart.
  have hgapEq : ∀ r : ℝ,
      gap r = RealSymmetric2.gap (mA r) (mC r) (mD r) := by
    intro r
    simp only [gap, RealSymmetric2.gap_apply]
    congr 1
    ring
  have hlowEq : ∀ r : ℝ,
      low r = RealSymmetric2.low (mA r) (mC r) (mD r) := by
    intro r
    dsimp [low]
    rw [RealSymmetric2.low_apply, hgapEq r]
  have hdenomEq : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom (mA r) (mC r) (mD r) := by
    intro r
    simp [denom, denomRad, RealSymmetric2.lowDenom_apply, hlowEq r]
  have hlowEqConcrete : ∀ r : ℝ,
      low r = RealSymmetric2.low (r ^ 2 * A r) (r * C r) (D r) := by
    intro r
    simpa [mA, mC, mD, X] using hlowEq r
  have hdenomEqConcrete : ∀ r : ℝ,
      denom r = RealSymmetric2.lowDenom (r ^ 2 * A r) (r * C r) (D r) := by
    intro r
    simpa [mA, mC, mD, X] using hdenomEq r
  have hqEq : ∀ r : ℝ,
      q r = (independentSecondGradientResiduals θ.1 r
        (L r) (H r) (Q r) (U r)).1 := by
    intro r
    simp [q, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X]
    ring
  have huEq : ∀ r : ℝ,
      u r = (independentSecondGradientResiduals θ.1 r
        (L r) (H r) (Q r) (U r)).2 := by
    intro r
    simp [u, independentSecondGradientResiduals, threeβ, δ, β, w₁, w₂, X]
    ring
  have hpair := hGL.prodMk hGH
  have hpairEq : ∀ r : ℝ,
      (gradientLow r, gradientHigh r) = independentRadiusSecondGradient (θ, r) := by
    intro r
    unfold independentRadiusSecondGradient independentSecondGradientFactors
    apply Prod.ext
    · dsimp [gradientLow, A, C, D, L, H, Q, U, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r, hqEq r, huEq r]
    · dsimp [gradientHigh, A, C, D, L, H, Q, U, X]
      rw [hlowEqConcrete r, hdenomEqConcrete r, hqEq r, huEq r]
  exact hpair.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r ↦ (hpairEq r).symm))

/-- The normalized second-leg spectral and gradient pairs have their corrected component
jets at the zero-radius base point. -/
lemma independentRadiusSecondComponentJetCertificate (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusSecondSpectral (θ, r))
        (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0 ∧
      HasDerivAt (fun r ↦ independentRadiusSecondGradient (θ, r))
        (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  -- Package the independently verified component jets for the recovery calculation.
  exact ⟨independentRadiusSecondSpectralJet θ, independentRadiusSecondGradientJet θ⟩

/-- An oriented planar frame with the prescribed low/high
    eigenvalue and gradient coordinates produces the normalized recovery triple, independently
    of the global sign chosen by the orientation test. -/
lemma orientedRecoveryTriple_eq_normalizedFactors_of_frame
    (a b d r spectralLow spectralHigh gradientLow gradientHigh : ℝ)
    (v : Fin 2 → ℝ) (hr : r ≠ 0)
    (hframe :
      OrientedEigenframe.frame a b d (WithLp.toLp 2 v) =
          EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∨
        OrientedEigenframe.frame a b d (WithLp.toLp 2 v) =
          -EuclideanPlane.frame (RealSymmetric2.lowVector a b d))
    (hlow : RealSymmetric2.low a b d = r ^ 2 * spectralLow)
    (hhigh : RealSymmetric2.high a b d = spectralHigh)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![gradientLow, r * gradientHigh]) :
    let F := OrientedEigenframe.frame a b d (WithLp.toLp 2 v)
    let w := F.transpose.mulVec v
    (CycleBoundaryState.recoveryRadius (RealSymmetric2.low a b d)
        (RealSymmetric2.high a b d) (w 0) (w 1),
      CycleBoundaryState.recoveryShape (RealSymmetric2.low a b d)
        (RealSymmetric2.high a b d) (w 0) (w 1),
      RealSymmetric2.high a b d) =
      (r * (spectralLow * gradientLow / (spectralHigh * gradientHigh)),
        spectralHigh * gradientHigh ^ 2 / (spectralLow * gradientLow ^ 2),
        spectralHigh) := by
  have hfixed :
      (CycleBoundaryState.recoveryRadius (RealSymmetric2.low a b d)
          (RealSymmetric2.high a b d) gradientLow (r * gradientHigh),
        CycleBoundaryState.recoveryShape (RealSymmetric2.low a b d)
          (RealSymmetric2.high a b d) gradientLow (r * gradientHigh),
        RealSymmetric2.high a b d) =
        (r * (spectralLow * gradientLow / (spectralHigh * gradientHigh)),
          spectralHigh * gradientHigh ^ 2 / (spectralLow * gradientLow ^ 2),
          spectralHigh) := by
    rw [hlow, hhigh]
    unfold CycleBoundaryState.recoveryRadius CycleBoundaryState.recoveryShape
    apply Prod.ext
    · simp only [Prod.fst]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp [hr]
    · apply Prod.ext
      · simp only [Prod.snd, Prod.fst]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp [hr]
      · rfl
  dsimp only
  rcases hframe with hframe | hframe
  · rw [hframe, hcoords]
    exact hfixed
  · rw [hframe]
    have hnegcoords :
        (-EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          -![gradientLow, r * gradientHigh] := by
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hcoords]
    rw [hnegcoords]
    have hinvariant := recoveryTriple_neg_neg (RealSymmetric2.low a b d)
      (RealSymmetric2.high a b d) gradientLow (r * gradientHigh)
    simpa using hinvariant.trans hfixed

/-- Negating a planar vector negates both columns of its
    canonical orthonormal frame. -/
lemma euclideanPlane_frame_neg_of_vector (e : EuclideanSpace ℝ (Fin 2)) :
    EuclideanPlane.frame (-e) = -EuclideanPlane.frame e := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
  · fin_cases j
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]

/-- Away from the orthogonality boundary, negating the gradient
    flips the oriented low-eigenvector frame by one global sign. -/
lemma orientedEigenframe_frame_negate_gradient_of_inner_ne_zero
    (a b d : ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (hinner : inner ℝ (RealSymmetric2.lowVector a b d) g ≠ 0) :
    OrientedEigenframe.frame a b d (-g) =
      -OrientedEigenframe.frame a b d g := by
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  by_cases hpos : 0 < inner ℝ (RealSymmetric2.lowVector a b d) g
  · have hneg : ¬ 0 < inner ℝ (RealSymmetric2.lowVector a b d) (-g) := by
      have hnonpos : inner ℝ (RealSymmetric2.lowVector a b d) (-g) ≤ 0 := by
        simpa only [inner_neg_right] using neg_nonpos.mpr (le_of_lt hpos)
      exact not_lt_of_ge hnonpos
    rw [if_pos hpos, if_neg hneg]
    exact euclideanPlane_frame_neg_of_vector _
  · have hnonpos : inner ℝ (RealSymmetric2.lowVector a b d) g ≤ 0 :=
      le_of_not_gt hpos
    have hneg : inner ℝ (RealSymmetric2.lowVector a b d) g < 0 :=
      lt_of_le_of_ne hnonpos hinner
    have hposNeg : 0 < inner ℝ (RealSymmetric2.lowVector a b d) (-g) := by
      simpa only [inner_neg_right] using neg_pos.mpr hneg
    rw [if_neg hpos, if_pos hposNeg]
    rw [euclideanPlane_frame_neg_of_vector]
    simp

/-- The recovered triple obtained from one raw DFP step,
    with its orientation choice kept explicit for downstream transport lemmas. -/
noncomputable def independentRawRecoveredTriple
    (M : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) : ℝ × ℝ × ℝ :=
  let secondStep := independentRawStep M g control
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  let g₂ := secondFrame.transpose.mulVec secondStep.2
  let lambdaMinus := RealSymmetric2.low
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  let lambdaPlus := RealSymmetric2.high
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    lambdaPlus)

/-- When the output gradient is not orthogonal to the low
    eigenvector, simultaneous sign changes in the input gradient leave raw recovery unchanged. -/
lemma independentRawRecoveredTriple_negate_gradient
    (M H₂ : Matrix (Fin 2) (Fin 2) ℝ) (g g₂ : Fin 2 → ℝ)
    (control : PlanarDFPControl)
    (hstep : independentRawStep M g control = (H₂, g₂))
    (hinner :
      inner ℝ
        (RealSymmetric2.lowVector (H₂ 0 0) (H₂ 0 1) (H₂ 1 1))
        (WithLp.toLp 2 g₂) ≠ 0) :
    independentRawRecoveredTriple M (-g) control =
      independentRawRecoveredTriple M g control := by
  have hnegstep : independentRawStep M (-g) control = (H₂, -g₂) := by
    rw [independentRawStep_negate_gradient, hstep]
  unfold independentRawRecoveredTriple
  rw [hnegstep, hstep]
  dsimp only
  have hframe := orientedEigenframe_frame_negate_gradient_of_inner_ne_zero
    (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) (WithLp.toLp 2 g₂) hinner
  rw [WithLp.toLp_neg, hframe]
  simp only [Matrix.transpose_neg, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]

/-- After a concrete second raw step has been identified,
    its frame-level recovery data determine the normalized independent-radius triple. -/
lemma independentRawRecoveredTriple_eq_normalizedFactors_of_secondStep
    (b r spectralLow spectralHigh gradientLow gradientHigh : ℝ)
    (M H₂ : Matrix (Fin 2) (Fin 2) ℝ) (g g₂ : Fin 2 → ℝ)
    (hstep : independentRawStep M g (TwoPhaseControls.second b) = (H₂, g₂))
    (hframe :
      OrientedEigenframe.frame (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) (WithLp.toLp 2 g₂) =
          EuclideanPlane.frame
            (RealSymmetric2.lowVector (H₂ 0 0) (H₂ 0 1) (H₂ 1 1)) ∨
        OrientedEigenframe.frame (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) (WithLp.toLp 2 g₂) =
          -EuclideanPlane.frame
            (RealSymmetric2.lowVector (H₂ 0 0) (H₂ 0 1) (H₂ 1 1)))
    (hlow : RealSymmetric2.low (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) =
      r ^ 2 * spectralLow)
    (hhigh : RealSymmetric2.high (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) = spectralHigh)
    (hcoords :
      (EuclideanPlane.frame
        (RealSymmetric2.lowVector (H₂ 0 0) (H₂ 0 1) (H₂ 1 1))).transpose.mulVec g₂ =
        ![gradientLow, r * gradientHigh])
    (hr : r ≠ 0) :
    independentRawRecoveredTriple M g (TwoPhaseControls.second b) =
      (r * (spectralLow * gradientLow / (spectralHigh * gradientHigh)),
        spectralHigh * gradientHigh ^ 2 / (spectralLow * gradientLow ^ 2),
        spectralHigh) := by
  unfold independentRawRecoveredTriple
  dsimp only
  rw [hstep]
  exact orientedRecoveryTriple_eq_normalizedFactors_of_frame
    (H₂ 0 0) (H₂ 0 1) (H₂ 1 1) r spectralLow spectralHigh gradientLow gradientHigh g₂ hr
    hframe hlow hhigh hcoords

end DFP.TwoLeg.Mixed
