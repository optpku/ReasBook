/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.MatrixSoundness
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Laurent
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section

open scoped ComplexOrder

namespace ADMM.UnitCircle.LowerCertificate

/-- Every finite rational Laurent expression is continuous on the compact
unit circle, including its zero-frequency point. -/
theorem evaluateLaurent_continuous_circle (p : Laurent) :
    Continuous (fun z : CircleFrequency ↦ evaluateLaurent p z) := by
  induction p with
  | nil => exact continuous_const
  | cons e p ih =>
    simp only [evaluateLaurent_cons]
    apply (continuous_const.mul ?_).add ih
    apply continuous_subtype_val.zpow₀
    intro z
    left
    exact norm_ne_zero_iff.mp (by rw [z.property]; norm_num)

theorem quotientMatrix_continuous_circle (A B C : ℂ → ℂ)
    (hA : Continuous (fun z : CircleFrequency ↦ A z))
    (hB : Continuous (fun z : CircleFrequency ↦ B z))
    (hC : Continuous (fun z : CircleFrequency ↦ C z)) :
    Continuous (fun z : CircleFrequency ↦ quotientMatrix A B C z) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [quotientMatrix, hermitianTwoByTwo, Function.comp_def] using
      Complex.continuous_ofReal.comp (Complex.continuous_re.comp hA)
  · simpa [quotientMatrix, hermitianTwoByTwo] using hC
  · simpa [quotientMatrix, hermitianTwoByTwo] using hC.star
  · simpa [quotientMatrix, hermitianTwoByTwo, Function.comp_def] using
      Complex.continuous_ofReal.comp (Complex.continuous_re.comp hB)

/-- The quotient is continued affinely in the relaxation parameter, retaining
the exact fixed endpoint quotient functions. -/
noncomputable def affineQuotientFamily (γ₀ L : ℝ)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (γ : ℝ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let θ := (γ - γ₀) / (L - γ₀)
  ((1 - θ : ℝ) : ℂ) • H₀ z + (θ : ℂ) • HL z

@[simp] theorem affineQuotientFamily_left (γ₀ L : ℝ)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    affineQuotientFamily γ₀ L H₀ HL γ₀ z = H₀ z := by simp [affineQuotientFamily]

theorem affineQuotientFamily_right {γ₀ L : ℝ} (h : γ₀ < L)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    affineQuotientFamily γ₀ L H₀ HL L z = HL z := by
  simp [affineQuotientFamily, div_self (sub_pos.mpr h).ne']

theorem affineQuotientFamily_isHermitian (γ₀ L γ : ℝ)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (h₀ : (H₀ z).IsHermitian) (hL : (HL z).IsHermitian) :
    (affineQuotientFamily γ₀ L H₀ HL γ z).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact h₀.smul (by simp [isSelfAdjoint_iff])
  · exact hL.smul (by simp [isSelfAdjoint_iff])

theorem affineQuotientFamily_continuous_circle (γ₀ L : ℝ)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (h₀ : Continuous (fun z : CircleFrequency ↦ H₀ z))
    (hL : Continuous (fun z : CircleFrequency ↦ HL z)) :
    Continuous (fun p : ℝ × CircleFrequency ↦ affineQuotientFamily γ₀ L H₀ HL p.1 p.2) := by
  have hθ : Continuous (fun p : ℝ × CircleFrequency ↦ (p.1 - γ₀) / (L - γ₀)) :=
    (continuous_fst.sub continuous_const).div_const _
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub hθ)).smul
    (h₀.comp continuous_snd)).add
    ((Complex.continuous_ofReal.comp hθ).smul (hL.comp continuous_snd))

/-- The parameter-affinity of the actual supply transports the two exact
endpoint scalar factorizations to every real parameter, including the
right continuation beyond `L`. -/
theorem affineQuotientFamily_factor {ℓ : ℕ} (c : LagWeights ℓ)
    {γ₀ L : ℝ} (hγ₀L : γ₀ < L)
    (H₀ HL : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (h₀ : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ₀ z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • H₀ z)
    (hL : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 L z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • HL z)
    (γ : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    supplySymbol c 1 γ z = (Complex.normSq (delaySymbol 1 z) : ℂ) •
      affineQuotientFamily γ₀ L H₀ HL γ z := by
  let θ := (γ - γ₀) / (L - γ₀)
  have heq : (1 - θ) * γ₀ + θ * L = γ := by
    dsimp [θ]
    field_simp [(sub_pos.mpr hγ₀L).ne']
    ring
  have h := supplySymbol_affine c 1 γ₀ L θ z
  rw [heq] at h
  rw [h, h₀ z hz, hL z hz]
  ext i j
  simp only [affineQuotientFamily, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp [θ]
  ring

/-- Endpoint quotient minors are a complete input interface to the fixed
margin lower-certificate claim. All continuity, affine extension, compactness,
Sylvester and matrix-order steps are discharged here. -/
theorem interval_coercivity_of_endpoint_quotients {ℓ : ℕ} (c : LagWeights ℓ)
    (κ γ₀ L U : ℝ) (hγ₀L : γ₀ < L) (hLU : L < U)
    (A₀ B₀ C₀ AL BL CL : ℂ → ℂ)
    (hA₀ : Continuous (fun z : CircleFrequency ↦ A₀ z))
    (hB₀ : Continuous (fun z : CircleFrequency ↦ B₀ z))
    (hC₀ : Continuous (fun z : CircleFrequency ↦ C₀ z))
    (hAL : Continuous (fun z : CircleFrequency ↦ AL z))
    (hBL : Continuous (fun z : CircleFrequency ↦ BL z))
    (hCL : Continuous (fun z : CircleFrequency ↦ CL z))
    (hentries₀ : ∀ z : ℂ, ‖z‖ = 1 →
      supplySymbol c 1 γ₀ z 0 0 = (Complex.normSq (delaySymbol 1 z) : ℂ) * A₀ z ∧
      supplySymbol c 1 γ₀ z 1 1 = (Complex.normSq (delaySymbol 1 z) : ℂ) * B₀ z ∧
      supplySymbol c 1 γ₀ z 0 1 = (Complex.normSq (delaySymbol 1 z) : ℂ) * C₀ z)
    (hentriesL : ∀ z : ℂ, ‖z‖ = 1 →
      supplySymbol c 1 L z 0 0 = (Complex.normSq (delaySymbol 1 z) : ℂ) * AL z ∧
      supplySymbol c 1 L z 1 1 = (Complex.normSq (delaySymbol 1 z) : ℂ) * BL z ∧
      supplySymbol c 1 L z 0 1 = (Complex.normSq (delaySymbol 1 z) : ℂ) * CL z)
    (hfirst₀ : ∀ z : ℂ, ‖z‖ = 1 → 0 < (A₀ z).re - κ)
    (hdet₀ : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((A₀ z).re - κ) * ((B₀ z).re - κ) - Complex.normSq (C₀ z))
    (hfirstL : ∀ z : ℂ, ‖z‖ = 1 → 0 < (AL z).re - κ)
    (hdetL : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((AL z).re - κ) * ((BL z).re - κ) - Complex.normSq (CL z)) :
    ∃ δ : ℝ, 0 < δ ∧ L + δ < U ∧ ∀ γ : ℝ, γ₀ ≤ γ → γ ≤ L + δ →
      HasCoercivityBound c γ κ := by
  let H₀ := quotientMatrix A₀ B₀ C₀
  let HL := quotientMatrix AL BL CL
  have hf₀ : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ₀ z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • H₀ z := by
    intro z hz
    exact factor_of_hermitian_entries (supplySymbol_isHermitian c 1 γ₀ z) _ _ _ _
      (hentries₀ z hz).1 (hentries₀ z hz).2.1 (hentries₀ z hz).2.2
  have hfL : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 L z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • HL z := by
    intro z hz
    exact factor_of_hermitian_entries (supplySymbol_isHermitian c 1 L z) _ _ _ _
      (hentriesL z hz).1 (hentriesL z hz).2.1 (hentriesL z hz).2.2
  apply interval_coercivity_of_quotient_continuation c κ γ₀ L U hγ₀L hLU
    (affineQuotientFamily γ₀ L H₀ HL)
  · exact affineQuotientFamily_continuous_circle γ₀ L H₀ HL
      (quotientMatrix_continuous_circle A₀ B₀ C₀ hA₀ hB₀ hC₀)
      (quotientMatrix_continuous_circle AL BL CL hAL hBL hCL)
  · intro γ z _
    exact affineQuotientFamily_isHermitian γ₀ L γ H₀ HL z
      (quotientMatrix_isHermitian _ _ _ _) (quotientMatrix_isHermitian _ _ _ _)
  · exact affineQuotientFamily_factor c hγ₀L H₀ HL hf₀ hfL
  · exact hasCoercivityBound_of_entry_quotients c γ₀ κ A₀ B₀ C₀
      (fun z hz ↦ (hentries₀ z hz).1) (fun z hz ↦ (hentries₀ z hz).2.1)
      (fun z hz ↦ (hentries₀ z hz).2.2) hfirst₀ hdet₀
  · intro z hz
    rw [affineQuotientFamily_right hγ₀L, quotientMatrix_sub_scalar]
    simpa [hermitianTwoByTwo] using hfirstL z hz
  · intro z hz
    rw [affineQuotientFamily_right hγ₀L, quotientMatrix_sub_scalar, hermitianTwoByTwo_det]
    simpa only [Complex.ofReal_re] using hdetL z hz

end ADMM.UnitCircle.LowerCertificate
