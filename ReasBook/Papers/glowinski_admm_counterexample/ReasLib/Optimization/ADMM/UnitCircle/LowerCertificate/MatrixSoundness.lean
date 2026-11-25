/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Sylvester
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.CoercivityInterpolation
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.StrictContinuation
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

open scoped ComplexOrder Topology

namespace ADMM.UnitCircle.LowerCertificate

/-- A Hermitian quotient is defined by the real diagonal parts and the full
complex cross entry. This remains meaningful at zero frequency. -/
noncomputable def quotientMatrix (A B C : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hermitianTwoByTwo (A z).re (B z).re (C z)

theorem hermitianTwoByTwo_isHermitian (a d : ℝ) (b : ℂ) :
    (hermitianTwoByTwo a d b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermitianTwoByTwo]

theorem quotientMatrix_isHermitian (A B C : ℂ → ℂ) (z : ℂ) :
    (quotientMatrix A B C z).IsHermitian := hermitianTwoByTwo_isHermitian _ _ _

/-- Three entry identities suffice for an exact Hermitian matrix factorization.
Taking real diagonal parts avoids dividing by the vanishing zero-frequency
factor or assuming realness of an unspecified quotient. -/
theorem factor_of_hermitian_entries {Q : Matrix (Fin 2) (Fin 2) ℂ}
    (hQ : Q.IsHermitian) (d : ℝ) (a b c : ℂ)
    (h00 : Q 0 0 = (d : ℂ) * a) (h11 : Q 1 1 = (d : ℂ) * b)
    (h01 : Q 0 1 = (d : ℂ) * c) :
    Q = (d : ℂ) • hermitianTwoByTwo a.re b.re c := by
  conv_lhs => rw [hermitian_eq_twoByTwo hQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTwoByTwo, h00, h11, h01, Complex.mul_re, Complex.star_def] <;> ring

/-- Subtracting the fixed margin preserves the explicit Hermitian form. -/
theorem quotientMatrix_sub_scalar (A B C : ℂ → ℂ) (κ : ℝ) (z : ℂ) :
    quotientMatrix A B C z - (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      hermitianTwoByTwo ((A z).re - κ) ((B z).re - κ) (C z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quotientMatrix, hermitianTwoByTwo, Complex.ofReal_sub]

/-- The scalar principal-minor certificates prove positivity of the full
shifted quotient, including its zero-frequency value. -/
theorem quotientMatrix_sub_scalar_posDef (A B C : ℂ → ℂ) (κ : ℝ) (z : ℂ)
    (hfirst : 0 < (A z).re - κ)
    (hdet : 0 < ((A z).re - κ) * ((B z).re - κ) - Complex.normSq (C z)) :
    (quotientMatrix A B C z - (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  rw [quotientMatrix_sub_scalar]
  exact hermitianTwoByTwo_posDef hfirst hdet

/-- Positive semidefiniteness of the quotient with the fixed margin transfers
to the actual supply bound, even where the scalar factor vanishes. -/
theorem hasCoercivityBound_of_factor {ℓ : ℕ} (c : LagWeights ℓ) (γ κ : ℝ)
    (H : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hfactor : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • H z)
    (hH : ∀ z : ℂ, ‖z‖ = 1 →
      (H z - (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    HasCoercivityBound c γ κ := by
  intro z hz
  have h := (hH z hz).smul (Complex.zero_le_real.mpr (Complex.normSq_nonneg (delaySymbol 1 z)))
  convert! h using 1
  rw [hfactor z hz]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The three exact scalar divisions and two strict scalar tests are a
complete endpoint certificate for the actual two-by-two supply. -/
theorem hasCoercivityBound_of_entry_quotients {ℓ : ℕ} (c : LagWeights ℓ) (γ κ : ℝ)
    (A B C : ℂ → ℂ)
    (h00 : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ z 0 0 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * A z)
    (h11 : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ z 1 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * B z)
    (h01 : ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ z 0 1 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * C z)
    (hfirst : ∀ z : ℂ, ‖z‖ = 1 → 0 < (A z).re - κ)
    (hdet : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((A z).re - κ) * ((B z).re - κ) - Complex.normSq (C z)) :
    HasCoercivityBound c γ κ := by
  apply hasCoercivityBound_of_factor c γ κ (quotientMatrix A B C)
  · intro z hz
    exact factor_of_hermitian_entries (supplySymbol_isHermitian c 1 γ z)
      _ _ _ _ (h00 z hz) (h11 z hz) (h01 z hz)
  · intro z hz
    exact (quotientMatrix_sub_scalar_posDef A B C κ z (hfirst z hz) (hdet z hz)).posSemidef

/-- Strict positivity of both principal minors persists uniformly on a
compact frequency set while keeping exactly the original scalar margin. -/
theorem shifted_posDef_right_continuation {X : Type} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (H : ℝ × X → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : Continuous H) (κ L U : ℝ) (hLU : L < U)
    (hHermitian : ∀ p : ℝ × X, (H p).IsHermitian)
    (hfirst : ∀ x ∈ K, 0 < ((H (L, x) -
      (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0).re)
    (hdet : ∀ x ∈ K, 0 < (H (L, x) -
      (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det.re) :
    ∃ δ : ℝ, 0 < δ ∧ L + δ < U ∧ ∀ γ ∈ Set.Icc L (L + δ), ∀ x ∈ K,
      (H (γ, x) - (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  let M := fun p : ℝ × X ↦ H p - (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hM : Continuous M := hH.sub continuous_const
  let f := fun p : ℝ × X ↦ min (M p 0 0).re (M p).det.re
  have hf : Continuous f :=
    (Complex.continuous_re.comp (hM.matrix_elem 0 0)).min
      (Complex.continuous_re.comp hM.matrix_det)
  have hpos : ∀ x ∈ K, 0 < f (L, x) := by
    intro x hx
    exact lt_min (hfirst x hx) (hdet x hx)
  obtain ⟨δ, hδ, hδU, he⟩ := strict_pos_right_continuation K hK f hf L U hLU hpos
  refine ⟨δ, hδ, hδU, ?_⟩
  intro γ hγ x hx
  have hm := lt_min_iff.mp (he γ hγ x hx)
  apply posDef_of_sylvester ?_ hm.1 hm.2
  apply (hHermitian (γ, x)).sub
  apply Matrix.isHermitian_one.smul
  simp [isSelfAdjoint_iff]

/-- The compact circle is represented without its pole at zero. -/
abbrev CircleFrequency := {z : ℂ // ‖z‖ = 1}

/-- A strict quotient certificate at the lower endpoint and an earlier
coercivity bound imply the full closed interval through a strict right
continuation, with the fixed coefficient `κ` unchanged. -/
theorem interval_coercivity_of_quotient_continuation {ℓ : ℕ} (c : LagWeights ℓ)
    (κ γ₀ L U : ℝ) (hγ₀L : γ₀ < L) (hLU : L < U)
    (H : ℝ → ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : Continuous (fun p : ℝ × CircleFrequency ↦ H p.1 p.2))
    (hHermitian : ∀ γ : ℝ, ∀ z : ℂ, ‖z‖ = 1 → (H γ z).IsHermitian)
    (hfactor : ∀ γ : ℝ, ∀ z : ℂ, ‖z‖ = 1 → supplySymbol c 1 γ z =
      (Complex.normSq (delaySymbol 1 z) : ℂ) • H γ z)
    (hstart : HasCoercivityBound c γ₀ κ)
    (hfirst : ∀ z : ℂ, ‖z‖ = 1 → 0 < ((H L z -
      (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0).re)
    (hdet : ∀ z : ℂ, ‖z‖ = 1 → 0 < (H L z -
      (κ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det.re) :
    ∃ δ : ℝ, 0 < δ ∧ L + δ < U ∧ ∀ γ : ℝ, γ₀ ≤ γ → γ ≤ L + δ →
      HasCoercivityBound c γ κ := by
  have hcircleCompact : IsCompact {z : ℂ | ‖z‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) 1
  letI : CompactSpace CircleFrequency := isCompact_iff_compactSpace.mp hcircleCompact
  obtain ⟨δ, hδ, hδU, he⟩ := shifted_posDef_right_continuation
    (Set.univ : Set CircleFrequency) isCompact_univ
    (fun p : ℝ × CircleFrequency ↦ H p.1 p.2) hH κ L U hLU
    (fun p ↦ hHermitian p.1 p.2 p.2.property)
    (fun z _ ↦ hfirst z z.property) (fun z _ ↦ hdet z z.property)
  have hfar : HasCoercivityBound c (L + δ) κ := by
    apply hasCoercivityBound_of_factor c (L + δ) κ (H (L + δ)) (hfactor (L + δ))
    intro z hz
    exact (he (L + δ) ⟨by linarith, le_rfl⟩ ⟨z, hz⟩ (Set.mem_univ _)).posSemidef
  refine ⟨δ, hδ, hδU, ?_⟩
  intro γ hγ₀ hγU
  exact hstart.on_interval hfar (by linarith) hγ₀ hγU

end ADMM.UnitCircle.LowerCertificate
