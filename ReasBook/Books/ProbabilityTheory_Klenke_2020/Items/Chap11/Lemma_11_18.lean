/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u}

/- Lemma 11.18 is `source-facing`: it is about the normalized branching population
`W_n = Z_n / m^n`. Its `core/canonical` owners are the martingale API for
`Filtration.natural Z hZ_sm` and the discrete-time constructor `martingale_nat`. The abbreviation
below is only the minimal `bridge/view` layer needed to keep the textbook notation reusable in the
later branching-process items of this chapter. -/
/-- The normalized branching-process sequence `W_n = Z_n / m^n` attached to a real-valued
generation-size process `Z`. -/
abbrev branchingNormalizedProcess (Z : ℕ → Ω → ℝ) (m : ℝ) : ℕ → Ω → ℝ :=
  fun n ↦ (m ^ n)⁻¹ • Z n

variable [MeasurableSpace Ω]

section Martingale

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {Z : ℕ → Ω → ℝ} {m : ℝ}

/-- Helper for Lemma 11.18: after one branching step, the extra factor `m` cancels exactly one
normalizing power of `m`. -/
private theorem branchingNormalizationScalar_cancel (hm : 0 < m) (n : ℕ) (x : ℝ) :
    (m ^ (n + 1))⁻¹ * (m * x) = (m ^ n)⁻¹ * x := by
  have hm0 : m ≠ 0 := hm.ne'
  -- Proof comment: expand `m^(n+1)` and clear the nonzero denominator once.
  field_simp [pow_succ, hm0, mul_assoc]
  ring

-- Proof sketch: show that the normalized process is strongly adapted to the natural filtration of
-- `Z`, use integrability of `Z_n / m^n`, and rewrite the assumed one-step conditional expectation
-- `E[Z_{n+1} | 𝓕_n] = m Z_n` into the normalized identity
-- `E[W_{n+1} | 𝓕_n] = W_n`; then apply `MeasureTheory.martingale_nat`.
/-- Lemma 11.18: if `W_n = Z_n / m^n` and the generation process satisfies the branching relation
`E[Z_{n+1} | 𝓕_n] = m Z_n` for the natural filtration of `Z`, then `W` is a martingale. -/
theorem branchingNormalizedProcess_martingale (hm : 0 < m)
    (hZ_sm : ∀ n, StronglyMeasurable (Z n)) (hZ_int : ∀ n, Integrable (Z n) μ)
    (h_step : ∀ n,
      μ[Z (n + 1) | (Filtration.natural Z hZ_sm) n] =ᵐ[μ] fun ω ↦ m * Z n ω) :
    Martingale (branchingNormalizedProcess Z m) (Filtration.natural Z hZ_sm) μ := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural Z hZ_sm
  let W : ℕ → Ω → ℝ := branchingNormalizedProcess Z m
  have hW_adapted : StronglyAdapted ℱ W := by
    intro n
    -- Proof comment: `W n` is just a deterministic scalar multiple of `Z n`.
    simpa [ℱ, W, branchingNormalizedProcess] using
      (Filtration.stronglyAdapted_natural hZ_sm n).const_smul ((m ^ n)⁻¹)
  have hW_int : ∀ n, Integrable (W n) μ := by
    intro n
    -- Proof comment: integrability is preserved under multiplication by the deterministic factor
    -- `(m^n)⁻¹`.
    simpa [W, branchingNormalizedProcess] using (hZ_int n).smul ((m ^ n)⁻¹)
  have hW_step : ∀ n, μ[W (n + 1) | ℱ n] =ᵐ[μ] W n := by
    intro n
    calc
      μ[W (n + 1) | ℱ n] =ᵐ[μ] (m ^ (n + 1))⁻¹ • μ[Z (n + 1) | ℱ n] := by
        -- Proof comment: pull the deterministic normalization factor through conditional
        -- expectation.
        simpa [ℱ, W, branchingNormalizedProcess] using
          (condExp_smul (μ := μ) ((m ^ (n + 1))⁻¹) (Z (n + 1)) (ℱ n))
      _ =ᵐ[μ] fun ω ↦ (m ^ (n + 1))⁻¹ * (m * Z n ω) := by
        -- Proof comment: replace the successor conditional expectation with the branching-step
        -- formula supplied in the hypotheses.
        simpa [Pi.smul_apply, smul_eq_mul, ℱ] using
          (h_step n).const_smul ((m ^ (n + 1))⁻¹)
      _ =ᵐ[μ] W n := by
        -- Proof comment: the normalization cancels one power of `m`, leaving `W n`.
        filter_upwards with ω
        simpa [W, branchingNormalizedProcess, Pi.smul_apply, smul_eq_mul] using
          branchingNormalizationScalar_cancel hm n (Z n ω)
  -- Proof comment: the one-step conditional expectation criterion is exactly `martingale_nat`.
  refine MeasureTheory.martingale_nat hW_adapted hW_int ?_
  intro n
  simpa [ℱ, W] using (hW_step n).symm

end Martingale

section Expectation

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Z : ℕ → Ω → ℝ} {m : ℝ}

variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]

-- Proof sketch: the martingale property makes the expectations of `W_n` constant in `n`. Since
-- `W_0 = Z_0 = 1` almost surely, `E[W_n] = 1`; multiplying by `m^n` gives `E[Z_n] = m^n`.
/-- If the normalized branching process is a martingale and the population starts from one
ancestor, then the expectations satisfy `E[Z_n] = m^n`. -/
theorem branchingProcess_expectation_eq_pow_mean (hm : 0 < m)
    (hW : Martingale (branchingNormalizedProcess Z m) ℱ μ) (hZ0 : ∀ᵐ ω ∂μ, Z 0 ω = 1)
    (n : ℕ) :
    μ[fun ω ↦ Z n ω] = m ^ n := by
  let W : ℕ → Ω → ℝ := branchingNormalizedProcess Z m
  have hW_mart : Martingale W ℱ μ := by
    simpa [W] using hW
  have hW_mean_eq : μ[W n] = μ[W 0] := by
    -- Proof comment: a martingale has the same expectation at every deterministic time.
    simpa [setIntegral_univ] using (hW_mart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
  have hW0_ae : W 0 =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
    -- Proof comment: the normalization at time `0` is trivial, so `W₀ = Z₀ = 1` almost surely.
    simpa [W, branchingNormalizedProcess] using hZ0
  have hW0_mean : μ[W 0] = (1 : ℝ) := by
    rw [integral_congr_ae hW0_ae]
    simp
  have hZ_recover : Z n = (m ^ n) • W n := by
    -- Proof comment: multiplying the normalized population by `m^n` recovers `Z_n`.
    funext ω
    simp [W, branchingNormalizedProcess, pow_ne_zero _ hm.ne']
  calc
    μ[fun ω ↦ Z n ω] = μ[(m ^ n) • W n] := by rw [hZ_recover]
    _ = (m ^ n) * μ[W n] := by
      simpa [smul_eq_mul] using MeasureTheory.integral_smul (m ^ n) (W n)
    _ = (m ^ n) * 1 := by rw [hW_mean_eq, hW0_mean]
    _ = m ^ n := by ring

end Expectation
