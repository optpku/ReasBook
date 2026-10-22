/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Helper for Corollary 16.8: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendsto_pnat_atTop_iff_succPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose back with `PNat.natPred` to recover the original `ℕ+` indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Corollary 16.8: a `ℕ+`-indexed CFP power approximation can be reindexed along
`Nat.toPNat'` to match the nat-indexed API used by Theorem 16.6. -/
private theorem existsNatIndexedCfpPowerApproximation
    {φ : ℝ → ℂ} {φs : ℕ+ → ℝ → ℂ}
    (hφs : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ t, Tendsto (fun n : ℕ+ ↦ (φs n t) ^ (n : ℕ)) atTop (𝓝 (φ t))) :
    ∃ ψs : ℕ → ℝ → ℂ,
      (∀ n : ℕ, IsCFP (ψs n)) ∧
        ∀ t, Tendsto (fun n : ℕ ↦ (ψs n t) ^ n) atTop (𝓝 (φ t)) := by
  let ψs : ℕ → ℝ → ℂ := fun n ↦ φs (Nat.toPNat' n)
  refine ⟨ψs, ?_, ?_⟩
  · intro n
    -- Proof comment: the reindexing keeps the same positive-index witness at every nat index.
    simpa [ψs] using hφs (Nat.toPNat' n)
  · intro t
    have hshiftPNat :
        Tendsto
          (fun n : ℕ ↦ (φs (Nat.succPNat n) t) ^ ((Nat.succPNat n : ℕ+) : ℕ))
          atTop
          (𝓝 (φ t)) :=
      (tendsto_pnat_atTop_iff_succPNat).1 (hpow t)
    have hshiftNat :
        Tendsto (fun n : ℕ ↦ (ψs (n + 1) t) ^ (n + 1)) atTop (𝓝 (φ t)) := by
      -- Proof comment: after shifting by one, `Nat.toPNat'` becomes exactly `Nat.succPNat`.
      simpa [ψs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using hshiftPNat
    -- Proof comment: a finite shift of a nat-indexed sequence does not change its `atTop` limit.
    exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshiftNat

/-
Corollary 16.8 is `source-facing`: it characterizes infinite divisibility directly at the
characteristic-function level by existence of a positive-integer-root approximation sequence. The
owner abstraction remains `IsInfinitelyDivisibleCFP`; the sequence in the right-hand side is
derived API, not new primitive data. The reverse implication is mediated by the chapter bridge
results in Theorem 16.6 / Corollary 16.7.
-/
-- Proof sketch: for the forward implication, take for each positive integer `n` the
-- characteristic-function root supplied by `IsInfinitelyDivisibleCFP`; then the `n`th
-- powers are exactly `φ`, so the sequence converges trivially. For the converse implication, apply
-- Corollary 16.7 to the pointwise limit of the `n`th powers of characteristic functions, using
-- the assumed continuity of `φ` at `0`.
/-- Corollary 16.8: a complex-valued function on `ℝ` that is continuous at `0` is an infinitely
divisible characteristic function if and only if there is a sequence of characteristic functions of
probability laws on `ℝ`, indexed by positive integers, whose `n`th pointwise powers converge to
`φ`. -/
theorem isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto
    {φ : ℝ → ℂ} (hφ : ContinuousAt φ 0) :
    IsInfinitelyDivisibleCFP φ ↔
      ∃ φs : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (φs n)) ∧
          ∀ t, Tendsto (fun n : ℕ+ ↦ (φs n t) ^ (n : ℕ)) atTop (𝓝 (φ t)) := by
  constructor
  · intro hdiv
    classical
    let φs : ℕ+ → ℝ → ℂ := fun n ↦ Classical.choose (hdiv n)
    refine ⟨φs, ?_, ?_⟩
    · intro n
      -- Proof comment: each chosen exact root is a characteristic function by construction.
      exact (Classical.choose_spec (hdiv n)).1
    · intro t
      have hconst : (fun n : ℕ+ ↦ (φs n t) ^ (n : ℕ)) = fun _ : ℕ+ ↦ φ t := by
        funext n
        -- Proof comment: the positive-integer root identity identifies every term with `φ t`.
        simpa [φs] using congrArg (fun f : ℝ → ℂ ↦ f t) (Classical.choose_spec (hdiv n)).2.symm
      -- Proof comment: once the powered sequence is pointwise constant, convergence is trivial.
      rw [hconst]
      exact tendsto_const_nhds
  · rintro ⟨φs, hφs, hpow⟩
    rcases existsNatIndexedCfpPowerApproximation hφs hpow with ⟨ψs, hψs, hpowNat⟩
    rcases
        (cfp_power_limit_iff_linearized_limit (φs := ψs) (hφs := hψs)).1
          ⟨φ, hpowNat, hφ⟩ with
      ⟨ψ, hlin, hψ0⟩
    have hφexp : φ = fun t : ℝ ↦ Complex.exp (ψ t) :=
      cfp_power_limit_eq_cexp_linearized_limit
        (φs := ψs) (φ := φ) (ψ := ψ) (hφs := hψs)
        (hpow := hpowNat) (hφ0 := hφ) (hlin := hlin)
    have hdivExp : IsInfinitelyDivisibleCFP (fun t : ℝ ↦ Complex.exp (ψ t)) :=
      levyKhinchin_exponential_has_characteristicRoots
        (φs := ψs) (ψ := ψ) hψs hlin hψ0
    -- Proof comment: Theorem 16.6 identifies the original limit with this exponential CFP.
    simpa [hφexp] using hdivExp
