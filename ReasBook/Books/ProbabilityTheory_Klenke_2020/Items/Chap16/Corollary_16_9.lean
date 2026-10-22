/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Corollary 16.9: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
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

/-- Helper for Corollary 16.9: characteristic-function infinite divisibility of `charFun μ`
forces infinite divisibility of the underlying probability law `μ`. -/
private theorem isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisibleCFP (charFun (μ : Measure ℝ))) :
    IsInfinitelyDivisible μ := by
  refine ⟨?_⟩
  intro n
  rcases hμ n with ⟨φn, hφncfp, hroot⟩
  rcases hφncfp with ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: the chosen CFP root is the characteristic function of a probability law `ν`,
  -- so `charFun_pow` identifies the `n`th convolution power of `ν` with the `n`th pointwise
  -- power of `φn`.
  calc
    charFun ((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (ν : Measure ℝ) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow ν (n : ℕ))
    _ = φn t ^ (n : ℕ) := by
          rw [hν]
    _ = charFun (μ : Measure ℝ) t := by
          simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) hroot).symm

/-- Helper for Corollary 16.9: exact `ℕ+`-indexed convolution roots transport weak convergence of
`μs` into convergence of the powered characteristic functions of those roots. -/
private theorem rootCharPow_tendsto_charFun
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (ρ : ℕ+ → ProbabilityMeasure ℝ)
    (hρpow : ∀ n : ℕ+, ρ n ^ (n : ℕ) = μs n.natPred)
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ+ ↦ charFun (ρ n : Measure ℝ) t ^ (n : ℕ)) atTop
        (𝓝 (charFun (μ : Measure ℝ) t)) := by
  intro t
  rw [tendsto_pnat_atTop_iff_succPNat]
  have hchar :
      Tendsto (fun n : ℕ ↦ charFun (μs n : Measure ℝ) t) atTop
        (𝓝 (charFun (μ : Measure ℝ) t)) := by
    simpa using (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hμ t)
  let g : ℕ → ℂ := fun n ↦ charFun (ρ (Nat.succPNat n) : Measure ℝ) t ^ ((Nat.succPNat n : ℕ+) : ℕ)
  have hg : g = fun n : ℕ ↦ charFun (μs n : Measure ℝ) t := by
    funext n
    -- Proof comment: rewrite the powered root characteristic function through the exact root
    -- identity `ρ (n + 1)^ (n + 1) = μs n`.
    calc
      g n
          = charFun ((ρ (Nat.succPNat n) ^ ((Nat.succPNat n : ℕ+) : ℕ) :
              ProbabilityMeasure ℝ) : Measure ℝ) t := by
                symm
                simpa [g] using
                  congrArg (fun f : ℝ → ℂ ↦ f t)
                    (ProbabilityMeasure.charFun_pow (ρ (Nat.succPNat n))
                      (((Nat.succPNat n : ℕ+) : ℕ)))
      _ = charFun (μs n : Measure ℝ) t := by
            simpa [Nat.natPred_succPNat] using
              congrArg (fun ν : ProbabilityMeasure ℝ ↦ charFun (ν : Measure ℝ) t)
                (hρpow (Nat.succPNat n))
  have hshift :
      (fun n : ℕ ↦ charFun (ρ (Nat.succPNat n) : Measure ℝ) t ^ ((Nat.succPNat n : ℕ+) : ℕ)) =
        fun n : ℕ ↦ charFun (μs n : Measure ℝ) t := by
    simpa [g] using hg
  -- Proof comment: rewrite the shifted `ℕ+`-indexed power sequence into the original
  -- characteristic-function sequence of `μs`.
  exact hshift.symm ▸ hchar

-- Proof sketch: fix a positive integer `k`. For each `n`, choose a `k`th convolution root `νₙ` of
-- `μs n`. Weak convergence gives pointwise convergence of the characteristic functions of `μs n`,
-- so Theorem 16.6 applies to the characteristic functions of the roots `νₙ` and yields a
-- probability measure whose `k`th convolution power is `μ`. Since `k` was arbitrary, `μ` is
-- infinitely divisible.
/-- Corollary 16.9: if a sequence of infinitely divisible probability measures on `ℝ` converges
weakly to a probability measure `μ`, then `μ` is infinitely divisible. -/
theorem isInfinitelyDivisible_of_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ n : ℕ, IsInfinitelyDivisible (μs n)) (hμ : Tendsto μs atTop (𝓝 μ)) :
    IsInfinitelyDivisible μ := by
  classical
  let ρ : ℕ+ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose ((hμs n.natPred).exists_root n)
  have hρpow : ∀ n : ℕ+, ρ n ^ (n : ℕ) = μs n.natPred := by
    intro n
    exact Classical.choose_spec ((hμs n.natPred).exists_root n)
  have hchar0 : ContinuousAt (charFun (μ : Measure ℝ)) 0 := by
    -- Proof comment: characteristic functions of probability measures are automatically
    -- continuous.
    simpa using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  have hcfp :
      IsInfinitelyDivisibleCFP (charFun (μ : Measure ℝ)) := by
    refine (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto hchar0).2 ?_
    refine ⟨fun n ↦ charFun (ρ n : Measure ℝ), ?_, ?_⟩
    · intro n
      -- Proof comment: each chosen convolution root is itself a probability law, so its
      -- characteristic function is a CFP.
      simpa using ProbabilityMeasure.isCFP_charFun (ρ n)
    · -- Proof comment: the exact convolution-root identities turn weak convergence of `μs`
      -- into the required powered-characteristic-function convergence.
      exact rootCharPow_tendsto_charFun ρ hρpow hμ
  -- Proof comment: once the limiting characteristic function is infinitely divisible in the
  -- CFP sense, the owner-side bridge reconstructs infinitely divisible convolution roots of `μ`.
  exact isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP hcfp

end MeasureTheory.ProbabilityMeasure
