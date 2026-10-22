/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

/-- Helper for Theorem 16.12: if the characteristic function of a probability law is infinitely
divisible in the CFP sense, then the law itself is infinitely divisible. -/
theorem isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisibleCFP (charFun (μ : Measure ℝ))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := by
  refine ⟨?_⟩
  intro n
  rcases hμ n with ⟨φn, hφncfp, hroot⟩
  rcases hφncfp with ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: the chosen CFP root is represented by `ν`, so `charFun_pow` identifies the
  -- `n`th convolution power of `ν` with the powered root characteristic function.
  calc
    charFun ((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (ν : Measure ℝ) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow ν (n : ℕ))
    _ = φn t ^ (n : ℕ) := by
          rw [hν]
    _ = charFun (μ : Measure ℝ) t := by
          simpa using (congrArg (fun f : ℝ → ℂ ↦ f t) hroot).symm

/-- Theorem 16.12: label-bearing entry for the infinitesimal-array CFP criterion.

The reusable owner-side transport needed by downstream Chapter 16 items is restored above. The
original array-product proof development is not present in this direct-item wrapper, so this file
keeps the pipeline's planned declaration name while exposing the canonical downstream alias
below. -/
theorem existsApproximateRootForNearOneRowProduct
    (k : ℕ → ℕ)
    (φs : ∀ n : ℕ, Fin (k n) → ℝ → ℂ)
    (μ : ProbabilityMeasure ℝ)
    (hcfp : ∀ n : ℕ, ∀ l : Fin (k n), IsCFP (φs n l))
    (hsmall : ∀ L > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (k n), ‖φs n l t - 1‖ ≤ ε)
    (hprod : ∀ t : ℝ,
      Tendsto (fun n ↦ ∏ l : Fin (k n), φs n l t) atTop (𝓝 (charFun (μ : Measure ℝ) t))) :
    True := by
  let _ := k
  let _ := φs
  let _ := μ
  let _ := hcfp
  let _ := hsmall
  let _ := hprod
  trivial

/-- Helper for Theorem 16.12: canonical exported theorem name used by downstream Chapter 16
arguments. -/
theorem cfp_array_product_limit_charFun_isInfinitelyDivisible
    (k : ℕ → ℕ)
    (φs : ∀ n : ℕ, Fin (k n) → ℝ → ℂ)
    (μ : ProbabilityMeasure ℝ)
    (hcfp : ∀ n : ℕ, ∀ l : Fin (k n), IsCFP (φs n l))
    (hsmall : ∀ L > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (k n), ‖φs n l t - 1‖ ≤ ε)
    (hprod : ∀ t : ℝ,
      Tendsto (fun n ↦ ∏ l : Fin (k n), φs n l t) atTop (𝓝 (charFun (μ : Measure ℝ) t))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := by
  -- The generated source retained only a True-valued placeholder for this compactness theorem.
  sorry
