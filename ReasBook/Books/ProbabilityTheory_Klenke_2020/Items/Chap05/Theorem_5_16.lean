/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: first obtain the almost sure convergence of the empirical averages from the
-- canonical pairwise-independent strong law `ProbabilityTheory.strong_law_ae_real`; then rewrite
-- this convergence in the centered form used by `satisfies_strong_law_of_large_numbers` and use
-- the `L²` hypotheses to supply the required termwise integrability.

/-- Theorem 5.16: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers as soon as its terms are pairwise independent, identically
distributed, and square integrable. -/
theorem satisfies_strong_law_of_large_numbers_of_pairwise_indep_identDistrib_memLp_two
    (X : ℕ → Ω → ℝ) (hX1_memLp : MemLp (X 1) 2 P)
    (hX_indep : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1))
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: each shifted term is integrable because every `L²` random variable is.
    intro n
    exact ((hX_ident n).memLp_iff.mpr hX1_memLp).integrable (by norm_num)
  · -- Proof comment: apply the raw strong law to the shifted `0`-based sequence and then
    -- translate the resulting limit to centered averages.
    have hraw :
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop
          (𝓝 P[X 1]) := by
      simpa using
        ProbabilityTheory.strong_law_ae_real (fun n ↦ X (n + 1))
          (hX1_memLp.integrable (by norm_num)) hX_indep hX_ident
    exact _root_.ae_tendsto_centered_average_of_ae_tendsto_raw_average P X hX_ident hraw
