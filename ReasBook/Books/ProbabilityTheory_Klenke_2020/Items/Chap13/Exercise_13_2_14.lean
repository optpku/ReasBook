/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

-- Proof sketch: this is the one-dimensional specialization of the canonical Skorohod-coupling
-- theorem from Chapter 17.
/-- Exercise 13.2.14: if probability measures `μs n` on `ℝ` converge weakly to `μ`, then there
exists a probability space carrying real random variables with laws `μ` and `μs n` whose sample
paths converge almost surely to the limit random variable. -/
theorem exists_real_skorokhod_representation_of_tendsto
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (X : Ω → ℝ) (Xs : ℕ → Ω → ℝ),
      HasLaw X (μ : Measure ℝ) (P : Measure Ω) ∧
        (∀ n : ℕ, HasLaw (Xs n) (μs n : Measure ℝ) (P : Measure Ω)) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Xs n ω) atTop (𝓝 (X ω))) := by
  simpa using exists_skorohod_coupling μ μs hweak
