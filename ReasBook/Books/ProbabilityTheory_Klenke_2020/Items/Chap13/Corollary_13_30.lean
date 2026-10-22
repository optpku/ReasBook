/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory MeasureTheory.FiniteMeasure

universe u

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [CompactSpace E]

-- Proof sketch: compactness of `E` makes every family of measures tight, so Theorem 13.29 gives a
-- convergent subsequence for any sequence of subprobability finite measures. The mass bound is
-- preserved in the limit because `μ ↦ μ.mass` is continuous and `{t : NNReal | t ≤ 1}` is closed.
/-- Corollary 13.30 (1): for a compact metric space `E`, the textbook set `\mathcal{M}_{\le 1}(E)`
of sub-probability measures is weakly sequentially compact, viewed canonically as the set of finite
measures on `E` with total mass at most `1`. -/
theorem subprobabilityMeasures_isSeqCompact :
    IsSeqCompact {μ : FiniteMeasure E | μ.mass ≤ 1} := by
  let F : Set (FiniteMeasure E) := {μ | μ.mass ≤ 1}
  have hF : ∀ μ ∈ F, μ.mass ≤ 1 := by
    -- Proof comment: the defining predicate of `F` is exactly the mass bound required by
    -- Theorem 13.29.
    intro μ hμ
    exact hμ
  have hTight : IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' F) := by
    -- Proof comment: on a compact base space every family of measures is tight.
    simpa [F] using
      (IsTightMeasureSet.of_compactSpace :
        IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' F))
  intro μs hμs
  -- Route correction: avoid the compactness-to-sequential-compactness shortcut on
  -- `FiniteMeasure E`; Theorem 13.29 already gives the subsequence extraction route needed here.
  obtain ⟨μ, φ, hφ, hconv⟩ :=
    isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet F hF hTight μs <| by
      simpa [F] using hμs
  have hclosed : IsClosed {ν : FiniteMeasure E | ν.mass ≤ 1} := by
    -- Proof comment: the limit remains a subprobability because total mass varies continuously.
    exact isClosed_le FiniteMeasure.continuous_mass continuous_const
  have hμ_mem : μ ∈ {ν : FiniteMeasure E | ν.mass ≤ 1} := by
    have hEventual : ∀ᶠ n in atTop, (μs ∘ φ) n ∈ {ν : FiniteMeasure E | ν.mass ≤ 1} := by
      -- Proof comment: every term of the extracted subsequence stays in the original family.
      exact Eventually.of_forall fun n ↦ by
        simpa using hμs (φ n)
    exact hclosed.mem_of_tendsto hconv hEventual
  exact ⟨μ, hμ_mem, φ, hφ, hconv⟩

/- Corollary 13.30 (2): for a compact metric space `E`, the textbook set `\mathcal{M}_1(E)` of
probability measures is weakly sequentially compact; in mathlib this is the canonical weak space
`ProbabilityMeasure E`, carrying the corresponding `SeqCompactSpace` instance. -/
#check (inferInstance : SeqCompactSpace (ProbabilityMeasure E))

end
