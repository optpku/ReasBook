/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_38

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: fix `x ∈ effectiveDomain f`. Proposition 16.38 gives graph points above
-- subdifferentiability points converging to `(x, f x)`, hence base points in `effectiveDomain f`
-- with `SubdifferentiableAt f` converging to `x`. This is exactly density of the
-- subdifferentiability domain in the subtype `effectiveDomain f`.
/-- Corollary 16.39: if `f ∈ Γ₀(H)`, then the points of `effectiveDomain f` at which `f` is
subdifferentiable form a dense subset of `effectiveDomain f`. -/
theorem dense_subdifferentiableAt_in_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Dense {x : effectiveDomain f | SubdifferentiableAt f x.1} := by
  rw [dense_iff_closure_eq]
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have hseq :=
      exists_subdifferentiableAt_sequence_tendsto_of_mem_effectiveDomain_of_mem_gammaZero
        hf x.2
    rcases hseq with ⟨xSeq, hxSeq_sub, hxSeq_tendsto, _⟩
    rw [mem_closure_iff_seq_limit]
    refine ⟨
      fun n ↦
        ⟨xSeq n,
          subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf
            ((subdifferentiableAt_iff_mem_dom f (xSeq n)).1 (hxSeq_sub n))⟩,
      ?_,
      ?_⟩
    · intro n
      exact hxSeq_sub n
    · exact tendsto_subtype_rng.mpr hxSeq_tendsto

end SubdifferentialCalculus

end ERealFunction
