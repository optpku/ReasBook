/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section Conjugation

variable {I : Type v} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: for each index `i`, the pointwise inequality `f i ≤ ⨆ j : I, f j` holds. Apply
-- the order-reversing property of Fenchel conjugation from Proposition 13.16(ii), then take the
-- infimum over `i` on the right-hand side.
/-- Proposition 13.28 (2): the Fenchel conjugate of a pointwise supremum is bounded above by the
pointwise infimum of the Fenchel conjugates. In particular, this recovers textbook clause (ii) for
a family of proper functions. -/
theorem conjugate_iSup_le_iInf_conjugate
    (f : I → H → EReal) :
    (⨆ i : I, f i)∗ ≤ ⨅ i : I, (f i)∗ := by
  refine le_iInf fun i ↦ ?_
  exact conjugate_antitone (le_iSup f i)

-- Proof sketch: the reverse inequality is immediate from antitonicity since `⨅ i, f i ≤ f i` for
-- every `i`. For the forward inequality, apply part (2) to the family of conjugates, bound the
-- resulting infimum of biconjugates above by `⨅ i, f i` using Proposition 13.16(i), and conjugate
-- back once more; a final use of Proposition 13.16(i) removes the outer biconjugation.
/-- Proposition 13.28 (1): the Fenchel conjugate of a pointwise infimum is the pointwise supremum
of the Fenchel conjugates. In particular, this recovers textbook clause (i) for a family of proper
functions. -/
theorem conjugate_iInf_eq_iSup_conjugate
    (f : I → H → EReal) :
    (⨅ i : I, f i)∗ = ⨆ i : I, (f i)∗ := by
  apply le_antisymm
  · have hconj : (⨆ i : I, (f i)∗)∗ ≤ ⨅ i : I, (f i)∗∗ :=
      conjugate_iSup_le_iInf_conjugate (fun i ↦ (f i)∗)
    have hle : (⨆ i : I, (f i)∗)∗ ≤ ⨅ i : I, f i :=
      hconj.trans <| iInf_mono fun i ↦ biconjugate_le (f i)
    exact (conjugate_antitone hle).trans <| biconjugate_le (⨆ i : I, (f i)∗)
  · refine iSup_le fun i ↦ ?_
    exact conjugate_antitone (iInf_le f i)

end Conjugation

end ERealFunction
