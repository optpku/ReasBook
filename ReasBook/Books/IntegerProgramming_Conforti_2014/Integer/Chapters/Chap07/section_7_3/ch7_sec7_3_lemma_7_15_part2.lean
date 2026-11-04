/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_16.OrderedFlowCoverApi

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 7.15 is source-facing in `flow_cover_recursive_lifting_eq_lifting_function`: the
recursive functions `fᵢ i` from `(7.19)` coincide with the lifting function `f` on `0 ≤ z ≤ b`.

The lifted inequality expressions that use those coefficients later in the chapter already live
under the canonical owner `OrderedFlowCover.flow_cover_lifted_value` from Theorem 7.16. This
supplemental file therefore keeps only direct recalls of the source-facing lemma and that owner,
rather than a parallel local `value`/`valid`/`pair-lifting` API. -/
#check flow_cover_recursive_lifting_eq_lifting_function
#check OrderedFlowCover.flow_cover_lifted_value
