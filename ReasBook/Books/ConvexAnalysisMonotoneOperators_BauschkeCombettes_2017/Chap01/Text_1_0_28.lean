/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 1.0.28: for a set `S` of extended reals, the canonical complete-lattice infimum `sInf S`
is its infimum, i.e. the greatest lower bound of `S`; this is exactly the `EReal` specialization
of the standard theorem `isGLB_sInf`. -/
recall isGLB_sInf {α : Type*} [CompleteSemilatticeInf α] (s : Set α) : IsGLB s (sInf s)

/- For `EReal`, the infimum of the empty set is `⊤`; this is the `EReal` specialization of the
canonical complete-lattice theorem `sInf_empty`. -/
recall sInf_empty {α : Type*} [CompleteLattice α] : sInf (∅ : Set α) = (⊤ : α)

/- For `EReal`, the supremum of the empty set is `⊥`; this is the `EReal` specialization of the
canonical complete-lattice theorem `sSup_empty`. -/
recall sSup_empty {α : Type*} [CompleteLattice α] : sSup (∅ : Set α) = (⊥ : α)

namespace EReal

/-- The supremum of a set of extended reals is the negative of the infimum of its negated image. -/
theorem sSup_eq_neg_sInf_image_neg (S : Set EReal) :
    sSup S = -sInf ((-·) '' S) := by
  apply neg_injective
  rw [neg_neg]
  change (negOrderIso (sSup S) : ERealᵒᵈ) = sSup (negOrderIso '' S)
  exact (negOrderIso.isLUB_image'.2 (isLUB_sSup S)).unique (isLUB_sSup _)

end EReal
