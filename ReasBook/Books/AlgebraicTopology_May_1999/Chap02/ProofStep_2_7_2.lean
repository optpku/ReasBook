/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace.Opens

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

/-- ProofStep 2.7.2: if an open cover is closed under finite intersections, then the binary
intersection `O i ∩ O j` of any two members is itself another member of the cover. This is the
overlap used in the van Kampen construction to compare the chosen cover elements. -/
-- Proof sketch: apply
-- `TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections` to the nonempty finite set
-- `{i, j}`. The resulting cover element is exactly the binary intersection of the two chosen
-- opens.
theorem exists_eq_inf
    {O : ι → Opens X}
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {i j : ι} :
    ∃ k, O k = O i ⊓ O j := by
  classical
  obtain ⟨k, hk⟩ := hinter ({i, j} : Finset ι) (by simp)
  refine ⟨k, ?_⟩
  simpa [Finset.inf'_insert, Finset.inf'_singleton] using hk.symm

end TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections
