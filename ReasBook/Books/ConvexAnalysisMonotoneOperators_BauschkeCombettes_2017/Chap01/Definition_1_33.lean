/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.33: sequential compactness of a subset `C` of a topological space is formalized by
the canonical predicate `IsSeqCompact C`. In the Hausdorff setting of the textbook, this is exactly
the statement that every sequence in `C` admits a subsequence, indexed by a strictly increasing map,
that converges to a point of `C`. -/
recall IsSeqCompact {X : Type u} [TopologicalSpace X] (C : Set X) : Prop
