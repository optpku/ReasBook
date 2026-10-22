/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.65: a topological space is metrizable when there exists a metric on the space whose
induced topology coincides with the given topology, formalized by the canonical predicate
`TopologicalSpace.MetrizableSpace`. -/
recall TopologicalSpace.MetrizableSpace (X : Type u) [TopologicalSpace X] : Prop
