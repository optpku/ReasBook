/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.39: for a subset `C` of a topological space, the closure of `C` is the canonical set
`closure C`, namely the smallest closed set containing `C`. -/
recall closure {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- Every set is contained in its closure. -/
#check subset_closure

/- The closure of a set is closed. -/
#check isClosed_closure

/- The closure is the smallest closed set containing the original set. -/
#check closure_minimal

/- The textbook notion that `C` is dense in `X` is the canonical predicate `Dense C`. -/
recall Dense {X : Type u} [TopologicalSpace X] (C : Set X) : Prop

/- A subset is dense exactly when its closure is the whole space. -/
#check dense_iff_closure_eq

/- A point belongs to the closure of `C` exactly when every neighborhood of that point meets
the set `C`. -/
#check mem_closure_iff_nhds
