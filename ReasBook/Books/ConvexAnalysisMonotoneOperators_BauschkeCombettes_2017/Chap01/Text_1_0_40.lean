/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.40: the boundary `bdry C` of a subset `C` of a topological space is formalized by
the canonical set `frontier C`. -/
recall frontier {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- Its defining equation in mathlib is the canonical theorem `closure_diff_interior`. -/
recall closure_diff_interior {X : Type u} [TopologicalSpace X] (C : Set X) :
    closure C \ interior C = frontier C
