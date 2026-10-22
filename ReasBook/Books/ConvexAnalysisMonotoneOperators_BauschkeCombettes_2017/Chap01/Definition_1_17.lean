/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.17: continuity of a map `f : X → Y` at a point `x : X` is formalized by the
canonical predicate `ContinuousAt f x`; global continuity is formalized by `Continuous f`. -/
recall ContinuousAt

/- Companion recall: global continuity of a map between topological spaces is formalized by the
canonical predicate `Continuous f`. -/
recall Continuous
