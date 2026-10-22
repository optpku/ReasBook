/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import AlgebraicTopology_May_1999.Chap03.Definition_3_7_4
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

/-
The core/canonical owner for the automorphism group of an object in a category is
`CategoryTheory.Aut X`.
-/
recall CategoryTheory.Aut {C : Type u} [Category C] (X : C) : Type _

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))

/- Definition 3.7.10: for a covering space `p : E → B`, the automorphism group `Aut(E)` is the
categorical automorphism group of the corresponding object `Over.mk (TopCat.ofHom p)` in the
over-category `Over (TopCat.of B)`. Equivalently, its elements are invertible maps of covering
spaces from `p` to itself over `B`. -/
#check (Aut (Over.mk (TopCat.ofHom p)))
