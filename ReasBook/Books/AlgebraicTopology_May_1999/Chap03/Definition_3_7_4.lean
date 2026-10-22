/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  (p : C(E, B)) (p' : C(E', B))

/- Definition 3.7.4: a map of covering spaces over `B`, from `p : C(E, B)` to `p' : C(E', B)`,
is a morphism in the over-category `Over (TopCat.of B)`. Equivalently, it is a
continuous map `g : C(E, E')` such that `p' ∘ g = p`. -/
#check (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))

section OverApi

variable {T : Type u} [Category.{v} T] {X Y : T}

/- An object of an over-category is given by a morphism with codomain `X`. -/
recall Over.mk (f : Y ⟶ X) : Over X

/- Equivalently, a morphism in an over-category is built from a commutative triangle. -/
recall Over.homMk {U V : Over X} (g : U.left ⟶ V.left)
    (hg : g ≫ V.hom = U.hom) : U ⟶ V

/- Every morphism in the over-category satisfies the defining commutative-triangle relation. -/
recall Over.w {U V : Over X} (g : U ⟶ V) : g.left ≫ V.hom = U.hom

end OverApi
