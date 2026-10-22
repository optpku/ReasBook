/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- Principle 1.1.5: the usual strict form of the invariance principle says that an
algebraic-topological invariant is homotopy invariant when homotopic maps induce the same
morphism on the associated algebraic data. -/
class IsHomotopyInvariant (A : TopCat ⥤ C) : Prop where
  /-- A homotopy-invariant algebraic-topological invariant sends homotopic maps to the same
  induced morphism. -/
  map_eq {X Y : TopCat} {p q : X ⟶ Y} (H : TopCat.Homotopy p q) : A.map p = A.map q

/-- A homotopy-invariant algebraic-topological invariant sends homotopic maps to the same
induced morphism. -/
theorem map_eq_of_homotopy
    {A : TopCat ⥤ C} [A.IsHomotopyInvariant] {X Y : TopCat}
    {p q : X ⟶ Y} (H : TopCat.Homotopy p q) :
    A.map p = A.map q :=
  IsHomotopyInvariant.map_eq H

end CategoryTheory.Functor
