/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Principle_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Functor

/- Method 1.1.6: the basic algebraic-topological method formalized in this chapter uses
homotopy invariance as its canonical core, then combines that with explicit computations on
standard spaces and maps and with deformation arguments reducing the target problem to those
computations. The formal owner for the homotopy-invariance step is
`CategoryTheory.Functor.map_eq_of_homotopy`. -/
recall map_eq_of_homotopy
    {A : TopCat ⥤ C} [A.IsHomotopyInvariant] {X Y : TopCat} {p q : X ⟶ Y}
    (H : TopCat.Homotopy p q) :
    A.map p = A.map q

end CategoryTheory.Functor
