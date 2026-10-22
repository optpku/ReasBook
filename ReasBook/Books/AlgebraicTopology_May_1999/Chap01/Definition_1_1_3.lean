/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 1.1.3: an algebraic-topological invariant with values in a category `C` is modeled
by a functor from topological spaces to `C`, sending each space `X` to an object `A(X)` and each
continuous map `p : X ⟶ Y` to the induced morphism `A(p) = p_*`. -/
#check TopCat ⥤ C
