/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.Groupoid

variable (C : Type u) [Category.{v} C] (x : C)

/- Definition 3.3.2 (1): the star `St_C(x)` is the canonical under-category `Under x`, whose
objects are morphisms of `C` with source `x`. -/
#check Under x

variable [Groupoid.{v} C]

/- Definition 3.3.2 (2): `π(C, x)` is the vertex group at `x`, i.e. the group structure on the
loop type `x ⟶ x` whose multiplication is categorical composition in the groupoid `C`. -/
#check Groupoid.vertexGroup x

end CategoryTheory.Groupoid
