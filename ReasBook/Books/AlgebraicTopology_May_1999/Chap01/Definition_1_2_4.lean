/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Definition 1.2.4: the reverse of a path `f : Path x y` is `Path.symm f`, corresponding to
the parametrization `s ↦ f (1 - s)`, and the constant loop at `x` is `Path.refl x`. -/
recall Path.symm (f : Path x y) : Path y x

/- The constant loop at a point is the constant path `Path.refl x`. -/
recall Path.refl (x : X) : Path x x
