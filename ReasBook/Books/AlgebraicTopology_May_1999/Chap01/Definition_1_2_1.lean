/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Definition 1.2.1: Two paths from `x` to `y` are equivalent when they are homotopic through
paths from `x` to `y`, so the endpoints remain fixed throughout the homotopy. -/
recall Path.Homotopic (f g : Path x y) : Prop
