/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/- Definition 1.2.2: a loop at `x` is a path from `x` to itself, namely an element of `Path x x`. -/
#check (Path x x)

/- The set `π₁(X, x)` is the quotient `Path.Homotopic.Quotient x x` of loops at `x` by
endpoint-fixed homotopy. -/
#check (Path.Homotopic.Quotient x x)
