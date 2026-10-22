/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 1.1.4: a homotopy between continuous maps `p q : C(X, Y)` is a continuous map
`I × X → Y` whose values at the endpoints `0` and `1` recover `p` and `q`; this is equivalent to
the textbook `X × I → Y` formulation by swapping the factors. -/
recall ContinuousMap.Homotopy (p q : C(X, Y)) : Type (max u v)
