/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.1.2: a map `p : X → Y` is continuous when the inverse image of every open set in
`Y` is open in `X`; for metric spaces this agrees with the usual epsilon-delta formulation. -/
recall Continuous {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) : Prop
