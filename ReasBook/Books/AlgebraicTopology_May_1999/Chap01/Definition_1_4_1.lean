/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Path.Homotopic.Quotient

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

/- Definition 1.4.1: a continuous map `p : X → Y` induces a map on loop classes, hence on
`π₁(X, x) = Path.Homotopic.Quotient x x`, by sending the class `[f]` to the class `[p ∘ f]`. -/
recall map (γ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁)
