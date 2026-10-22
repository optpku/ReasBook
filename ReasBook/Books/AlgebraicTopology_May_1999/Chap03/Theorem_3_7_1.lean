/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FundamentalGroup

universe u v w

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsCoveringMap

variable {p : E → B} [PathConnectedSpace X] [LocPathConnectedSpace X]

/- Theorem 3.7.1: the covering-space lifting criterion is the canonical mathlib theorem
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`. -/
recall IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
    {E : Type u} {X : Type v} {A : Type w}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E → X}
    (cov : IsCoveringMap p) [PathConnectedSpace A] [LocPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (le :
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f

end IsCoveringMap
