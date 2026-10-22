/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (X : Type u) (Y : Type v)

/-
Text 1.0.8: a set-valued operator from `X` to `Y` is canonically just a map
`X → Set Y`.
-/
#check X → Set Y

end

-- Compatibility alias used by subsequent textbook items.
abbrev SetValuedOperator (X : Type u) (Y : Type v) : Type (max u v) := X → Set Y

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- The graph of a set-valued operator consists of the pairs `(x, u)` with `u ∈ A x`. -/
def graph (A : SetValuedOperator X Y) : SetRel X Y := { xu | xu.2 ∈ A xu.1 }

prefix:100 "gra " => SetValuedOperator.graph

/-- Membership in the graph of a set-valued operator is equivalent to membership in the
corresponding value set. -/
@[simp] theorem mem_graph (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  Iff.rfl

/-- Compatibility form of `mem_graph` using the original `_iff` suffix. -/
theorem mem_graph_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  mem_graph A x u

end SetValuedOperator
