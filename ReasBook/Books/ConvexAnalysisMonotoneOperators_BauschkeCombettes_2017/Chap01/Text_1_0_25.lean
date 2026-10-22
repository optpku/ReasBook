/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u v w

namespace Net

variable {X : Type u} {A : Type v} {B : Type w}

/-- Text 1.0.25: a net `y` is a subnet of a net `x` via `k` exactly when the textbook
reindexing-and-cofinality condition holds, equivalently when `y = x ∘ k` and `k` tends to
`atTop`. -/
theorem isSubnetOfVia_iff [Preorder A] [Preorder B] [IsDirectedOrder A] [IsDirectedOrder B]
    [Nonempty B] {x : A → X} {y : B → X} {k : B → A} :
    (y = x ∘ k ∧ ∀ a : A, ∃ d : B, ∀ b : B, d ≤ b → a ≤ k b) ↔
      y = x ∘ k ∧ Tendsto k atTop atTop := by
  rw [tendsto_atTop_atTop]

end Net
