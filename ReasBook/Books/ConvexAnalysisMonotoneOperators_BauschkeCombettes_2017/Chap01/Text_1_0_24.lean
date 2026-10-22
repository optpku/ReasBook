/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Net

variable {A : Type u} {X : Type v} [Preorder A] [IsDirectedOrder A] [Nonempty A]

/-- A net is eventually in `Y` exactly when all sufficiently large indices map into `Y`. -/
theorem eventuallyIn_iff_exists_forall_ge_mem (x : A → X) (Y : Set X) :
    (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y := by
  exact
    (Filter.eventually_atTop : (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y)

/-- A net is frequently in `Y` exactly when every tail contains an index whose value lies in
`Y`. -/
theorem frequentlyIn_iff_forall_exists_ge_mem (x : A → X) (Y : Set X) :
    (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y := by
  exact
    (Filter.frequently_atTop : (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y)

end Net
