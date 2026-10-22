/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

universe u v w

open scoped Cardinal

-- Declarations for this item will be appended below by the statement pipeline.

/-- Corollary 1-1-3: Any two bases of the same free group have the same cardinality. This common
cardinality is the rank of the free group. -/
-- Proof sketch: A basis identifies `F` with a free group on its indexing type. Composing the
-- isomorphism coming from `b₁` with the one coming from `b₂` gives an isomorphism
-- `FreeGroup ι ≃* FreeGroup κ`, hence an equivalence `ι ≃ κ` by `Equiv.ofFreeGroupEquiv`; then
-- apply `Equiv.lift_cardinal_eq`.
theorem FreeGroupBasis.cardinal_eq {F : Type u} [Group F] {ι : Type v} {κ : Type w}
    (b₁ : FreeGroupBasis ι F) (b₂ : FreeGroupBasis κ F) :
    Cardinal.lift.{w} #ι = Cardinal.lift.{v} #κ := by
  simpa using
    (Equiv.ofFreeGroupEquiv (MulEquiv.trans b₁.repr.symm b₂.repr)).lift_cardinal_eq
