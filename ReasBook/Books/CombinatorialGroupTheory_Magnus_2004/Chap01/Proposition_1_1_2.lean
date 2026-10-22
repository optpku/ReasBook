/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1

universe u

open scoped Cardinal

-- Declarations for this item will be appended below by the statement pipeline.

-- Layer triage:
-- `source-facing`: the subset-style basis hypotheses `IsFreeGroupBasis X₁` and
--   `IsFreeGroupBasis X₂`.
-- `core/canonical`: `FreeGroupBasis ι F` is the owner abstraction for a group with a chosen free
--   basis.
-- `bridge/view`: `FreeGroupBasis.ofUniqueLift X Subtype.val` turns the textbook subset universal
--   property into the owner basis data.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofUniqueLift` is the canonical bridge from the source universal property to a
--    chosen basis.
-- 2. `FreeGroupBasis.map` transports a chosen basis across a group isomorphism.
-- 3. `FreeGroupBasis.reindex` transports a chosen basis across an equivalence of indexing types.
-- 4. `FreeGroupBasis.cardinal_eq` is the chapter owner theorem that any two bases of the same
--    free group have the same cardinality.
--
-- Primitive vs. derived:
-- the primitive source data are only the two subset-style basis hypotheses. The chosen owner-side
-- bases arise canonically from `FreeGroupBasis.ofUniqueLift`, and the group isomorphism in the
-- reverse direction is derived by reindexing one chosen basis along an equivalence of the index
-- types.

namespace FreeGroupBasis

/-- Two groups carrying chosen free bases are isomorphic if and only if those bases have the same
cardinality. -/
theorem nonempty_mulEquiv_iff_cardinal_eq {F₁ : Type u} {F₂ : Type u} [Group F₁] [Group F₂]
    {ι₁ : Type u} {ι₂ : Type u} (b₁ : FreeGroupBasis ι₁ F₁) (b₂ : FreeGroupBasis ι₂ F₂) :
    Nonempty (F₁ ≃* F₂) ↔ #ι₁ = #ι₂ := by
  constructor
  · rintro ⟨e⟩
    simpa using (b₁.map e).cardinal_eq b₂
  · intro hι
    obtain ⟨eι⟩ : Nonempty (ι₁ ≃ ι₂) := Cardinal.eq.mp hι
    exact ⟨(b₁.reindex eι).repr.trans b₂.repr.symm⟩

end FreeGroupBasis

/-- Proposition 1-1-2: If `X₁` and `X₂` are bases of the free groups `F₁` and `F₂`, then `F₁` and
`F₂` are isomorphic if and only if `X₁` and `X₂` have the same cardinality. -/
-- Proof sketch: bridge the two source-facing hypotheses to the owner abstraction
-- `FreeGroupBasis.ofUniqueLift Xᵢ Subtype.val hXᵢ`, then apply the owner theorem
-- `FreeGroupBasis.nonempty_mulEquiv_iff_cardinal_eq`.
theorem free_group_mulEquiv_iff_basis_cardinal_eq {F₁ : Type u} {F₂ : Type u} [Group F₁]
    [Group F₂] {X₁ : Set F₁} {X₂ : Set F₂} (hX₁ : IsFreeGroupBasis X₁)
    (hX₂ : IsFreeGroupBasis X₂) :
    Nonempty (F₁ ≃* F₂) ↔ #X₁ = #X₂ := by
  let b₁ : FreeGroupBasis X₁ F₁ := FreeGroupBasis.ofUniqueLift X₁ Subtype.val hX₁
  let b₂ : FreeGroupBasis X₂ F₂ := FreeGroupBasis.ofUniqueLift X₂ Subtype.val hX₂
  simpa using FreeGroupBasis.nonempty_mulEquiv_iff_cardinal_eq b₁ b₂
