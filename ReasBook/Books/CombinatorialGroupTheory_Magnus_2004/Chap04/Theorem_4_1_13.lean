/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Monoid

section

variable {ι : Type v} {F : Type u} {A : ι → Type w}
variable [Group F] [IsFreeGroup F] [Group.FG F]
variable [∀ i, Group (A i)]

/-!
Primary domain: indexed free products of groups and free-group decompositions.

Layer triage:
- `source-facing`: a finitely generated free group `F`, a surjection `φ : F →* CoprodI A`,
  and a decomposition of `F` as an indexed free product of subgroup factors mapping onto the
  canonical factor subgroups.
- `core/canonical`: `IsFreeGroup` for the ambient free-group hypothesis, `CoprodI` with its
  canonical inclusions `CoprodI.of`, and `Subgroup.map` for the image condition.
- `bridge/view`: the textbook equality `F = *ᵢ H i` is expressed by a multiplicative equivalence
  `CoprodI (fun i ↦ H i) ≃* F` whose restriction to each canonical inclusion is the
  corresponding subgroup embedding. Proposition `3-3-7` already states this theorem at the owner
  level used here, so this file should recall that theorem directly rather than restating a local
  copy.

Domain sampling:
1. `CoprodI` is mathlib's owner abstraction for indexed free products.
2. `CoprodI.of` is the canonical factor inclusion, including for subgroup-indexed free products.
3. `CoprodI.lift` is the universal-property owner for maps out of an indexed free product.
4. `exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct` from
   Proposition `3-3-7` is the project owner theorem for this finitely generated source-facing
   statement, while
   `Subgroup.map` is the canonical owner for the factor-image condition.

Primitive vs. derived:
- primitive public data: the finitely generated free group `F`, the factor family `A`, and the
  surjection
  `φ : F →* CoprodI A`;
- derived API: the subgroup family `H`, the free-product equivalence onto `F`, the compatibility
  of that equivalence with the canonical inclusions, and the image-identification equalities.
-/

/- Theorem `4-1-13` adds no new owner-level API beyond Proposition `3-3-7`, so this file recalls
that upstream theorem directly instead of restating its interface as a parallel local item. -/
#check (exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct :
  ∀ (_ : Nonempty ι) (φ : F →* CoprodI A) (_ : Function.Surjective φ),
    ∃ H : ι → Subgroup F, ∃ e : CoprodI (fun i ↦ H i) ≃* F,
      (∀ i, e.toMonoidHom.comp CoprodI.of = (H i).subtype) ∧
        ∀ i, Subgroup.map φ (H i) = (CoprodI.of : A i →* CoprodI A).range)

end
