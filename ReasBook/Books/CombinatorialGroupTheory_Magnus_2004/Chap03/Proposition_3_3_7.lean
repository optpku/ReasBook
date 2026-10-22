/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Monoid

section

variable {ι : Type v} {F : Type u} {A : ι → Type w}
variable [Group F] [IsFreeGroup F] [Group.FG F]
variable [∀ i, Group (A i)]

-- Primary domain: indexed free products of groups and free-group decompositions.
--
-- Layer triage:
-- `source-facing`: a finitely generated free group `F`, a surjection `φ : F →* CoprodI A`
-- onto an indexed free product, and a family of subgroup factors in `F` mapping onto the given
-- factors.
-- `core/canonical`: `IsFreeGroup` is the owner predicate for free groups, `CoprodI` is the
-- owner abstraction for indexed free products, and `Subgroup.map` expresses the image of each
-- subgroup factor under `φ`.
-- `bridge/view`: the equality `F = * F_λ` is rendered by an isomorphism from the indexed free
-- product of subgroup factors onto `F` whose canonical inclusions agree with the subgroup
-- embeddings.
-- Domain sampling:
-- 1. `CoprodI` with its canonical inclusions `CoprodI.of` is the owner abstraction
--    for indexed free products.
-- 2. `CoprodI.lift` is the universal-property owner that would control the eventual proof.
-- 3. `IsFreeGroup` together with `[Group.FG F]` is the chapter/mathlib owner interface for a
--    finitely generated free group; any chosen finite basis is derived data.
-- 4. `Subgroup.map` is the canonical owner for the image condition `F_λ φ = A_λ`.
--
-- Primitive vs. derived:
-- the primitive public data are the finitely generated free group `F`, the factor family `A`, and
-- the surjection `φ : F →* CoprodI A`; the subgroup family `H`, the free-product equivalence
-- `CoprodI (fun i ↦ H i) ≃* F`, and the factor-image equalities are all derived API.

/-- Proposition 3-3-7: if a finitely generated free group `F` surjects onto a nonempty indexed
free product `CoprodI A`, then `F` splits as an indexed free product of subgroup factors whose
images under the surjection are exactly the canonical factor subgroups of `CoprodI A`. -/
-- Proof sketch: choose a finite graph model for `F` and refine the quotient map to a labelled
-- complex over the free product. Modify the complex by adjoining binding ties until the common
-- intersection of the factor subcomplexes is a tree. Seifert-van Kampen then identifies `F` with
-- the free product of the factor subgroups, and surjectivity of `φ` forces each factor image to be
-- the corresponding canonical factor subgroup.
theorem exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct
    (hι : Nonempty ι) (φ : F →* CoprodI A) (hφ : Function.Surjective φ) :
    ∃ H : ι → Subgroup F, ∃ e : CoprodI (fun i ↦ H i) ≃* F,
      (∀ i, e.toMonoidHom.comp CoprodI.of = (H i).subtype) ∧
      ∀ i, Subgroup.map φ (H i) = (CoprodI.of : A i →* CoprodI A).range := sorry

end
