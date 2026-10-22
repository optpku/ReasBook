/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Projective

/-!
Primary domain: projective objects in the category of groups.

Layer triage:
- `source-facing`: projective groups, expressed by lifting homomorphisms along surjective group
  homomorphisms.
- `core/canonical`: `CategoryTheory.Projective` on `GrpCat`.
- `bridge/view`: the concrete group-hom lifting statement obtained from the owner abstraction using
  `GrpCat.epi_iff_surjective`.

Domain sampling:
1. `CategoryTheory.Projective` is mathlib's owner predicate for projective objects.
2. `Projective.factorThru` and `Projective.factorThru_comp` are the canonical factorization API for
   maps out of a projective object through an epimorphism.
3. `GrpCat.epi_iff_surjective` is the category-specific bridge identifying epimorphisms in
   `GrpCat` with surjective group homomorphisms.
4. `Projective.factors` is the primitive existence statement; the theorem below is the derived
   source-facing reformulation in ordinary group-hom language.

Primitive vs. derived:
the primitive owner-side data are only the projective factorization property in `GrpCat`; the
explicit lifting statement for surjective homomorphisms is derived from that owner abstraction and
should remain a bridge theorem rather than a parallel owner definition.
-/

/- Definition 1-1-5: a projective group is a projective object of `GrpCat`, equivalently a group
whose homomorphisms lift along surjective homomorphisms. -/
#check (Projective : GrpCat → Prop)

/-- A group is projective exactly when every homomorphism out of it lifts along surjective
group homomorphisms. -/
-- Proof sketch: use `GrpCat.epi_iff_surjective` to rewrite surjective homomorphisms as
-- epimorphisms in `GrpCat`, and then apply the defining factorization property of
-- `Projective`.
theorem group_projective_iff_lifts_along_surjective
    {P : Type u} [Group P] :
    Projective (GrpCat.of P) ↔
      ∀ ⦃G H : Type u⦄ [Group G] [Group H]
        (γ : G →* H) (_ : Function.Surjective γ) (π : P →* H),
        ∃ φ : P →* G, γ.comp φ = π := by
  constructor
  · intro hP G H _ _ γ hγ π
    letI : Projective (GrpCat.of P) := hP
    let γ' : GrpCat.of G ⟶ GrpCat.of H := GrpCat.ofHom γ
    let π' : GrpCat.of P ⟶ GrpCat.of H := GrpCat.ofHom π
    haveI : Epi γ' := (GrpCat.epi_iff_surjective γ').2 hγ
    refine ⟨(factorThru π' γ').hom, ?_⟩
    ext x
    change γ ((factorThru π' γ').hom x) = π x
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (factorThru_comp π' γ')) x
  · intro hLift
    refine ⟨fun {G H} π γ ↦ ?_⟩
    intro _hγepi
    have hγ : Function.Surjective γ.hom := (GrpCat.epi_iff_surjective γ).1 inferInstance
    obtain ⟨φ, hφ⟩ := hLift γ.hom hγ π.hom
    refine ⟨GrpCat.ofHom φ, ?_⟩
    ext x
    simpa using DFunLike.congr_fun hφ x
