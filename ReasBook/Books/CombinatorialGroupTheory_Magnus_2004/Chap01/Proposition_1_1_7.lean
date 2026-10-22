/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Projective

/-!
Primary domain: projective objects and retract subgroups in `GrpCat`.

Layer triage:
- `source-facing`: a projective group and the textbook assertion that it is isomorphic to a retract
  subgroup of a free group.
- `core/canonical`: `CategoryTheory.Projective`, `CategoryTheory.Retract`, `IsFreeGroup`, and the
  split-mono owner API in `GrpCat`.
- `bridge/view`: the subgroup inclusion `R.subtype`, together with
  `Subgroup.subtype_isSplitMono_iff_exists_leftInverse`, identifies “retract subgroup” with the
  categorical split-inclusion condition.

Domain sampling:
1. `CategoryTheory.Projective` is the owner abstraction for projective objects.
2. `Adjunction.map_projective` applied to `GrpCat.adj` is the owner-side route from projective
   types to projective free groups.
3. `CategoryTheory.Retract.projective` is the canonical theorem that retracts of projective objects
   are projective.
4. `Subgroup.subtype_isSplitMono_iff_exists_leftInverse` in `Definition_1_1_6` is the chapter's
   owner-level criterion for retract subgroups.

Primitive vs. derived:
the source-facing primitive data are the free ambient group, the subgroup, the isomorphism with
`P`, and the split inclusion of that subgroup. Projectivity of free groups and projectivity of the
retract subgroup are derived from the owner abstractions above and should not be reproved as
parallel local APIs.
-/

/-- Proposition 1-1-7: A group is projective exactly when it is isomorphic to a retract subgroup
of some free group. -/
-- Proof sketch: if `P` is projective, lift the identity of `P` along the canonical surjection
-- `FreeGroup P → P`; the image of the lift is then a retract subgroup of `FreeGroup P`
-- canonically isomorphic to `P`. Conversely, a retract subgroup of a free group is free, and
-- freeness transports across `MulEquiv`.
theorem projective_group_iff_isomorphic_to_retract_of_free_group {P : Type u} [Group P] :
    Projective (GrpCat.of P) ↔
      ∃ F : GrpCat.{u}, IsFreeGroup F ∧
        ∃ R : Subgroup F, ∃ _ : P ≃* R, IsSplitMono (GrpCat.ofHom R.subtype) := by
  constructor
  · intro hP
    let π : FreeGroup P →* P := FreeGroup.lift id
    have hπ : Function.Surjective π := fun p ↦ ⟨FreeGroup.of p, by simp [π]⟩
    obtain ⟨σ, hσ⟩ :=
      group_projective_iff_lifts_along_surjective.1 hP π hπ (MonoidHom.id P)
    let R : Subgroup (FreeGroup P) := σ.range
    let ρ : FreeGroup P →* R := (σ.comp π).codRestrict R fun x ↦ ⟨π x, rfl⟩
    have hρ : Function.LeftInverse ρ R.subtype := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨p, rfl⟩
      apply Subtype.ext
      simpa using congrArg σ (DFunLike.congr_fun hσ p)
    have hσ' : Function.LeftInverse π σ := fun x ↦ DFunLike.congr_fun hσ x
    have hR : IsSplitMono (GrpCat.ofHom R.subtype) :=
      (Subgroup.subtype_isSplitMono_iff_exists_leftInverse R).2 ⟨ρ, hρ⟩
    exact ⟨GrpCat.of (FreeGroup P), inferInstance, R, MonoidHom.ofLeftInverse hσ', hR⟩
  · rintro ⟨F, hF, R, e, hR⟩
    letI : IsFreeGroup F := hF
    let X : GrpCat := GrpCat.of (FreeGroup (IsFreeGroup.Generators F))
    have eFree : X ≃* F := IsFreeGroup.mulEquiv F
    letI : Projective X :=
      Adjunction.map_projective GrpCat.adj (IsFreeGroup.Generators F) inferInstance
    letI : Projective F := Projective.of_iso eFree.toGrpIso inferInstance
    let i : GrpCat.of ↥R ⟶ F := GrpCat.ofHom R.subtype
    have hi : IsSplitMono i := by
      simpa [i] using hR
    letI : IsSplitMono i := hi
    have hR_retract : Retract (GrpCat.of ↥R) F :=
      { i := i
        r := retraction i
        retract := IsSplitMono.id i }
    have hR_projective : Projective (GrpCat.of ↥R) := hR_retract.projective
    exact Projective.of_iso e.symm.toGrpIso hR_projective
