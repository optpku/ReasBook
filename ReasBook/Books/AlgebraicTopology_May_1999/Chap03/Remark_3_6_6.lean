/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v

open CategoryTheory

variable {G : Type u₁} [Groupoid.{v} G]
variable {B : Type u₂} [Groupoid.{v} B]
variable {ι : G ⥤ B}

namespace MulAction

/-- Transport transitivity across a compatible equivalence of acting groups and underlying sets. -/
theorem IsTransitive.of_mulEquiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x)
    (h : IsTransitive H X) :
    IsTransitive K Y := by
  rcases h with ⟨hX, hpre⟩
  let f : X →ₑ[eH] Y :=
    { toFun := eX
      map_smul' := hcompat }
  have hf : Function.Bijective f := eX.bijective
  refine ⟨hX.map eX, ?_⟩
  exact (MulAction.isPretransitive_congr eH.surjective hf).mp hpre

/-- Transitivity is invariant under a compatible equivalence of acting groups and underlying
sets. -/
theorem isTransitive_iff_of_mulEquiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x) :
    IsTransitive H X ↔ IsTransitive K Y := by
  constructor
  · exact IsTransitive.of_mulEquiv eH eX hcompat
  · intro h
    refine IsTransitive.of_mulEquiv eH.symm eX.symm ?_ h
    intro k y
    apply eX.injective
    simpa using (hcompat (eH.symm k) (eX.symm y)).symm

end MulAction

namespace CategoryTheory.Functor

/-- Restriction along an equivalence of groupoids preserves and reflects transitivity of set-valued
functors. -/
theorem isTransitive_iff_comp_of_isEquivalence
    {C : Type*} [Groupoid C] {D : Type*} [Groupoid D]
    (F : C ⥤ D) [F.IsEquivalence] (T : D ⥤ Type v) :
    IsTransitive T ↔ IsTransitive (F ⋙ T) := by
  rw [Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive,
    Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive]
  let e := F.asEquivalence
  let hF : F.FullyFaithful := .ofFullyFaithful F
  constructor
  · intro hT c
    letI := vertexGroupMulAction (F ⋙ T) c
    letI := vertexGroupMulAction T (F.obj c)
    let eEnd := hF.mulEquivEnd c
    rcases hT (F.obj c) with ⟨hx, hpre⟩
    let f : (F ⋙ T).obj c →ₑ[eEnd] T.obj (F.obj c) :=
      { toFun := id
        map_smul' := fun g x ↦ by
          simpa [eEnd, vertexGroupMulAction_smul_eq_map] using
            (vertexGroupMulAction_smul_eq_map (F ⋙ T) c g x) }
    have hf : Function.Bijective f := Function.bijective_id
    exact ⟨hx, (MulAction.isPretransitive_congr eEnd.surjective hf).mpr hpre⟩
  · intro hFT d
    let c := e.inverse.obj d
    let i : F.obj c ≅ d := e.counitIso.app d
    letI := vertexGroupMulAction (F ⋙ T) c
    letI : MulAction (End c) (T.obj (F.obj c)) := vertexGroupMulAction (F ⋙ T) c
    letI := vertexGroupMulAction T d
    let eEnd := (hF.mulEquivEnd c).trans i.conj
    have hc : MulAction.IsTransitive (End c) (T.obj (F.obj c)) := hFT c
    exact (MulAction.isTransitive_iff_of_mulEquiv eEnd (T.mapIso i).toEquiv fun g x ↦ by
      change
        T.map i.hom (T.map (F.map g) x) =
          T.map (i.inv ≫ F.map g ≫ i.hom) (T.map i.hom x)
      have hi : T.map i.inv (T.map i.hom x) = x := by
        rw [← T.map_comp_apply]
        simp
      rw [T.map_comp_apply, T.map_comp_apply, hi]).mp hc

end CategoryTheory.Functor

/-- Remark 3.6.6: restriction along a skeleton inclusion `ι : G ⥤ B` identifies `B`-sets with
`G`-sets by making precomposition with `ι` an equivalence of functor categories. -/
-- Proof sketch: a skeleton inclusion is an equivalence by `hι.eqv`, and precomposition with an
-- equivalence is again an equivalence by the standard `whiskeringLeft` functor-category API.
theorem restrictionAlongSkeleton_isEquivalence (hι : IsSkeletonOf B G ι) :
    Functor.IsEquivalence ((Functor.whiskeringLeft G B (Type v)).obj ι) := by
  letI : ι.IsEquivalence := hι.eqv
  infer_instance

/-- Restriction along a skeleton inclusion preserves and reflects transitivity of groupoid actions
on sets. -/
-- Proof sketch: use a quasi-inverse to the skeleton inclusion to transport points and loops
-- between `G` and `B`; the orbit condition on each fiber is unchanged under these identifications.
theorem isTransitive_iff_comp_of_isSkeletonOf
    (hι : IsSkeletonOf B G ι) (T : B ⥤ Type v) :
    Functor.IsTransitive T ↔ Functor.IsTransitive (ι ⋙ T) := by
  letI : ι.IsEquivalence := hι.eqv
  simpa using Functor.isTransitive_iff_comp_of_isEquivalence ι T
