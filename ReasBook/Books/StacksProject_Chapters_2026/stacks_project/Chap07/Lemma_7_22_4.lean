module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_14_1
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C)

/- Domain-style sampling for Lemma 7.22.4:
- primary domain: adjunctions between Grothendieck sites and the continuity/cocontinuity owner
  abstractions;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.IsCocontinuous`,
  `IsMorphismOfSites`,
  `Adjunction.isCocontinuous_iff_coverPreserving`,
  `RepresentablyFlat.of_isRightAdjoint`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for a continuous right adjoint `v`;
  `core/canonical`: the owner predicates `Functor.IsContinuous`, `Functor.IsCocontinuous`, and
    `IsMorphismOfSites`;
  `bridge/view`: the adjunction equivalence
    `Adjunction.isCocontinuous_iff_coverPreserving`.

Primitive data are the adjunction `u ⊣ v` and continuity of the right adjoint `v`. The
cover-preserving owner on `v` and the representable flatness of `v` are derived API: the former
is used only internally to recover cocontinuity of `u`, while the latter, together with
continuity, yields that `v` defines a morphism of sites.
-/
/-- Helper for Lemma 7.22.4: the adjunction identifies the presheaf represented by `U` after
precomposition with `u.op` with the presheaf represented by `v.obj U`. -/
noncomputable def continuous_right_adjoint_shrinkYonedaIso
    (adj : u ⊣ v) (U : D) :
    u.op ⋙ shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U ≅
      shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U) := by
  -- Compare both presheaves objectwise by the adjunction hom-set bijection.
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine Equiv.toIso ?_
    refine (shrinkYonedaObjObjEquiv).trans ?_
    refine (adj.homEquiv _ _).trans ?_
    exact shrinkYonedaObjObjEquiv.symm
  · intro X Y f
    -- Naturality is exactly `Adjunction.homEquiv_naturality_left` after translating through
    -- `shrinkYonedaObjObjEquiv`.
    ext x
    apply shrinkYonedaObjObjEquiv.injective
    dsimp
    rw [show shrinkYonedaObjObjEquiv
          ((shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U).map (u.map f.unop).op x) =
        u.map f.unop ≫ shrinkYonedaObjObjEquiv x from
          shrinkYonedaObjObjEquiv_obj_map (g := (u.map f.unop).op) (f := x)]
    rw [show shrinkYonedaObjObjEquiv
          ((shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U)).map f
            (shrinkYonedaObjObjEquiv.symm ((adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x)))) =
        f.unop ≫ (adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x) from by
          rw [shrinkYonedaObjObjEquiv_obj_map]
          simp]
    simpa using Adjunction.homEquiv_naturality_left adj f.unop (shrinkYonedaObjObjEquiv x)

/-- Helper for Lemma 7.22.4: under the adjunction, membership in the pushforward sieve is exactly
membership in the original sieve. -/
lemma continuous_right_adjoint_mem_functorPushforward_iff
    (adj : u ⊣ v) {U : D} (S : Sieve U) {X : C} (g : u.obj X ⟶ U) :
    S.functorPushforward v ((adj.homEquiv X U) g) ↔ S g := by
  constructor
  · intro hg
    rcases hg with ⟨Z, h, k, hh, hk⟩
    -- Pull the pushforward factorization back across the adjunction equivalence.
    have hfactor : g = (adj.homEquiv X Z).symm k ≫ h := by
      calc
        g = (adj.homEquiv X U).symm ((adj.homEquiv X U) g) := by simp
        _ = (adj.homEquiv X U).symm (k ≫ v.map h) := by rw [hk]
        _ = (adj.homEquiv X Z).symm k ≫ h := by
          simpa using adj.homEquiv_naturality_right_symm k h
    -- The original sieve is downward closed, so the pulled-back factorization stays inside it.
    rw [hfactor]
    exact S.downward_closed hh _
  · intro hg
    -- The adjunction unit gives the canonical witness that the image of `g` lies in the
    -- pushforward sieve.
    refine ⟨u.obj X, g, adj.unit.app X, hg, ?_⟩
    simpa using adj.homEquiv_unit (X := X) (Y := U) (f := g)

/-- Helper for Lemma 7.22.4: the whiskered shrink subfunctor is naturally identified with the
shrink subfunctor of the pushed-forward sieve. -/
noncomputable def continuous_right_adjoint_pushforward_shrinkFunctor_iso
    (adj : u ⊣ v) (U : D) (S : Sieve U) :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj u.op).obj
      ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).toFunctor) ≅
        ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).toFunctor) := by
  -- Restrict the ambient adjunction-induced isomorphism to the relevant sieve subfunctors.
  refine NatIso.ofComponents ?_ ?_
  · intro X
    let e :
        (u.op ⋙ shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U).obj X ≃
          (shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U)).obj X :=
      (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}.trans (adj.homEquiv (unop X) U)).trans
        (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}).symm
    refine Equiv.toIso ?_
    refine Equiv.subtypeEquiv e ?_
    intro x
    -- On underlying arrows, the restricted equivalence is exactly the adjunction hom-equivalence.
    change S (shrinkYonedaObjObjEquiv x) ↔
      S.functorPushforward v (shrinkYonedaObjObjEquiv (e x))
    rw [show e x = (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}).symm
        ((adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x)) by
          rfl]
    simp
    exact (continuous_right_adjoint_mem_functorPushforward_iff
      (u := u) (v := v) adj S (X := unop X) (g := shrinkYonedaObjObjEquiv x)).symm
  · intro X Y f
    -- Naturality is inherited from the ambient `shrinkYoneda` isomorphism.
    ext x
    apply Subtype.ext
    simpa [Equiv.subtypeEquiv] using
      congr_fun
        ((continuous_right_adjoint_shrinkYonedaIso (u := u) (v := v) adj U).hom.naturality f)
        x.1

/-- Helper for Lemma 7.22.4: after rewriting the ambient representable presheaf along the
adjunction, the transformed shrink inclusion agrees with the shrink inclusion of the pushed
forward sieve. -/
noncomputable def continuous_right_adjoint_pushforward_shrinkFunctor_arrowIso
    (adj : u ⊣ v) (U : D) (S : Sieve U) :
    Arrow.mk (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj u.op).map
      ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι)) ≅
      Arrow.mk ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι) := by
  -- Package the domain and codomain identifications into an isomorphism of arrows.
  refine Arrow.isoMk' _ _
    (continuous_right_adjoint_pushforward_shrinkFunctor_iso (u := u) (v := v) adj U S)
    (continuous_right_adjoint_shrinkYonedaIso (u := u) (v := v) adj U) ?_
  ext X x
  rfl

/-- Lemma 7.22.4: if the right adjoint `v : (\mathcal D, K) ⥤ (\mathcal C, J)` is continuous,
then its left adjoint `u : (\mathcal C, J) ⥤ (\mathcal D, K)` is cocontinuous. This is the
source-facing owner needed to apply Lemmas `7.22.1` and `7.22.2`. -/
theorem leftAdjoint_isCocontinuous_of_continuous_rightAdjoint
    (adj : u ⊣ v) [v.IsContinuous K J] : u.IsCocontinuous J K := by
  have hcover : CoverPreserving K J v := by
    -- Route correction: convert continuity into a covering statement through the sheaf
    -- `Functor.closedSieves J`, after transporting the shrink inclusion across the adjunction.
    refine ⟨?_⟩
    intro U S hS
    let A := Type (max u₁ u₂ v₁ v₂)
    let H : (Dᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op
    -- Continuity sends the `W`-class of the covering shrink inclusion in `K` to the
    -- corresponding `W`-class in `J`.
    have hWS : K.W (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι :=
      Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ u₂ v₁ v₂} K S hS
    have hW : J.W (H.map (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι) :=
      v.W_map_of_adjunction_of_isContinuous K J H (adj.op.whiskerLeft A)
        (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι hWS
    -- The only remaining comparison is to rewrite this transformed shrink inclusion as the
    -- shrink inclusion of `S.functorPushforward v`.
    have hWPush : J.W ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι) := by
      exact (J.W.arrow_mk_iso_iff
        (continuous_right_adjoint_pushforward_shrinkFunctor_arrowIso
          (u := u) (v := v) adj U S)).1 hW
    let P : Cᵒᵖ ⥤ A :=
      (Functor.closedSieves J).toFunctor ⋙
        CategoryTheory.uliftFunctor.{max u₂ v₂, max u₁ v₁}
    have hP : Presheaf.IsSheaf J P := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact Presieve.isSheaf_comp_uliftFunctor J (classifier_isSheaf J)
    -- Apply the `W`-statement to the sheaf of closed sieves and then use its classifier
    -- property to recover the covering condition.
    have hBij : Function.Bijective (fun g : _ ⟶ P ↦
        (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι ≫ g) :=
      hWPush P hP
    have hSheafForP : Presieve.IsSheafFor P (S.functorPushforward v).arrows :=
      (Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp _ P).2 hBij
    have hSheafFor : Presieve.IsSheafFor (Functor.closedSieves J).toFunctor
        (S.functorPushforward v).arrows := by
      rwa [Presieve.isSheafFor_comp_uliftFunctor_iff] at hSheafForP
    exact (GrothendieckTopology.mem_iff_isSheafFor_closedSieves J _).2 hSheafFor
  exact (Adjunction.isCocontinuous_iff_coverPreserving J K adj).2 hcover

/-- A continuous right adjoint defines the morphism of sites occurring in Lemma `7.22.4`. -/
theorem rightAdjoint_isMorphismOfSites_of_continuous
    (adj : u ⊣ v) [v.IsContinuous K J] : IsMorphismOfSites K J v := by
  let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
  let _ : RepresentablyFlat v := inferInstance
  exact isMorphismOfSites_of_isContinuous_representablyFlat K J v

/- Owner recall: this is exactly the canonical adjunction equivalence between cocontinuity of the
left adjoint and cover preservation of the right adjoint. -/
recall Adjunction.isCocontinuous_iff_coverPreserving

end CategoryTheory
