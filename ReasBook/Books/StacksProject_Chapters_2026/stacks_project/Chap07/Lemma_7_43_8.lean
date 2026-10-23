module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_43_7
public import stacks_project.Chap07.Lemma_7_41_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (i : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K)

/- Domain-style sampling for Lemma 7.43.8:
- primary domain: closed immersions of topoi and the owner-level consequences for the direct-image
  functor and the adjunction counit;
- sampled owner API:
  `MorphismOfTopoiIn.IsClosedImmersion`,
  `MorphismOfTopoiIn.IsEmbedding`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  the canonical implication theorems from `Lemma_7_41_1`;
- best owner abstraction: the source-facing class `MorphismOfTopoiIn.IsClosedImmersion i`, whose
  primitive data are only the embedding structure and the closed-subtopos condition on
  `(i _*).essImage`;
- primitive data: `i.IsClosedImmersion`;
- derived API: the canonical fully faithful structure on `(i _*)` together with the reflection and
  preservation properties on `(i _*)` that this lemma records for closed immersions.

Source/core/bridge triage:
- `source-facing`: the closed-immersion consequences listed in Lemma 7.43.8;
- `core/canonical`: `MorphismOfTopoiIn.IsEmbedding`, `(i _*).Full`,
  `(i _*).Faithful`, `IsIso i.adjunction.counit`, and the standard
  `Preserves`/`Reflects` owner classes on `(i _*)`;
- `bridge/view`: the passage from `i.IsClosedImmersion` to those owner-level consequences. -/

/-- Lemma 7.43.8 (1): for a closed immersion of topoi, the direct-image functor `i_*` is fully
faithful. -/
noncomputable instance closedImmersion_pushforwardFullyFaithful [i.IsClosedImmersion] :
    (i _*).FullyFaithful :=
  .ofFullyFaithful (i _*)

/-- Helper for Lemma 7.43.8: a full faithful functor preserves any chosen colimit shape once its
essential image is closed under that shape. -/
private theorem preservesColimitsOfShape_of_essImage_closed
    {A : Type*} [Category A] {B : Type*} [Category B]
    {S : Type*} [Category S]
    (F : A ⥤ B) [HasColimitsOfShape S A] [HasColimitsOfShape S B]
    [F.Full] [F.Faithful] [F.essImage.IsClosedUnderColimitsOfShape S] :
    PreservesColimitsOfShape S F := by
  -- Factor through the essential image: the first factor is an equivalence, and the inclusion
  -- preserves these colimits because the essential image is closed under them.
  letI : HasColimitsOfShape S F.EssImageSubcategory := inferInstance
  letI : PreservesColimitsOfShape S F.essImage.ι := inferInstance
  letI : PreservesColimitsOfShape S F.toEssImage := inferInstance
  exact preservesColimitsOfShape_of_natIso (Functor.toEssImageCompι F)

/-- Helper for Lemma 7.43.8: `WalkingSpan.zero` is the initial object of the pushout shape. -/
private noncomputable def walkingSpan_zero_isInitial :
    IsInitial (WalkingSpan.zero) := by
  refine IsInitial.ofUniqueHom (fun j ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
  cases j with
  | none => exact 𝟙 _
  | some j =>
      cases j with
      | left => exact WalkingSpan.Hom.fst
      | right => exact WalkingSpan.Hom.snd

/-- Helper for Lemma 7.43.8: the closed-subtopos witness rewrites the essential image of a closed
immersion into the source-facing product-projection condition. -/
private theorem closedImmersion_essImage_eq_prod_fst [i.IsClosedImmersion] :
    ∃ F : Sheaf J (Type w),
      IsSubterminal F ∧
      (i _*).essImage =
        fun G : Sheaf J (Type w) ↦
        IsIso (prod.fst : F ⨯ G ⟶ F) := by
  let h : i.IsClosedImmersion := inferInstance
  have hClosed : IsClosedSubtopos (i _*).essImage := h.isClosedSubtopos
  exact hClosed.exists_subterminal

/-- Helper for Lemma 7.43.8: the closed-subtopos product-projection condition is stable under
connected colimits. -/
private theorem prod_fst_closed_under_connected_colimits
    {S : Type} [Category.{0} S] [IsConnected S]
    [HasColimitsOfShape S (Sheaf J (Type w))]
    (F : Sheaf J (Type w))
    [PreservesColimitsOfShape S (prod.functor.obj F)] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun G : Sheaf J (Type w) ↦
        IsIso (prod.fst : F ⨯ G ⟶ F))
      S := by
  let P : ObjectProperty (Sheaf J (Type w)) :=
    fun G ↦ IsIso (prod.fst : F ⨯ G ⟶ F)
  letI : P.IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro G G' e hG
    haveI : IsIso (prod.fst : F ⨯ G ⟶ F) := by
      simpa [P] using hG
    have hcomp : IsIso ((prod.functor.obj F).map e.hom ≫
        (prod.fst : F ⨯ G' ⟶ F)) := by
      change IsIso (prod.map (𝟙 F) e.hom ≫ (prod.fst : F ⨯ G' ⟶ F))
      simpa using (inferInstance : IsIso (prod.fst : F ⨯ G ⟶ F))
    haveI : IsIso ((prod.functor.obj F).map e.hom) := by
      infer_instance
    exact IsIso.of_isIso_comp_left ((prod.functor.obj F).map e.hom)
      (prod.fst : F ⨯ G' ⟶ F)
  change P.IsClosedUnderColimitsOfShape S
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨L, hL⟩
  let T : Sheaf J (Type w) ⥤ Sheaf J (Type w) := prod.functor.obj F
  haveI : PreservesColimitsOfShape S T := by
    change PreservesColimitsOfShape S (prod.functor.obj F)
    infer_instance
  let c := T.mapCocone (colimit.cocone L)
  have hc : IsColimit c := isColimitOfPreserves T (colimit.isColimit L)
  let α : L ⋙ T ≅ (Functor.const S).obj F :=
    NatIso.ofComponents
      (fun j ↦ by
        have hLj : IsIso (prod.fst : F ⨯ L.obj j ⟶ F) := by
          simpa [P] using hL j
        letI := hLj
        change F ⨯ L.obj j ≅ F
        exact asIso (prod.fst : F ⨯ L.obj j ⟶ F))
      (fun {j j'} f ↦ by
        simp [T])
  let hConst :
      IsColimit (Limits.constCocone S F) :=
    Limits.isColimitConstCocone S F
  let e : c.pt ≅ F :=
    IsColimit.coconePointsIsoOfNatIso hc hConst α
  have he : e.hom = (prod.fst : F ⨯ colimit L ⟶ F) := by
    apply hc.hom_ext
    intro j
    have hcomp := IsColimit.comp_coconePointsIsoOfNatIso_hom hc hConst α j
    simpa [c, T, e, α] using hcomp
  change IsIso (prod.fst : F ⨯ colimit L ⟶ F)
  rw [← he]
  infer_instance

/-- Helper for Lemma 7.43.8: the essential-image factorization of a closed immersion makes the
direct-image functor preserve coequalizers. -/
private theorem closedImmersion_pushforwardPreservesCoequalizers_aux [i.IsClosedImmersion]
    [HasColimitsOfShape WalkingParallelPair (Sheaf J (Type w))]
    [HasColimitsOfShape WalkingParallelPair (Sheaf K (Type w))]
    [prodPres :
      ∀ F : Sheaf J (Type w),
        PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj F)] :
    PreservesColimitsOfShape WalkingParallelPair (i _*) := by
  rcases closedImmersion_essImage_eq_prod_fst
      (C := C) (D := D) (J := J) (K := K) (i := i) with
    ⟨F, _hFsub, hEss⟩
  letI : PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj F) := prodPres F
  -- The closed witness identifies the essential image with the source-facing product condition,
  -- and connected coequalizer shapes are stable under the fixed-product functor.
  haveI : (i _*).essImage.IsClosedUnderColimitsOfShape WalkingParallelPair := by
    simpa [hEss] using
      prod_fst_closed_under_connected_colimits
        (J := J) (S := WalkingParallelPair) F
  -- Factor `i_*` through its essential image and use closure of that image under coequalizers.
  let h : i.IsClosedImmersion := inferInstance
  letI : (i _*).Full := h.toIsEmbedding.toFull
  letI : (i _*).Faithful := h.toIsEmbedding.toFaithful
  exact preservesColimitsOfShape_of_essImage_closed (S := WalkingParallelPair) (i _*)

/-- Helper for Lemma 7.43.8: the essential-image factorization of a closed immersion makes the
direct-image functor preserve pushouts. -/
private theorem closedImmersion_pushforwardPreservesPushouts_aux [i.IsClosedImmersion]
    [HasColimitsOfShape WalkingSpan (Sheaf J (Type w))]
    [HasColimitsOfShape WalkingSpan (Sheaf K (Type w))]
    [prodPres :
      ∀ F : Sheaf J (Type w),
        PreservesColimitsOfShape WalkingSpan (prod.functor.obj F)] :
    PreservesColimitsOfShape WalkingSpan (i _*) := by
  rcases closedImmersion_essImage_eq_prod_fst
      (C := C) (D := D) (J := J) (K := K) (i := i) with
    ⟨F, _hFsub, hEss⟩
  letI : PreservesColimitsOfShape WalkingSpan (prod.functor.obj F) := prodPres F
  -- The same product-projection description is stable under pushouts by the connected-colimit
  -- exactness argument from the source proof.
  haveI : (i _*).essImage.IsClosedUnderColimitsOfShape WalkingSpan := by
    simpa [hEss] using
      prod_fst_closed_under_connected_colimits
        (J := J) (S := WalkingSpan) F
  -- Factor `i_*` through its essential image and use closure of that image under pushouts.
  let h : i.IsClosedImmersion := inferInstance
  letI : (i _*).Full := h.toIsEmbedding.toFull
  letI : (i _*).Faithful := h.toIsEmbedding.toFaithful
  exact preservesColimitsOfShape_of_essImage_closed (S := WalkingSpan) (i _*)

/-- Helper for Lemma 7.43.8: the counit of the closed-immersion adjunction is an isomorphism
because `i_*` is fully faithful. -/
private theorem closedImmersion_counit_isIso [i.IsClosedImmersion] :
    IsIso i.adjunction.counit := by
  -- Closed immersions are embeddings, so the standard adjunction theorem applies directly.
  let h : i.IsClosedImmersion := inferInstance
  letI : (i _*).Full := h.toIsEmbedding.toFull
  letI : (i _*).Faithful := h.toIsEmbedding.toFaithful
  exact Adjunction.counit_isIso_of_R_fully_faithful i.adjunction

/-- Lemma 7.43.8 (2): for a closed immersion of topoi, the direct-image functor `i_*` sends
surjections to surjections. -/
instance closedImmersion_pushforwardPreservesEpimorphisms [i.IsClosedImmersion]
    [HasColimitsOfShape WalkingSpan (Sheaf J (Type w))]
    [HasColimitsOfShape WalkingSpan (Sheaf K (Type w))]
    [∀ F : Sheaf J (Type w),
      PreservesColimitsOfShape WalkingSpan (prod.functor.obj F)] :
    (i _*).PreservesEpimorphisms := by
  -- The source proof first establishes pushout preservation and then invokes the owner-level
  -- implication from Lemma 7.41.1.
  exact pushforwardPreservesPushouts_implies_pushforwardPreservesEpimorphisms
    (f := i) (closedImmersion_pushforwardPreservesPushouts_aux (i := i))

/-- Lemma 7.43.8 (3): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with coequalizers. -/
instance closedImmersion_pushforwardPreservesCoequalizers [i.IsClosedImmersion]
    [HasColimitsOfShape WalkingParallelPair (Sheaf J (Type w))]
    [HasColimitsOfShape WalkingParallelPair (Sheaf K (Type w))]
    [∀ F : Sheaf J (Type w),
      PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj F)] :
    PreservesColimitsOfShape WalkingParallelPair (i _*) := by
  -- This is the coequalizer half of the essential-image argument implemented above.
  exact closedImmersion_pushforwardPreservesCoequalizers_aux (i := i)

/-- Lemma 7.43.8 (4): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with pushouts. -/
instance closedImmersion_pushforwardPreservesPushouts [i.IsClosedImmersion]
    [HasColimitsOfShape WalkingSpan (Sheaf J (Type w))]
    [HasColimitsOfShape WalkingSpan (Sheaf K (Type w))]
    [∀ F : Sheaf J (Type w),
      PreservesColimitsOfShape WalkingSpan (prod.functor.obj F)] :
    PreservesColimitsOfShape WalkingSpan (i _*) := by
  -- This is the pushout half of the essential-image argument implemented above.
  exact closedImmersion_pushforwardPreservesPushouts_aux (i := i)

/-- Lemma 7.43.8 (5): for a closed immersion of topoi, the direct-image functor `i_*` reflects
injections. -/
instance closedImmersion_pushforwardReflectsMonomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsMonomorphisms := by
  -- Once the counit is an isomorphism, the generic owner theorem gives reflection of monomorphisms.
  exact counitIsIso_implies_pushforwardReflectsMonomorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

/-- Lemma 7.43.8 (6): for a closed immersion of topoi, the direct-image functor `i_*` reflects
surjections. -/
instance closedImmersion_pushforwardReflectsEpimorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsEpimorphisms := by
  -- The same counit-isomorphism bridge yields reflection of epimorphisms.
  exact counitIsIso_implies_pushforwardReflectsEpimorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

/-- Lemma 7.43.8 (7): for a closed immersion of topoi, the direct-image functor `i_*` reflects
isomorphisms. -/
instance closedImmersion_pushforwardReflectsIsomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsIsomorphisms := by
  -- The counit-isomorphism criterion also gives reflection of isomorphisms.
  exact counitIsIso_implies_pushforwardReflectsIsomorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

end

end MorphismOfTopoiIn

end CategoryTheory
