module

public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite Equiv
open scoped CategoryTheory

universe uI vI uJ vJ uC vC

namespace CategoryTheory

/- Domain-style sampling for Remark 4.22.7:
- primary domain: pro-objects via the pro-coyoneda lemma in `CategoryTheory.Limits`.
- inspected owner-level declarations:
  `Limits.colimitCoyonedaHomIsoLimit'`,
  `Limits.colimitObjIsoColimitCompEvaluation`,
  `Types.limitEquivSections`,
  `uliftCoyonedaEquiv`.
- best owner abstraction: `Limits.colimitCoyonedaHomIsoLimit'`.
  The public theorem below is a bridge from that owner to the universe-lifted source-facing
  pro-object formula used in this chapter, with the limit target returned in its plain form.

Primitive-vs-derived split:
- primitive data: the diagram `F : I ⥤ C`.
- core owner: the colimit object `colimit (F.op ⋙ uliftCoyoneda.{uI})`.
- derived API: the Hom-colimit functor notation `proSystemHomColimitFunctor F`;
  pointwise evaluation uses the upstream owner
  `Limits.colimitObjIsoColimitCompEvaluation`, and the final limit target is unlifted again via
  `Limits.preservesLimitIso` for `Types.uliftFunctor`.

Source/core/bridge triage:
- `source-facing`: `proSystemHomColimitFunctor F`, the textbook `X ↦ colim_i Hom(F_i, X)`.
- `core/canonical`: `Limits.colimitCoyonedaHomIsoLimit'`.
- `bridge/view`: the ulift-coyoneda-to-sections comparison needed to express the same
  pro-coyoneda bridge at the universe level used in this chapter, followed by the canonical
  removal of the final `ULift` on the limit object. -/

/-- The Hom-colimit functor attached to a diagram `F`, sending `X` to
`colim_i Hom(F(i), X)`, with the Hom-sets ulifted only as much as needed for the indexing
category of `F`. -/
noncomputable abbrev proSystemHomColimitFunctor
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    (F : I ⥤ C) : C ⥤ Type (max uI vC) :=
  colimit (F.op ⋙ uliftCoyoneda.{uI})

section

variable {I : Type uI} {J : Type uJ} {C : Type uC}
variable [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
variable {F : I ⥤ C} {G : J ⥤ C}

noncomputable def uliftCoyonedaNatTransEquivSections
    (G : J ⥤ C) (H : C ⥤ Type (max uI uJ vC)) :
    ((G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ (Functor.const Jᵒᵖ).obj H) ≃ (G ⋙ H).sections where
  toFun τ :=
    ⟨
      fun j ↦ uliftCoyonedaEquiv.{max uI uJ} (τ.app (op j)),
      fun {j j'} g ↦ by
        simpa using
          (uliftCoyonedaEquiv_naturality.{max uI uJ} (τ.app (op j)) (G.map g)).trans
            (congrArg (uliftCoyonedaEquiv.{max uI uJ}) (τ.naturality g.op))
    ⟩
  invFun s :=
    { app := fun j ↦ uliftCoyonedaEquiv.{max uI uJ}.symm (s.1 j.unop)
      naturality := fun j j' g ↦ by
        simp only [Functor.const_obj_map]
        let hs := congrArg
          (uliftCoyonedaEquiv.{max uI uJ}.symm)
          (s.2 g.unop)
        simpa using
          (uliftCoyonedaEquiv_symm_map.{max uI uJ} (G.map g.unop) (s.1 j'.unop)).symm.trans hs }
  left_inv τ := by
    ext j X x
    rcases x with ⟨x⟩
    simpa using (FunctorToTypes.naturality _ _ (τ.app j) x (ULift.up (𝟙 _))).symm
  right_inv s := by
    ext j
    exact apply_symm_apply (uliftCoyonedaEquiv.{max uI uJ}) (s.1 j)

noncomputable def colimitUliftCoyonedaHomEquivLimit
    (G : J ⥤ C) (H : C ⥤ Type (max uI uJ vC)) :
    (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃ limit (G ⋙ H) := by
  let i :
      (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃
        ((G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ (Functor.const Jᵒᵖ).obj H) :=
    (Equiv.ulift : ULift (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃ _).symm.trans
      (IsColimit.homIso (colimit.isColimit (G.op ⋙ uliftCoyoneda.{max uI uJ})) H).toEquiv
  exact ((i.trans (uliftCoyonedaNatTransEquivSections G H)).trans
    (Types.limitEquivSections _).symm)

/-- Remark 4.22.7: for any diagrams `F : \mathcal I \to \mathcal C` and
`G : \mathcal J \to \mathcal C`, the limit of the diagram
`G ⋙ proSystemHomColimitFunctor F` identifies with morphisms from the formal pro-object of `G`
`colim_j Hom(G(j), -)` to the Hom-colimit functor of `F`.
This is the canonical pro-object bridge underlying the textbook formula
`\varprojlim_j \varinjlim_i \operatorname{Hom}(F_i, G_j)`. The explicit `HasLimit` hypothesis is
exactly the small-universe assumption needed to return the final inverse limit without an extra
`ULift`. -/
noncomputable def proObjectHomEquivLimitProSystemHomColimitFunctor
    (F : I ⥤ C) (G : J ⥤ C) [HasLimit (G ⋙ proSystemHomColimitFunctor F)] :
    (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶
      proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ}) ≃
    limit (G ⋙ proSystemHomColimitFunctor F) := by
  let e :
      limit (G ⋙ proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ, max uI vC}) ≃
        limit (G ⋙ proSystemHomColimitFunctor F) :=
    (preservesLimitIso
      (uliftFunctor.{uJ, max uI vC})
      (G ⋙ proSystemHomColimitFunctor F)).symm.toEquiv.trans
      (Equiv.ulift :
        ULift (limit (G ⋙ proSystemHomColimitFunctor F)) ≃
          limit (G ⋙ proSystemHomColimitFunctor F))
  exact
    (colimitUliftCoyonedaHomEquivLimit G
      (proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ, max uI vC})).trans e

/-- The comparison map of `proObjectHomEquivLimitProSystemHomColimitFunctor` is bijective. -/
-- Proof sketch: this is immediate because the comparison is packaged as an equivalence.
theorem proObjectHomEquivLimitProSystemHomColimitFunctor_bijective
    (F : I ⥤ C) (G : J ⥤ C) [HasLimit (G ⋙ proSystemHomColimitFunctor F)] :
    Function.Bijective (proObjectHomEquivLimitProSystemHomColimitFunctor F G) := by
  -- The theorem is purely formal: every equivalence has a bijective underlying function.
  simpa using (proObjectHomEquivLimitProSystemHomColimitFunctor F G).bijective

end

end CategoryTheory
