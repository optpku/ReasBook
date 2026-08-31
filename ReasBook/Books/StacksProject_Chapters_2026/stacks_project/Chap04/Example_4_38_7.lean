module

public import stacks_project.Chap04.Example_4_3_4
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Example_4_38_5
public import stacks_project.Chap04.Lemma_4_35_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite
open BasedFunctor
open CategoryOfElements
open CostructuredArrow
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.38.7:
- primary domain: representable presheaves, categories of elements, and slice categories over a
  fixed base object.
- inspected owner-level declarations:
  `CategoryOfElements.costructuredArrowYonedaEquivalence`,
  `CostructuredArrow.post`,
  `Functor.toOver`,
  `BasedFunctor.IsEquivalenceOverBase`.
- best owner abstraction: the canonical equivalence between the slice category `Over X` and the
  costructured-arrow model of `h[X]` is the strict `Functor.toOver` functor
  `costructuredArrowYonedaToOver X`, whose inverse data is canonically supplied by
  `CostructuredArrow.post (𝟭 C) yoneda X`; the source-facing equivalence of Example 4.38.7 is
  then the private owner equivalence `costructuredArrowYonedaOverEquivalence X`, composed with
  `CategoryOfElements.costructuredArrowYonedaEquivalence`. The only genuinely extra data needed
  in this file is the strict over-base lift of that canonical equivalence functor.
- primitive data: the source-facing equivalence
  `representableElementsOpToOverEquivalence X : h[X].Elementsᵒᵖ ≌ Over X`.
- derived API: the strict over-base comparison morphism in `FibredInGroupoidsOver C`, obtained by
  reusing the functor underlying that equivalence, together with the
  source-facing category equivalence `h[X].Elementsᵒᵖ ≌ Over X`, and the over-base equivalence
  statement.

Source/core/bridge triage:
- `source-facing`: `representableElementsOpToOverEquivalence`;
- `core/canonical`: `FibredInGroupoidsOver.ofFunctor (Over.forget X)`,
  `costructuredArrowYonedaEquivalence`, `CostructuredArrow.post (𝟭 C) yoneda X`;
- `bridge/view`: the owner morphism `representableElementsOpToOver X`, obtained directly from the
  functor underlying `representableElementsOpToOverEquivalence X`. -/

theorem costructuredArrowYonedaToOver_w (X : C)
    {Y Z : CostructuredArrow yoneda h[X]} (g : Y ⟶ Z) :
    (CostructuredArrow.proj yoneda h[X]).map g ≫ yonedaEquiv Z.hom = yonedaEquiv Y.hom := by
  change g.left ≫ yonedaEquiv Z.hom = yonedaEquiv Y.hom
  rw [← CostructuredArrow.w g]
  simpa using (yonedaEquiv_naturality Z.hom g.left)

noncomputable def costructuredArrowYonedaToOver (X : C) :
    CostructuredArrow yoneda h[X] ⥤ Over X :=
  Functor.toOver (CostructuredArrow.proj yoneda h[X]) X
    (fun Y ↦ yonedaEquiv Y.hom)
    (fun g ↦ costructuredArrowYonedaToOver_w X g)

private theorem costructuredArrowYonedaToOver_unit_hom_eq
    (X : C) (Z : CostructuredArrow yoneda h[X]) :
    yoneda.map (yonedaEquiv Z.hom) = Z.hom := by
  apply yonedaEquiv.injective
  change yonedaEquiv (yoneda.map (yonedaEquiv Z.hom)) = yonedaEquiv Z.hom
  simpa using (yonedaEquiv_yoneda_map (yonedaEquiv Z.hom))

noncomputable def costructuredArrowYonedaOverEquivalence (X : C) :
    CostructuredArrow yoneda h[X] ≌ Over X where
  functor := costructuredArrowYonedaToOver X
  inverse := CostructuredArrow.post (𝟭 C) yoneda X
  unitIso :=
    NatIso.ofComponents
      (fun Z ↦
        CostructuredArrow.isoMk (Iso.refl _) (by
          simpa [costructuredArrowYonedaToOver] using
            costructuredArrowYonedaToOver_unit_hom_eq X Z))
      (by
        intro Y Z f
        apply CostructuredArrow.hom_ext
        simp [costructuredArrowYonedaToOver])
  counitIso :=
    NatIso.ofComponents
      (fun Y ↦
        Over.isoMk (Iso.refl _) (by
          simpa [costructuredArrowYonedaToOver] using (yonedaEquiv_yoneda_map Y.hom).symm))
      (by
        intro Y Z f
        ext
        simp [costructuredArrowYonedaToOver])
  functor_unitIso_comp Z := by
    ext
    simp [costructuredArrowYonedaToOver]

/-- Example 4.38.7: the opposite category of elements of the representable presheaf `h_X` is
canonically equivalent to the slice category `C/X`. This is the categorical form of the
identification of objects and morphisms in `h_X.Elementsᵒᵖ` with arrows and commutative triangles
over `X`. -/
noncomputable def representableElementsOpToOverEquivalence (X : C) :
    h[X].Elementsᵒᵖ ≌ Over X :=
  (costructuredArrowYonedaEquivalence h[X]).trans
    (costructuredArrowYonedaOverEquivalence X)

theorem representableElementsOpToOver_comp_forget (X : C) :
    (representableElementsOpToOverEquivalence X).functor ⋙ Over.forget X = (π h[X]).leftOp := by
  have hToOver :
      costructuredArrowYonedaToOver X ⋙ Over.forget X =
        CostructuredArrow.proj yoneda h[X] := by
    simpa [costructuredArrowYonedaToOver] using
      (Functor.toOver_comp_forget (CostructuredArrow.proj yoneda h[X]) X
        (fun Y ↦ yonedaEquiv Y.hom)
        (fun g ↦ costructuredArrowYonedaToOver_w X g))
  calc
    (representableElementsOpToOverEquivalence X).functor ⋙ Over.forget X =
        toCostructuredArrow h[X] ⋙ costructuredArrowYonedaToOver X ⋙ Over.forget X := rfl
    _ = toCostructuredArrow h[X] ⋙ CostructuredArrow.proj yoneda h[X] := by
      exact congrArg
        (fun F : CostructuredArrow yoneda h[X] ⥤ C ↦ toCostructuredArrow h[X] ⋙ F) hToOver
    _ = (π h[X]).leftOp := rfl

/-- Bridge/view for Example 4.38.7: the source-facing equivalence above, upgraded to the canonical
owner morphism over `C` from the category of elements of `h[X]` to the slice projection
`Over.forget X`. -/
noncomputable abbrev representableElementsOpToOver (X : C) :
    FibredInGroupoidsMor
      (FibredInGroupoidsOver.ofFunctor ((π h[X]).leftOp))
      (FibredInGroupoidsOver.ofFunctor (Over.forget X)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := (representableElementsOpToOverEquivalence X).functor
      w := representableElementsOpToOver_comp_forget X }

/-- Lemma 4.38.6, applied to the representable presheaf `h_X`: the category fibred in sets
attached to `h_X` is equivalent over `C` to the slice category `C/X`. This is the over-the-base
form of Example 4.38.7. -/
theorem representableElementsOpToOver_isEquivalenceOverBase (X : C) :
    (representableElementsOpToOver X).IsEquivalenceOverBase := by
  apply FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
  simpa [representableElementsOpToOver] using
    (inferInstance : (representableElementsOpToOverEquivalence X).functor.IsEquivalence)

end CategoryTheory
