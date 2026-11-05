module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import stacks_project.Chap04.Lemma_4_18_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.6:
- primary domain: finite nonempty colimits in `CategoryTheory.Limits`, viewed through passage to
  the opposite category;
- sampled owner API:
  `HasFiniteConnectedColimits`,
  `HasFiniteNonemptyLimits`,
  `hasColimitsOfShape_of_hasLimitsOfShape_op`,
  `hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers`,
  `hasCoequalizers_of_hasPushouts_and_binary_coproducts`;
- best owner abstraction: the source-facing colimit owner `HasFiniteNonemptyColimits`, with the
  opposite-category owner `HasFiniteNonemptyLimits Cᵒᵖ` as the internal core;
- primitive data: no new primitive data beyond the core owner `HasFiniteNonemptyLimits Cᵒᵖ`;
- derived API: the source-facing bridge owner, the finite-nonempty-shape colimit transfer
  instance, and the atomic `↔` reformulations below;
- layer triage:
  - `source-facing`: `HasFiniteNonemptyColimits` and the finite-nonempty-colimit statements of
    Lemma 4.18.6;
  - `core/canonical`: `HasFiniteNonemptyLimits` on the opposite category;
  - `bridge/view`: the instance transfer lemma and the source-facing colimit equivalences
    below. -/

/-- A category has finite nonempty colimits when its opposite has finite nonempty limits. -/
abbrev HasFiniteNonemptyColimits : Prop :=
  HasFiniteNonemptyLimits Cᵒᵖ

instance hasColimitsOfShape_of_hasFiniteNonemptyColimits
    [HasFiniteNonemptyColimits C] (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasColimitsOfShape J C := by
  let _ : HasLimitsOfShape Jᵒᵖ Cᵒᵖ := by infer_instance
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

attribute [instance 100] hasColimitsOfShape_of_hasFiniteNonemptyColimits

/-- Lemma 4.18.6 (1): a category `C` has finite nonempty colimits if and only if it has binary
coproducts and coequalizers. -/
theorem finite_nonempty_colimits_iff_binary_coproducts_and_coequalizers :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasCoequalizers C := by
  constructor
  · intro h
    let _ : HasFiniteNonemptyColimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hBC, hCE⟩
    let _ : HasBinaryCoproducts C := hBC
    let _ : HasCoequalizers C := hCE
    infer_instance

/-- Lemma 4.18.6 (2): a category `C` has finite nonempty colimits if and only if it has binary
coproducts and pushouts. -/
theorem finite_nonempty_colimits_iff_binary_coproducts_and_pushouts :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasPushouts C := by
  constructor
  · intro h
    let _ : HasFiniteNonemptyColimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hBC, hPO⟩
    let _ : HasBinaryCoproducts C := hBC
    let _ : HasPushouts C := hPO
    infer_instance

end CategoryTheory.Limits
