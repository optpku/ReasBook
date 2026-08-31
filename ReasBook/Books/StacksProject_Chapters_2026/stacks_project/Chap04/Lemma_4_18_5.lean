module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import stacks_project.Chap04.Lemma_4_18_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.5:
- primary domain: finite connected colimit shapes in `CategoryTheory.Limits`, expressed via
  opposite categories;
- sampled owner API:
  `HasFiniteConnectedLimits`,
  `finite_connected_limits_iff_equalizers_and_pullbacks`;
- best owner abstraction: the chapter-level canonical owner remains `HasFiniteConnectedLimits` on
  `Cᵒᵖ`; `HasFiniteConnectedColimits` is only the source-facing opposite-side view of that owner;
- primitive data: no new primitive data beyond the owner predicate `HasFiniteConnectedLimits Cᵒᵖ`;
- derived API: only the colimit-shape instance below;
- layer triage:
  - `source-facing`: `finite_connected_colimits_iff_coequalizers_and_pushouts`;
  - `core/canonical`: `HasFiniteConnectedLimits`;
  - `bridge/view`: `HasFiniteConnectedColimits` and the shape-transfer instance below. -/

/-- A category has finite connected colimits when its opposite has finite connected limits. This
is the canonical owner/view split for the colimit notion in this chapter. -/
abbrev HasFiniteConnectedColimits : Prop :=
  HasFiniteConnectedLimits Cᵒᵖ

instance hasColimitsOfShape_of_hasFiniteConnectedColimits
    [HasFiniteConnectedColimits C] (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasColimitsOfShape J C :=
  hasColimitsOfShape_of_hasLimitsOfShape_op

attribute [instance 100] hasColimitsOfShape_of_hasFiniteConnectedColimits

/-- Lemma 4.18.5: a category has colimits of every finite connected small diagram if and only if
it has coequalizers and pushouts. -/
-- Proof sketch: coequalizers and pushouts are themselves finite connected colimits, so the
-- forward implication is immediate. For the converse, apply Lemma 4.18.2 to the opposite
-- category, where coequalizers and pushouts become equalizers and pullbacks.
theorem finite_connected_colimits_iff_coequalizers_and_pushouts :
    HasFiniteConnectedColimits C ↔
      HasCoequalizers C ∧ HasPushouts C := by
  constructor
  · intro h
    let _ : HasFiniteConnectedLimits Cᵒᵖ := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hcoeq, hpo⟩
    let _ : HasCoequalizers C := hcoeq
    let _ : HasPushouts C := hpo
    exact hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks Cᵒᵖ

end CategoryTheory.Limits
