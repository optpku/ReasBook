module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

/- Domain-style sampling for Lemma 4.23.3:
- primary domain: right exactness and finite-colimit preservation in category theory;
- sampled owner API:
  `rightExactFunctor`,
  `rightExactFunctor_iff`,
  `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`,
  `preservesFiniteColimits_of_preservesInitial_and_pushouts`,
  `preservesColimitsOfShape_pempty_of_preservesInitial`;
- best owner abstraction: the chapter's right-exactness owner `rightExactFunctor C D`;
- source/core/bridge triage:
  `source-facing`: the textbook decompositions of right exactness into
  coproducts-plus-coequalizers and initial-object-plus-pushouts;
  `core/canonical`: `rightExactFunctor C D`, with companion simplification
  `rightExactFunctor_iff`;
  `bridge/view`: the two equivalences below.

Primitive data here are the relevant shape-preservation assumptions. The finite-colimit predicate is
derived API through `rightExactFunctor_iff`, so this file should stay a thin bridge to the
canonical mathlib constructors rather than keeping a parallel public surface phrased directly in
`PreservesFiniteColimits`. -/

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Companion recall: the converse directions are already owned by the canonical mathlib
constructors below. -/
recall preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
recall preservesFiniteColimits_of_preservesInitial_and_pushouts

/-- Lemma 4.23.3 (1): a functor is right exact if and only if it preserves finite coproducts and
coequalizers. -/
-- Proof sketch: one direction is immediate because finite coproducts and coequalizers are finite
-- colimits. Conversely, use
-- `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`.
theorem rightExactFunctor_iff_preserves_finite_coproducts_and_coequalizers
    [HasCoequalizers C] [HasFiniteCoproducts C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesFiniteCoproducts F ∧ PreservesColimitsOfShape WalkingParallelPair F := by
  rw [rightExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hcoprod, hcoeq⟩
    letI := hcoprod
    letI := hcoeq
    exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts F

/-- Lemma 4.23.3 (2): a functor is right exact if and only if it preserves initial objects and
pushouts. -/
-- Proof sketch: one direction is immediate because initial objects and pushouts are finite
-- colimits. Conversely, pass from preservation of the initial object to preservation of
-- `Discrete PEmpty`-shaped colimits via `preservesColimitsOfShape_pempty_of_preservesInitial`,
-- then apply `preservesFiniteColimits_of_preservesInitial_and_pushouts`.
theorem rightExactFunctor_iff_preserves_initial_and_pushouts
    [HasInitial C] [HasPushouts C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesColimit (Functor.empty.{0} C) F ∧ PreservesColimitsOfShape WalkingSpan F := by
  rw [rightExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hinitial, hpushouts⟩
    letI : PreservesColimit (Functor.empty.{0} C) F := hinitial
    letI : PreservesColimitsOfShape (Discrete PEmpty) F :=
      preservesColimitsOfShape_pempty_of_preservesInitial F
    letI := hpushouts
    exact preservesFiniteColimits_of_preservesInitial_and_pushouts F

end CategoryTheory.Limits
