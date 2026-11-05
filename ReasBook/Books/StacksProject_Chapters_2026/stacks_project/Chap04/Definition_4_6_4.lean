module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.6.4:
- primary domain: morphism properties and pullbacks in `CategoryTheory`.
- inspected owner declarations:
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isPullback`,
  `(𝟭 C).relativelyRepresentable`,
  `Limits.HasPullbacksAlong`.
- best owner abstraction: the identity-functor specialization `(𝟭 C).relativelyRepresentable`.
- primitive-vs-derived split:
  primitive data: only the morphism `f`.
  derived API: the pullback-existence package `HasPullbacksAlong f`, and the chosen pullback
    square extracted from relative representability via `hf.isPullback g`. -/

/- Source/core/bridge triage for Definition 4.6.4:
- source-facing: the Stacks-project equivalence between representable morphisms and existence of
  pullbacks along the morphism.
- core/canonical: `(𝟭 C).relativelyRepresentable`.
- bridge/view: `HasPullbacksAlong`.

This item keeps the canonical owner specialization as the main entry and the textbook pullback
formulation only as a companion bridge theorem. -/

/- Definition 4.6.4: a morphism `f : x ⟶ y` is representable precisely when it belongs to the
canonical morphism property `(𝟭 C).relativelyRepresentable`. -/
#check (𝟭 C).relativelyRepresentable

/- Companion owner: pullbacks existing along a fixed morphism are recorded by
`Limits.HasPullbacksAlong`. -/
recall Limits.HasPullbacksAlong

/-- Bridge/view companion to Definition 4.6.4: a morphism is representable in the canonical
identity-functor sense exactly when pullbacks along it exist. -/
-- Proof sketch: specialize `Functor.relativelyRepresentable` to the identity functor `𝟭 C`. For
-- a morphism `g : z ⟶ y`, the representing square is precisely a pullback square for `g` along `f`.
theorem relativelyRepresentable_iff_hasPullbacksAlong {x y : C} (f : x ⟶ y) :
    (𝟭 C).relativelyRepresentable f ↔ HasPullbacksAlong f := by
  constructor
  · intro hf z g
    -- The representing square for `g` already gives the required pullback of `g` along `f`.
    simpa using (hf.isPullback g).flip.hasPullback
  · intro hg z g
    -- Repackage the canonical pullback of `g` and `f` as the identity-functor witness.
    letI : HasPullback g f := hg g
    refine ⟨pullback g f, pullback.fst g f, pullback.snd g f, ?_⟩
    simpa using (IsPullback.of_hasPullback g f).flip

end CategoryTheory
