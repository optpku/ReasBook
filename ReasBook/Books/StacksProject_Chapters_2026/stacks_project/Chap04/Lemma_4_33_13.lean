module

public import stacks_project.Chap04.Lemma_4_33_4
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open IsPreFibered

section

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/- Domain-style sampling for Lemma 4.33.13:
- primary domain: fibred categories, strongly cartesian morphisms, and pullbacks in the total
  category;
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsPreFibered.pullbackObj`,
  `Functor.IsPreFibered.pullbackMap`,
  `Functor.IsPreFibered.pullbackObj_proj`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `strongly_cartesian_pullback_isPullback`;
- best owner abstraction: `Functor.IsFibered`, with the canonical chosen pullback lift supplied by
  `Functor.IsPreFibered.pullbackObj` / `Functor.IsPreFibered.pullbackMap`, and pullback existence
  upstairs derived from the owner-level `IsPullback` theorem in Lemma 4.33.4;
- primitive data: the fibred functor `p`, the strongly cartesian morphism `φ`, and the base
  pullback of `p.map φ` and `p.map ψ`;
- derived API: the canonical chosen pullback lift of the second base projection, the resulting
  source-facing pullback square upstairs, and the weaker `HasPullback φ ψ` corollary.

Source/core/bridge triage:
- `source-facing`: a chosen pullback square above the base pullback, whose second projection is
  strongly cartesian;
- `core/canonical`: `Functor.IsFibered` and `strongly_cartesian_pullback_isPullback`;
- `bridge/view`: `Functor.IsPreFibered.pullbackMap` as the canonical chosen lift, and the theorem
  `hasPullback_of_isStronglyCartesian`, which repackages the canonical pullback square as a
  `HasPullback` instance. -/
-- Proof sketch: use mathlib's canonical pullback lift
-- `IsPreFibered.pullbackObj rfl (pullback.snd (p.map φ) (p.map ψ))` and
-- `IsPreFibered.pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))`. In a fibered category this
-- map is cartesian, hence strongly cartesian by
-- `IsFibered.isStronglyCartesian_of_isCartesian`; the owner-level theorem
-- `strongly_cartesian_pullback_isPullback` then identifies the resulting chosen square upstairs as
-- a pullback square.
/-- Lemma 4.33.13: if `p : E ⥤ C` is fibered, `φ : x ⟶ y` is strongly cartesian, and the pullback
of `p.map φ` and `p.map ψ` exists in the base, then the canonical pullback lift of
`pullback.snd (p.map φ) (p.map ψ)` forms a pullback square of `φ` and `ψ` in the total category.
Its apex lies over the base pullback by `pullbackObj_proj`, and its right leg is strongly
cartesian by the canonical `IsFibered` pullback-lift instance. -/
theorem chosen_pullback_isPullback_of_isStronglyCartesian
    (p : E ⥤ C) [p.IsFibered]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ
        (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
        (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)) ≫ ψ))
      (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)))
      φ ψ := by
  -- The canonical lift of the second base projection is cartesian, hence strongly cartesian.
  letI :
      p.IsStronglyCartesian (pullback.snd (p.map φ) (p.map ψ))
        (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))) :=
    IsFibered.isStronglyCartesian_of_isCartesian p
      (pullback.snd (p.map φ) (p.map ψ))
      (pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ)))
  -- Lemma 4.33.4 identifies this canonical strongly cartesian lift with the desired pullback
  -- square upstairs.
  simpa using
    (strongly_cartesian_pullback_isPullback (p := p) (φ := φ) (ψ := ψ)
      (a := pullbackMap rfl (pullback.snd (p.map φ) (p.map ψ))))

/- Companion bridge: forgetting the chosen strongly cartesian right leg recovers the ordinary
existence of a pullback of `φ` and `ψ` in the total category. -/
-- Proof sketch: apply `HasPullback.of_isPullback` to the canonical pullback square from
-- `chosen_pullback_isPullback_of_isStronglyCartesian`.
theorem hasPullback_of_isStronglyCartesian
    (p : E ⥤ C) [p.IsFibered]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ] :
    HasPullback φ ψ := by
  -- Forget the chosen pullback square and retain only the existence of the pullback upstairs.
  exact
    (chosen_pullback_isPullback_of_isStronglyCartesian (p := p) (φ := φ)
      (ψ := ψ)).hasPullback

end

end CategoryTheory.Functor
