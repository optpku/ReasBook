module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_35_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsCartesian IsStronglyCartesian

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.35.2:
- primary domain: categories fibred in groupoids over a base functor.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.IsFibered`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `Functor.Fiber`.
- best owner abstraction: `IsFibredInGroupoids` as the source-facing owner built directly on the
  canonical fibred-category API. This file should stay at the bridge/view layer between that owner
  and the fiberwise groupoid criterion, rather than introducing a second wrapper around the same
  `Functor.IsFibered` and `Functor.Fiber` data.
- primitive data: `p.IsFibered` together with the fiberwise groupoid condition
  `∀ U, IsGroupoid (p.Fiber U)`.
- derived API: the owner field `IsFibredInGroupoids.isStronglyCartesian_map`.

Source/core/bridge triage:
- `source-facing`: `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`.
- `bridge/view`: `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`, upgrading
  `p.IsFibered` plus groupoid fibers to `IsFibredInGroupoids p`. -/

/-- Helper for Lemma 4.35.2: if every standard fiber of a fibered functor is a groupoid, then any
morphism in the total category is strongly cartesian. -/
private theorem isStronglyCartesian_of_fiber_groupoid
    {p : S ⥤ C} [p.IsFibered]
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) {x y : S} (φ : x ⟶ y) :
    p.IsStronglyCartesian (p.map φ) φ := by
  let U := p.obj x
  -- Choose a cartesian lift of the base map of `φ`; fiberedness upgrades it to a strongly
  -- cartesian lift over the same arrow in the base.
  obtain ⟨z, ψ, hψ⟩ := IsPreFibered.exists_isCartesian p rfl (p.map φ)
  letI : p.IsCartesian (p.map φ) ψ := hψ
  letI : p.IsStronglyCartesian (p.map φ) ψ :=
    IsFibered.isStronglyCartesian_of_isCartesian p (p.map φ) ψ
  letI : IsGroupoid (p.Fiber U) := hfiber U
  -- Compare `φ` with the chosen lift. This comparison is vertical, hence invertible in the fiber.
  let χ : x ⟶ z := IsCartesian.map p (p.map φ) ψ φ
  have hχ : χ ≫ ψ = φ := IsCartesian.fac p (p.map φ) ψ φ
  haveI : IsIso (homMk p U χ) := by infer_instance
  haveI : IsIso χ := by
    simpa using
      (inferInstance : IsIso (((fiberInclusion : p.Fiber U ⥤ S).map (homMk p U χ))))
  -- A vertical isomorphism is strongly cartesian over the identity, so composing with `ψ`
  -- transfers strong cartesianness to `φ`.
  letI : p.IsStronglyCartesian (𝟙 U) χ := of_isIso p (𝟙 U) χ
  simpa [hχ] using
    (inferInstance : p.IsStronglyCartesian (𝟙 U ≫ p.map φ) (χ ≫ ψ))

/-- A fibered functor whose standard fibers are groupoids is fibred in groupoids. -/
theorem isFibredInGroupoids_of_isFibered_and_fiber_groupoid
    (p : S ⥤ C) (hp : p.IsFibered) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsFibredInGroupoids p := by
  letI : p.IsFibered := hp
  exact
    { toIsFibered := hp
      isStronglyCartesian_map φ := isStronglyCartesian_of_fiber_groupoid hfiber φ }

-- Proof sketch: one direction is built into `IsFibredInGroupoids`: fiberedness is inherited from
-- the class, and every fiber is a groupoid by `IsFibredInGroupoids.fiber_isGroupoid`. Conversely,
-- assume `p` is fibered and every fiber is a groupoid; for any `φ : y ⟶ x`, choose a cartesian
-- lift of `p.map φ` with codomain `x`, upgrade it to a strongly cartesian lift via the canonical
-- `IsFibered` owner API, compare `y` with that lift inside the relevant fiber, and use that
-- fiberwise morphisms are isomorphisms to conclude that `φ` itself is strongly cartesian.
/-- Lemma 4.35.2: a functor `p : S ⥤ C` is fibred in groupoids exactly when it is fibred and each
fiber category `p.Fiber U` is a groupoid. -/
theorem isFibredInGroupoids_iff_isFibered_and_fiber_groupoid
    (p : S ⥤ C) :
    IsFibredInGroupoids p ↔ p.IsFibered ∧ ∀ U : C, IsGroupoid (p.Fiber U) := by
  constructor
  · intro hp
    letI : IsFibredInGroupoids p := hp
    exact ⟨hp.toIsFibered, fun U ↦ IsFibredInGroupoids.fiber_isGroupoid U⟩
  · rintro ⟨hp, hfiber⟩
    exact isFibredInGroupoids_of_isFibered_and_fiber_groupoid p hp hfiber

/- Companion recall: once `p` is fibred in groupoids, the owner field
`IsFibredInGroupoids.isStronglyCartesian_map` states that every morphism of the total category is
strongly cartesian over its image in the base. -/
recall IsFibredInGroupoids.isStronglyCartesian_map

end CategoryTheory
