module

public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_33_13

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/- Domain-style sampling for Lemma 4.35.15:
- primary domain: fibred categories in groupoids and pullbacks in the total category;
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.hasPullback_of_isStronglyCartesian`,
  `Functor.IsStronglyCartesian`,
  `Functor.IsPreFibered.pullbackMap`;
- best owner abstraction: `Functor.hasPullback_of_isStronglyCartesian`, which is the canonical
  pullback-existence theorem upstairs. The current file should stay only a source-facing
  specialization that discharges the strong-cartesianness hypothesis using
  `IsFibredInGroupoids.isStronglyCartesian_map`.
- primitive data: the functor `p`, the total-category morphisms `φ` and `ψ`, and the base
  pullback hypothesis on `p.map φ` and `p.map ψ`;
- derived API: the induced `HasPullback φ ψ` instance.

Source/core/bridge triage:
- `source-facing`: `hasPullback_of_isFibredInGroupoids`;
- `core/canonical`: `Functor.hasPullback_of_isStronglyCartesian`;
- `bridge/view`: the instance field `IsFibredInGroupoids.isStronglyCartesian_map`, which upgrades
  the source hypothesis to the canonical owner hypothesis. -/
-- Proof sketch: in a category fibred in groupoids, every morphism is strongly cartesian over its image in the base. The canonical owner theorem `hasPullback_of_isStronglyCartesian` then applies directly to `φ`.
/-- Lemma 4.35.15: if `p : E ⥤ C` is fibred in groupoids and the pullback of `p.map φ` and `p.map ψ` exists in the base, then `φ` and `ψ` admit a pullback in the total category. -/
theorem hasPullback_of_isFibredInGroupoids
    (p : E ⥤ C) [IsFibredInGroupoids p]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] :
    HasPullback φ ψ :=
  hasPullback_of_isStronglyCartesian p φ ψ

end

end CategoryTheory.Functor
