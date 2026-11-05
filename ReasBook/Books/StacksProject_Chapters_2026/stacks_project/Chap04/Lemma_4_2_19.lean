module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap04.Lemma_4_2_18
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/- Domain-style sampling for Lemma 4.2.19:
- `Functor.IsEquivalence` is the owner predicate for a functor being an equivalence of categories.
- `Functor.IsEquivalence.faithful`, `Functor.IsEquivalence.full`, and
  `Functor.IsEquivalence.essSurj` are the derived canonical accessors.
- `Functor.Full` and `Functor.Faithful` are the owner predicates for the two halves of the
  full-faithful criterion.
- `Functor.FullyFaithful` is a derived bundled witness, obtained canonically from
  `Functor.Full` and `Functor.Faithful` when needed.
- `Functor.asEquivalence` upgrades the owner predicate to the canonical equivalence object.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by the `Prop`-valued
  class `Functor.IsEquivalence`.
- derived API: fullness, faithfulness, essential surjectivity, and the bridge from
  `Functor.IsEquivalence` to the textbook full-faithful-essentially-surjective criterion
  below. -/

/- Source/core/bridge triage for Lemma 4.2.19:
- `source-facing`: the textbook criterion "full, faithful, essentially surjective".
- `core/canonical`: `Functor.IsEquivalence`.
- `bridge/view`: `isEquivalence_iff_full_faithful_essSurj`, phrased through hom-set
  bijectivity to package "full and faithful" into one atomic clause. -/

/- Canonical owner data for this item live in mathlib's predicates `Functor.IsEquivalence`,
`Functor.Full`, `Functor.Faithful`, and `Functor.EssSurj`. -/

-- Proof sketch: `Functor.IsEquivalence` has fields giving `F.Full`, `F.Faithful`, and
-- `F.EssSurj`; the first two are equivalent to bijectivity of `F.map` on every hom-set, so this
-- is the textbook full-faithful-essentially-surjective criterion in one atomic conjunction.
/-- Lemma 4.2.19: a functor is an equivalence of categories exactly when it is fully faithful,
together with essential surjectivity; here full and faithful are packaged as bijectivity on every
hom-set so the statement remains atomic while matching the textbook criterion. -/
theorem isEquivalence_iff_full_faithful_essSurj (F : A ⥤ B) :
    F.IsEquivalence ↔
      (∀ X Y : A, Function.Bijective
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) ∧
        F.EssSurj := by
  constructor
  · intro hEq
    -- Extract the canonical full-faithful-essentially-surjective data from the equivalence witness.
    letI : F.IsEquivalence := hEq
    refine ⟨?_, inferInstance⟩
    -- Convert full and faithful into bijectivity on each hom-set.
    intro X Y
    exact (Functor.FullyFaithful.ofFullyFaithful F).map_bijective X Y
  · rintro ⟨hbij, hEss⟩
    -- Route correction: follow the source proof by choosing objectwise preimages from essential
    -- surjectivity and then invoking Lemma 4.2.18.
    letI : F.Faithful := ⟨fun {X Y} ↦ (hbij X Y).injective⟩
    letI : F.Full := ⟨fun {X Y} ↦ (hbij X Y).surjective⟩
    letI : F.EssSurj := hEss
    -- The chosen preimages are the canonical `objPreimage`s supplied by essential surjectivity.
    exact
      F.fully_faithful_isEquivalence_of_objwise_iso
        (fun X ↦ F.objPreimage X)
        (fun X ↦ (F.objObjPreimageIso X).symm)

end Functor
end CategoryTheory
