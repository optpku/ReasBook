module

public import stacks_project.Chap04.Definition_4_27_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling:
- source-facing owner: `IsSaturatedMultiplicativeSystem`
- core/canonical owners already present upstream: `W.HasLeftCalculusOfFractions`,
  `W.HasRightCalculusOfFractions`, `W.IsMultiplicative`, and `W.RespectsIso`
- best owner abstraction: a saturated multiplicative system is a source-facing extension of the
  left and right calculus-of-fractions owners by the Stacks saturation axiom

Primitive data are exactly the left and right calculus-of-fractions owner instances together with
the Stacks saturation axiom. Derived API such as closure under isomorphisms should be exposed
through the canonical mathlib morphism-property owners rather than by parallel local wrappers.
-/

/- Source/core/bridge triage:
- `source-facing`: `IsSaturatedMultiplicativeSystem`
- `core/canonical`: `HasLeftCalculusOfFractions`, `HasRightCalculusOfFractions`,
  `IsMultiplicative`, `RespectsIso`
- `bridge/view`: the derived inclusion `isomorphisms C ≤ W`
-/

/-- Definition 4.27.20: a multiplicative system `W` is saturated if whenever `f`, `g`, and `h`
are composable and both composites `f ≫ g` and `g ≫ h` lie in `W`, then `g` itself lies in
`W`. -/
class IsSaturatedMultiplicativeSystem (W : MorphismProperty C) : Prop where
  toHasLeftCalculusOfFractions : W.HasLeftCalculusOfFractions
  toHasRightCalculusOfFractions : W.HasRightCalculusOfFractions
  saturation {X0 X1 X2 X3 : C} (f : X0 ⟶ X1) (g : X1 ⟶ X2) (h : X2 ⟶ X3)
      (_ : W (f ≫ g)) (_ : W (g ≫ h)) : W g

attribute [instance] IsSaturatedMultiplicativeSystem.toHasLeftCalculusOfFractions
attribute [instance] IsSaturatedMultiplicativeSystem.toHasRightCalculusOfFractions

namespace IsSaturatedMultiplicativeSystem

lemma isomorphisms_le (W : MorphismProperty C) [IsSaturatedMultiplicativeSystem W] :
    isomorphisms C ≤ W := by
  intro X Y f hf
  let e : X ≅ Y := asIso f
  have h₁ : W (e.inv ≫ e.hom) := by simpa using W.id_mem Y
  have h₂ : W (e.hom ≫ e.inv) := by simpa using W.id_mem X
  simpa using saturation e.inv e.hom e.inv h₁ h₂

instance respectsIso (W : MorphismProperty C) [IsSaturatedMultiplicativeSystem W] :
    W.RespectsIso :=
  respectsIso_of_isStableUnderComposition <| isomorphisms_le W

end IsSaturatedMultiplicativeSystem

/-- The class of isomorphisms is a saturated multiplicative system. -/
instance : IsSaturatedMultiplicativeSystem (isomorphisms C) where
  toHasLeftCalculusOfFractions := inferInstance
  toHasRightCalculusOfFractions := inferInstance
  saturation := by
    intro X0 X1 X2 X3 f g h hfg hgh
    rw [isomorphisms.iff] at hfg hgh ⊢
    letI : IsSplitEpi g :=
      IsSplitEpi.mk'
        { section_ := inv (f ≫ g) ≫ f
          id := by simp [Category.assoc] }
    letI : Mono g := mono_of_mono g h
    exact isIso_of_mono_of_isSplitEpi g

end MorphismProperty
end CategoryTheory
