module

public import stacks_project.Chap04.Lemma_4_27_9
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe w v v' u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.17:
- primary domain: localization of morphism properties and finite-limit preservation;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `Functor.q_isLocalization`,
  `Functor.IsLocalization.preservesFiniteColimits`,
  `preservesFiniteLimits_of_op`;
- best owner abstraction: `PreservesFiniteLimits L` for a localization functor `L`, obtained by
  transporting the colimit-preservation theorem for `L.op` across opposites.

Primitive-vs-derived split:
- primitive data: the morphism property `W`;
- derived API: the source-facing instance `PreservesFiniteLimits W.Q`, together with the companion
  bridge theorem `Functor.IsLocalization.preservesFiniteLimits` for any chosen localization
  functor `L`. -/

/- Source/core/bridge triage for Lemma 4.27.17:
- source-facing: the Stacks lemma for the canonical localization functor `W.Q`.
- core/canonical: the owner property is `PreservesFiniteLimits`.
- bridge/view: `Functor.IsLocalization.preservesFiniteLimits` transports the canonical
  finite-colimit preservation theorem for `W.op` across opposites, and the instance that follows
  is the derived owner property for the canonical localization functor `W.Q`. -/

namespace Functor.IsLocalization

-- Proof sketch: apply Lemma 4.27.9 to the opposite morphism property `W.op`, obtaining that
-- `L.op` preserves finite colimits, and then transport back across opposites via
-- `preservesFiniteLimits_of_op`.
/-- Lemma 4.27.17: any localization functor of a right multiplicative system preserves finite
limits. -/
theorem preservesFiniteLimits {D : Type w} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization W] :
    PreservesFiniteLimits L := by
  -- Apply Lemma 4.27.9 to the opposite localization model and transport it to `L.op`.
  let e := Localization.equivalenceFromModel L.op W.op
  letI : PreservesFiniteColimits W.op.Q := localization_Q_preservesFiniteColimits (W := W.op)
  letI : PreservesFiniteColimits e.functor := by infer_instance
  letI : PreservesFiniteColimits (W.op.Q ⋙ e.functor) :=
    Limits.comp_preservesFiniteColimits W.op.Q e.functor
  letI : PreservesFiniteColimits L.op :=
    preservesFiniteColimits_of_natIso (Localization.qCompEquivalenceFromModelFunctorIso L.op W.op)
  -- Opposite finite-colimit preservation is equivalent to finite-limit preservation on `L`.
  exact preservesFiniteLimits_of_op L

end Functor.IsLocalization

/-- The canonical localization functor of a right multiplicative system preserves finite limits. -/
instance : PreservesFiniteLimits W.Q :=
  Functor.IsLocalization.preservesFiniteLimits W W.Q

end CategoryTheory
