module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Remark_7_14_8
public import stacks_project.Chap07.Proposition_7_14_7
public import stacks_project.Chap07.Lemma_7_33_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Types

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.33.2:
- primary domain: points of sites, cofiltered categories of elements, and left exact stalk/fiber
  functors on set-valued sheaves;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `Functor.isCofiltered_elements`,
  `preservesTerminal_of_terminal_and_image_terminal`,
  `terminal_image_and_pullbacks_iff_preserves_finite_limits`,
  `comp_preservesFiniteLimits`;
- source/core/bridge triage:
  `source-facing`: the explicit Stacks hypotheses that `u` sends the terminal object to a singleton
    and each pullback square to a pullback of sets bijectively;
  `core/canonical`: `PreservesFiniteLimits u`, `IsCofiltered u.Elements`, and the chapter owner
    instance `PreservesFiniteLimits (sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber)`;
  `bridge/view`: the private theorem below upgrading the pullback-comparison hypothesis to the
    canonical owner `PreservesLimitsOfShape WalkingCospan u`; the terminal singleton similarly
    upgrades to terminal preservation via Proposition `7.14.7`, and Remark `7.14.8` then supplies
    the canonical finite-limit-preservation owner on `u`.

Primitive data here are only the functor `u` and the explicit terminal/pullback conditions from the
Stacks statement. Preservation of terminal objects and pullbacks, cofilteredness of `u.Elements`,
and finite-limit preservation of the associated stalk functor are derived API, so the file should
reuse the canonical owners for those conclusions rather than duplicating the final finite-limit
bridge locally.
-/
/- Definition 7.32.2: a point of the site `(C, J)` is the canonical mathlib notion
`CategoryTheory.GrothendieckTopology.Point`; the present item proves the left-exactness clause for
the concrete functors arising in Stacks, Lemma 7.33.2. -/
recall CategoryTheory.GrothendieckTopology.Point

-- Proof sketch: each pullback comparison for `u` is an isomorphism in `Type`, so `u` preserves
-- pullbacks. The terminal-object clause is handled separately by the chapter bridge theorem
-- `preservesTerminal_of_terminal_and_image_terminal`.
/-- Internal bridge from the pullback-comparison hypothesis of Stacks, Lemma 7.33.2 to the
canonical owner `PreservesLimitsOfShape WalkingCospan`. -/
private theorem preservesPullbacks_of_pullback_bijective
    [HasPullbacks C] (u : C ⥤ Type w)
    (h_pullback : ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Bijective (pullbackComparison u f g)) :
    PreservesLimitsOfShape WalkingCospan u :=
  { preservesLimit := by
      intro K
      let f : K.obj WalkingCospan.left ⟶ K.obj WalkingCospan.one := K.map WalkingCospan.Hom.inl
      let g : K.obj WalkingCospan.right ⟶ K.obj WalkingCospan.one := K.map WalkingCospan.Hom.inr
      have : PreservesLimit (cospan f g) u := by
        letI : IsIso (pullbackComparison u f g) := (isIso_iff_bijective _).2 (h_pullback f g)
        exact PreservesPullback.of_iso_comparison u
      exact preservesLimit_of_iso_diagram u (diagramIsoCospan K).symm }

-- Proof sketch: combine the preceding finite-limit-preservation bridge with the canonical mathlib
-- theorem `Functor.isCofiltered_elements`.
/-- Lemma 7.33.2: if a set-valued functor on a site with a final object and fibred products sends
the final object to a singleton and sends pullback squares to pullbacks of sets bijectively, then
its category of neighbourhoods `u.Elements` is cofiltered. -/
theorem isCofiltered_elements_of_terminal_singleton_and_pullback_bijective
    [HasTerminal C] [HasPullbacks C] (u : C ⥤ Type w)
    (h_terminal : Unique (u.obj (⊤_ C)))
    (h_pullback : ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Bijective (pullbackComparison u f g)) :
    IsCofiltered u.Elements := by
  let h_terminal' : IsTerminal (u.obj (⊤_ C)) := (Types.isTerminalEquivUnique _).symm h_terminal
  let _ : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_terminal_and_image_terminal u (⊤_ C) terminalIsTerminal h_terminal'
  let _ : PreservesLimitsOfShape WalkingCospan u :=
    preservesPullbacks_of_pullback_bijective u h_pullback
  let _ : PreservesLimitsOfShape (Discrete PEmpty) u :=
    preservesLimitsOfShape_pempty_of_preservesTerminal u
  let _ : PreservesFiniteLimits u :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  exact Functor.isCofiltered_elements u

-- Proof sketch: first apply the previous theorem to get that `u.Elements` is cofiltered; then
-- synthesize the canonical finite-limit-preservation instance for the sheaf-restricted
-- `u.presheafFiber`.
/- Lemma 7.33.2, consequently clause: in the small-universe case needed by
`Functor.presheafFiber`, the associated stalk functor on set-valued sheaves commutes with finite
limits. This is the left-exactness clause in Definition 7.32.2 for the point built from `u` once
the covering-surjectivity axiom is supplied separately. -/
theorem stalkFunctor_preservesFiniteLimits_of_terminal_singleton_and_pullback_bijective
    (J : GrothendieckTopology C) [HasTerminal C] [HasPullbacks C]
    (u : C ⥤ Type (max u v)) [InitiallySmall.{max u v} u.Elements]
    (h_terminal : Unique (u.obj (⊤_ C)))
    (h_pullback : ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Bijective (pullbackComparison u f g)) :
    PreservesFiniteLimits (sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber) := by
  letI := isCofiltered_elements_of_terminal_singleton_and_pullback_bijective u h_terminal h_pullback
  infer_instance

end CategoryTheory
