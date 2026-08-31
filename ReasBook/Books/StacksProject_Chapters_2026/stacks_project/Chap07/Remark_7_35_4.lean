module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.Topology.Sheaves.Points
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_25_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace
open scoped MorphismOfTopoiIn

universe v u

namespace CategoryTheory

attribute [local instance] uliftCategory

open GrothendieckTopology

section

/-
Domain-style sampling for Remark 7.35.4:
- primary domain: localization morphisms of topoi and the stalks of their direct images on a
  Grothendieck site;
- sampled owner API:
  `GrothendieckTopology.over`,
  `Over.forget`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.over`,
  `localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber`;
- best owner abstraction: the canonical localization morphism from Definition `7.25.1`,
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J : MorphismOfTopoiIn J (J.over U))`,
  together with its direct image `j_{U,*}`, the point-fiber owner `p.sheafFiber`, and the
  localized-point owner `p.over x`;
- primitive data: a site `(C, J)`, an object `U`, a point `p`, and a sheaf `𝒢` on
  `(C/U, J.over U)`;
- derived API: the sigma-type stalk formula from Lemma `7.35.3` for `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: the remark that the stalk decomposition of Lemma `7.35.3` does not remain
  valid after replacing `j_{U!}` by `j_{U,*}`;
- `core/canonical`: the localization owner
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*`,
  `p.sheafFiber`, and `p.over x`;
- `bridge/view`: the cocontinuous site-level realization of `j_{U,*}` by
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward` and the proposition-level
  `IsIsomorphic` formulation of the would-be sigma decomposition.

This remark introduces no new owner construction. The file should therefore keep only the
owner-level negative statement for the localization direct image `j_{U,*}`, leaving any
right-Kan-extension presentation of that owner to a separate bridge theorem if needed.
-/

-- Proof sketch: use a counterexample site where the direct image functor for localization does
-- not admit the stalk decomposition from Lemma `7.35.3`. This shows that replacing `j_{U!}` by
-- `j_{U,*}` in that statement does not produce a theorem valid for all sites, points, and
-- localized sheaves.
/-- Helper for Remark 7.35.4: for the canonical opens-site point attached to `x`, the fiber over an
open `U` is empty when `x ∉ U`. -/
theorem opens_pointGrothendieckTopology_fiber_isEmpty_of_not_mem
    {X : Type u} [TopologicalSpace X] (x : X) (U : Opens X) (hx : x ∉ U) :
    IsEmpty ((Opens.pointGrothendieckTopology x).fiber.obj U) := by
  -- The fiber is the singleton witness that `x ∈ U`, so a point outside `U` gives a contradiction.
  refine ⟨fun t ↦ hx t.down.down⟩

/-- Helper for Remark 7.35.4: the localization direct image sends the terminal sheaf on the slice
site to a terminal sheaf on the ambient site because it is a right adjoint. -/
noncomputable def localization_pushforward_terminal_isTerminal
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
    (U : C) :
    IsTerminal
      (((Over.forget U).sheafPushforwardCocontinuous (Type (max u v)) (J.over U) J).obj (⊤_ _)) :=
  let jstar := (Over.forget U).sheafPushforwardCocontinuous (Type (max u v)) (J.over U) J
  -- The direct image is a right adjoint, hence it preserves terminal objects.
  let _ : PreservesLimits jstar :=
    ((Over.forget U).sheafAdjunctionCocontinuous (Type (max u v)) (J.over U) J).rightAdjoint_preservesLimits
  show IsTerminal (jstar.obj (⊤_ (Sheaf (J.over U) (Type (max u v))))) from
    IsTerminal.isTerminalObj jstar (⊤_ (Sheaf (J.over U) (Type (max u v)))) terminalIsTerminal

/-- Helper for Remark 7.35.4: the stalk of the terminal localization pushforward is terminal, so
its underlying type has a unique element. -/
noncomputable def stalk_terminal_of_terminal_pushforward
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
    (U : C) (p : Point.{max u v} J) :
    IsTerminal
      (p.sheafFiber.obj
        (((Over.forget U).sheafPushforwardCocontinuous (Type (max u v)) (J.over U) J).obj
          (⊤_ _))) :=
  -- The stalk functor preserves finite limits, so it carries terminal sheaves to terminal types.
  IsTerminal.isTerminalObj p.sheafFiber _
    (localization_pushforward_terminal_isTerminal (J := J) U)

/-- Helper for Remark 7.35.4: in the lifted discrete two-point category, the bottom-topology point
supported at `false` has empty fiber over `true`. -/
theorem pointBot_fiber_isEmpty_of_distinct_discrete_objects :
    let C₀ : Type u := ULiftHom.{v} (ULift.{u} (Discrete Bool))
    let x₀ : C₀ := ULiftHom.objUp (ULift.up (Discrete.mk false))
    let U₀ : C₀ := ULiftHom.objUp (ULift.up (Discrete.mk true))
    IsEmpty ((GrothendieckTopology.pointBot.{max u v} x₀).fiber.obj U₀) := by
  dsimp
  refine ⟨fun t ↦ ?_⟩
  -- Convert the fiber element to the corresponding morphism `false ⟶ true`.
  let f :
      (ULiftHom.objUp (ULift.up (Discrete.mk false : Discrete Bool)) :
        ULiftHom.{v} (ULift.{u} (Discrete Bool))) ⟶
      (ULiftHom.objUp (ULift.up (Discrete.mk true : Discrete Bool)) :
        ULiftHom.{v} (ULift.{u} (Discrete Bool))) :=
    shrinkYonedaObjObjEquiv t
  -- Projecting this morphism back to `Discrete Bool` forces `false = true`.
  have hbool : false = true := by
    let f' : (ULift.up.{u, 0} (Discrete.mk false : Discrete Bool)) ⟶
        (ULift.up.{u, 0} (Discrete.mk true : Discrete Bool)) := f.down
    let f'' : (Discrete.mk false : Discrete Bool) ⟶ Discrete.mk true :=
      (ULift.downFunctor : ULift.{u} (Discrete Bool) ⥤ Discrete Bool).map f'
    simpa using (Discrete.eq_of_hom f'')
  cases hbool

/-- Helper for Remark 7.35.4: if the point fiber over `U` is empty, then the sigma-indexed
decomposition over localized points is empty as well. -/
theorem sigma_pointOver_isEmpty_of_fiber_isEmpty
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
    (p : Point.{max u v} J) (U : C) (𝒢 : Sheaf (J.over U) (Type (max u v)))
    [IsEmpty (p.fiber.obj U)] :
    IsEmpty (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := by
  refine ⟨fun z ↦ ?_⟩
  -- Any sigma-term already contains an impossible index `x : p.fiber.obj U`.
  exact (inferInstance : IsEmpty (p.fiber.obj U)).false z.1

/-- Helper for Remark 7.35.4: a unique type cannot be isomorphic to an empty type. -/
theorem not_isomorphic_of_unique_left_isEmpty_right
    (A B : Type (max u v)) [Unique A] [IsEmpty B] :
    ¬ IsIsomorphic A B := by
  rintro ⟨e⟩
  -- The image of the unique element would give an element of the empty target.
  exact (inferInstance : IsEmpty B).false (e.hom default)

/-- Remark 7.35.4: the direct analogue of
`localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber` obtained by replacing
`j_{U!}` with the localization direct image functor `j_{U,*}` is not valid in general. -/
theorem localizationPushforward_sheafFiber_isomorphic_sigma_pointOver_sheafFiber_not_forall :
    ¬ ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
        (U : C) (p : Point.{max u v} J) (𝒢 : Sheaf (J.over U) (Type (max u v))),
        IsIsomorphic
          (p.sheafFiber.obj
            (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj 𝒢)))
          (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := by
  intro h
  -- Route correction: replace the unfinished opens-site transport with the bottom-topology
  -- discrete two-point counterexample from the source-faithful plan.
  let C₀ : Type u := ULiftHom.{v} (ULift.{u} (Discrete Bool))
  let J₀ : GrothendieckTopology C₀ := ⊥
  let x₀ : C₀ := ULiftHom.objUp (ULift.up (Discrete.mk false : Discrete Bool))
  let U₀ : C₀ := ULiftHom.objUp (ULift.up (Discrete.mk true : Discrete Bool))
  let p₀ : Point.{max u v} J₀ := GrothendieckTopology.pointBot.{max u v} x₀
  let 𝒢₀ : Sheaf (J₀.over U₀) (Type (max u v)) := ⊤_ _
  -- The chosen point has no branch over the distinct localization object.
  have hEmptyFiber : IsEmpty (p₀.fiber.obj U₀) := by
    simpa [C₀, x₀, U₀, p₀] using
      pointBot_fiber_isEmpty_of_distinct_discrete_objects
  let _ : IsEmpty (p₀.fiber.obj U₀) := hEmptyFiber
  -- The left-hand stalk is terminal because `j_{U,*}` preserves terminal sheaves.
  let _ :
      Unique
        (p₀.sheafFiber.obj
          (((((Over.forget U₀).morphismOfTopoiInOfCocontinuous (J₀.over U₀) J₀) _*).obj 𝒢₀))) := by
    simpa only [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using
      (Types.isTerminalEquivUnique _
        (stalk_terminal_of_terminal_pushforward (J := J₀) U₀ p₀))
  -- The right-hand sigma type is empty because its index type is already empty.
  let _ :
      IsEmpty (Σ x : p₀.fiber.obj U₀, (p₀.over x).sheafFiber.obj 𝒢₀) :=
    sigma_pointOver_isEmpty_of_fiber_isEmpty p₀ U₀ 𝒢₀
  -- Specializing the universal claim to this counterexample produces a map into an empty type.
  obtain ⟨e⟩ := h U₀ p₀ 𝒢₀
  exact (inferInstance : IsEmpty (Σ x : p₀.fiber.obj U₀, (p₀.over x).sheafFiber.obj 𝒢₀)).false
    (e.hom default)

end

end CategoryTheory
