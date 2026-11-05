module

public import stacks_project.Chap04.Lemma_4_36_4.Strictification.Reindex

@[expose] public section

universe v₁ v₂ v₃ vS u₁ u₂ u₃ w

namespace CategoryTheory

open Bicategory
open BasedFunctor
open Functor
open Fiber
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Helper for Lemma 4.36.4: the forward comparison sends an object of `S` to its strict identity
presentation over the same base object. -/
noncomputable def pullback_strictification_identity_presentation
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor') where
  base := p.obj x
  fiber :=
    { target := p.obj x
      arrow := 𝟙 (p.obj x)
      fiberObj := Fiber.mk (rfl : p.obj x = p.obj x) }

/-- Helper for Lemma 4.36.4: the strict identity presentation lies over the same base object as
the original object of `S`. -/
theorem pullback_strictification_identity_presentation_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation p hc x).base = p.obj x := by
  -- The identity presentation was defined to keep the original base object unchanged.
  rfl

/-- Helper for Lemma 4.36.4: the identity presentation in the strict fiber over `U` forgets to
the ordinary identity pullback object `((𝟙 U)^* x)`. This is the object-level bridge needed when
the forward comparison functor sends `x` to its strict identity presentation. -/
theorem pullback_strictification_identity_presentation_forget
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U : C} (x : Fiber p U) :
    pullbackStrictificationFiberForget p hc U
        { target := U, arrow := 𝟙 U, fiberObj := x } =
      (hc.pullbackFunctor (𝟙 U)).obj x := by
  -- This is just the defining evaluation of the forgetful functor on the identity presentation.
  rfl

/-- Helper for Lemma 4.36.4: evaluating a strict object forgets only the chosen pullback
presentation and lands back in the original total category. -/
noncomputable def pullback_strictification_evaluation_obj
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    (X : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')) :
    S :=
  (pullbackStrictificationFiberForget p hc X.base X.fiber).1

/-- Helper for Lemma 4.36.4: evaluating the strict identity presentation of `x` literally gives
the chosen identity pullback object over `p.obj x`. This isolates the object-level comparison used
by the future identity-presentation functor. -/
theorem pullback_strictification_identity_presentation_evaluation_obj_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    pullback_strictification_evaluation_obj p hc
        (pullback_strictification_identity_presentation p hc x) =
      ((hc.pullbackFunctor (𝟙 (p.obj x))).obj (Fiber.mk (rfl : p.obj x = p.obj x))).1 := by
  -- Both sides are definitional expansions of the same chosen identity pullback object.
  rfl

/-- Helper for Lemma 4.36.4: evaluating a strict object stays over the same base object. This is
the object-level base compatibility needed for the eventual evaluation quasi-inverse. -/
theorem pullback_strictification_evaluation_obj_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    (X : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')) :
    p.obj (pullback_strictification_evaluation_obj p hc X) = X.base := by
  -- The forgotten strict fiber object is, by construction, an object of the fiber over `X.base`.
  exact (pullbackStrictificationFiberForget p hc X.base X.fiber).2

/-- Helper for Lemma 4.36.4: evaluating a reindexed strict presentation just evaluates the same
chosen pullback presentation along the composite base arrow. This is the object-level bridge
needed for the future evaluation functor on morphisms. -/
theorem pullback_strictification_evaluation_reindex_obj_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U) (X : PullbackStrictificationFiber p hc U) :
    pullback_strictification_evaluation_obj p hc
        { base := V
          fiber := pullbackStrictificationReindexObj p hc g X } =
      ((hc.pullbackFunctor (g ≫ X.arrow)).obj X.fiberObj).1 := by
  -- Reindexing changes only the stored pullback arrow, so evaluation is definitionally the
  -- chosen pullback object along the composite `g ≫ X.arrow`.
  cases X with
  | mk target arrow fiberObj =>
      rfl

/-- Helper for Lemma 4.36.4: the evaluated reindexed strict presentation still lies over the
domain of the reindexing morphism. This packages the base computation that the evaluation
comparison will need after rewriting the object part along composite pullbacks. -/
theorem pullback_strictification_evaluation_reindex_obj_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U) (X : PullbackStrictificationFiber p hc U) :
    p.obj
        (pullback_strictification_evaluation_obj p hc
          { base := V
            fiber := pullbackStrictificationReindexObj p hc g X }) =
      V := by
  -- This is the general evaluation-base computation applied to the reindexed strict object.
  simpa using
    (pullback_strictification_evaluation_obj_base p hc
      { base := V
        fiber := pullbackStrictificationReindexObj p hc g X })

/-- Helper for Lemma 4.36.4: a strict morphism evaluates to its vertical component followed by
the chosen pullback arrow over the base part. This is the concrete map used by the future
evaluation functor from the strictification back to `p`. -/
noncomputable def pullback_strictification_evaluation_map
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    pullback_strictification_evaluation_obj p hc X ⟶
      pullback_strictification_evaluation_obj p hc Y :=
  -- Compare the strict reindexed target `(φ.base ≫ Y.fiber.arrow)^* Y.fiberObj` with the iterated
  -- pullback `φ.base^*(Y.fiber.arrow^* Y.fiberObj)` before applying the chosen pullback arrow.
  φ.fiber.1 ≫
    ((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1 ≫
      hc.map φ.base (pullbackStrictificationFiberForget p hc Y.base Y.fiber)

/-- Helper for Lemma 4.36.4: the evaluated strict morphism lies over the same base arrow as the
original co-Grothendieck morphism. This is the base-compatibility input needed when packaging the
future evaluation functor as a based functor over `C`. -/
theorem pullback_strictification_evaluation_vertical_component_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    p.IsHomLift (𝟙 X.base)
      (φ.fiber.1 ≫ ((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1) := by
  -- The vertical part of a strict morphism is already a morphism in the fiber over `X.base`, and
  -- the chosen comparison to the composite pullback is likewise vertical.
  let α :=
    φ.fiber.1 ≫ ((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1
  have hφfiber :
      p.IsHomLift (𝟙 X.base) (Fiber.fiberInclusion.map φ.fiber) := φ.fiber.2
  have hcomp :
      p.IsHomLift (𝟙 X.base)
        (((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1) := by
    simpa using ((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).2
  simpa [α] using
    (@IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
      (𝟙 X.base) (Fiber.fiberInclusion.map φ.fiber) hφfiber X.base
      (((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1) hcomp)

/-- Helper for Lemma 4.36.4: the evaluated strict morphism lies over the same base arrow as the
original co-Grothendieck morphism. This is the base-compatibility input needed when packaging the
future evaluation functor as a based functor over `C`. -/
theorem pullback_strictification_evaluation_map_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    p.IsHomLift φ.base (pullback_strictification_evaluation_map p hc φ) := by
  -- First package the strict fiber morphism together with the composite-pullback comparison as a
  -- vertical arrow, then append the chosen pullback map lifting `φ.base`.
  let α :=
    φ.fiber.1 ≫ ((hc.pullbackCompIso Y.fiber.arrow φ.base).hom.app Y.fiber.fiberObj).1
  have hα : p.IsHomLift (𝟙 X.base) α :=
    pullback_strictification_evaluation_vertical_component_isHomLift p hc φ
  have hmap :
      p.IsHomLift φ.base
        (hc.map φ.base (pullbackStrictificationFiberForget p hc Y.base Y.fiber)) := by
    exact
      (hc.isStronglyCartesian φ.base
        (pullbackStrictificationFiberForget p hc Y.base Y.fiber)).toIsHomLift
  simpa [pullback_strictification_evaluation_map, α] using
    (@IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _
      X.base α hα _ _ φ.base
      (hc.map φ.base (pullbackStrictificationFiberForget p hc Y.base Y.fiber))
      hmap)

/-- Helper for Lemma 4.36.4: the evaluated strict morphism lies over the base morphism `φ.base`
after rewriting the source and target objects by the canonical evaluation-base equalities. This
is the exact over-base equation needed when packaging the future evaluation functor as a based
functor. -/
theorem pullback_strictification_evaluation_map_over_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    p.map (pullback_strictification_evaluation_map p hc φ) =
      eqToHom (pullback_strictification_evaluation_obj_base p hc X) ≫
        φ.base ≫
          eqToHom (pullback_strictification_evaluation_obj_base p hc Y).symm := by
  -- Convert the lift witness into the explicit equation in the base category.
  let hX := pullback_strictification_evaluation_obj_base p hc X
  let hY := pullback_strictification_evaluation_obj_base p hc Y
  letI : p.IsHomLift φ.base (pullback_strictification_evaluation_map p hc φ) :=
    pullback_strictification_evaluation_map_isHomLift p hc φ
  simpa [hX, hY] using
    (IsHomLift.fac' p φ.base (pullback_strictification_evaluation_map p hc φ))

/-- Helper for Lemma 4.36.4: evaluation sends a strict object and strict morphism over exactly
the stored base object and base morphism, up to the canonical object-base equalities. This packages
the concrete based-functor data without reopening the transport-heavy evaluation definition. -/
theorem pullback_strictification_evaluation_over_base_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    p.obj (pullback_strictification_evaluation_obj p hc X) = X.base ∧
      p.map (pullback_strictification_evaluation_map p hc φ) =
        eqToHom (pullback_strictification_evaluation_obj_base p hc X) ≫
          φ.base ≫
            eqToHom (pullback_strictification_evaluation_obj_base p hc Y).symm := by
  constructor
  · exact pullback_strictification_evaluation_obj_base p hc X
  · exact pullback_strictification_evaluation_map_over_base p hc φ

/-- Helper for Lemma 4.36.4: evaluation is over the strictification projection surface,
with only the canonical object-base equalities on source and target. This is the based-functor
surface of the source-text evaluation map `(x, f) ↦ f^*x`. -/
theorem pullback_strictification_evaluation_projection_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (φ : X ⟶ Y) :
    p.obj (pullback_strictification_evaluation_obj p hc X) =
        (pullback_strictification_projection_surface p hc).obj X ∧
      p.map (pullback_strictification_evaluation_map p hc φ) =
        eqToHom (pullback_strictification_evaluation_obj_base p hc X) ≫
          (pullback_strictification_projection_surface p hc).map φ ≫
            eqToHom (pullback_strictification_evaluation_obj_base p hc Y).symm := by
  constructor
  · exact pullback_strictification_evaluation_obj_base p hc X
  · exact pullback_strictification_evaluation_map_over_base p hc φ

/-- Helper for Lemma 4.36.4: evaluating the strict identity presentation of an object gives
something canonically isomorphic to the original object via the chosen identity-pullback
comparison. This is the objectwise unit candidate for the eventual comparison equivalence. -/
theorem pullback_strictification_identity_presentation_evaluation_nonempty_iso
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    Nonempty
      (pullback_strictification_evaluation_obj p hc
          (pullback_strictification_identity_presentation p hc x) ≅
        x) := by
  -- The evaluation object is exactly the chosen pullback of `x` along the identity, and
  -- `hc.pullbackIdIso` identifies that pullback object with `x` inside the fiber.
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  refine ⟨{ hom := e.hom.1, inv := e.inv.1, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · exact congrArg Subtype.val e.hom_inv_id
  · exact congrArg Subtype.val e.inv_hom_id

/-- Helper for Lemma 4.36.4: choose the canonical isomorphism from the evaluation of the strict
identity presentation back to the original object. This packages the previously proved
nonemptiness witness into a reusable objectwise unit isomorphism. -/
noncomputable def pullback_strictification_identity_presentation_evaluation_iso
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    pullback_strictification_evaluation_obj p hc
        (pullback_strictification_identity_presentation p hc x) ≅ x :=
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  { hom := e.hom.1
    inv := e.inv.1
    hom_inv_id := congrArg Subtype.val e.hom_inv_id
    inv_hom_id := congrArg Subtype.val e.inv_hom_id }

/-- Helper for Lemma 4.36.4: the chosen unit comparison for the identity presentation retracts
back to the identity on the evaluated strict object. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_hom_inv_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
      𝟙
        (pullback_strictification_evaluation_obj p hc
          (pullback_strictification_identity_presentation p hc x)) := by
  -- This is the `hom_inv_id` identity of the chosen comparison isomorphism.
  exact (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom_inv_id

/-- Helper for Lemma 4.36.4: the chosen unit isomorphism from the evaluation of the identity
presentation back to `x` is vertical over the identity on the base object `p.obj x`. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_hom_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.IsHomLift (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom := by
  -- This is exactly the lift proof carried by the identity-pullback comparison component.
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  simpa [pullback_strictification_identity_presentation_evaluation_iso, xFiber, e] using e.hom.2

/-- Helper for Lemma 4.36.4: the inverse of the chosen unit isomorphism for the identity
presentation is also vertical over the identity on `p.obj x`. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_inv_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.IsHomLift (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv := by
  -- The inverse comparison component is likewise vertical in the standard fiber.
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  simpa [pullback_strictification_identity_presentation_evaluation_iso, xFiber, e] using e.inv.2

/-- Helper for Lemma 4.36.4: evaluating the strict identity presentation of `x` lands over the
same base object as `x` itself. This is the base equality later needed to rewrite vertical unit
components into literal `eqToHom` maps. -/
theorem pullback_strictification_identity_presentation_evaluation_obj_base_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.obj
        (pullback_strictification_evaluation_obj p hc
          (pullback_strictification_identity_presentation p hc x)) =
      p.obj x := by
  -- Combine the general evaluation-base computation with the fact that the identity presentation
  -- stays over `p.obj x`.
  simpa [pullback_strictification_identity_presentation_base] using
    (pullback_strictification_evaluation_obj_base p hc
      (pullback_strictification_identity_presentation p hc x))

/-- Helper for Lemma 4.36.4: the hom component of the chosen unit isomorphism for the identity
presentation lies over the identity on `p.obj x`. This is the exact base equation needed when the
future unit natural isomorphism is promoted to a based natural transformation. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_hom_over_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
      eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x) := by
  -- Convert the previously established lift witness into the corresponding base equality.
  let hbase := pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x
  letI : p.IsHomLift (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom :=
    pullback_strictification_identity_presentation_evaluation_iso_hom_isHomLift p hc x
  simpa [hbase] using
    (IsHomLift.fac' p (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom)

/-- Helper for Lemma 4.36.4: the inverse component of the chosen unit isomorphism for the
identity presentation also lies over the identity on `p.obj x`. This is the matching base
equation for the inverse direction of the future based unit isomorphism. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_inv_over_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
      eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x).symm := by
  -- The inverse component is vertical for the same reason, so its base map is the identity.
  let hbase := pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x
  letI : p.IsHomLift (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv :=
    pullback_strictification_identity_presentation_evaluation_iso_inv_isHomLift p hc x
  simpa [hbase] using
    (IsHomLift.fac' p (𝟙 (p.obj x))
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv)

/-- Helper for Lemma 4.36.4: the chosen unit isomorphism for the identity presentation is vertical
in both directions over the identity on `p.obj x`. This packages the two base equalities that the
future based unit isomorphism will need. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_over_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x) ∧
      p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
        eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x).symm := by
  -- Package the already-verified hom-side and inv-side base equations into one reusable lemma for
  -- the later equivalence-over-base construction.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_over_base p hc x
  · exact pullback_strictification_identity_presentation_evaluation_iso_inv_over_base p hc x

/-- Helper for Lemma 4.36.4: the hom component of the objectwise unit comparison for the
identity presentation is simultaneously a lift over the identity and the expected over-base
rewrite map. This is the exact objectwise package later needed to build the unit-side based
natural isomorphism. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_hom_lift_and_over_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.IsHomLift (𝟙 (p.obj x))
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ∧
      p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x) := by
  -- Combine the lift-theoretic and over-base forms of the hom component into one reusable unit
  -- package for the remaining comparison-functor construction.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_isHomLift p hc x
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_over_base p hc x

/-- Helper for Lemma 4.36.4: the identity-presentation comparison is vertical in both directions
over the identity on `p.obj x`. This is the lift-theoretic form of the over-base package needed
when the future unit isomorphism is assembled as a based natural isomorphism. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.IsHomLift (𝟙 (p.obj x))
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ∧
      p.IsHomLift (𝟙 (p.obj x))
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv := by
  -- Package the two verticality statements so the later based unit only has to consume one lemma.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_isHomLift p hc x
  · exact pullback_strictification_identity_presentation_evaluation_iso_inv_isHomLift p hc x

/-- Helper for Lemma 4.36.4: the hom component of the chosen unit isomorphism is literally the
hom component of the identity-pullback comparison in the fiber over `p.obj x`. This exposes the
exact comparison map needed when later packaging the comparison over the base. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_hom_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
      (((hc.pullbackIdIso (p.obj x)).symm.app
          (Fiber.mk (rfl : p.obj x = p.obj x))).hom.1) := by
  -- The chosen unit isomorphism was defined by reusing exactly this identity-pullback component.
  rfl

/-- Helper for Lemma 4.36.4: the inverse component of the chosen unit isomorphism is literally
the inverse component of the identity-pullback comparison in the fiber over `p.obj x)`. This
gives the matching explicit inverse map for later comparison calculations. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_inv_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
      (((hc.pullbackIdIso (p.obj x)).symm.app
          (Fiber.mk (rfl : p.obj x = p.obj x))).inv.1) := by
  -- The inverse was chosen from the same identity-pullback comparison isomorphism.
  rfl

/-- Helper for Lemma 4.36.4: the chosen comparison isomorphism between the evaluation of the
identity presentation and the original object satisfies both triangle identities. This packages
the two-sided inverse data that the eventual unit natural isomorphism will use. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_triangle
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
      𝟙
        (pullback_strictification_evaluation_obj p hc
          (pullback_strictification_identity_presentation p hc x)) ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        𝟙 x := by
  -- Package the two inverse identities of the chosen comparison isomorphism for later reuse.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_inv_id p hc x
  · exact (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv_hom_id

/-- Helper for Lemma 4.36.4: the unit comparison from the evaluation of the identity
presentation back to `x` packages both verticality statements and both triangle identities in one
place. This is the exact local datum needed when the future identity-presentation functor is
promoted to an equivalence over the base. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.IsHomLift (𝟙 (p.obj x))
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ∧
      p.IsHomLift (𝟙 (p.obj x))
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
        𝟙
          (pullback_strictification_evaluation_obj p hc
            (pullback_strictification_identity_presentation p hc x)) ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        𝟙 x := by
  -- Bundle the two already proved verticality facts with the two inverse identities so the
  -- later unit construction can consume a single package.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_isHomLift p hc x
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_inv_isHomLift p hc x
  exact pullback_strictification_identity_presentation_evaluation_iso_triangle p hc x

/-- Helper for Lemma 4.36.4: the chosen comparison isomorphism from the evaluation of the
identity presentation back to `x` simultaneously records both over-base equations and both
triangle identities. This is the exact objectwise package needed for the future unit-side based
natural isomorphism. -/
theorem pullback_strictification_identity_presentation_evaluation_iso_over_base_triangle
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x) ∧
      p.map (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
        eqToHom (pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x).symm ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv =
        𝟙
          (pullback_strictification_evaluation_obj p hc
            (pullback_strictification_identity_presentation p hc x)) ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
        𝟙 x := by
  -- Combine the already proved over-base identities with the two inverse identities into one
  -- objectwise package for the later unit-side equivalence data.
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_hom_over_base p hc x
  constructor
  · exact pullback_strictification_identity_presentation_evaluation_iso_inv_over_base p hc x
  exact pullback_strictification_identity_presentation_evaluation_iso_triangle p hc x

/-- Helper for Lemma 4.36.4: a morphism in the original total category induces the fiber component
of the forward comparison between strict identity presentations. -/
noncomputable def pullback_strictification_identity_presentation_fiber_map
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    ((hc.pullbackFunctor (𝟙 (p.obj x))).obj (Fiber.mk (rfl : p.obj x = p.obj x))) ⟶
      ((hc.pullbackFunctor (p.map f)).obj (Fiber.mk (rfl : p.obj y = p.obj y))) := by
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  let hs : p.IsStronglyCartesian (p.map f) (hc.map (p.map f) yFiber) :=
    hc.isStronglyCartesian (p.map f) yFiber
  have hf : p.IsHomLift (p.map f) (e.hom.1 ≫ f) := by
    have he : p.IsHomLift (𝟙 (p.obj x)) e.hom.1 := e.hom.2
    have hff : p.IsHomLift (p.map f) f := inferInstance
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _ (p.obj x) e.hom.1 he _ _
      (p.map f) f hff
  let m :=
    @IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (p.map f) (hc.map (p.map f) yFiber) hs
      _ _ (𝟙 (p.obj x)) (p.map f) (Category.id_comp (p.map f)).symm (e.hom.1 ≫ f) hf
  have hm : p.IsHomLift (𝟙 (p.obj x)) m :=
    @IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ (p.map f)
      (hc.map (p.map f) yFiber) hs _ _ (𝟙 (p.obj x)) (p.map f)
      (Category.id_comp (p.map f)).symm (e.hom.1 ≫ f) hf
  exact (show ((hc.pullbackFunctor (𝟙 (p.obj x))).obj xFiber) ⟶
      ((hc.pullbackFunctor (p.map f)).obj yFiber) from
    Functor.Fiber.homMk p (p.obj x) m)

/-- Helper for Lemma 4.36.4: the concrete fiber component for the identity-presentation
comparison factors through the chosen pullback arrow as the original morphism preceded by the
identity-pullback comparison. -/
theorem pullback_strictification_identity_presentation_fiber_map_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_fiber_map p hc f) ≫
        hc.map (p.map f) yFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ f := by
  dsimp only
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  let e := ((hc.pullbackIdIso (p.obj x)).symm.app xFiber)
  let hs : p.IsStronglyCartesian (p.map f) (hc.map (p.map f) yFiber) :=
    hc.isStronglyCartesian (p.map f) yFiber
  have hf : p.IsHomLift (p.map f) (e.hom.1 ≫ f) := by
    have he : p.IsHomLift (𝟙 (p.obj x)) e.hom.1 := e.hom.2
    have hff : p.IsHomLift (p.map f) f := inferInstance
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _ (p.obj x) e.hom.1 he _ _
      (p.map f) f hff
  change (@IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (p.map f)
      (hc.map (p.map f) yFiber) hs _ _ (𝟙 (p.obj x)) (p.map f)
      (Category.id_comp (p.map f)).symm (e.hom.1 ≫ f) hf) ≫
      hc.map (p.map f) yFiber = e.hom.1 ≫ f
  exact @IsStronglyCartesian.fac _ _ _ _ p _ _ _ _ (p.map f)
    (hc.map (p.map f) yFiber) hs _ _ (𝟙 (p.obj x)) (p.map f)
    (Category.id_comp (p.map f)).symm (e.hom.1 ≫ f) hf

/-- Helper for Lemma 4.36.4: the identity-presentation fiber component is vertical over the
identity on the source base. -/
theorem pullback_strictification_identity_presentation_fiber_map_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    p.IsHomLift (𝟙 (p.obj x))
      (Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_fiber_map p hc f)) := by
  exact (pullback_strictification_identity_presentation_fiber_map p hc f).2

/-- Helper for Lemma 4.36.4: a morphism in the original category gives a morphism between
the strict identity presentations. -/
noncomputable def pullback_strictification_identity_presentation_map
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    pullback_strictification_identity_presentation p hc x ⟶
      pullback_strictification_identity_presentation p hc y where
  base := p.map f
  fiber := by
    change ((hc.pullbackFunctor (𝟙 (p.obj x))).obj
        (Fiber.mk (rfl : p.obj x = p.obj x))) ⟶
      ((hc.pullbackFunctor (p.map f ≫ 𝟙 (p.obj y))).obj
        (Fiber.mk (rfl : p.obj y = p.obj y)))
    exact pullback_strictification_identity_presentation_fiber_map p hc f ≫
      eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj
        (Fiber.mk (rfl : p.obj y = p.obj y))) (Category.comp_id (p.map f)).symm)

/-- Helper for Lemma 4.36.4: the forward identity-presentation morphism lies over the
original base morphism. -/
theorem pullback_strictification_identity_presentation_map_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    (pullback_strictification_identity_presentation_map p hc f).base = p.map f := by
  rfl

/-- Helper for Lemma 4.36.4: the fiber component of the forward identity-presentation morphism is
the concrete strongly-cartesian comparison followed by the single target identity transport. -/
theorem pullback_strictification_identity_presentation_map_fiber
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    (pullback_strictification_identity_presentation_map p hc f).fiber =
      pullback_strictification_identity_presentation_fiber_map p hc f ≫
        eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj
          (Fiber.mk (rfl : p.obj y = p.obj y))) (Category.comp_id (p.map f)).symm) := by
  rfl

/-- Helper for Lemma 4.36.4: after the single target-identity transport built into the
identity-presentation morphism, the fiber component factors through the chosen pullback arrow as the
original morphism preceded by the identity-pullback comparison. -/
theorem pullback_strictification_identity_presentation_map_fiber_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc f).fiber ≫
        hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ f := by
  dsimp only
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  rw [pullback_strictification_identity_presentation_map_fiber]
  have htransport0 :=
    pullback_strictification_eqToHom_component_postcompose_eq
      (p := p) (hc := hc) (f := p.map f) (g := p.map f ≫ 𝟙 (p.obj y))
      (e := (Category.comp_id (p.map f)).symm) (x := yFiber)
  have htransport :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
            (Category.comp_id (p.map f)).symm)) ≫
        hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber = hc.map (p.map f) yFiber := by
    simpa using htransport0
  have hfac := pullback_strictification_identity_presentation_fiber_map_fac
    (p := p) (hc := hc) f
  calc
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_fiber_map p hc f ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
            (Category.comp_id (p.map f)).symm)) ≫
        hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber
        = Fiber.fiberInclusion.map
            (pullback_strictification_identity_presentation_fiber_map p hc f) ≫
          hc.map (p.map f) yFiber := by
          rw [Functor.map_comp, Category.assoc, htransport]
    _ = (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ f := by
      simpa [xFiber, yFiber] using hfac

/-- Helper for Lemma 4.36.4: in the identity case, the fully packaged forward
identity-presentation morphism factors through the chosen identity pullback comparison. This is the
small concrete datum needed before proving the whole `map_id` law. -/
theorem pullback_strictification_identity_presentation_map_id_fiber_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (𝟙 x)).fiber ≫
        hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ 𝟙 x := by
  dsimp only
  simpa using
    (pullback_strictification_identity_presentation_map_fiber_fac
      (p := p) (hc := hc) (f := 𝟙 x))

/-- Helper for Lemma 4.36.4: the forward identity-presentation comparison preserves identity
morphisms on the base field. Keep this separate from the fiber equality so later `Hom.ext` calls do
not try to simplify the transport-heavy fiber component. -/
theorem pullback_strictification_identity_presentation_map_id_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_identity_presentation_map p hc (𝟙 x)).base =
      (𝟙 (pullback_strictification_identity_presentation p hc x) :
        pullback_strictification_identity_presentation p hc x ⟶
          pullback_strictification_identity_presentation p hc x).base := by
  change p.map (𝟙 x) = 𝟙 (p.obj x)
  simpa using p.map_id x

/-- Helper for Lemma 4.36.4: the forward identity-presentation comparison preserves composition
on the base field. This isolates the easy part of the eventual functoriality proof from the fiber
transport calculation. -/
theorem pullback_strictification_identity_presentation_map_comp_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    (pullback_strictification_identity_presentation_map p hc (f ≫ g)).base =
      (pullback_strictification_identity_presentation_map p hc f ≫
        pullback_strictification_identity_presentation_map p hc g).base := by
  change p.map (f ≫ g) = p.map f ≫ p.map g
  simpa using p.map_comp f g

/-- Helper for Lemma 4.36.4: the target-side base arrow of the composite identity-presentation
comparison is the expected composite pullback arrow followed by the target identity. This is the
base equality that controls the final `eqToHom` transport in the `map_comp` fiber calculation. -/
theorem pullback_strictification_identity_presentation_map_comp_target_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    (pullback_strictification_identity_presentation_map p hc f ≫
        pullback_strictification_identity_presentation_map p hc g).base ≫ 𝟙 (p.obj z) =
      p.map (f ≫ g) ≫ 𝟙 (p.obj z) := by
  -- Postcompose the already-proved base equality with the target identity to obtain exactly the
  -- transport used by the final strict fiber comparison.
  change (p.map f ≫ p.map g) ≫ 𝟙 (p.obj z) = p.map (f ≫ g) ≫ 𝟙 (p.obj z)
  simpa using
    congrArg (fun k ↦ k ≫ 𝟙 (p.obj z))
      (pullback_strictification_identity_presentation_map_comp_base p hc f g).symm

/-- Helper for Lemma 4.36.4: the final target-side `eqToHom` transport in the composite
identity-presentation comparison disappears after postcomposition with the chosen pullback arrow.
This isolates the last base-change rewrite needed before the remaining strict composite fiber
factorization. -/
theorem pullback_strictification_identity_presentation_map_comp_target_transport_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
          (pullback_strictification_identity_presentation_map_comp_target_base
            p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      hc.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).base ≫
          𝟙 (p.obj z)) zFiber := by
  dsimp only
  let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
  -- This is the standard postcomposition collapse for `eqToHom` transports between equal
  -- pullback arrows, specialized to the target-side base equality of the composite.
  have htransport :
      Fiber.fiberInclusion.map
          ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))).app zFiber) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      hc.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).base ≫
          𝟙 (p.obj z)) zFiber := by
    exact
      pullback_strictification_eqToHom_component_postcompose_eq
        (p := p) (hc := hc)
        (f := (pullback_strictification_identity_presentation_map p hc f ≫
          pullback_strictification_identity_presentation_map p hc g).base ≫ 𝟙 (p.obj z))
        (g := p.map (f ≫ g) ≫ 𝟙 (p.obj z))
        (e := pullback_strictification_identity_presentation_map_comp_target_base p hc f g)
        (x := zFiber)
  simpa using htransport

/-- Helper for Lemma 4.36.4: on the strictification projection surface, the forward comparison
preserves identity morphisms over the base. This is the over-`C` part of the eventual functor law. -/
theorem pullback_strictification_identity_presentation_projection_map_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    (pullback_strictification_projection_surface p hc).map
        (pullback_strictification_identity_presentation_map p hc (𝟙 x)) =
      (pullback_strictification_projection_surface p hc).map
        (𝟙 (pullback_strictification_identity_presentation p hc x)) := by
  change p.map (𝟙 x) = 𝟙 (p.obj x)
  simpa using p.map_id x

/-- Helper for Lemma 4.36.4: on the strictification projection surface, the forward comparison
preserves composition over the base. This records the easy over-`C` part separately from the fiber
transport calculation. -/
theorem pullback_strictification_identity_presentation_projection_map_comp
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    (pullback_strictification_projection_surface p hc).map
        (pullback_strictification_identity_presentation_map p hc (f ≫ g)) =
      (pullback_strictification_projection_surface p hc).map
        (pullback_strictification_identity_presentation_map p hc f ≫
          pullback_strictification_identity_presentation_map p hc g) := by
  change p.map (f ≫ g) = p.map f ≫ p.map g
  simpa using p.map_comp f g

/-- Helper for Lemma 4.36.4: the inverse object-transport appearing in the strict identity
reindexing of an identity presentation factors through the chosen identity pullback arrow. This is
the concrete fiber-side piece of the right hand side of the eventual `map_id` proof. -/
theorem pullback_strictification_identity_presentation_id_reindex_transport_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let X : PullbackStrictificationFiber p hc (p.obj x) :=
      { target := p.obj x, arrow := 𝟙 (p.obj x), fiberObj := xFiber }
    Fiber.fiberInclusion.map
        (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
          (pullback_strictification_reindex_obj_id p hc (p.obj x) X)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) := by
  dsimp only
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  change Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber)
          (Category.id_comp (𝟙 (p.obj x)))).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1)
  have htransport :=
    pullback_strictification_eqToHom_component_postcompose_eq
      (p := p) (hc := hc) (f := 𝟙 (p.obj x))
      (g := 𝟙 (p.obj x) ≫ 𝟙 (p.obj x))
      (e := (Category.id_comp (𝟙 (p.obj x))).symm) (x := xFiber)
  have htarget :
      ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 =
        hc.map (𝟙 (p.obj x)) xFiber := by
    simpa [PullbackChoice.pullbackIdIso] using
      hc.pullbackIdComponentIso_inv_eq (p.obj x) xFiber
  simpa using htransport.trans htarget.symm

/-- Helper for Lemma 4.36.4: the actual co-Grothendieck identity morphism on an identity
presentation has the same concrete fiber factor as the strict identity-reindexing transport. -/
theorem pullback_strictification_identity_presentation_id_fiber_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let X := pullback_strictification_identity_presentation p hc x
    Fiber.fiberInclusion.map ((𝟙 X : X ⟶ X).fiber) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) := by
  dsimp only
  rw [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber]
  rw [Functor.toPseudofunctor'_mapId]
  dsimp [eqToIso]
  rw [CategoryTheory.Cat.eqToHom_app]
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  change Fiber.fiberInclusion.map
        (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
          (pullback_strictification_reindex_obj_id p hc (p.obj x)
            ({ target := p.obj x, arrow := 𝟙 (p.obj x), fiberObj := xFiber } :
              PullbackStrictificationFiber p hc (p.obj x)))).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1)
  exact pullback_strictification_identity_presentation_id_reindex_transport_fac
    (p := p) (hc := hc) (x := x)

/-- Helper for Lemma 4.36.4: the identity-presentation map preserves identity morphisms. -/
theorem pullback_strictification_identity_presentation_map_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    pullback_strictification_identity_presentation_map p hc (𝟙 x) =
      𝟙 (pullback_strictification_identity_presentation p hc x) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    (pullback_strictification_identity_presentation_map_id_base p hc x) ?_
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  apply pullback_strictification_hom_ext p hc (p.map (𝟙 x) ≫ 𝟙 (p.obj x))
  change Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (𝟙 x)).fiber ≫
      hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) (Fiber.mk (rfl : p.obj x = p.obj x)) = _
  rw [pullback_strictification_identity_presentation_map_id_fiber_fac]
  rw [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber]
  rw [Functor.toPseudofunctor'_mapId]
  dsimp [eqToIso]
  rw [CategoryTheory.Cat.eqToHom_app]
  let Xfiber : PullbackStrictificationFiber p hc (p.obj x) :=
    { target := p.obj x, arrow := 𝟙 (p.obj x), fiberObj := xFiber }
  have ebase : 𝟙 (p.obj x) ≫ 𝟙 (p.obj x) = p.map (𝟙 x) ≫ 𝟙 (p.obj x) := by
    simpa using congrArg (fun k ↦ k ≫ 𝟙 (p.obj x)) (p.map_id x)
  change ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 ≫ 𝟙 x =
    Fiber.fiberInclusion.map
      (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
          (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm ≫
        eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase)) ≫
      hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber
  rw [Functor.map_comp]
  have hB0 :
      Fiber.fiberInclusion.map
          (((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) ebase)).app xFiber)) ≫
        hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber =
      hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber := by
    exact
      (pullback_strictification_eqToHom_component_postcompose_eq
        (p := p) (hc := hc)
        (f := 𝟙 (p.obj x) ≫ 𝟙 (p.obj x))
        (g := p.map (𝟙 x) ≫ 𝟙 (p.obj x))
        (e := ebase) (x := xFiber))
  have hB :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase)) ≫
        hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber =
      hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber := by
    simpa using hB0
  have hA :=
    pullback_strictification_identity_presentation_id_reindex_transport_fac
      (p := p) (hc := hc) (x := x)
  have hAfac :
      ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 =
        Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber := by
    simpa [Xfiber] using hA.symm
  have hAB :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
      (Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase))) ≫
        hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber := by
    calc
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber =
          Fiber.fiberInclusion.map
            (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
              (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
          (Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase)) ≫
            hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber) := by
            exact congrArg
              (fun k ↦ Fiber.fiberInclusion.map
                (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
                  (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫ k)
              hB.symm
      _ = (Fiber.fiberInclusion.map
            (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
              (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
          Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase))) ≫
          hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber := by
            rw [Category.assoc]
  have hAid :
      ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 ≫ 𝟙 x =
        (Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber) ≫ 𝟙 x :=
    congrArg (fun k ↦ k ≫ 𝟙 x) hAfac
  have hABid :
      (Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        hc.map (𝟙 (p.obj x) ≫ 𝟙 (p.obj x)) xFiber) ≫ 𝟙 x =
      (Fiber.fiberInclusion.map
          (eqToHom (congrArg (pullbackStrictificationFiberForget p hc (p.obj x))
            (pullback_strictification_reindex_obj_id p hc (p.obj x) Xfiber)).symm) ≫
        Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj xFiber) ebase))) ≫
        hc.map (p.map (𝟙 x) ≫ 𝟙 (p.obj x)) xFiber := by
    refine (congrArg (fun k ↦ k ≫ 𝟙 x) hAB).trans ?_
    exact eq_of_heq (by simp)
  exact hAid.trans hABid

/-- Helper for Lemma 4.36.4: the identity-presentation map of a composite has the expected
concrete fiber factor. This is the left-hand factorization used in the eventual composition law. -/
theorem pullback_strictification_identity_presentation_map_comp_lhs_fiber_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (f ≫ g)).fiber ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ (f ≫ g) := by
  dsimp only
  simpa using
    (pullback_strictification_identity_presentation_map_fiber_fac
      (p := p) (hc := hc) (f := f ≫ g))

/-- Helper for Lemma 4.36.4: the verified prefix of the composite identity-presentation proof is
already in place. Namely, the base fields compose correctly, and the direct composite map has the
expected postcomposed fiber factor. This isolates the remaining blocker to the raw composite-fiber
normalization on the right-hand side. -/
theorem pullback_strictification_identity_presentation_map_comp_verified_prefix
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    (pullback_strictification_identity_presentation_map p hc (f ≫ g)).base =
      (pullback_strictification_identity_presentation_map p hc f ≫
        pullback_strictification_identity_presentation_map p hc g).base ∧
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (f ≫ g)).fiber ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ (f ≫ g) := by
  -- Package the already-established base computation and left-hand postcomposition factorization
  -- so later retries can focus only on the composite-fiber normalization frontier.
  constructor
  · exact pullback_strictification_identity_presentation_map_comp_base p hc f g
  · exact pullback_strictification_identity_presentation_map_comp_lhs_fiber_fac p hc f g

end CategoryTheory
