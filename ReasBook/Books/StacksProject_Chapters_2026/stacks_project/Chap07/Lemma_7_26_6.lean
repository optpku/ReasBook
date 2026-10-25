module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Continuous


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u w

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.26.6:
- primary domain: sheaf descent along the slice-site pseudofunctor `U ↦ Sh(C/U)`;
- sampled owner API:
  `GrothendieckTopology.pseudofunctorOver`,
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPullbackId`,
  `Functor.sheafPushforwardContinuousComp'`;
- source-facing layer: `AbsoluteGlueing J`, the textbook datum of sheaves on all slice sites
  `C/U` with pullback comparison isomorphisms and cocycle compatibility;
- core/canonical owner: strong/cartesian sections of the slice-site sheaf pseudofunctor
  `J.pseudofunctorOver (Type w)`;
- bridge/view: the concrete transition maps `transition f`, which unpack that owner-level action
  entrywise.

Primitive data here are exactly the local sheaves `obj U` and the transition isomorphisms
`transition f`. The category structure on these data is derived API. There is an upstream owner
view via strong transformations into `J.pseudofunctorOver (Type w)`, but exposing that directly
would replace the textbook family-of-sheaves surface by terminal-category plumbing. This lemma
therefore keeps the source-facing object while reusing the owner pullback API and keeping the
derived category layer minimal.
-/

/-- An absolute glueing on a site consists of a sheaf on each localization `C/U`, together with
pullback isomorphisms along morphisms in `C` satisfying the usual identity and cocycle
compatibilities. -/
structure AbsoluteGlueing where
  /-- The local sheaf on the slice site `C/U`. -/
  obj (U : C) : Sheaf (J.over U) (Type w)
  /-- Pulling back the local sheaf on `C/U` along `f : V ⟶ U` identifies it with the local sheaf on
  `C/V`. -/
  transition {U V : C} (f : V ⟶ U) :
      (J.overMapPullback (Type w) f).obj (obj U) ≅ obj V
  /-- The transition attached to an identity morphism is the canonical identity pullback
  isomorphism. -/
  transition_id (U : C) :
      transition (𝟙 U) = (J.overMapPullbackId (Type w) U).app (obj U)
  /-- The transitions satisfy the expected cocycle condition for composable morphisms. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
      (J.overMapPullbackComp (Type w) g f).app (obj U) ≪≫ transition (g ≫ f) =
        (J.overMapPullback (Type w) g).mapIso (transition f) ≪≫ transition g

namespace AbsoluteGlueing

/-- A morphism of absolute glueings is a family of local morphisms compatible with the
transition isomorphisms. -/
@[ext] structure Hom (F G : AbsoluteGlueing J) where
  /-- The component on the localization at `U`. -/
  app (U : C) : F.obj U ⟶ G.obj U
  /-- Compatibility of the local components with pullback along morphisms. -/
  naturality {U V : C} (f : V ⟶ U) :
      CommSq ((J.overMapPullback (Type w) f).map (app U))
        (F.transition f).hom (G.transition f).hom (app V)

theorem absoluteGlueing_id_naturality (F : AbsoluteGlueing J) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((J.overMapPullback (Type w) f).map (𝟙 (F.obj U)))
        (F.transition f).hom (F.transition f).hom (𝟙 (F.obj V)) := by
  intro U V f
  exact .mk (by simp)

def absoluteGlueingId (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom J F F where
  app U := 𝟙 (F.obj U)
  naturality := absoluteGlueing_id_naturality J F

theorem absoluteGlueing_comp_naturality
    {F G H : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((J.overMapPullback (Type w) f).map (α.app U ≫ β.app U))
        (F.transition f).hom (H.transition f).hom (α.app V ≫ β.app V) := by
  intro U V f
  exact .mk <| by
    rw [Functor.map_comp, Category.assoc, (β.naturality f).w]
    rw [← Category.assoc, (α.naturality f).w]
    simp [Category.assoc]

def absoluteGlueingComp
    {F G H : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) :
    AbsoluteGlueing.Hom J F H where
  app U := α.app U ≫ β.app U
  naturality := absoluteGlueing_comp_naturality J α β

theorem absoluteGlueing_id_comp
    {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    absoluteGlueingComp J (absoluteGlueingId J F) α = α := by
  ext U
  simp [absoluteGlueingComp, absoluteGlueingId]

theorem absoluteGlueing_comp_id
    {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    absoluteGlueingComp J α (absoluteGlueingId J G) = α := by
  ext U
  simp [absoluteGlueingComp, absoluteGlueingId]

theorem absoluteGlueing_assoc
    {F G H K : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) (γ : AbsoluteGlueing.Hom J H K) :
    absoluteGlueingComp J (absoluteGlueingComp J α β) γ =
      absoluteGlueingComp J α (absoluteGlueingComp J β γ) := by
  ext U
  simp [absoluteGlueingComp, Category.assoc]

end AbsoluteGlueing

/-- The category of absolute glueings on the site `(C, J)`. -/
instance : Category (AbsoluteGlueing J) where
  Hom F G := AbsoluteGlueing.Hom J F G
  id := AbsoluteGlueing.absoluteGlueingId J
  comp α β := AbsoluteGlueing.absoluteGlueingComp J α β
  id_comp := AbsoluteGlueing.absoluteGlueing_id_comp J
  comp_id := AbsoluteGlueing.absoluteGlueing_comp_id J
  assoc := AbsoluteGlueing.absoluteGlueing_assoc J

/-- The functor sending a sheaf on `(C, J)` to its canonical absolute glueing. -/
theorem sheafToAbsoluteGlueing_transition_id
    (F : Sheaf J (Type w)) (U : C) :
    (Functor.sheafPushforwardContinuousComp' (Over.mapForget (𝟙 U))
      (Type w) (J.over U) (J.over U) J).app F =
      (J.overMapPullbackId (Type w) U).app (F.over U) := by
  -- The canonical relocalization comparison over `𝟙 U` is exactly the owner identity
  -- pullback comparison specialized to `F.over U`.
  ext X x
  simp [Over.mapForget, Over.mapForget_eq]

theorem sheafToAbsoluteGlueing_transition_comp
    (F : Sheaf J (Type w)) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullbackComp (Type w) g f).app (F.over U) ≪≫
      (Functor.sheafPushforwardContinuousComp' (Over.mapForget (g ≫ f))
        (Type w) (J.over W) (J.over U) J).app F =
      (J.overMapPullback (Type w) g).mapIso
        ((Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
          (Type w) (J.over V) (J.over U) J).app F) ≪≫
        (Functor.sheafPushforwardContinuousComp' (Over.mapForget g)
          (Type w) (J.over W) (J.over V) J).app F := by
  -- The canonical relocalization comparison for `g ≫ f` is the composite of the
  -- comparisons for `f` and `g`, exactly as encoded by `J.overMapPullbackComp`.
  ext X x
  simp [Over.mapForget, Over.mapForget_eq]

noncomputable def sheafToAbsoluteGlueingFunctor :
    Sheaf J (Type w) ⥤ AbsoluteGlueing J where
  obj F :=
    { obj := fun U ↦ F.over U
      transition := fun {U V} f ↦
        (Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
          (Type w) (J.over V) (J.over U) J).app F
      transition_id := sheafToAbsoluteGlueing_transition_id J F
      transition_comp := sheafToAbsoluteGlueing_transition_comp J F }
  map {F G} η :=
    { app := fun U ↦ (J.overPullback (Type w) U).map η
      naturality := by
        intro U V f
        exact .mk <| by
          simpa using
            (Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
              (Type w) (J.over V) (J.over U) J).hom.naturality η }
  map_id F := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    rfl
  map_comp η θ := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    rfl

/-- Helper for Lemma 7.26.6: evaluating the transition isomorphism for `f : V ⟶ U` at the
terminal object `V/V` identifies the fiber over `Over.mk f` with the reconstructed value at `V`.
-/
theorem absoluteGlueing_over_map_obj_terminal_eq {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  change Over.mk ((𝟙 V) ≫ f) = Over.mk f
  simpa using congrArg Over.mk (Category.id_comp f)

/-- Helper for Lemma 7.26.6: evaluating the transition isomorphism for `f : V ⟶ U` at `V/V`
and rewriting the pullback fiber identifies the section over `Over.mk f` with the reconstructed
value at `V`. -/
noncomputable def absoluteGlueing_transition_app_terminal
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (F.obj U).1.obj (Opposite.op (Over.mk f)) ⟶
      (F.obj V).1.obj (Opposite.op (Over.mk (𝟙 V))) :=
  eqToHom
      (congrArg (fun X ↦ (F.obj U).1.obj (Opposite.op X)) (absoluteGlueing_over_map_obj_terminal_eq f)).symm ≫
    (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))

/-- Helper for Lemma 7.26.6: the inverse component of `Over.mapId` at the terminal slice object is
the explicit transport from `Over.map (𝟙 U)` back to `Over.mk (𝟙 U)`. -/
theorem over_map_id_inv_terminal {U : C} :
    (Over.mapId U).inv.app (Over.mk (𝟙 U)) =
      eqToHom (GrothendieckTopology.absoluteGlueing_over_map_obj_terminal_eq (𝟙 U)).symm := by
  apply Over.OverMorphism.ext
  simp [Over.mapId]

/-- Helper for Lemma 7.26.6: the tautological slice morphism over a composite factors through the
intermediate slice object. -/
theorem over_homMk_comp
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)) =
      (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g) ≫
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f) := by
  apply Over.OverMorphism.ext
  simp [Over.homMk, CostructuredArrow.homMk]

/-- Helper for Lemma 7.26.6: pulling the terminal slice object `W/W` first along `g` and then
along `f` lands at the slice object classified by the composite `g ≫ f`. -/
theorem over_map_obj_terminal_comp_eq
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (Over.map f).obj ((Over.map g).obj (Over.mk (𝟙 W))) = Over.mk (g ≫ f) := by
  -- Unfolding the two successive slice pullbacks reduces the comparison to associativity in `C`.
  change Over.mk (((𝟙 W) ≫ g) ≫ f) = Over.mk (g ≫ f)
  simp [Category.assoc]

/-- Helper for Lemma 7.26.6: after rewriting the identity transition by the owner pullback
comparison, the terminal component is the identity on the fiber over `U/U`. -/
theorem absolute_glueing_transition_id_terminal_comparison
    (F : AbsoluteGlueing J) (U : C) :
    eqToHom (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
      (GrothendieckTopology.absoluteGlueing_over_map_obj_terminal_eq (𝟙 U))).symm ≫
      ((J.overMapPullbackId (Type _) U).app (F.obj U)).hom.hom.app
        (Opposite.op (Over.mk (𝟙 U))) = 𝟙 _ := by
  -- Evaluate the owner identity comparison on the terminal slice object and simplify the
  -- `Over.mapId` transport; on elements this is literally the identity function.
  ext x
  simp [GrothendieckTopology.overMapPullbackId_hom_app_hom_app]
  rw [over_map_id_inv_terminal]
  rw [CategoryTheory.eqToHom_op]
  let hterminal : Opposite.op ((Over.map (𝟙 U)).obj (Over.mk (𝟙 U))) =
      Opposite.op (Over.mk (𝟙 U)) :=
    congrArg Opposite.op (GrothendieckTopology.absoluteGlueing_over_map_obj_terminal_eq (𝟙 U))
  simpa [hterminal, CategoryTheory.eqToHom_map] using
    (FunctorToTypes.eqToHom_map_comp_apply (F := (F.obj U).obj)
      (p := hterminal.symm) (q := hterminal) x)

/-- Helper for Lemma 7.26.6: the slice arrow `U/U ⟶ U/U` induced by `Over.homMk (𝟙 U)` acts as the
identity on sections. -/
theorem absolute_glueing_terminal_slice_id_map
    (F : AbsoluteGlueing J) (U : C) :
    (F.obj U).obj.map (show Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U) from Over.homMk (𝟙 U)).op = 𝟙 _ := by
  -- The terminal arrow `U/U ⟶ U/U` is the identity in the slice.
  have hhom :
      (show Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U) from Over.homMk (𝟙 U)) = 𝟙 _ := by
    ext
    simp [Over.homMk, CostructuredArrow.homMk]
  simpa [hhom]

/-- Helper for Lemma 7.26.6: the transition map along `f : V ⟶ U` is natural with respect to the
terminal arrow `Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)`. -/
theorem absolute_glueing_transition_homMk_naturality
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ((J.overMapPullback (Type w) f).obj (F.obj U)).obj.map
        (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op ≫
      (F.transition f).hom.hom.app (Opposite.op (Over.mk g)) =
        (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
          (F.obj V).obj.map
            (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op := by
  -- This is exactly naturality of the underlying presheaf morphism for `F.transition f`.
  simpa using
    ((F.transition f).hom.hom).naturality
      ((show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op)

/-- Helper for Lemma 7.26.6: evaluating the pullback of `F.obj U` along `f : V ⟶ U` at the
terminal object `V/V` recovers the fiber over `Over.mk f`. -/
theorem absolute_glueing_pullback_terminal_obj
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) =
      (F.obj U).obj.obj (Opposite.op (Over.mk f)) := by
  -- On presheaves this is exactly the object equality `(Over.map f).obj (V/V) = Over.mk f`.
  change (F.obj U).obj.obj (Opposite.op ((Over.map f).obj (Over.mk (𝟙 V)))) =
      (F.obj U).obj.obj (Opposite.op (Over.mk f))
  simpa using
    congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X)) (absoluteGlueing_over_map_obj_terminal_eq f)

/-- Helper for Lemma 7.26.6: evaluating the twice-pulled-back sheaf at the terminal object `W/W`
recovers the fiber of `F.obj U` over the composite arrow `g ≫ f`. -/
theorem absolute_glueing_pullback_comp_terminal_obj
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
        (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 W))) =
      (F.obj U).obj.obj (Opposite.op (Over.mk (g ≫ f))) := by
  -- The successive slice pullbacks land at the composite arrow by `over_map_obj_terminal_comp_eq`.
  change
    (F.obj U).obj.obj (Opposite.op ((Over.map f).obj ((Over.map g).obj (Over.mk (𝟙 W))))) =
      (F.obj U).obj.obj (Opposite.op (Over.mk (g ≫ f)))
  simpa using
    congrArg
      (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
      (over_map_obj_terminal_comp_eq f g)

/-- Helper for Lemma 7.26.6: evaluating the second pullback at the terminal object `W/W`
matches evaluating the first pullback at the slice object classified by `g : W ⟶ V`. -/
theorem absolute_glueing_pullback_homMk_obj
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
      (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 W))) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj (Opposite.op (Over.mk g)) := by
  -- The second pullback evaluates on `W/W` through the object equality
  -- `(Over.map g).obj (Over.mk (𝟙 W)) = Over.mk g`.
  change
    ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
      (Opposite.op ((Over.map g).obj (Over.mk (𝟙 W)))) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj (Opposite.op (Over.mk g))
  simpa using
    congrArg
      (fun X ↦ ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj (Opposite.op X))
      (absoluteGlueing_over_map_obj_terminal_eq g)

/-- Helper for Lemma 7.26.6: for a `Type`-valued functor, applying `eqToHom` is the same as the
corresponding dependent cast. -/
theorem eqToHom_apply_eq_cast
    {D : Type*} [Category D] {G : D ⥤ Type*} {X Y : D} (p : X = Y) (x : G.obj X) :
    eqToHom (congrArg G.obj p) x = cast (congrArg G.obj p) x := by
  cases p
  rfl

/-- Helper for Lemma 7.26.6: on a presheaf over the opposite slice, a dependent cast along an
object equality is the same as mapping along the corresponding `eqToHom`. -/
theorem section_cast_eq_map_eqToHom_op
    {U : C} {P : (Over U)ᵒᵖ ⥤ Type w} {X Y : (Over U)ᵒᵖ} (q : X = Y) (s : P.obj X) :
    Eq.mp (congrArg P.obj q) s = P.map (eqToHom q) s := by
  -- The cast and the `eqToHom` action agree after reducing to the reflexive equality case.
  cases q
  simpa

/-- Helper for Lemma 7.26.6: a `Type`-valued natural transformation commutes with transport
along an equality of objects. -/
theorem natTrans_app_cast_eq
    {D : Type*} [Category D] {P Q : D ⥤ Type w} (α : P ⟶ Q) {X Y : D} (q : X = Y) (s : P.obj X) :
    α.app Y (Eq.mp (congrArg P.obj q) s) = Eq.mp (congrArg Q.obj q) (α.app X s) := by
  cases q
  rfl

/-- Helper for Lemma 7.26.6: after identifying the three slice objects appearing in the
composite restriction with their terminal presentations, the direct composite slice arrow agrees
with the iterated pullback arrow in `(Over U)ᵒᵖ`. -/
theorem absolute_glueing_pullback_terminal_transport_comp_op_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (show Opposite.op (Over.mk (𝟙 U)) ⟶ Opposite.op ((Over.map f).obj (Over.mk g)) from
        (show Opposite.op (Over.mk (𝟙 U)) ⟶ Opposite.op (Over.mk (g ≫ f)) from
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op) ≫
          eqToHom
            ((congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm.trans
              (congrArg Opposite.op
                (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g))))) =
      (show Opposite.op (Over.mk (𝟙 U)) ⟶ Opposite.op ((Over.map f).obj (Over.mk g)) from
        (show Opposite.op (Over.mk (𝟙 U)) ⟶ Opposite.op (Over.mk f) from
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op) ≫
          eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm ≫
            ((Over.map f).map (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g)).op) := by
  -- The only remaining categorical input is the tautological factorization
  -- `Over.homMk (g ≫ f) = Over.homMk g ≫ Over.homMk f`.
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.eqToHom_left, over_homMk_comp, Over.map]

/-- Helper for Lemma 7.26.6: the transported terminal section obtained from the direct composite
restriction agrees with the section obtained by first restricting along `f` and then along `g`. -/
theorem absolute_glueing_pullback_terminal_transport_comp
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : (F.obj U).obj.obj (Opposite.op (Over.mk (𝟙 U)))) :
    Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
        (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) =
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
        (Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x)) := by
  -- The opposite-slice arrow identity is now isolated in
  -- `absolute_glueing_pullback_terminal_transport_comp_op_hom`. The remaining gap is purely
  -- `Type`-valued transport normalization: rewrite the two `Eq.mp` casts as the corresponding
  -- `eqToHom` actions on the opposite slice, then apply `(F.obj U).obj.map` to the helper.
  have hcast₁ :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) := by
    simpa [absolute_glueing_pullback_homMk_obj] using
      section_cast_eq_map_eqToHom_op
        (P := ((J.overMapPullback (Type _) f).obj (F.obj U)).obj)
        (q := congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))
        (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x))
  have hcast₂ :
      Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x) =
        (F.obj U).obj.map
          (eqToHom (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x) := by
    simpa [absolute_glueing_pullback_comp_terminal_obj] using
      section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)
  have hcast₃ :
      Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x) =
        (F.obj U).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x) := by
    simpa [absolute_glueing_pullback_terminal_obj] using
      section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
        ((F.obj U).obj.map
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x)
  have hleft :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
          ((F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) := by
    rw [hcast₁]
    exact congrArg
      (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))))
      hcast₂
  have hright :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          (Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm
            ((F.obj U).obj.map
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x)) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          ((F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
            ((F.obj U).obj.map
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x)) := by
    exact congrArg
      (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op)
      hcast₃
  have hmap_eqToHom_g :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))) =
        (F.obj U).obj.map
          (eqToHom
            (congrArg Opposite.op
              (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))) := by
    ext y
    change
      (F.obj U).obj.map
          (((Over.map f).op).map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))) y =
        (F.obj U).obj.map
          (eqToHom
            (congrArg Opposite.op
              (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))) y
    simpa using
      congrArg
        (fun k ↦ (F.obj U).obj.map k y)
        (CategoryTheory.eqToHom_map ((Over.map f).op)
          (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
  have hleft' :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)) =
        (F.obj U).obj.map
          (eqToHom
            ((congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm.trans
              (congrArg Opposite.op
                (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))))
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x) := by
    rw [hleft]
    rw [hmap_eqToHom_g]
    simpa using
      (FunctorToTypes.eqToHom_map_comp_apply (F := (F.obj U).obj)
        (p := (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
        (q := congrArg Opposite.op
          (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)).symm
  rw [hleft', hright]
  -- Apply the already-proved opposite-slice morphism equality to the presheaf `F.obj U`.
  simpa [FunctorToTypes.map_comp_apply] using
    congrArg (fun k ↦ (F.obj U).obj.map k x)
      (absolute_glueing_pullback_terminal_transport_comp_op_hom f g)

/-- Helper for Lemma 7.26.6: the terminal component of `Over.mapComp g f` is the explicit
transport from the iterated pullback slice object to the direct composite slice object. -/
theorem over_mapComp_terminal_app_eqToHom_op
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op =
      eqToHom
        (congrArg Opposite.op
          (congrArg (fun F : Over W ⥤ Over U => F.obj (Over.mk (𝟙 W)))
            (Over.mapComp_eq g f))).symm := by
  -- The owner comparison is the identity isomorphism on the functor equality `Over.mapComp_eq`.
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.mapComp]

/-- Helper for Lemma 7.26.6: applying the terminal component of `Over.mapComp g f` to a section
transported from `Over.mk (g ≫ f)` gives the direct pullback transport for `g ≫ f`. -/
theorem over_mapComp_terminal_section_transport
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : (F.obj U).obj.obj (Opposite.op (Over.mk (g ≫ f)))) :
    (F.obj U).obj.map (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op)
        (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm x) =
      Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm x := by
  -- Rewrite both transports as `eqToHom` actions and compose the owner comparison with the
  -- terminal-object identifications.
  let q₁ :
      Opposite.op (Over.mk (g ≫ f)) =
        Opposite.op ((Over.map g ⋙ Over.map f).obj (Over.mk (𝟙 W))) :=
    (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm
  let q₂ :
      Opposite.op ((Over.map g ⋙ Over.map f).obj (Over.mk (𝟙 W))) =
        Opposite.op ((Over.map (g ≫ f)).obj (Over.mk (𝟙 W))) :=
    (congrArg Opposite.op
      (congrArg (fun F' : Over W ⥤ Over U => F'.obj (Over.mk (𝟙 W)))
        (Over.mapComp_eq g f))).symm
  have hcast :
      Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm x =
        (F.obj U).obj.map (eqToHom q₁) x := by
    simpa [q₁, absolute_glueing_pullback_comp_terminal_obj] using
      section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := q₁)
        x
  have hcomp :
      (F.obj U).obj.map (eqToHom q₂) ((F.obj U).obj.map (eqToHom q₁) x) =
        (F.obj U).obj.map (eqToHom (q₁.trans q₂)) x := by
    simpa [FunctorToTypes.map_comp_apply, q₁, q₂] using
      (FunctorToTypes.eqToHom_map_comp_apply
        (F := (F.obj U).obj)
        (p := q₁)
        (q := q₂)
        x)
  have hq :
      q₁.trans q₂ =
        (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm := by
    simp [q₁, q₂]
  rw [over_mapComp_terminal_app_eqToHom_op]
  calc
    (F.obj U).obj.map (eqToHom q₂)
        (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm x)
      = (F.obj U).obj.map (eqToHom q₂) ((F.obj U).obj.map (eqToHom q₁) x) := by
          exact congrArg ((F.obj U).obj.map (eqToHom q₂)) hcast
    _ = (F.obj U).obj.map (eqToHom (q₁.trans q₂)) x := hcomp
    _ = Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm x := by
      rw [hq]
      symm
      simpa [absolute_glueing_pullback_terminal_obj] using
        section_cast_eq_map_eqToHom_op
          (P := (F.obj U).obj)
          (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
          x

/-- Helper for Lemma 7.26.6: evaluating `F.transition f` on the terminal object pulled back along
`g` is the same as first transporting the input to the explicit slice object `Over.mk g` and then
transporting the output back to the terminal presentation. -/
theorem absolute_glueing_transition_terminal_cast
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (y : ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
      (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 W)))) :
    (F.transition f).hom.hom.app (Opposite.op ((Over.map g).obj (Over.mk (𝟙 W)))) y =
      eqToHom
        (congrArg
          ((F.obj V).obj.obj)
          (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
        ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
          (Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y)) := by
  -- Apply natural-transformation transport along the terminal-object equality for `Over.map g`,
  -- then invert the resulting output cast.
  let q : Opposite.op ((Over.map g).obj (Over.mk (𝟙 W))) = Opposite.op (Over.mk g) :=
    congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)
  have hcast :=
    natTrans_app_cast_eq
      (α := (F.transition f).hom.hom)
      (q := q)
      (s := y)
  have hcast' :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk g))
          (Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y) =
        Eq.mp
          (congrArg ((F.obj V).obj.obj) q)
          ((F.transition f).hom.hom.app
            (Opposite.op ((Over.map g).obj (Over.mk (𝟙 W)))) y) := by
    simpa [q, absolute_glueing_pullback_homMk_obj] using hcast
  have hcast'' :=
    congrArg
      (Eq.mp
        (congrArg
          ((F.obj V).obj.obj)
          (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
      hcast'
  simpa [q, eqToHom_apply_eq_cast] using hcast''.symm

/-- Helper for Lemma 7.26.6: the reconstructed restriction map attached to
`f : V ⟶ U` sends a section of `F.obj U` over `U/U` to the corresponding section of `F.obj V`
over `V/V`. -/
noncomputable def absoluteGlueingToPresheafMap
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (F.obj U).1.obj (Opposite.op (Over.mk (𝟙 U))) ⟶
      (F.obj V).1.obj (Opposite.op (Over.mk (𝟙 V))) :=
  (F.obj U).1.map (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op ≫
    absoluteGlueing_transition_app_terminal J F f

/-- Helper for Lemma 7.26.6: the reconstructed restriction map for an identity morphism is the
identity map. -/
theorem absolute_glueing_to_presheaf_map_id
    (F : AbsoluteGlueing J) (U : C) :
    absoluteGlueingToPresheafMap J F (𝟙 U) = 𝟙 _ := by
  -- Route correction: after unfolding the reconstructed map, the owner identity comparison
  -- and the canonical slice identity both normalize directly.
  rw [GrothendieckTopology.absoluteGlueingToPresheafMap,
    GrothendieckTopology.absoluteGlueing_transition_app_terminal, F.transition_id,
    absolute_glueing_terminal_slice_id_map]
  simpa using absolute_glueing_transition_id_terminal_comparison (J := J) F U

/-- Helper for Lemma 7.26.6: the reconstructed restriction maps compose as expected. -/
theorem absolute_glueing_to_presheaf_map_comp
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    absoluteGlueingToPresheafMap J F (g ≫ f) =
      absoluteGlueingToPresheafMap J F f ≫ absoluteGlueingToPresheafMap J F g := by
  -- Route correction: evaluate the cocycle identity at the terminal object in `Over W`, then use
  -- naturality of `F.transition f` at `Over.homMk g` to rewrite the middle term into the explicit
  -- `Over.homMk` coordinates used by the reconstructed restriction maps.
  ext x
  have hcomp :=
    congrArg
      (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
      (F.transition_comp f g)
  have hnat := absolute_glueing_transition_homMk_naturality (J := J) F f g
  let y :
      ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
        (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 W))) :=
    Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
      ((F.obj U).obj.map
        (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op x)
  let z :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm
      ((F.obj U).obj.map
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x)
  have hy := congrFun hcomp y
  have hz := congrFun hnat z
  -- First normalize the input transported through the two pullback presentations of `Over.mk g`.
  have htransport :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z := by
    simpa [y, z] using
      absolute_glueing_pullback_terminal_transport_comp (J := J) F f g x
  have hy_left :
      (F.transition (g ≫ f)).hom.hom.app (Opposite.op (Over.mk (𝟙 W)))
        ((F.obj U).obj.map
          (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op)
          y) =
        absoluteGlueingToPresheafMap J F (g ≫ f) x := by
    -- The owner `Over.mapComp` comparison already gives the direct terminal transport on the
    -- left side of the cocycle evaluation.
    have hdirect :
        Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) =
          (F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) := by
      simpa [absolute_glueing_pullback_terminal_obj] using
        section_cast_eq_map_eqToHom_op
          (P := (F.obj U).obj)
          (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
            x)
    have hterm :
        (F.obj U).obj.map
            (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op)
            y =
          (F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) := by
      exact
        (over_mapComp_terminal_section_transport (J := J) F f g
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
            x)).trans hdirect
    have hterminal :
        (F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) := by
      rw [← section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
          x)]
      symm
      exact
        eqToHom_apply_eq_cast
          (G := (F.obj U).obj)
          (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
            x)
    have hterm' :
        (F.obj U).obj.map
            (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op)
            y =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk (𝟙 U) from Over.homMk (g ≫ f)).op
              x) := by
      exact hterm.trans hterminal
    simpa [GrothendieckTopology.absoluteGlueingToPresheafMap,
      GrothendieckTopology.absoluteGlueing_transition_app_terminal,
      FunctorToTypes.map_comp_apply, y] using
      congrArg
        ((F.transition (g ≫ f)).hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
        hterm'
  have hz' :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk g))
          (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
            (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z) =
        (F.obj V).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z) := by
    -- This is the pointwise form of naturality of `F.transition f` along `Over.homMk g`.
    simpa [FunctorToTypes.map_comp_apply] using hz
  have hz_terminal :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z =
        absoluteGlueingToPresheafMap J F f x := by
    -- Unfolding `z` and the reconstructed restriction along `f` leaves only the standard
    -- terminal-object cast appearing in `absoluteGlueing_transition_app_terminal`.
    have hz_input :
        z =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
            ((F.obj U).obj.map
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
              x) := by
      simpa [z, absolute_glueing_pullback_terminal_obj] using
        (eqToHom_apply_eq_cast
          (G := (F.obj U).obj)
          (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
            x)).symm
    calc
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z
        =
          (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
            (eqToHom
              (congrArg
                ((F.obj U).obj.obj)
                (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
              ((F.obj U).obj.map
                (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
                x)) := by
            exact congrArg
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))))
              hz_input
      _ = absoluteGlueingToPresheafMap J F f x := by
            simp [GrothendieckTopology.absoluteGlueingToPresheafMap,
              GrothendieckTopology.absoluteGlueing_transition_app_terminal,
              FunctorToTypes.map_comp_apply]
  have hy_right :
      (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
          ((J.overMapPullback (Type _) g).mapIso (F.transition f) ≪≫ F.transition g) y =
        (absoluteGlueingToPresheafMap J F f ≫ absoluteGlueingToPresheafMap J F g) x := by
    -- Rewrite the pulled-back transition at the terminal object into the explicit `Over.mk g`
    -- coordinates, then use `htransport` and `hz'` to recover the iterated restriction map.
    apply congrArg ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
    calc
      ((J.overMapPullback (Type _) g).mapIso (F.transition f)).hom.hom.app
          (Opposite.op (Over.mk (𝟙 W))) y
        = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
              (Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y)) := by
            simpa using
              absolute_glueing_transition_terminal_cast (J := J) F f g y
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
              (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
                (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z)) := by
            exact congrArg
              (eqToHom
                (congrArg
                  ((F.obj V).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
              (congrArg
                ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)))
                htransport)
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.obj V).obj.map
              (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z)) := by
            exact congrArg
              (eqToHom
                (congrArg
                  ((F.obj V).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
              hz'
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.obj V).obj.map
              (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
              (absoluteGlueingToPresheafMap J F f x)) := by
            exact congrArg
              (fun s ↦
                eqToHom
                  (congrArg
                    ((F.obj V).obj.obj)
                    (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
                  ((F.obj V).obj.map
                    (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op s))
              hz_terminal
  exact hy_left.symm.trans (hy.trans hy_right)

/-- Helper for Lemma 7.26.6: the reconstructed presheaf uses the local sheaf on `C/U`
evaluated at the terminal object `U/U`. -/
noncomputable def absoluteGlueingToPresheaf (F : AbsoluteGlueing J) : Cᵒᵖ ⥤ Type w where
  obj U := (F.obj U.unop).1.obj (Opposite.op (Over.mk (𝟙 U.unop)))
  map f := absoluteGlueingToPresheafMap J F f.unop
  map_id := by
    intro U
    simpa using absolute_glueing_to_presheaf_map_id J F U.unop
  map_comp := by
    intro U V W f g
    simpa using absolute_glueing_to_presheaf_map_comp J F f.unop g.unop

/-- Helper for Lemma 7.26.6: every slice object is the canonical `Over.mk` of its structure map.
-/
theorem over_eq_mk_hom {U : C} (Y : Over U) : Y = Over.mk Y.hom := by
  -- Unpacking a slice object shows that it is completely determined by its map to `U`.
  cases Y
  rfl

/-- Helper for Lemma 7.26.6: every slice morphism is the canonical `Over.homMk` built from its
underlying arrow and commutativity witness. -/
theorem over_homMk_eq
    {U : C} {Y₁ Y₂ : Over U} (k : Y₁ ⟶ Y₂) :
    Over.homMk k.left (Over.w k) = k := by
  -- Morphisms in `Over U` are determined by their underlying arrow, so the proof field is
  -- irrelevant once the source and target are fixed.
  apply CommaMorphism.ext
  · rfl
  · rfl

/-- Helper for Lemma 7.26.6: the canonical `Over.homMk` over `Y₂.hom` factors through the source
object equality coming from `Over.w k`. -/
theorem over_homMk_transport
    {U : C} {Y₁ Y₂ : Over U} (k : Y₁ ⟶ Y₂) :
    (show Over.mk (k.left ≫ Y₂.hom) ⟶ Y₂ from Over.homMk k.left) =
      eqToHom ((congrArg Over.mk (Over.w k)).trans (over_eq_mk_hom (U := U) Y₁)) ≫ k := by
  -- Route correction: normalize the arbitrary slice morphism itself before transporting the
  -- comparison map, so the remaining naturality step only sees one `eqToHom`.
  simpa using
    (over_homMk_eq (U := U)
      (k := eqToHom ((congrArg Over.mk (Over.w k)).trans
        (over_eq_mk_hom (U := U) Y₁)) ≫ k))

/-- Helper for Lemma 7.26.6: the canonical presentation of an already canonical slice object is
definitionally trivial. -/
theorem over_eq_mk_hom_mk {U V : C} (f : V ⟶ U) :
    over_eq_mk_hom (U := U) (Over.mk f) = rfl := by
  rfl

/-- Helper for Lemma 7.26.6: an arbitrary slice morphism factors through the canonical
`Over.mk` coordinates of its source and target. -/
theorem over_homMk_transport_factorization
    {U : C} {Y₁ Y₂ : Over U} (k : Y₁ ⟶ Y₂) :
    k =
      eqToHom ((over_eq_mk_hom (U := U) Y₁).trans (congrArg Over.mk (Over.w k).symm)) ≫
        (show Over.mk (k.left ≫ Y₂.hom) ⟶ Over.mk Y₂.hom from Over.homMk k.left) ≫
          eqToHom (over_eq_mk_hom (U := U) Y₂).symm := by
  -- Morphisms in `Over U` are determined by their underlying arrows, so once the source and
  -- target transports are explicit the factorization is a left-component computation.
  apply Over.OverMorphism.ext
  simp [Over.eqToHom_left]

/-- Helper for Lemma 7.26.6: the forward component of the local comparison
`F.obj U ≅ (absoluteGlueingToPresheaf J F)|_{C/U}` sends a section over `Y` to the corresponding
terminal section of `F.obj Y.left`. -/
noncomputable def absolute_glueing_over_iso_hom_app
    (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    (F.obj U).1.obj (Opposite.op Y) ⟶
      ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).obj (Opposite.op Y) :=
  eqToHom (congrArg (fun X ↦ (F.obj U).1.obj (Opposite.op X)) (over_eq_mk_hom Y)) ≫
    absoluteGlueing_transition_app_terminal J F Y.hom

/-- Helper for Lemma 7.26.6: changing the arrow used to present a canonical slice object only
changes the terminal comparison map by the corresponding source transport. -/
theorem absolute_glueing_transition_app_terminal_congr
    (F : AbsoluteGlueing J) {U V : C} {f g : V ⟶ U} (hfg : f = g) :
    eqToHom (congrArg (fun X ↦ (F.obj U).1.obj (Opposite.op (Over.mk X))) hfg) ≫
      absoluteGlueing_transition_app_terminal (J := J) F g =
        absoluteGlueing_transition_app_terminal (J := J) F f := by
  -- Once the arrow labels agree, both terminal comparison maps are definitionally the same.
  cases hfg
  simp [absoluteGlueing_transition_app_terminal]

/-- Helper for Lemma 7.26.6: changing the presenting arrow of a canonical slice object rewrites the
entire forward local-comparison map by the corresponding source transport. -/
theorem absolute_glueing_over_iso_hom_app_transport
    (F : AbsoluteGlueing J) {U V : C} {f g : V ⟶ U} (hfg : f = g) :
    eqToHom (congrArg (fun X ↦ (F.obj U).1.obj (Opposite.op (Over.mk X))) hfg) ≫
      absolute_glueing_over_iso_hom_app (J := J) F (Over.mk g) =
        absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) := by
  -- On canonical slice objects the comparison map is just the terminal transition map.
  cases hfg
  simp [absolute_glueing_over_iso_hom_app, over_eq_mk_hom_mk]

/-- Helper for Lemma 7.26.6: the inverse component of the local comparison
`F.obj U ≅ (absoluteGlueingToPresheaf J F)|_{C/U}` is obtained by applying the inverse transition
at the terminal object and transporting back from `Over.mk Y.hom` to `Y`. -/
noncomputable def absolute_glueing_over_iso_inverse_app
    (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).obj (Opposite.op Y) ⟶
      (F.obj U).1.obj (Opposite.op Y) :=
  (F.transition Y.hom).inv.hom.app (Opposite.op (Over.mk (𝟙 Y.left))) ≫
    eqToHom (absolute_glueing_pullback_terminal_obj (J := J) F Y.hom) ≫
      eqToHom (congrArg (fun X ↦ (F.obj U).1.obj (Opposite.op X)) (over_eq_mk_hom Y).symm)

/-- Helper for Lemma 7.26.6: the forward and inverse local comparison components compose to the
identity on sections over a slice object. -/
theorem absolute_glueing_over_iso_hom_inv_id
    (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    absolute_glueing_over_iso_hom_app (J := J) F Y ≫
      absolute_glueing_over_iso_inverse_app (J := J) F Y = 𝟙 _ := by
  -- Reduce to the canonical presentation `Y = Over.mk Y.hom`, where the comparison is the
  -- terminal component of `F.transition Y.hom` followed by its inverse.
  cases Y with
  | mk Yleft Yright f =>
      change absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) ≫
          absolute_glueing_over_iso_inverse_app (J := J) F (Over.mk f) = 𝟙 _
      have q :
          (F.obj U).1.obj (Opposite.op (Over.mk f)) =
            ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
              (Opposite.op (Over.mk (𝟙 Yleft))) := by
        simpa [absolute_glueing_pullback_terminal_obj] using
          (congrArg
            (fun X ↦ (F.obj U).1.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq f)).symm
      ext x
      have hcore :
          (F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) (eqToHom q x)) =
            eqToHom q x := by
        have hh :
            ((F.transition f).hom.hom ≫ (F.transition f).inv.hom).app
                (Opposite.op (Over.mk (𝟙 Yleft))) =
              ((𝟙 (((J.overMapPullback (Type _) f).obj (F.obj U)).obj) :
                  ((J.overMapPullback (Type _) f).obj (F.obj U)).obj ⟶
                    ((J.overMapPullback (Type _) f).obj (F.obj U)).obj)).app
                (Opposite.op (Over.mk (𝟙 Yleft))) := by
          exact
            NatTrans.congr_app
              (ObjectProperty.isoHom_inv_id_hom (e := F.transition f))
              (Opposite.op (Over.mk (𝟙 Yleft)))
        exact congrFun hh (eqToHom q x)
      calc
        eqToHom q.symm
            ((F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) (eqToHom q x)))
          = eqToHom q.symm (eqToHom q x) := by
              exact congrArg (eqToHom q.symm) hcore
        _ = x := by
          simpa using
            (FunctorToTypes.eqToHom_map_comp_apply (F := 𝟭 (Type _))
              (p := q) (q := q.symm) x)

/-- Helper for Lemma 7.26.6: the inverse and forward local comparison components compose to the
identity on the restricted reconstructed presheaf. -/
theorem absolute_glueing_over_iso_inv_hom_id
    (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    absolute_glueing_over_iso_inverse_app (J := J) F Y ≫
      absolute_glueing_over_iso_hom_app (J := J) F Y = 𝟙 _ := by
  -- The same normalization reduces the statement to the inverse/hom identity for
  -- `F.transition Y.hom` at the terminal slice object.
  cases Y with
  | mk Yleft Yright f =>
      change absolute_glueing_over_iso_inverse_app (J := J) F (Over.mk f) ≫
          absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) = 𝟙 _
      have q :
          (F.obj U).1.obj (Opposite.op (Over.mk f)) =
            ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
              (Opposite.op (Over.mk (𝟙 Yleft))) := by
        simpa [absolute_glueing_pullback_terminal_obj] using
          (congrArg
            (fun X ↦ (F.obj U).1.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq f)).symm
      ext x
      have hcast :
          eqToHom q
              (eqToHom q.symm
                ((F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) x)) =
            (F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) x := by
        simpa using
          (FunctorToTypes.eqToHom_map_comp_apply (F := 𝟭 (Type _))
            (p := q.symm) (q := q)
            ((F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) x))
      calc
        (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
            (eqToHom q
              (eqToHom q.symm
                ((F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) x)))
          =
            (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
              ((F.transition f).inv.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) x) := by
                exact congrArg
                  ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
                  hcast
        _ = x := by
          have hh :
              ((F.transition f).inv.hom ≫ (F.transition f).hom.hom).app
                  (Opposite.op (Over.mk (𝟙 Yleft))) =
                ((𝟙 ((F.obj Yleft).obj) : (F.obj Yleft).obj ⟶ (F.obj Yleft).obj)).app
                  (Opposite.op (Over.mk (𝟙 Yleft))) := by
            exact
              NatTrans.congr_app
                (ObjectProperty.isoInv_hom_id_hom (e := F.transition f))
                (Opposite.op (Over.mk (𝟙 Yleft)))
          exact congrFun hh x

/-- Helper for Lemma 7.26.6: after identifying the two presentations of the iterated pullback
terminal object, the direct restriction along `Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f`
coincides with first transporting to the terminal object for `f` and then restricting along `g`.
-/
theorem absolute_glueing_pullback_terminal_transport_homMk_op_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (show Opposite.op (Over.mk f) ⟶ Opposite.op (Over.mk (g ≫ f)) from
        (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op) ≫
      eqToHom
        ((congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm.trans
          (congrArg Opposite.op
            (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))) =
      eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm ≫
        ((Over.map f).map (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g)).op := by
  -- The two opposite-slice arrows become identical after unpacking the corresponding
  -- `Over.homMk` and `Over.map` morphisms.
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.eqToHom_left, Over.map]

/-- Helper for Lemma 7.26.6: transporting the direct restriction of a section over `Over.mk f`
to the iterated pullback terminal object agrees with first transporting that section to the
terminal object for `f` and then restricting along `g`. -/
theorem absolute_glueing_pullback_terminal_transport_homMk
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : (F.obj U).obj.obj (Opposite.op (Over.mk f))) :
    Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
      (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) =
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
        (Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm x) := by
  -- Route correction: this is the same cast-normalization pattern as the terminal-composite
  -- lemma, but the source section now already lies over `Over.mk f`.
  have hcast₁ :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) := by
    simpa [absolute_glueing_pullback_homMk_obj] using
      section_cast_eq_map_eqToHom_op
        (P := ((J.overMapPullback (Type _) f).obj (F.obj U)).obj)
        (q := congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))
        (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x))
  have hcast₂ :
      Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) =
        (F.obj U).obj.map
          (eqToHom (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
    simpa [absolute_glueing_pullback_comp_terminal_obj] using
      section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)
  have hcast₃ :
      Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm x =
        (F.obj U).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
          x := by
    simpa [absolute_glueing_pullback_terminal_obj] using
      section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
        x
  have hleft :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
          ((F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) := by
    rw [hcast₁]
    exact congrArg
      (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))))
      hcast₂
  have hright :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          (Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm x) =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          ((F.obj U).obj.map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
            x) := by
    exact congrArg
      (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
        (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op)
      hcast₃
  have hmap_eqToHom_g :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g))) =
        (F.obj U).obj.map
          (eqToHom
            (congrArg Opposite.op
              (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))) := by
    ext y
    change
      (F.obj U).obj.map
          (((Over.map f).op).map
            (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))) y =
        (F.obj U).obj.map
          (eqToHom
            (congrArg Opposite.op
              (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))) y
    simpa using
      congrArg
        (fun k ↦ (F.obj U).obj.map k y)
        (CategoryTheory.eqToHom_map ((Over.map f).op)
          (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)))
  have hleft' :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g)
          (Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)) =
        (F.obj U).obj.map
          (eqToHom
            ((congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm.trans
              (congrArg Opposite.op
                (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))))
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
    rw [hleft]
    rw [hmap_eqToHom_g]
    simpa using
      (FunctorToTypes.eqToHom_map_comp_apply (F := (F.obj U).obj)
        (p := (congrArg Opposite.op (over_map_obj_terminal_comp_eq f g)).symm)
        (q := congrArg Opposite.op
          (congrArg (fun X ↦ (Over.map f).obj X) (absoluteGlueing_over_map_obj_terminal_eq g)))
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)).symm
  rw [hleft', hright]
  -- Apply the normalized opposite-slice morphism identity to the presheaf `F.obj U`.
  simpa [FunctorToTypes.map_comp_apply] using
    congrArg (fun k ↦ (F.obj U).obj.map k x)
      (absolute_glueing_pullback_terminal_transport_homMk_op_hom f g)

/-- Helper for Lemma 7.26.6: the forward local comparison from `F.obj U` to the restriction of
the reconstructed presheaf is natural in arrows of `Over U`. -/
theorem absolute_glueing_over_iso_hom_naturality_homMk
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (F.obj U).1.map (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op ≫
      absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (g ≫ f)) =
    absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) ≫
      ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).map
        (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op := by
  -- In the canonical `Over.mk` coordinates, the source proof is the cocycle for `F.transition`
  -- evaluated at the terminal object `W/W`.
  ext x
  have hcomp :=
    congrArg
      (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
      (F.transition_comp f g)
  let y :
      ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
        (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 W))) :=
    Eq.mp (absolute_glueing_pullback_comp_terminal_obj (J := J) F f g).symm
      ((F.obj U).obj.map
        (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)
  let z :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F f).symm x
  have hy := congrFun hcomp y
  have hnat := absolute_glueing_transition_homMk_naturality (J := J) F f g
  have hz := congrFun hnat z
  have htransport :
      Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y =
        ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z := by
    simpa [y, z] using
      absolute_glueing_pullback_terminal_transport_homMk (J := J) F f g x
  have hy_left :
      (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
          ((J.overMapPullbackComp (Type _) g f).app (F.obj U) ≪≫ F.transition (g ≫ f)) y =
        ((F.obj U).1.map (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op ≫
            absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (g ≫ f))) x := by
    -- The left side is already the direct terminal evaluation defining the canonical comparison
    -- at `Over.mk (g ≫ f)`.
    have hterm :
        (F.obj U).obj.map (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op) y =
          Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
      simpa [y] using
        over_mapComp_terminal_section_transport (J := J) F f g
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)
    have hterminal :
        Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
      have hcast :
          Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm
              ((F.obj U).obj.map
                (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) =
            (F.obj U).obj.map
              (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
              ((F.obj U).obj.map
                (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
        simpa [absolute_glueing_pullback_terminal_obj] using
          section_cast_eq_map_eqToHom_op
            (P := (F.obj U).obj)
            (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)
      rw [hcast]
      rw [← section_cast_eq_map_eqToHom_op
        (P := (F.obj U).obj)
        (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
        ((F.obj U).obj.map
          (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)]
      exact
        (eqToHom_apply_eq_cast
          (G := (F.obj U).obj)
          (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
          ((F.obj U).obj.map
            (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x)).symm
    have hterm' :
        (F.obj U).obj.map (((Over.mapComp g f).hom.app (Over.mk (𝟙 W))).op) y =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            ((F.obj U).obj.map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op x) := by
      exact hterm.trans hterminal
    simpa [absolute_glueing_over_iso_hom_app,
      GrothendieckTopology.absoluteGlueing_transition_app_terminal,
      FunctorToTypes.map_comp_apply, y] using
      congrArg
        ((F.transition (g ≫ f)).hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
        hterm'
  have hz' :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk g))
          (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
            (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z) =
        (F.obj V).obj.map
          (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
          ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z) := by
    -- This is the pointwise form of naturality of `F.transition f` along `Over.homMk g`.
    simpa [FunctorToTypes.map_comp_apply] using hz
  have hz_terminal :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z =
        absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) x := by
    -- Evaluating the terminal component of `F.transition f` on the explicit terminal transport
    -- of `x` recovers the local comparison at `Over.mk f`.
    have hz_input :
        z =
          eqToHom
            (congrArg
              ((F.obj U).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
            x := by
      simpa [z, absolute_glueing_pullback_terminal_obj] using
        (eqToHom_apply_eq_cast
          (G := (F.obj U).obj)
          (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
          x).symm
    calc
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z
        =
          (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
            (eqToHom
              (congrArg
                ((F.obj U).obj.obj)
                (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
              x) := by
            exact congrArg
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))))
              hz_input
      _ = absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) x := by
            simp [absolute_glueing_over_iso_hom_app,
              GrothendieckTopology.absoluteGlueing_transition_app_terminal]
  have hy_right :
      (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
          ((J.overMapPullback (Type _) g).mapIso (F.transition f) ≪≫ F.transition g) y =
        (absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) ≫
            ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).map
              (show Over.mk (g ≫ f) ⟶ Over.mk f from Over.homMk g).op) x := by
    -- Rewrite the pulled-back transition at the terminal object into the explicit `Over.mk g`
    -- coordinates, then use `htransport` and `hz'` to recover the iterated restriction map.
    apply congrArg ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 W))))
    calc
      ((J.overMapPullback (Type _) g).mapIso (F.transition f)).hom.hom.app
          (Opposite.op (Over.mk (𝟙 W))) y
        = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
              (Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g) y)) := by
            simpa using
              absolute_glueing_transition_terminal_cast (J := J) F f g y
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
              (((J.overMapPullback (Type _) f).obj (F.obj U)).obj.map
                (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op z)) := by
            exact congrArg
              (eqToHom
                (congrArg
                  ((F.obj V).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
              (congrArg
                ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)))
                htransport)
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.obj V).obj.map
              (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) z)) := by
            exact congrArg
              (eqToHom
                (congrArg
                  ((F.obj V).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
              hz'
      _ = eqToHom
            (congrArg
              ((F.obj V).obj.obj)
              (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((F.obj V).obj.map
              (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op
              (absolute_glueing_over_iso_hom_app (J := J) F (Over.mk f) x)) := by
            exact congrArg
              (fun s ↦
                eqToHom
                  (congrArg
                    ((F.obj V).obj.obj)
                    (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
                  ((F.obj V).obj.map
                    (show Over.mk g ⟶ Over.mk (𝟙 V) from Over.homMk g).op s))
              hz_terminal
  exact hy_left.symm.trans (hy.trans hy_right)

/-- Helper for Lemma 7.26.6: after rewriting a general slice morphism as the canonical
`Over.homMk` of its left component, the local-comparison naturality square reduces to the
canonical `Over.mk`/`Over.homMk` case. -/
theorem absolute_glueing_over_iso_hom_naturality_eqToHom
    (F : AbsoluteGlueing J) {U : C} {Y₁ Y₂ : Over U} (p : Y₁ = Y₂) :
    (F.obj U).1.map (eqToHom p).op ≫
      absolute_glueing_over_iso_hom_app (J := J) F Y₁ =
    absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫
      ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).map (eqToHom p).op := by
  -- Naturality along an equality is just transport on both sides of the comparison map.
  cases p
  simp [absolute_glueing_over_iso_hom_app]

/-- Helper for Lemma 7.26.6: after rewriting a general slice morphism as the canonical
`Over.homMk` of its left component, the local-comparison naturality square reduces to the
canonical `Over.mk`/`Over.homMk` case. -/
theorem absolute_glueing_over_iso_hom_naturality
    (F : AbsoluteGlueing J) {U : C} {Y₁ Y₂ : Over U} (k : Y₁ ⟶ Y₂) :
    (F.obj U).1.map k.op ≫ absolute_glueing_over_iso_hom_app (J := J) F Y₁ =
      absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫
        ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F).map k.op := by
  -- Route correction: split the arbitrary slice morphism into source transport, the canonical
  -- `Over.homMk`, and target transport, so the source proof reduces to the canonical case.
  let p₁ : Y₁ = Over.mk (k.left ≫ Y₂.hom) :=
    (over_eq_mk_hom (U := U) Y₁).trans (congrArg Over.mk (Over.w k).symm)
  let p₂ : Y₂ = Over.mk Y₂.hom := over_eq_mk_hom (U := U) Y₂
  let k₀ : Over.mk (k.left ≫ Y₂.hom) ⟶ Over.mk Y₂.hom := Over.homMk k.left
  let A := (F.obj U).1
  let B := ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F)
  have hk :
      k = eqToHom p₁ ≫ k₀ ≫ eqToHom p₂.symm := by
    simpa [p₁, p₂, k₀] using over_homMk_transport_factorization (U := U) k
  have hk_op :
      k.op = (eqToHom p₂.symm).op ≫ k₀.op ≫ (eqToHom p₁).op := by
    simpa [Category.assoc, p₁, p₂, k₀] using congrArg Quiver.Hom.op hk
  have hsource :
      A.map (eqToHom p₁).op ≫ absolute_glueing_over_iso_hom_app (J := J) F Y₁ =
        absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (k.left ≫ Y₂.hom)) ≫
          B.map (eqToHom p₁).op := by
    -- First peel off the source transport from `Y₁` to its canonical `Over.mk` model.
    simpa [A, B] using
      absolute_glueing_over_iso_hom_naturality_eqToHom (J := J) (F := F) (p := p₁)
  have hmiddle :
      A.map k₀.op ≫ absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (k.left ≫ Y₂.hom)) =
        absolute_glueing_over_iso_hom_app (J := J) F (Over.mk Y₂.hom) ≫ B.map k₀.op := by
    -- The middle square is now exactly the canonical `Over.homMk` naturality statement.
    simpa [A, B, k₀] using
      absolute_glueing_over_iso_hom_naturality_homMk
        (J := J) (F := F) (f := Y₂.hom) (g := k.left)
  have htarget :
      A.map (eqToHom p₂.symm).op ≫ absolute_glueing_over_iso_hom_app (J := J) F (Over.mk Y₂.hom) =
        absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫ B.map (eqToHom p₂.symm).op := by
    -- Finally move from the canonical target `Over.mk Y₂.hom` back to the original `Y₂`.
    simpa [A] using
      absolute_glueing_over_iso_hom_naturality_eqToHom (J := J) (F := F) (p := p₂.symm)
  have htarget_map :
      B.map (eqToHom p₂.symm).op = 𝟙 _ := by
    -- Forgetting a slice equality only remembers the left-object equality, which is definitional
    -- for `p₂ : Y₂ = Over.mk Y₂.hom`.
    simp [B]
  calc
    A.map k.op ≫ absolute_glueing_over_iso_hom_app (J := J) F Y₁
      = A.map ((eqToHom p₂.symm).op) ≫
          A.map k₀.op ≫
            A.map ((eqToHom p₁).op) ≫
              absolute_glueing_over_iso_hom_app (J := J) F Y₁ := by
          simpa [hk_op, Functor.map_comp, Category.assoc]
    _ = A.map ((eqToHom p₂.symm).op) ≫
          A.map k₀.op ≫
            absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (k.left ≫ Y₂.hom)) ≫
              B.map ((eqToHom p₁).op) := by
          -- Compose the source transport square on the right of the two preceding factors.
          exact congrArg (fun t ↦ A.map ((eqToHom p₂.symm).op) ≫ A.map k₀.op ≫ t) hsource
    _ = A.map ((eqToHom p₂.symm).op) ≫
          absolute_glueing_over_iso_hom_app (J := J) F (Over.mk Y₂.hom) ≫
            B.map k₀.op ≫ B.map ((eqToHom p₁).op) := by
          -- Then splice in the canonical `Over.homMk` square in the middle.
          simpa [Category.assoc] using
            congrArg (fun t ↦ A.map ((eqToHom p₂.symm).op) ≫ t ≫ B.map ((eqToHom p₁).op))
              hmiddle
    _ = absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫
          B.map ((eqToHom p₂.symm).op) ≫
            B.map k₀.op ≫ B.map ((eqToHom p₁).op) := by
          -- The target transport square finishes the passage back to the original `Y₂`.
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ B.map k₀.op ≫ B.map ((eqToHom p₁).op)) htarget
    _ = absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫
          B.map k₀.op ≫ B.map ((eqToHom p₁).op) := by
          -- On the reconstructed side the forgotten equality transport is the identity map.
          simp_rw [htarget_map]
          ext x
          rfl
    _ = absolute_glueing_over_iso_hom_app (J := J) F Y₂ ≫
          B.map k.op := by
          rw [hk_op, Functor.map_comp, Functor.map_comp]
          simp_rw [htarget_map]
          ext x
          rfl

/-- Helper for Lemma 7.26.6: each local sheaf `F.obj U` identifies with the restriction of the
reconstructed presheaf to the slice site `C/U`. -/
noncomputable def absoluteGlueingOverIso
    (F : AbsoluteGlueing J) (U : C) :
    (F.obj U).1 ≅ (Over.forget U).op ⋙ absoluteGlueingToPresheaf J F :=
  NatIso.ofComponents
    (fun Y ↦
      { hom := absolute_glueing_over_iso_hom_app (J := J) F Y.unop
        inv := absolute_glueing_over_iso_inverse_app (J := J) F Y.unop
        hom_inv_id := absolute_glueing_over_iso_hom_inv_id (J := J) F Y.unop
        inv_hom_id := absolute_glueing_over_iso_inv_hom_id (J := J) F Y.unop })
    (fun {Y₁ Y₂} k ↦ by
      -- Naturality is exactly the componentwise compatibility proved above.
      simpa using
        absolute_glueing_over_iso_hom_naturality
          (J := J) F (Y₁ := Y₂.unop) (Y₂ := Y₁.unop) k.unop)

/-- Helper for Lemma 7.26.6: compatibility of a family of sections for a base cover
`f : Xᵢ ⟶ U` is equivalent to compatibility for the induced family of arrows
`Over.mk (f i) ⟶ Over.mk (𝟙 U)` in the slice category. -/
theorem compatible_over_terminal_iff
    (P : Cᵒᵖ ⥤ Type w) {U : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U)
    (x : ∀ i, P.obj (Opposite.op (X i))) :
    Presieve.Arrows.Compatible P f x ↔
      Presieve.Arrows.Compatible ((Over.forget U).op ⋙ P)
        (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i))) x := by
  constructor
  · intro hx i j Z gi gj h
    exact hx i j Z.left gi.left gj.left (by simpa using (Over.forget U).congr_map h)
  · intro hx i j Z gi gj h
    let Z' : Over U := Over.mk (gi ≫ f i)
    exact hx i j Z' (Over.homMk gi) (Over.homMk gj (by simpa [Z'] using h.symm)) (by
      ext
      simp [Z', h])

/-- Helper for Lemma 7.26.6: for a family `f : Xᵢ ⟶ U`, the sheaf condition for a presheaf `P`
on the base arrows `f` is equivalent to the sheaf condition for the restricted presheaf on the
induced slice arrows `Over.mk (f i) ⟶ Over.mk (𝟙 U)`. -/
theorem isSheafFor_over_terminal_ofArrows_iff
    (P : Cᵒᵖ ⥤ Type w) {U : C} {ι : Type*} (X : ι → C) (f : ∀ i, X i ⟶ U) :
    Presieve.IsSheafFor P (Presieve.ofArrows X f) ↔
      Presieve.IsSheafFor ((Over.forget U).op ⋙ P)
        (Presieve.ofArrows (fun i ↦ Over.mk (f i))
          (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i)))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      obtain ⟨y, hy⟩ := h.2 ⟨x.1, (compatible_over_terminal_iff P f x.1).2 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      obtain ⟨y, hy⟩ := h.2 ⟨x.1, (compatible_over_terminal_iff P f x.1).1 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i

/-- Helper for Lemma 7.26.6: the presheaf reconstructed from an absolute glueing datum is a
sheaf on `(C, J)`. -/
theorem absoluteGlueingToPresheaf_isSheaf
    (F : AbsoluteGlueing J) :
    Presheaf.IsSheaf J (absoluteGlueingToPresheaf J F) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS
  obtain ⟨ι, X, f, rfl⟩ := S.exists_eq_ofArrows
  have hlocal :
      Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F) :=
    (Presheaf.isSheaf_of_iso_iff (absoluteGlueingOverIso (J := J) F U)).1 (F.obj U).property
  have hcover :
      Sieve.ofArrows (fun i ↦ Over.mk (f i))
        (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i))) ∈
          (J.over U) (Over.mk (𝟙 U)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      Presieve.functorPushforward_overForget]
    simp only [Over.mk_left, Over.forget_obj, Presieve.map_ofArrows, Over.forget_map,
      Over.homMk_left, Sieve.generate_sieve]
    exact hS
  have hlocal' :
      Presieve.IsSheafFor ((Over.forget U).op ⋙ absoluteGlueingToPresheaf J F)
        (Presieve.ofArrows (fun i ↦ Over.mk (f i))
          (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i)))) := by
    rw [Presieve.isSheafFor_iff_generate
      (R := Presieve.ofArrows (fun i ↦ Over.mk (f i))
        (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i))))]
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 hlocal) _ hcover
  rw [← Presieve.isSheafFor_iff_generate (R := Presieve.ofArrows X f)]
  exact
    (isSheafFor_over_terminal_ofArrows_iff
      (P := absoluteGlueingToPresheaf J F) (U := U) X f).2 hlocal'

/-- Helper for Lemma 7.26.6: the absolute-glueing reconstruction on objects lands in sheaves. -/
noncomputable def absoluteGlueingToSheaf (F : AbsoluteGlueing J) :
    Sheaf J (Type w) :=
  ⟨absoluteGlueingToPresheaf J F, absoluteGlueingToPresheaf_isSheaf (J := J) F⟩

/-- Helper for Lemma 7.26.6: a morphism of absolute glueing data induces a morphism of the
reconstructed presheaves by evaluating each local component at the terminal slice object. -/
theorem absolute_glueing_hom_terminal_naturality
    {F G : AbsoluteGlueing J} (α : F ⟶ G) {U V : C} (f : V ⟶ U) :
    absoluteGlueingToPresheafMap J F f ≫ (α.app V).hom.app (Opposite.op (Over.mk (𝟙 V))) =
      (α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) ≫ absoluteGlueingToPresheafMap J G f := by
  -- Evaluate the absolute-glueing square on the terminal object `V/V`, then normalize the
  -- pullback cast back to the explicit slice object `Over.mk f`.
  ext x
  let xf : (F.obj U).obj.obj (Opposite.op (Over.mk f)) :=
    (F.obj U).obj.map
      (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x
  let yf :
      ((J.overMapPullback (Type _) f).obj (F.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp
      (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
        (absoluteGlueing_over_map_obj_terminal_eq f)).symm
      xf
  let yg :
      ((J.overMapPullback (Type _) f).obj (G.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp
      (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
        (absoluteGlueing_over_map_obj_terminal_eq f)).symm
      ((G.obj U).obj.map
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
        ((α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) x))
  have hlocal :
      (α.app U).hom.app (Opposite.op (Over.mk f)) xf =
        (G.obj U).obj.map
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
          ((α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) x) := by
    -- This is ordinary naturality of the local morphism `α.app U` along `Over.homMk f`.
    simpa [xf, FunctorToTypes.map_comp_apply] using
      congrFun
        ((α.app U).hom.naturality
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op)
        x
  have hpullback :
      (((J.overMapPullback (Type _) f).map (α.app U)).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) yf = yg := by
    -- Transport the input cast across `α.app U`, then replace the middle term by `hlocal`.
    have hcast :
        (((J.overMapPullback (Type _) f).map (α.app U)).hom.app
            (Opposite.op (Over.mk (𝟙 V)))) yf =
          Eq.mp
            (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
              (absoluteGlueing_over_map_obj_terminal_eq f)).symm
            ((α.app U).hom.app (Opposite.op (Over.mk f)) xf) := by
      simpa [yf] using
        (natTrans_app_cast_eq
          (α := (α.app U).hom)
          (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
          (s := xf))
    rw [hcast, hlocal]
    rfl
  have hsq :
      (G.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yg =
        (α.app V).hom.app (Opposite.op (Over.mk (𝟙 V)))
          ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yf) := by
    -- The compatibility square for `α` is now an equality between the two terminal evaluations.
    have hsq' :=
      congrFun
        (congrArg
          (fun τ ↦ τ.hom.app (Opposite.op (Over.mk (𝟙 V))))
          (α.naturality f).w)
        yf
    have hsq'' :
        (G.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
            ((((J.overMapPullback (Type _) f).map (α.app U)).hom.app
              (Opposite.op (Over.mk (𝟙 V)))) yf) =
          (α.app V).hom.app (Opposite.op (Over.mk (𝟙 V)))
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yf) := by
      simpa [FunctorToTypes.map_comp_apply] using hsq'
    rw [hpullback] at hsq''
    exact hsq''
  have hyf :
      eqToHom
          (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq f)).symm
          xf = yf := by
    simpa [yf] using
      (eqToHom_apply_eq_cast
        (G := (F.obj U).obj)
        (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
        xf)
  have hyg :
      eqToHom
          (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq f)).symm
          ((G.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
            ((α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) x)) = yg := by
    simpa [yg] using
      (eqToHom_apply_eq_cast
        (G := (G.obj U).obj)
        (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq f)).symm)
        ((G.obj U).obj.map
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
          ((α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) x)))
  calc
    (α.app V).hom.app (Opposite.op (Over.mk (𝟙 V)))
        ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
          (eqToHom
            (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
              (absoluteGlueing_over_map_obj_terminal_eq f)).symm
            xf))
      =
        (α.app V).hom.app (Opposite.op (Over.mk (𝟙 V)))
          ((F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yf) := by
            rw [hyf]
    _ =
        (G.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yg := hsq.symm
    _ =
        (G.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
          (eqToHom
            (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
              (absoluteGlueing_over_map_obj_terminal_eq f)).symm
            ((G.obj U).obj.map
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
              ((α.app U).hom.app (Opposite.op (Over.mk (𝟙 U))) x))) := by
            rw [hyg]
/-- Helper for Lemma 7.26.6: the reconstructed sheaf construction extends to a functor on
absolute glueing data. -/
noncomputable def absoluteGlueingToSheafFunctor :
    AbsoluteGlueing J ⥤ Sheaf J (Type w) where
  obj := absoluteGlueingToSheaf J
  map {F G} α :=
    ObjectProperty.homMk
      { app := fun U ↦ (α.app U.unop).hom.app (Opposite.op (Over.mk (𝟙 U.unop)))
        naturality := by
          intro U V f
          simpa using
            absolute_glueing_hom_terminal_naturality
              (J := J) α f.unop }
  map_id F := by
    -- Terminal evaluation of the identity local morphisms is the identity reconstructed map.
    apply Sheaf.hom_ext
    rfl
  map_comp {F G H} α β := by
    -- Terminal evaluation commutes with composition because the local components do.
    apply Sheaf.hom_ext
    rfl

/-- Helper for Lemma 7.26.6: reconstructing the canonical absolute glueing of a sheaf recovers
the original restriction map on sections. -/
theorem sheaf_to_absolute_glueing_reconstruction_map
    (F : Sheaf J (Type w)) {U V : C} (f : V ⟶ U) :
    absoluteGlueingToPresheafMap J ((sheafToAbsoluteGlueingFunctor J).obj F) f =
      F.obj.map f.op := by
  -- For canonical glueing data, the terminal-evaluation restriction is just the original
  -- sheaf restriction along `f`.
  ext x
  simp [absoluteGlueingToPresheafMap, absoluteGlueing_transition_app_terminal,
    sheafToAbsoluteGlueingFunctor, Sheaf.over, Over.mapForget, Over.mapForget_eq]

/-- Helper for Lemma 7.26.6: the underlying presheaf of the reconstructed canonical absolute
glueing is naturally isomorphic to the original sheaf. -/
noncomputable def sheaf_to_absolute_glueing_reconstruction_presheafIso
    (F : Sheaf J (Type w)) :
    F.obj ≅ (absoluteGlueingToSheaf J ((sheafToAbsoluteGlueingFunctor J).obj F)).obj :=
  NatIso.ofComponents
    (fun U ↦ Iso.refl _)
    (fun {U V} f ↦ by
      -- The reconstructed restriction maps agree objectwise with the original sheaf maps.
      simpa [absoluteGlueingToSheaf, absoluteGlueingToPresheaf] using
        (sheaf_to_absolute_glueing_reconstruction_map
          (J := J) F f.unop).symm)

/-- Helper for Lemma 7.26.6: the canonical glueing reconstruction fixes every sheaf. -/
noncomputable def sheaf_to_absolute_glueing_reconstruction_unitIso :
    𝟭 (Sheaf J (Type w)) ≅
      sheafToAbsoluteGlueingFunctor J ⋙ absoluteGlueingToSheafFunctor J :=
  NatIso.ofComponents
    (fun F ↦
      -- Lift the presheaf-level reconstruction isomorphism through the sheaf property.
      ObjectProperty.isoMk (Presheaf.IsSheaf J)
        (sheaf_to_absolute_glueing_reconstruction_presheafIso (J := J) F))
    (fun {F G} η ↦ by
      -- On underlying presheaves the reconstruction unit is the identity, so naturality is
      -- exactly extensionality for sheaf morphisms.
      apply Sheaf.hom_ext
      rfl)

/-- Helper for Lemma 7.26.6: the canonical transition of the reconstructed sheaf along
`f : V ⟶ U`, evaluated at `Y : Over V`, is the identity after unfolding the owner
`Over.mapForget` comparison. -/
theorem reconstructed_transition_component_homMk
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) (Y : Over V) :
    ((((sheafToAbsoluteGlueingFunctor J).obj (absoluteGlueingToSheaf J F)).transition f).hom.hom.app
        (Opposite.op Y)) = 𝟙 _ := by
  -- Unfold the canonical transition for the reconstructed sheaf and normalize the owner
  -- `Over.mapForget` comparison on the slice object `Y`.
  cases Y with
  | mk Yleft Yright g =>
      ext x
      -- The owner comparison reduces to the reconstructed restriction map along `𝟙 Yleft`,
      -- and that map was already proved to be the identity.
      simpa [sheafToAbsoluteGlueingFunctor, absoluteGlueingToSheaf, absoluteGlueingToPresheaf,
        Sheaf.over, Over.mapForget, Over.mapForget_eq] using
        congrFun (absolute_glueing_to_presheaf_map_id (J := J) F Yleft) x

/-- Helper for Lemma 7.26.6: the local comparison isomorphisms `absoluteGlueingOverIso`
rewrite the pulled-back comparison map at `Y : Over V` into the direct source-proof composite
through `F.transition f`. -/
theorem reconstructed_transition_source_transport
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) (Y : Over V)
    (x : ((J.overMapPullback (Type w) f).obj (F.obj U)).obj.obj (Opposite.op Y)) :
    absolute_glueing_over_iso_hom_app (J := J) F ((Over.map f).obj Y) x =
      absolute_glueing_over_iso_hom_app (J := J) F Y
        ((F.transition f).hom.hom.app (Opposite.op Y) x) := by
  -- Route correction: after passing to the canonical `Over.mk` coordinates of `Y`, the square is
  -- exactly the cocycle for `F.transition` evaluated at the terminal object over `Y.left`.
  cases Y with
  | mk Yleft Yright g =>
      change
        absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (g ≫ f)) x =
          absolute_glueing_over_iso_hom_app (J := J) F (Over.mk g)
            ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)) x)
      let y :
          ((J.overMapPullback (Type _) f ⋙ J.overMapPullback (Type _) g).obj
            (F.obj U)).obj.obj (Opposite.op (Over.mk (𝟙 Yleft))) :=
        Eq.mp (absolute_glueing_pullback_homMk_obj (J := J) F f g).symm x
      have hy :
          (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              ((J.overMapPullbackComp (Type _) g f).app (F.obj U) ≪≫ F.transition (g ≫ f)) y =
            (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              ((J.overMapPullback (Type _) g).mapIso (F.transition f) ≪≫ F.transition g) y := by
        exact
          congrFun
            (congrArg
              (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              (F.transition_comp f g))
            y
      have hy_left :
          (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              ((J.overMapPullbackComp (Type _) g f).app (F.obj U) ≪≫ F.transition (g ≫ f)) y =
            absolute_glueing_over_iso_hom_app (J := J) F (Over.mk (g ≫ f)) x := by
        -- The direct composite side is already the canonical comparison at `Over.mk (g ≫ f)`.
        have hterm :
            (F.obj U).obj.map (((Over.mapComp g f).hom.app (Over.mk (𝟙 Yleft))).op) y =
              Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm x := by
          simpa [y] using
            over_mapComp_terminal_section_transport (J := J) F f g x
        have hterminal :
            Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm x =
              eqToHom
                (congrArg
                  ((F.obj U).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
                x := by
          have hcast :
              Eq.mp (absolute_glueing_pullback_terminal_obj (J := J) F (g ≫ f)).symm x =
                (F.obj U).obj.map
                  (eqToHom (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
                  x := by
            simpa [absolute_glueing_pullback_terminal_obj] using
              section_cast_eq_map_eqToHom_op
                (P := (F.obj U).obj)
                (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
                x
          rw [hcast]
          rw [← section_cast_eq_map_eqToHom_op
            (P := (F.obj U).obj)
            (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
            x]
          exact
            (eqToHom_apply_eq_cast
              (G := (F.obj U).obj)
              (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
              x).symm
        have hterm' :
            (F.obj U).obj.map (((Over.mapComp g f).hom.app (Over.mk (𝟙 Yleft))).op) y =
              eqToHom
                (congrArg
                  ((F.obj U).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq (g ≫ f))).symm)
                x := by
          exact hterm.trans hterminal
        simpa [absolute_glueing_over_iso_hom_app,
          GrothendieckTopology.absoluteGlueing_transition_app_terminal,
          FunctorToTypes.map_comp_apply, y] using
          congrArg
            ((F.transition (g ≫ f)).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
            hterm'
      have hy_right :
          (fun e ↦ e.hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              ((J.overMapPullback (Type _) g).mapIso (F.transition f) ≪≫ F.transition g) y =
            absolute_glueing_over_iso_hom_app (J := J) F (Over.mk g)
              ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)) x) := by
        -- Rewrite the pulled-back source section into the explicit `Over.mk g` coordinates first.
        let p := absolute_glueing_pullback_homMk_obj (J := J) F f g
        have hcast :
            Eq.mp p y = x := by
          simpa [p, y, eqToHom_apply_eq_cast] using
            (FunctorToTypes.eqToHom_map_comp_apply (F := 𝟭 (Type _))
              (p := p.symm) (q := p) x)
        have hmid :
            ((J.overMapPullback (Type _) g).mapIso (F.transition f)).hom.hom.app
                (Opposite.op (Over.mk (𝟙 Yleft))) y =
              eqToHom
                (congrArg
                  ((F.obj V).obj.obj)
                  (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
                ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)) x) := by
          calc
            ((J.overMapPullback (Type _) g).mapIso (F.transition f)).hom.hom.app
                (Opposite.op (Over.mk (𝟙 Yleft))) y
              = eqToHom
                  (congrArg
                    ((F.obj V).obj.obj)
                    (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
                  ((F.transition f).hom.hom.app (Opposite.op (Over.mk g))
                    (Eq.mp p y)) := by
                  simpa [p] using
                    absolute_glueing_transition_terminal_cast (J := J) F f g y
            _ = eqToHom
                  (congrArg
                    ((F.obj V).obj.obj)
                    (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
                  ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)) x) := by
                  exact congrArg
                    (eqToHom
                      (congrArg
                        ((F.obj V).obj.obj)
                        (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm))
                    (congrArg
                      ((F.transition f).hom.hom.app (Opposite.op (Over.mk g)))
                      hcast)
        simpa [absolute_glueing_over_iso_hom_app,
          GrothendieckTopology.absoluteGlueing_transition_app_terminal] using
          congrArg
            ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
            hmid
      exact hy_left.symm.trans (hy.trans hy_right)

/-- Helper for Lemma 7.26.6: the local comparison isomorphisms `absoluteGlueingOverIso`
should assemble into a morphism of absolute glueings from `F` to the canonical glueing of its
reconstruction. -/
theorem absolute_glueing_over_iso_transition_compat
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    CommSq
      ((J.overMapPullback (Type w) f).map
        (ObjectProperty.homMk ((absoluteGlueingOverIso (J := J) F U).hom)))
      (F.transition f).hom
      (((sheafToAbsoluteGlueingFunctor J).obj (absoluteGlueingToSheaf J F)).transition f).hom
      (ObjectProperty.homMk ((absoluteGlueingOverIso (J := J) F V).hom)) := by
  -- After evaluating at `Y : Over V`, the reconstructed owner transition is the identity, so the
  -- square reduces to the direct comparison between the pulled-back source component and the
  -- right-path composite through `F.transition f`.
  refine .mk ?_
  ext Y x
  simpa [absoluteGlueingOverIso, reconstructed_transition_component_homMk (J := J) F f Y.unop,
    FunctorToTypes.map_comp_apply] using
    reconstructed_transition_source_transport (J := J) F f Y.unop x

/-- Helper for Lemma 7.26.6: the presheaf-level local comparison upgrades to an isomorphism of
sheaves on the slice site `C/U`. -/
noncomputable def absoluteGlueingOverSheafIso
    (F : AbsoluteGlueing J) (U : C) :
    F.obj U ≅ ((sheafToAbsoluteGlueingFunctor J).obj (absoluteGlueingToSheaf J F)).obj U :=
  ObjectProperty.isoMk (Presheaf.IsSheaf (J.over U)) (absoluteGlueingOverIso (J := J) F U)

/-- Helper for Lemma 7.26.6: the forward local comparison maps commute with morphisms of
absolute glueing data. -/
theorem absolute_glueing_over_iso_hom_map_compat
    {F G : AbsoluteGlueing J} (α : F ⟶ G) {U : C} (Y : Over U) :
    (α.app U).hom.app (Opposite.op Y) ≫ absolute_glueing_over_iso_hom_app (J := J) G Y =
      absolute_glueing_over_iso_hom_app (J := J) F Y ≫
        (α.app Y.left).hom.app (Opposite.op (Over.mk (𝟙 Y.left))) := by
  -- After passing to the canonical presentation `Y = Over.mk Y.hom`, the statement is the
  -- terminal evaluation of the square `α.naturality Y.hom`.
  cases Y with
  | mk Yleft Yright g =>
      ext x
      let yf :
          ((J.overMapPullback (Type _) g).obj (F.obj U)).obj.obj
            (Opposite.op (Over.mk (𝟙 Yleft))) :=
        Eq.mp
          (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq g)).symm
          x
      let yg :
          ((J.overMapPullback (Type _) g).obj (G.obj U)).obj.obj
            (Opposite.op (Over.mk (𝟙 Yleft))) :=
        Eq.mp
          (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
            (absoluteGlueing_over_map_obj_terminal_eq g)).symm
          ((α.app U).hom.app (Opposite.op (Over.mk g)) x)
      have hpullback :
          (((J.overMapPullback (Type _) g).map (α.app U)).hom.app
              (Opposite.op (Over.mk (𝟙 Yleft)))) yf = yg := by
        -- The pullbacked component of `α.app U` only has to absorb the terminal-object cast.
        simpa [yf] using
          (natTrans_app_cast_eq
            (α := (α.app U).hom)
            (q := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            (s := x))
      have hsq :
          (G.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) yg =
            (α.app Yleft).hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
              ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) yf) := by
        -- Evaluate the absolute-glueing square for `α` along `g` at the terminal object of
        -- `Over Yleft`.
        have hsq' :=
          congrFun
            (congrArg
              (fun τ ↦ τ.hom.app (Opposite.op (Over.mk (𝟙 Yleft))))
              (α.naturality g).w)
            yf
        have hsq'' :
            (G.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
                ((((J.overMapPullback (Type _) g).map (α.app U)).hom.app
                  (Opposite.op (Over.mk (𝟙 Yleft)))) yf) =
              (α.app Yleft).hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
                ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft))) yf) := by
          simpa [FunctorToTypes.map_comp_apply] using hsq'
        rw [hpullback] at hsq''
        exact hsq''
      have hyf :
          eqToHom
              (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
                (absoluteGlueing_over_map_obj_terminal_eq g)).symm
              x = yf := by
        simpa [yf] using
          (eqToHom_apply_eq_cast
            (G := (F.obj U).obj)
            (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            x)
      have hyg :
          eqToHom
              (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
                (absoluteGlueing_over_map_obj_terminal_eq g)).symm
              ((α.app U).hom.app (Opposite.op (Over.mk g)) x) = yg := by
        simpa [yg] using
          (eqToHom_apply_eq_cast
            (G := (G.obj U).obj)
            (p := (congrArg Opposite.op (absoluteGlueing_over_map_obj_terminal_eq g)).symm)
            ((α.app U).hom.app (Opposite.op (Over.mk g)) x))
      -- Rewrite both local comparisons to their terminal evaluations and then apply `hsq`.
      change
        (G.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
            (eqToHom
              (congrArg (fun X ↦ (G.obj U).obj.obj (Opposite.op X))
                (absoluteGlueing_over_map_obj_terminal_eq g)).symm
              ((α.app U).hom.app (Opposite.op (Over.mk g)) x)) =
          (α.app Yleft).hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
            ((F.transition g).hom.hom.app (Opposite.op (Over.mk (𝟙 Yleft)))
              (eqToHom
                (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
                  (absoluteGlueing_over_map_obj_terminal_eq g)).symm
                x))
      rw [hyg, hyf]
      exact hsq

/-- Helper for Lemma 7.26.6: the forward local comparison squares package into a morphism square
against the reconstructed map induced by `α`. -/
theorem absolute_glueing_over_iso_map_compat
    {F G : AbsoluteGlueing J} (α : F ⟶ G) (U : C) :
    CommSq
      (α.app U)
      (ObjectProperty.homMk ((absoluteGlueingOverIso (J := J) F U).hom))
      (ObjectProperty.homMk ((absoluteGlueingOverIso (J := J) G U).hom))
      (((sheafToAbsoluteGlueingFunctor J).map ((absoluteGlueingToSheafFunctor J).map α)).app U) := by
  -- Evaluate both local comparison maps at `Y : Over U`; the reconstructed map is just terminal
  -- evaluation of `α.app Y.left`.
  refine .mk ?_
  ext Y x
  simpa [absoluteGlueingOverIso, sheafToAbsoluteGlueingFunctor, absoluteGlueingToSheafFunctor,
    FunctorToTypes.map_comp_apply] using
    congrFun (absolute_glueing_over_iso_hom_map_compat (J := J) α Y.unop) x

/-- Helper for Lemma 7.26.6: the local comparison isomorphisms assemble into the counit for the
reconstruction equivalence on absolute glueing data. -/
noncomputable def absoluteGlueing_reconstruction_counitIso :
    absoluteGlueingToSheafFunctor J ⋙ sheafToAbsoluteGlueingFunctor J ≅
      𝟭 (AbsoluteGlueing J) := by
  -- Use the inverse local comparisons as the counit components, and derive their naturality by
  -- inverting the already-established forward comparison squares.
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine
      { hom :=
          { app := fun U ↦ (absoluteGlueingOverSheafIso (J := J) F U).symm.hom
            naturality := by
              intro U V f
              simpa using
                (CommSq.horiz_inv
                  (f := (J.overMapPullback (Type w) f).mapIso
                    (absoluteGlueingOverSheafIso (J := J) F U))
                  (i := absoluteGlueingOverSheafIso (J := J) F V)
                  (absolute_glueing_over_iso_transition_compat (J := J) F f)) }
        inv :=
          { app := fun U ↦ (absoluteGlueingOverSheafIso (J := J) F U).hom
            naturality := by
              intro U V f
              simpa using absolute_glueing_over_iso_transition_compat (J := J) F f }
        hom_inv_id := by
          apply AbsoluteGlueing.Hom.ext
          funext U
          apply Sheaf.hom_ext
          ext Y x
          simpa [absoluteGlueingOverIso, FunctorToTypes.map_comp_apply] using
            congrFun (absolute_glueing_over_iso_inv_hom_id (J := J) F Y.unop) x
        inv_hom_id := by
          apply AbsoluteGlueing.Hom.ext
          funext U
          apply Sheaf.hom_ext
          ext Y x
          simpa [absoluteGlueingOverIso, FunctorToTypes.map_comp_apply] using
            congrFun (absolute_glueing_over_iso_hom_inv_id (J := J) F Y.unop) x }
  · intro F G α
    apply AbsoluteGlueing.Hom.ext
    funext U
    exact
      (CommSq.vert_inv
        (g := absoluteGlueingOverSheafIso (J := J) F U)
        (h := absoluteGlueingOverSheafIso (J := J) G U)
        (absolute_glueing_over_iso_map_compat (J := J) α U)).w

-- Proof sketch: from an absolute glueing datum, form the presheaf `U ↦ ℱ_U(U)` with restriction
-- maps induced by the transition isomorphisms; the cocycle gives functoriality and the local
-- identifications `ℱ_U ≅ ℱ|_{C/U}` show the resulting presheaf is a sheaf. This construction is
-- quasi-inverse to `sheafToAbsoluteGlueingFunctor`.
/-- Lemma 7.26.6: the category `Sh(C)` is equivalent to the category of absolute glueings via the
functor sending a sheaf on `C` to its canonical absolute glueing. -/
instance sheafToAbsoluteGlueingFunctor_isEquivalence :
    Functor.IsEquivalence (sheafToAbsoluteGlueingFunctor J) := by
  -- Route correction: the reconstruction functor and the source-side unit are now explicit, so
  -- the only remaining work is to assemble `absoluteGlueingOverIso` into the counit on
  -- absolute glueing data.
  exact Functor.IsEquivalence.mk'
    (absoluteGlueingToSheafFunctor J)
    (sheaf_to_absolute_glueing_reconstruction_unitIso (J := J))
    (absoluteGlueing_reconstruction_counitIso (J := J))

end GrothendieckTopology
end CategoryTheory
