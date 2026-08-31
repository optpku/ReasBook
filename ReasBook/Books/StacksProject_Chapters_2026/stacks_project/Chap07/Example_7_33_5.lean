module

public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.Topology.Sheaves.Points
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat
open TopologicalSpace
open CategoryTheory.Limits
open Opposite

universe u v

namespace CategoryTheory

open GrothendieckTopology.Point.Hom
open GrothendieckTopology.Point.ofIsCofiltered

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 7.33.5:
- primary domain: points of the opens site of a topological space and the identification of their
  site-theoretic fibers with ordinary stalks;
- sampled owner API:
  `Opens.pointGrothendieckTopology`,
  `GrothendieckTopology.Point.ofIsCofiltered`,
  `TopCat.Presheaf.stalk`,
  `GrothendieckTopology.Point.Hom.presheafFiber`;
- source/core/bridge triage:
  `source-facing`: the textbook point of `X_{Zar}` attached to `x` together with its fiber and
    stalk descriptions;
  `core/canonical`: `Opens.pointGrothendieckTopology x` and `TopCat.Presheaf.stalk`;
  `bridge/view`: the neighborhood-site point built from `OpenNhds.inclusion x` and the resulting
    comparison isomorphism on presheaf fibers.

Primitive data are only the point `x`, the neighborhood inclusion functor, and the presheaf/sheaf
whose fiber is being computed. The singleton-or-empty description of fibers is derived API from
the canonical point owner, while the stalk comparison is a bridge from the site point to the
usual neighborhood-colimit presentation of stalks.
-/

@[simp] theorem Opens.pointGrothendieckTopology_fiber_nonempty_iff (x : X) (U : Opens X) :
    Nonempty ((Opens.pointGrothendieckTopology x).fiber.obj U) ↔ x ∈ U := by
  simp [Opens.pointGrothendieckTopology]

theorem Opens.pointGrothendieckTopology_fiber_isEmpty (x : X) (U : Opens X) (hx : x ∉ U) :
    IsEmpty ((Opens.pointGrothendieckTopology x).fiber.obj U) := by
  refine ⟨fun t ↦ hx t.down.down⟩

/- Example 7.33.5: for a point `x : X`, the corresponding point of the opens site `X_{Zar}` is
the canonical mathlib point `Opens.pointGrothendieckTopology x`. Its fiber over an open `U` is
empty when `x ∉ U` and nonempty exactly when `x ∈ U`; the singleton claim then follows from the
upstream instance `Subsingleton ((Opens.pointGrothendieckTopology x).fiber.obj U)`. The companion
declarations here are `Opens.pointGrothendieckTopology_fiber_isEmpty` and
`Opens.pointGrothendieckTopology_fiber_nonempty_iff`. -/
recall Opens.pointGrothendieckTopology

instance (x : X) : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall (OpenNhds x)

theorem openNhdsInclusion_coverLift (x : X) :
    ∀ ⦃U : Opens X⦄ (R : Sieve U) (_ : R ∈ Opens.grothendieckTopology X U)
      ⦃V : OpenNhds x⦄ (f : (OpenNhds.inclusion x).obj V ⟶ U),
      ∃ (Y : Opens X) (g : Y ⟶ U) (_ : R g) (W : OpenNhds x) (q : W ⟶ V)
        (a : (OpenNhds.inclusion x).obj W ⟶ Y),
        a ≫ g = (OpenNhds.inclusion x).map q ≫ f := by
  intro U R hR V f
  obtain ⟨Y, g, hg, hy⟩ := hR x (f.le V.2)
  let Yx : OpenNhds x := ⟨Y, hy⟩
  refine ⟨Y, g, hg, Yx ⊓ V, OpenNhds.infLERight Yx V, OpenNhds.infLELeft Yx V, ?_⟩
  subsingleton

noncomputable def openNhdsPoint (x : X) :
    (Opens.grothendieckTopology X).Point :=
  GrothendieckTopology.Point.ofIsCofiltered
    (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x)

noncomputable def pointGrothendieckTopology_hom_openNhdsPoint (x : X) :
    Opens.pointGrothendieckTopology x ⟶ openNhdsPoint x where
  hom.app U z := by
    classical
    let z' : (fiber (OpenNhds.inclusion x)).obj U := by
      simpa [openNhdsPoint, GrothendieckTopology.Point.ofIsCofiltered] using z
    let hsurj := fiberMk_jointly_surjective z'
    let V := Classical.choose hsurj
    let f := Classical.choose (Classical.choose_spec hsurj)
    exact ULift.up (PLift.up (f.le V.2))
  hom.naturality _ _ _ := by
    ext z
    subsingleton

noncomputable def openNhdsPoint_hom_pointGrothendieckTopology (x : X) :
    openNhdsPoint x ⟶ Opens.pointGrothendieckTopology x where
  hom.app U z := by
    change ULift (PLift (x ∈ U)) at z
    let Ux : OpenNhds x := ⟨U, z.down.down⟩
    exact fiberMk (show (OpenNhds.inclusion x).obj Ux ⟶ U from 𝟙 U)
  hom.naturality _ _ _ := by
    ext z
    subsingleton

noncomputable def pointGrothendieckTopologyIsoOpenNhdsPoint (x : X) :
    Opens.pointGrothendieckTopology x ≅ openNhdsPoint x where
  hom := pointGrothendieckTopology_hom_openNhdsPoint x
  inv := openNhdsPoint_hom_pointGrothendieckTopology x
  hom_inv_id := by
    ext U z
    subsingleton
  inv_hom_id := by
    ext U z
    subsingleton

section

variable {C : Type v} [Category.{u} C] [HasColimits C]

noncomputable def pointGrothendieckTopology_presheafFiber_iso_openNhdsPoint
    (x : X) :
    ((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C) ≅
      ((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C) where
  hom := (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber
  inv := (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber
  hom_inv_id := by
    calc
      (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber ≫
          (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber =
          ((pointGrothendieckTopologyIsoOpenNhdsPoint x).hom ≫
              (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv).presheafFiber := by
            exact
              (presheafFiber_comp
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv).symm
      _ = presheafFiber (𝟙 (Opens.pointGrothendieckTopology x)) := by
        rw [(pointGrothendieckTopologyIsoOpenNhdsPoint x).hom_inv_id]
      _ = 𝟙 (((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C)) := by
        exact presheafFiber_id (Opens.pointGrothendieckTopology x)
  inv_hom_id := by
    calc
      (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber ≫
          (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber =
          ((pointGrothendieckTopologyIsoOpenNhdsPoint x).inv ≫
              (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom).presheafFiber := by
            exact
              (presheafFiber_comp
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom).symm
      _ = presheafFiber (𝟙 (openNhdsPoint x)) := by
        rw [(pointGrothendieckTopologyIsoOpenNhdsPoint x).inv_hom_id]
      _ = 𝟙 (((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C)) := by
        exact presheafFiber_id (openNhdsPoint x)

/-- Helper for Example 7.33.5: the site-theoretic fiber of the neighborhood-site point is the
ordinary stalk because both are colimits of the same neighborhood diagram. -/
noncomputable def openNhdsPoint_presheafFiber_obj_iso_stalk
    (x : X) (P : X.Presheaf C) :
    ((openNhdsPoint x).presheafFiber.obj P) ≅ TopCat.Presheaf.stalk P x :=
  IsColimit.coconePointUniqueUpToIso
    (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone
      (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ P))

/-- Helper for Example 7.33.5: the comparison isomorphism sends each canonical neighborhood leg of
the site-theoretic fiber cocone to the usual germ map. -/
theorem openNhdsPoint_presheafFiber_obj_iso_stalk_hom_comp_toPresheafFiberOfIsCofiltered
    (x : X) (P : X.Presheaf C) (U : OpenNhds x) :
    GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered
        (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) U P ≫
      (openNhdsPoint_presheafFiber_obj_iso_stalk x P).hom =
        TopCat.Presheaf.germ P U.1 x U.2 := by
  -- Both maps are the `U`-leg of the two colimit cocones for the neighborhood diagram.
  simpa [TopCat.Presheaf.germ] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (P := GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone
        (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P)
      (Q := colimit.isColimit ((OpenNhds.inclusion x).op ⋙ P))
      (j := op U))

/-- Helper for Example 7.33.5: the objectwise comparison isomorphisms are natural in the
presheaf, so they assemble into the stalk comparison natural isomorphism. -/
theorem openNhdsPoint_presheafFiber_obj_iso_stalk_naturality
    (x : X) {P Q : X.Presheaf C} (g : P ⟶ Q) :
    ((openNhdsPoint x).presheafFiber.map g) ≫
        (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom =
      (openNhdsPoint_presheafFiber_obj_iso_stalk x P).hom ≫
        (TopCat.Presheaf.stalkFunctor C x).map g := by
  -- Compare the two candidate maps after precomposing with each neighborhood leg.
  apply
    (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone
      (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P).hom_ext
  intro U
  -- After rewriting the opposite-indexed leg through `U.unop`, the goal is the usual naturality
  -- relation between presheaf morphisms and germ maps.
  have hleft :
      (GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone
          (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P).ι.app U ≫
        (openNhdsPoint x).presheafFiber.map g ≫
          (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom =
      g.app (op ((OpenNhds.inclusion x).obj U.unop)) ≫
        TopCat.Presheaf.germ Q U.unop.1 x U.unop.2 := by
    have hnat :=
      GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_naturality
        (p := OpenNhds.inclusion x) (hp := openNhdsInclusion_coverLift x) (g := g) (U := U.unop)
    calc
      (GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone
          (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P).ι.app U ≫
        (openNhdsPoint x).presheafFiber.map g ≫
          (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom =
          (GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered
              (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) U.unop P ≫
            (openNhdsPoint x).presheafFiber.map g) ≫
              (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom := by
                simp [GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone,
                  Category.assoc]
      _ =
          (g.app (op ((OpenNhds.inclusion x).obj U.unop)) ≫
            GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered
              (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) U.unop Q) ≫
              (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom := by
                simpa [openNhdsPoint] using congrArg
                  (fun k ↦ k ≫ (openNhdsPoint_presheafFiber_obj_iso_stalk x Q).hom) hnat
      _ =
          g.app (op ((OpenNhds.inclusion x).obj U.unop)) ≫
            TopCat.Presheaf.germ Q U.unop.1 x U.unop.2 := by
              rw [Category.assoc,
                openNhdsPoint_presheafFiber_obj_iso_stalk_hom_comp_toPresheafFiberOfIsCofiltered
                  (x := x) (P := Q) (U := U.unop)]
  have hright :
      (GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone
          (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P).ι.app U ≫
        (openNhdsPoint_presheafFiber_obj_iso_stalk x P).hom ≫
          (TopCat.Presheaf.stalkFunctor C x).map g =
      TopCat.Presheaf.germ P U.unop.1 x U.unop.2 ≫
        (TopCat.Presheaf.stalkFunctor C x).map g := by
    refine Eq.trans
      (b := (GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered
          (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) U.unop P ≫
        (openNhdsPoint_presheafFiber_obj_iso_stalk x P).hom) ≫
          (TopCat.Presheaf.stalkFunctor C x).map g)
      ?_ ?_
    · simp [GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone, Category.assoc]
    · rw [openNhdsPoint_presheafFiber_obj_iso_stalk_hom_comp_toPresheafFiberOfIsCofiltered
        (x := x) (P := P) (U := U.unop)]
      rfl
  refine Eq.trans hleft ?_
  refine Eq.trans ?_ hright.symm
  simpa [Category.assoc] using
    (TopCat.Presheaf.stalkFunctor_map_germ
      (C := C) (U := U.unop.1) (x := x) (hx := U.unop.2) g).symm

noncomputable def openNhdsPoint_presheafFiber_iso_stalkFunctor
    (x : X) :
    ((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C) ≅ TopCat.Presheaf.stalkFunctor C x :=
  NatIso.ofComponents
    (fun P ↦ openNhdsPoint_presheafFiber_obj_iso_stalk x P)
    (fun {_ _} g ↦ openNhdsPoint_presheafFiber_obj_iso_stalk_naturality (C := C) x g)

noncomputable def pointGrothendieckTopology_presheafFiber_iso_stalkFunctor
    (x : X) :
    ((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C) ≅
      TopCat.Presheaf.stalkFunctor C x :=
  pointGrothendieckTopology_presheafFiber_iso_openNhdsPoint x ≪≫
    openNhdsPoint_presheafFiber_iso_stalkFunctor x

noncomputable def pointGrothendieckTopology_presheafFiber_obj_iso_stalk
    (x : X) (P : X.Presheaf C) :
    (((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C)).obj P ≅
      TopCat.Presheaf.stalk P x :=
  (pointGrothendieckTopology_presheafFiber_iso_stalkFunctor x).app P

noncomputable def pointGrothendieckTopology_sheafFiber_obj_iso_stalk
    (x : X) (F : X.Sheaf C) :
    (((Opens.pointGrothendieckTopology x).sheafFiber : X.Sheaf C ⥤ C)).obj F ≅
      TopCat.Presheaf.stalk F.presheaf x :=
  (Functor.isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) C)
    (pointGrothendieckTopology_presheafFiber_iso_stalkFunctor x)).app F

end

/- The associated textbook stalk is the usual stalk of a presheaf on `X`, formalized in mathlib as
`TopCat.Presheaf.stalk`. For the canonical opens-site point `Opens.pointGrothendieckTopology x`,
the main comparison is the natural isomorphism
`pointGrothendieckTopology_presheafFiber_iso_stalkFunctor`, whose componentwise presheaf and sheaf
forms are `pointGrothendieckTopology_presheafFiber_obj_iso_stalk` and
`pointGrothendieckTopology_sheafFiber_obj_iso_stalk`. -/
recall TopCat.Presheaf.stalk

end CategoryTheory
