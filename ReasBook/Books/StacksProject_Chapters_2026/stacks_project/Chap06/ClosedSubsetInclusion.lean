module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Lemma_6_21_5

@[expose] public section

open TopCat TopologicalSpace

universe u

namespace TopCat

/-- The inclusion morphism of a subset into its ambient topological space. -/
abbrev subsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion morphism of a closed subset into its ambient topological space. -/
abbrev closedSubsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  subsetInclusion X Z

end TopCat

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open scoped TopCat

section SubsetSheafPushforward

universe v w

variable {X : TopCat.{v}}
variable {C : Type w} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Helper for Stacks 00AF/00AG: after the presheaf pullback unit is sheafified, the inverse
pullback comparison recovers the sheaf pullback unit on sections. -/
private theorem sheaf_pullbackIso_inv_toSheafify_unit_app {Y T : TopCat.{v}}
    (f : Y ⟶ T) (G : TopCat.Sheaf C T) (U : Opens T) :
    (((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app (op U)) ≫
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).app
            (op ((Opens.map f).obj U))) ≫
        (((TopCat.Sheaf.pullbackIso C f).inv.app G).hom.app (op ((Opens.map f).obj U))) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom.app (op U)) := by
  -- Compare the sheaf pullback adjunction with the sheafification construction adjunction.
  have hunit :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G) ≫
          (TopCat.Sheaf.pushforward C f).map ((TopCat.Sheaf.pullbackIso C f).hom.app G) =
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y)).unit.app
          G := by
    simpa [TopCat.Sheaf.pullbackIso, TopCat.Sheaf.pullbackPushforwardAdjunction] using
      (Adjunction.unit_leftAdjointUniq_hom_app
        (TopCat.Sheaf.pullbackPushforwardAdjunction C f)
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y))
        G)
  -- Evaluate the comparison after forgetting to presheaves and then on the chosen open.
  have htransport :
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom.app (op U)) ≫
        (((TopCat.Sheaf.pullbackIso C f).hom.app G).hom.app (op ((Opens.map f).obj U))) =
      (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y)).unit.app
          G).hom.app (op U)) := by
    have h := congrArg (fun k ↦ k.hom.app (op U)) hunit
    change ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom ≫
        ((TopCat.Sheaf.pushforward C f).map ((TopCat.Sheaf.pullbackIso C f).hom.app G)).hom).app
          (op U)) = _ at h
    rw [NatTrans.comp_app] at h
    change (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom.app (op U)) ≫
        (((TopCat.Sheaf.pullbackIso C f).hom.app G).hom.app (op ((Opens.map f).obj U))) =
      _ at h
    exact h
  -- Expose the construction unit as the presheaf unit followed by sheafification.
  have hconstruction :
      (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y)).unit.app
          G).hom.app (op U)) =
      (((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app (op U)) ≫
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).app
            (op ((Opens.map f).obj U))) := by
    set_option backward.isDefEq.respectTransparency false in
    have h_lanUnit :
        ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y)).unit.app
            G).hom =
          (Opens.map f).op.lanUnit.app G.obj ≫
            (Opens.map f).op.whiskerLeft
              (CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
                (((Opens.map f).op.lan).obj G.obj)) := by
      change (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology T) C).map
          ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map f) C (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y)).unit.app
              G) = _
      simp only [CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
        CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback,
        Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
        sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.id_obj,
        Functor.comp_obj, Functor.comp_map, Category.assoc]
      simp [Functor.lanAdjunction_unit]
    simpa [TopCat.Presheaf.pullbackPushforwardAdjunction, TopCat.Presheaf.pullback,
      Category.assoc] using congrArg (fun k ↦ k.app (op U)) h_lanUnit
  rw [← Category.assoc, ← htransport.trans hconstruction]
  -- Cancel the pullback comparison against its inverse at the section object.
  have hcancel :
      (((TopCat.Sheaf.pullbackIso C f).hom.app G).hom.app (op ((Opens.map f).obj U))) ≫
        (((TopCat.Sheaf.pullbackIso C f).inv.app G).hom.app (op ((Opens.map f).obj U))) =
      𝟙 _ := by
    have h := congrArg (fun k ↦ k.hom.app (op ((Opens.map f).obj U)))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso C f) G)
    change ((((TopCat.Sheaf.pullbackIso C f).hom.app G).hom ≫
        ((TopCat.Sheaf.pullbackIso C f).inv.app G).hom).app (op ((Opens.map f).obj U))) =
      ((𝟙 ((TopCat.Sheaf.pullback C f).obj G) :
          ((TopCat.Sheaf.pullback C f).obj G) ⟶ ((TopCat.Sheaf.pullback C f).obj G))).hom.app
        (op ((Opens.map f).obj U)) at h
    rw [NatTrans.comp_app] at h
    simpa using h
  let c := (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom.app (op U))
  let α := (((TopCat.Sheaf.pullbackIso C f).hom.app G).hom.app (op ((Opens.map f).obj U)))
  let β := (((TopCat.Sheaf.pullbackIso C f).inv.app G).hom.app (op ((Opens.map f).obj U)))
  change (c ≫ α) ≫ β = c
  calc
    (c ≫ α) ≫ β = c ≫ (α ≫ β) := Category.assoc c α β
    _ = c ≫ 𝟙 _ := congrArg (fun t ↦ c ≫ t) (by simpa [α, β] using hcancel)
    _ = c := Category.comp_id c

/-- Helper for Stacks 00AF/00AG: the sectionwise form of the pullback-comparison
normalization. -/
private theorem sheaf_pullbackIso_inv_toSheafify_unit_section_eq {Y T : TopCat.{v}}
    (f : Y ⟶ T) (G : TopCat.Sheaf C T) (U : Opens T)
    (s : CC (G.1.obj (op U))) :
    (((TopCat.Sheaf.pullbackIso C f).inv.app G).1.app (op ((Opens.map f).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).app
            (op ((Opens.map f).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app
            (op U)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).1.app (op U)) s) := by
  -- Apply the morphism equality to the chosen section and expand concrete composition.
  have h := sheaf_pullbackIso_inv_toSheafify_unit_app (C := C) f G U
  have hs := congrArg (fun k ↦ k s) h
  calc
    (((TopCat.Sheaf.pullbackIso C f).inv.app G).1.app (op ((Opens.map f).obj U)))
        (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).app
              (op ((Opens.map f).obj U)))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app
              (op U)) s))
      = (((((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app
            (op U)) ≫
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).app
              (op ((Opens.map f).obj U))) ≫
          (((TopCat.Sheaf.pullbackIso C f).inv.app G).1.app
            (op ((Opens.map f).obj U)))) s) := by
            rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
            rfl
    _ = ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).1.app (op U)) s) := by
          simpa using hs

/-- Helper for Stacks 00AF/00AG: the sheafification unit sends a stalk germ to the corresponding
sheafified germ. -/
private theorem toSheafify_stalk_map_germ_apply {Y : TopCat.{v}}
    (F : Y.Presheaf C) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t : CC (F.obj (op W))) :
    ((TopCat.Presheaf.stalkFunctor C y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) F))
      (F.germ W y hy t) =
      (TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology Y) F) W y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y) F).app (op W) t) := by
  -- This is the standard germ computation for the stalk functor map.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) F) t)

/-- Helper for Stacks 00AF/00AG: the inverse pullback comparison sends a sheafified stalk germ to
the corresponding germ in the sheaf pullback. -/
private theorem pullbackIso_inv_stalk_map_germ_apply {Y T : TopCat.{v}}
    (f : Y ⟶ T) (G : TopCat.Sheaf C T) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t : CC ((sheafify (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G)).obj (op W))) :
    ((TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map
          ((TopCat.Sheaf.pullbackIso C f).inv.app G)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj G))
          W y hy) t) =
      (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ W y hy
        ((((TopCat.Sheaf.pullbackIso C f).inv.app G).1.app (op W)) t) := by
  -- This is the same stalk-functor germ computation for the inverse pullback comparison.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      ((TopCat.Sheaf.forget C Y).map
        ((TopCat.Sheaf.pullbackIso C f).inv.app G)) t)

omit [HasLimits C] in
/-- Helper for Stacks 00AF/00AG: the symmetric stalk image of a sheaf isomorphism is the stalk map
of the inverse component. -/
private theorem stalkFunctor_mapIso_symm_hom_eq_map_inv {Y : TopCat.{v}}
    {F G : TopCat.Sheaf C Y} (e : F ≅ G) (y : Y) :
    ((TopCat.Presheaf.stalkFunctor C y).mapIso
        ((TopCat.Sheaf.forget C Y).mapIso e)).symm.hom =
      (TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map e.inv) := by
  -- The symmetric isomorphism map is definitionally the map induced by the inverse morphism.
  rfl

/-- Helper for Stacks 00AF/00AG: the sheaf-level stalk pullback comparison sends germs to the
germs produced by the sheaf pullback unit. -/
private theorem sheaf_stalkPullbackIso_germ_apply {Y T : TopCat.{v}}
    (f : Y ⟶ T) (G : TopCat.Sheaf C T) (U : Opens T) (y : Y)
    (hy : y ∈ (Opens.map f).obj U) (s : CC (G.1.obj (op U))) :
    ((TopCat.Sheaf.stalkPullbackIso f G y).hom)
      (G.presheaf.germ U (f y) hy s) =
      (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ ((Opens.map f).obj U) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).1.app
            (op U)) s) := by
  -- Expand the sheaf-level comparison into the presheaf stalk map and sheafification.
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, asIso_hom, stalkFunctor_mapIso_symm_hom_eq_map_inv]
  change
    (((TopCat.Presheaf.stalkPullbackIso C f G.presheaf y).hom ≫
      ((TopCat.Presheaf.stalkFunctor C y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Presheaf.pullback C f).obj G.obj))) ≫
      ((TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map ((TopCat.Sheaf.pullbackIso C f).app G).inv)))
      (G.presheaf.germ U (f y) hy s)) =
      (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ ((Opens.map f).obj U) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).1.app
            (op U)) s)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  let t : CC (((TopCat.Presheaf.pullback C f).obj G.1).obj (op ((Opens.map f).obj U))) :=
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app (op U)) s)
  -- First compute the presheaf pullback stalk comparison on the original germ.
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso C f G.presheaf y).hom
          (G.presheaf.germ U (f y) hy s) =
        (((TopCat.Presheaf.pullback C f).obj G.1).germ
          ((Opens.map f).obj U) y hy t) := by
    calc
      (TopCat.Presheaf.stalkPullbackIso C f G.presheaf y).hom
          (G.presheaf.germ U (f y) hy s)
        = ((G.presheaf.germ U (f y) hy ≫
              (TopCat.Presheaf.stalkPullbackIso C f G.presheaf y).hom) s) := by
            rw [ConcreteCategory.comp_apply]
      _ = ((((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G.1).app
              (op U) ≫
              (((TopCat.Presheaf.pullback C f).obj G.1).germ
                ((Opens.map f).obj U) y hy)) s) := by
            exact congrArg
              (fun k ↦ k s)
              (TopCat.Presheaf.germ_stalkPullbackHom C f G.1 y U hy)
      _ = (((TopCat.Presheaf.pullback C f).obj G.1).germ
          ((Opens.map f).obj U) y hy t) := by
            rw [ConcreteCategory.comp_apply]
            rfl
  calc
    ((TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map ((TopCat.Sheaf.pullbackIso C f).app G).inv))
      (((TopCat.Presheaf.stalkFunctor C y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Presheaf.pullback C f).obj G.obj)))
        ((TopCat.Presheaf.stalkPullbackIso C f G.presheaf y).hom
          (G.presheaf.germ U (f y) hy s)))
      =
        ((TopCat.Presheaf.stalkFunctor C y).map
          ((TopCat.Sheaf.forget C Y).map ((TopCat.Sheaf.pullbackIso C f).app G).inv))
        (((TopCat.Presheaf.stalkFunctor C y).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
            ((TopCat.Presheaf.pullback C f).obj G.obj)))
          (((TopCat.Presheaf.pullback C f).obj G.1).germ ((Opens.map f).obj U) y hy t)) := by
            rw [hpresheaf]
    -- Then pass through sheafification and the inverse pullback comparison.
    _ =
        ((TopCat.Presheaf.stalkFunctor C y).map
          ((TopCat.Sheaf.forget C Y).map ((TopCat.Sheaf.pullbackIso C f).app G).inv))
          ((TopCat.Presheaf.germ
            (sheafify (Opens.grothendieckTopology Y)
              ((TopCat.Presheaf.pullback C f).obj G.obj))
            ((Opens.map f).obj U) y hy)
            ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
              ((TopCat.Presheaf.pullback C f).obj G.obj)).app
              (op ((Opens.map f).obj U)) t)) := by
          rw [toSheafify_stalk_map_germ_apply]
    _ =
        (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ ((Opens.map f).obj U) y hy
          ((((TopCat.Sheaf.pullbackIso C f).inv.app G).1.app (op ((Opens.map f).obj U)))
            (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
              ((TopCat.Presheaf.pullback C f).obj G.obj)).app
                (op ((Opens.map f).obj U))) t)) := by
          simpa using
            (pullbackIso_inv_stalk_map_germ_apply (C := C) f G ((Opens.map f).obj U) y hy
              (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
                ((TopCat.Presheaf.pullback C f).obj G.obj)).app
                  (op ((Opens.map f).obj U))) t))
    _ = (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ ((Opens.map f).obj U) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).1.app
            (op U)) s) := by
          dsimp [t]
          simpa using congrArg
            (fun q ↦ (((TopCat.Sheaf.pullback C f).obj G).presheaf).germ
              ((Opens.map f).obj U) y hy q)
            (sheaf_pullbackIso_inv_toSheafify_unit_section_eq (C := C) f G U s)

section

variable {Z : Set X}

local notation "sZ" => X.subsetInclusion Z

omit [HasWeakSheafify (Opens.grothendieckTopology ↑X) C] in
/-- Helper for Stacks 00AF/00AG: the right triangle identity for pullback and pushforward,
evaluated on sections of a pushed-forward sheaf. -/
private theorem subsetSheaf_counit_unit_section_eq
    (F : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X)
    (s : CC ((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).obj (op U))) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).1.app
        (op ((Opens.map sZ).obj U)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s) = s := by
  -- Evaluate the right triangle identity for the adjunction on the open `U`.
  change
    (((TopCat.Sheaf.pushforward C sZ).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F)).1.app (op U))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s) = s
  have h := congrArg (fun k ↦ (k.1.app (op U)))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).right_triangle_components F)
  change (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
          ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) ≫
        (((TopCat.Sheaf.pushforward C sZ).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F)).1.app (op U)) =
      𝟙 _ at h
  have hs := congrArg (fun k ↦ k s) h
  calc
    (((TopCat.Sheaf.pushforward C sZ).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F)).1.app (op U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
              ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)
      = (𝟙 ((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).obj (op U))) s := by
          simpa only [CategoryTheory.comp_apply] using hs
    _ = s := by
          exact ConcreteCategory.id_apply s

omit [HasWeakSheafify (Opens.grothendieckTopology ↑X) C] in
/-- Helper for Stacks 00AF/00AG: on stalks over points of the subset, the counit composite is the
standard stalk-pushforward map. -/
private theorem subsetSheaf_counit_stalk_comp_eq
    (F : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) :
    (TopCat.Sheaf.stalkPullbackIso sZ ((TopCat.Sheaf.pushforward C sZ).obj F) z).hom ≫
      ((TopCat.Presheaf.stalkFunctor C z).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom) =
    F.presheaf.stalkPushforward C sZ z := by
  -- Compare the two maps by testing them on germs over neighborhoods of the image of `z`.
  apply TopCat.Presheaf.stalk_hom_ext (((TopCat.Sheaf.pushforward C sZ).obj F).presheaf)
  intro U hzU
  apply ConcreteCategory.hom_ext
  intro s
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  -- The sheaf stalk-pullback comparison turns the pushed-forward germ into a pullback germ.
  have hleft₁ :
      ((TopCat.Sheaf.stalkPullbackIso sZ ((TopCat.Sheaf.pushforward C sZ).obj F) z).hom)
          ((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).germ U (sZ z) hzU s) =
        ((((TopCat.Sheaf.pullback C sZ).obj ((TopCat.Sheaf.pushforward C sZ).obj F)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
                ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)) := by
    simpa using (sheaf_stalkPullbackIso_germ_apply (C := C)
      (f := sZ) (G := ((TopCat.Sheaf.pushforward C sZ).obj F))
      (U := U) (y := z) (hy := hzMap) (s := s))
  -- The unit followed by the counit is the identity on pushed-forward sections.
  have hsection :
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).1.app
          (op ((Opens.map sZ).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
              ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s) = s := by
    exact subsetSheaf_counit_unit_section_eq (C := C) (F := F) (U := U) (s := s)
  -- Mapping a germ through the counit applies the counit to the represented section.
  have hleft₂ :
      ((TopCat.Presheaf.stalkFunctor C z).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom)
        ((((TopCat.Sheaf.pullback C sZ).obj ((TopCat.Sheaf.pushforward C sZ).obj F)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
                ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)) =
        F.presheaf.germ ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).1.app
              (op ((Opens.map sZ).obj U)))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
                  ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)) := by
    simpa using (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map sZ).obj U) z hzMap
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
          ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s))
  -- The right side is the canonical stalk-pushforward computation for the subtype inclusion.
  have hright :
      ((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).germ U (sZ z) hzU ≫
        F.presheaf.stalkPushforward C sZ z) s =
      F.presheaf.germ ((Opens.map sZ).obj U) z hzMap s := by
    simpa [ConcreteCategory.comp_apply] using congrArg (fun k ↦ k s)
      (TopCat.Presheaf.stalkPushforward_germ C sZ F.presheaf U z hzU)
  calc
    (((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).germ U (sZ z) hzU ≫
        ((TopCat.Sheaf.stalkPullbackIso sZ ((TopCat.Sheaf.pushforward C sZ).obj F) z).hom ≫
          ((TopCat.Presheaf.stalkFunctor C z).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom))) s)
        = ((TopCat.Presheaf.stalkFunctor C z).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom)
        ((((TopCat.Sheaf.pullback C sZ).obj ((TopCat.Sheaf.pushforward C sZ).obj F)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)) := by
            rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
            rw [hleft₁]
            rfl
    _ = F.presheaf.germ ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).1.app
            (op ((Opens.map sZ).obj U)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((TopCat.Sheaf.pushforward C sZ).obj F)).1.app (op U)) s)) := hleft₂
    _ = F.presheaf.germ ((Opens.map sZ).obj U) z hzMap s := by
          rw [hsection]
    _ = (((((TopCat.Sheaf.pushforward C sZ).obj F).presheaf).germ U (sZ z) hzU ≫
          F.presheaf.stalkPushforward C sZ z) s) := by
          symm
          exact hright

omit [HasWeakSheafify (Opens.grothendieckTopology ↑X) C] in
/-- Helper for Stacks 00AF/00AG: the stalk map of the counit at a point of the subset is an
isomorphism. -/
private theorem subsetSheaf_counit_stalk_map_isIso
    (F : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) :
    IsIso (((TopCat.Presheaf.stalkFunctor C z).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom)) := by
  let e := TopCat.Sheaf.stalkPullbackIso sZ ((TopCat.Sheaf.pushforward C sZ).obj F) z
  -- The subtype inclusion is inducing, so the standard stalk-pushforward map is an isomorphism.
  have hpush : IsIso (F.presheaf.stalkPushforward C sZ z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      C Topology.IsInducing.subtypeVal F.presheaf z
  -- The previous composite computation identifies the counit stalk map with this isomorphism.
  have hEq :
      ((TopCat.Presheaf.stalkFunctor C z).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom) =
        e.inv ≫ F.presheaf.stalkPushforward C sZ z := by
    apply (cancel_epi e.hom).1
    have hcomp :
        e.hom ≫ ((TopCat.Presheaf.stalkFunctor C z).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app F).hom) =
          F.presheaf.stalkPushforward C sZ z := by
      simpa [e] using subsetSheaf_counit_stalk_comp_eq (C := C) (F := F) z
    simpa [hcomp]
  rw [hEq]
  exact CategoryTheory.IsIso.comp_isIso' (inferInstance : IsIso e.inv) hpush

end

omit [HasWeakSheafify (Opens.grothendieckTopology ↑X) C] in
/-- The counit `i⁻¹ i_* ⟶ 𝟭` of the pullback–pushforward adjunction along a subset inclusion
`i = subsetInclusion X Z` is an isomorphism.

This is the substantive content of the full-faithfulness half of Stacks 00AF/00AG: the counit is
checked stalkwise, and at a point of `Z` the resulting map is identified with the standard
`stalkPushforward` map for the inducing map `Subtype.val`. -/
theorem subsetSheafPushforward_counit_isIso (Z : Set X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C (X.subsetInclusion Z)).counit :=
  by
    -- The source proof's `i^{-1} i_* = id` is realized by checking the counit on every stalk.
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro z
    exact subsetSheaf_counit_stalk_map_isIso (C := C) (Z := Z) (F := F) z

/-- For the inclusion `i : Z → X` of a subset
(in particular a closed subset), the sheaf pushforward `i_* : Sh(Z) ⥤ Sh(X)` is fully faithful.

This is the upstream owner recalled by Lemma 6.32.2 (sheaves of sets) and Lemma 6.32.3 (sheaves of
abelian groups). It is constructed as the right adjoint of the pullback–pushforward adjunction
together with the invertibility of the counit (`subsetSheafPushforward_counit_isIso`); the
`FullyFaithful` datum is just the formal consequence. -/
noncomputable def subsetSheafPushforward_fullyFaithful (Z : Set X) :
    (TopCat.Sheaf.pushforward C (X.subsetInclusion Z)).FullyFaithful :=
  letI := subsetSheafPushforward_counit_isIso (C := C) Z
  (TopCat.Sheaf.pullbackPushforwardAdjunction C (X.subsetInclusion Z)).fullyFaithfulROfIsIsoCounit

end SubsetSheafPushforward
