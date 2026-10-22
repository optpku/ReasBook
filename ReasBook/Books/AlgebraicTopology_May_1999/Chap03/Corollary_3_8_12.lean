/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import AlgebraicTopology_May_1999.Chap03.Corollary_3_7_8
import AlgebraicTopology_May_1999.Chap03.Lemma_3_8_11
import AlgebraicTopology_May_1999.Chap03.Theorem_3_6_1
import AlgebraicTopology_May_1999.Chap03.Theorem_3_8_2
import AlgebraicTopology_May_1999.Chap03.Construction_3_6_3
import AlgebraicTopology_May_1999.Chap03.Lemma_3_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open FundamentalGroupoid
open CategoryTheory.Groupoid.CategoryTheory

variable {B : Type u} [TopologicalSpace B]

namespace FundamentalGroupoid

/-- The fundamental groupoid of a path-connected space is connected. -/
theorem isConnected
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    CategoryTheory.IsConnected (FundamentalGroupoid X) := by
  refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
  intro α F x y
  ext
  exact CategoryTheory.Discrete.eq_of_hom <|
    F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)

end FundamentalGroupoid

namespace ConnectedCoveringSpace

/-- The fundamental groupoid of the total space of a connected covering space is connected. -/
theorem fundamentalGroupoid_isConnected (X : ConnectedCoveringSpace B) :
    CategoryTheory.IsConnected (FundamentalGroupoid X.obj.left) := by
  letI := X.pathConnectedSpace
  exact FundamentalGroupoid.isConnected X.obj.left

/-- A connected covering space over `B`, viewed as a connected covering functor over `Π(B)`. -/
noncomputable def toFundamentalGroupoidCovering (X : ConnectedCoveringSpace B) :
    ConnectedCovering (FundamentalGroupoid B) :=
  ⟨{ left := FundamentalGroupoid X.obj.left
      , groupoid_left := inferInstance,
      hom := X.isPathConnectedCoveringMap.fundamentalGroupoidMap },
    ⟨X.isPathConnectedCoveringMap.fundamentalGroupoidMap_isCovering,
      fundamentalGroupoid_isConnected X⟩⟩

private theorem fundamentalGroupoidMapHom_comm {X Y : ConnectedCoveringSpace B} (f : X ⟶ Y) :
    FundamentalGroupoid.map (TopCat.Hom.hom f.hom.left) ⋙
      Y.isPathConnectedCoveringMap.fundamentalGroupoidMap =
        X.isPathConnectedCoveringMap.fundamentalGroupoidMap := by
  simpa using congrArg (fun F ↦ F.toFunctor) <|
    IsPathConnectedCoveringMap.fundamentalGroupoidMapHom_comm
      X.isPathConnectedCoveringMap Y.isPathConnectedCoveringMap f.hom

/-- A morphism of covering spaces over `B` induces a morphism of the associated connected
coverings over `Π(B)`. -/
noncomputable def toFundamentalGroupoidCoveringHom {X Y : ConnectedCoveringSpace B} (f : X ⟶ Y) :
    toFundamentalGroupoidCovering X ⟶ toFundamentalGroupoidCovering Y :=
  ObjectProperty.homMk <|
    GroupoidFunctorOver.homMk
      (show (toFundamentalGroupoidCovering X).obj.left ⥤
          (toFundamentalGroupoidCovering Y).obj.left from
        FundamentalGroupoid.map (TopCat.Hom.hom f.hom.left))
      (fundamentalGroupoidMapHom_comm f)

/-- The induced morphism on connected fundamental-groupoid coverings is the identity on identity
maps. -/
-- Proof sketch: `FundamentalGroupoid.map` sends identity continuous maps to identity functors, so
-- the resulting morphism of connected coverings is the identity.
theorem toFundamentalGroupoidCoveringHom_id (X : ConnectedCoveringSpace B) :
    toFundamentalGroupoidCoveringHom (𝟙 X) = 𝟙 (toFundamentalGroupoidCovering X) := by
  apply ObjectProperty.hom_ext
  apply GroupoidFunctorOver.Hom.ext
  -- Rewrite the owner-level identity to the literal identity functor on `Π(X)`.
  change FundamentalGroupoid.map (ContinuousMap.id X.obj.left) = 𝟭 (FundamentalGroupoid X.obj.left)
  exact FundamentalGroupoid.map_id (X := X.obj.left)

/-- The induced morphism on connected fundamental-groupoid coverings respects composition. -/
-- Proof sketch: this is functoriality of `FundamentalGroupoid.map`, rewritten in the canonical
-- owner category `ConnectedCovering (Π(B))`.
theorem toFundamentalGroupoidCoveringHom_comp {X Y Z : ConnectedCoveringSpace B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    toFundamentalGroupoidCoveringHom (f ≫ g) =
      toFundamentalGroupoidCoveringHom f ≫ toFundamentalGroupoidCoveringHom g := by
  apply ObjectProperty.hom_ext
  apply GroupoidFunctorOver.Hom.ext
  -- Rewrite to the raw functoriality statement for `FundamentalGroupoid.map`.
  change
    FundamentalGroupoid.map ((TopCat.Hom.hom g.hom.left).comp (TopCat.Hom.hom f.hom.left)) =
      FundamentalGroupoid.map (TopCat.Hom.hom f.hom.left) ⋙
        FundamentalGroupoid.map (TopCat.Hom.hom g.hom.left)
  exact FundamentalGroupoid.map_comp (TopCat.Hom.hom g.hom.left) (TopCat.Hom.hom f.hom.left)

/-- The functor sending a connected covering space over `B` to its induced connected covering
functor over the fundamental groupoid `Π(B)`. -/
noncomputable def fundamentalGroupoidFunctor :
    ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B) where
  obj X := toFundamentalGroupoidCovering X
  map {_ _} f := toFundamentalGroupoidCoveringHom f
  map_id X := toFundamentalGroupoidCoveringHom_id X
  map_comp f g := toFundamentalGroupoidCoveringHom_comp f g

/-- Helper for Corollary 3.8.12: forgetting a morphism of connected coverings of `Π(B)` to the
underlying over-morphism in `Cat` keeps exactly the same functor data. -/
private theorem connectedCoveringHomToOver_comm
    {X Y : ConnectedCovering (FundamentalGroupoid B)} (f : X ⟶ Y) :
    f.hom.left.toCatHom ≫ Y.obj.hom.toCatHom = X.obj.hom.toCatHom := by
  -- The over-category commutativity is already packaged in the connected-covering morphism.
  simpa using congrArg Functor.toCatHom f.hom.comm

/-- Helper for Corollary 3.8.12: forgetting a morphism of connected coverings of `Π(B)` to the
underlying over-morphism in `Cat` keeps exactly the same functor data. -/
private noncomputable def connectedCoveringHomToOver
    {X Y : ConnectedCovering (FundamentalGroupoid B)} (f : X ⟶ Y) :
    Over.mk X.obj.hom.toCatHom ⟶ Over.mk Y.obj.hom.toCatHom :=
  Over.homMk f.hom.left.toCatHom (connectedCoveringHomToOver_comm f)

/-- Helper for Corollary 3.8.12: forgetting to `Over (Cat.of Π(B))` is injective on morphisms of
connected coverings. -/
private theorem connectedCoveringHomToOver_injective
    {X Y : ConnectedCovering (FundamentalGroupoid B)} :
    Function.Injective (@connectedCoveringHomToOver B _ X Y) := by
  intro f g h
  apply ObjectProperty.hom_ext
  apply GroupoidFunctorOver.Hom.ext
  -- Equality in `Over` already identifies the underlying functors of the packaged morphisms.
  simpa using congrArg (fun k => k.left.toFunctor) h

/-- Helper for Corollary 3.8.12: the packaged morphism of connected coverings coincides with the
unpackaged `Over`-morphism used in Corollary 3.7.8. -/
private theorem connectedCoveringHomToOver_toFundamentalGroupoidCoveringHom
    {X Y : ConnectedCoveringSpace B} (f : X ⟶ Y) :
    connectedCoveringHomToOver (toFundamentalGroupoidCoveringHom f) =
      IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom
        X.isPathConnectedCoveringMap Y.isPathConnectedCoveringMap f.hom := by
  -- Both constructions are the same morphism after forgetting from the full subcategory owner.
  apply Over.OverMorphism.ext
  rfl

/-- Helper for Corollary 3.8.12: Corollary 3.7.8 identifies maps of connected covering spaces
with maps of the induced coverings over `Π(B)`, so the induced map on hom-sets is injective. -/
private theorem toFundamentalGroupoidCoveringHom_injective [LocPathConnectedSpace B]
    {X Y : ConnectedCoveringSpace B} :
    Function.Injective (@toFundamentalGroupoidCoveringHom B _ X Y) := by
  intro f g hfg
  let pX : C(X.obj.left, B) := show C(X.obj.left, B) from X.obj.hom.hom
  let pY : C(Y.obj.left, B) := show C(Y.obj.left, B) from Y.obj.hom.hom
  have hpX : IsPathConnectedCoveringMap pX := by
    simpa [pX] using X.isPathConnectedCoveringMap
  have hpY : IsPathConnectedCoveringMap pY := by
    simpa [pY] using Y.isPathConnectedCoveringMap
  letI : LocPathConnectedSpace X.obj.left :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace hpX
  letI : LocPathConnectedSpace Y.obj.left :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace hpY
  have hbij :=
    IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom_bijective
      hpX hpY
  have hf :
      IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom hpX hpY f.hom =
        connectedCoveringHomToOver (toFundamentalGroupoidCoveringHom f) := by
    simpa [pX, pY] using
      (connectedCoveringHomToOver_toFundamentalGroupoidCoveringHom f).symm
  have hg :
      IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom hpX hpY g.hom =
        connectedCoveringHomToOver (toFundamentalGroupoidCoveringHom g) := by
    simpa [pX, pY] using
      (connectedCoveringHomToOver_toFundamentalGroupoidCoveringHom g).symm
  apply ObjectProperty.hom_ext
  apply hbij.1
  -- Forget to the owner used in Corollary 3.7.8, use injectivity there, and repackage back.
  exact hf.trans <| (congrArg connectedCoveringHomToOver hfg).trans hg.symm

/-- Helper for Corollary 3.8.12: Corollary 3.7.8 also shows that every morphism of induced
connected coverings over `Π(B)` comes from a morphism of the original covering spaces. -/
private theorem toFundamentalGroupoidCoveringHom_surjective [LocPathConnectedSpace B]
    {X Y : ConnectedCoveringSpace B} :
    Function.Surjective (@toFundamentalGroupoidCoveringHom B _ X Y) := by
  intro F
  let pX : C(X.obj.left, B) := show C(X.obj.left, B) from X.obj.hom.hom
  let pY : C(Y.obj.left, B) := show C(Y.obj.left, B) from Y.obj.hom.hom
  have hpX : IsPathConnectedCoveringMap pX := by
    simpa [pX] using X.isPathConnectedCoveringMap
  have hpY : IsPathConnectedCoveringMap pY := by
    simpa [pY] using Y.isPathConnectedCoveringMap
  letI : LocPathConnectedSpace X.obj.left :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace hpX
  letI : LocPathConnectedSpace Y.obj.left :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace hpY
  have hbij :=
    IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom_bijective
      hpX hpY
  let K := connectedCoveringHomToOver F
  rcases hbij.2 K with ⟨h, hh⟩
  have hh' :
      connectedCoveringHomToOver (toFundamentalGroupoidCoveringHom (ObjectProperty.homMk h)) =
        IsPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom hpX hpY h := by
    simpa [pX, pY] using
      connectedCoveringHomToOver_toFundamentalGroupoidCoveringHom (ObjectProperty.homMk h)
  refine ⟨ObjectProperty.homMk h, ?_⟩
  apply connectedCoveringHomToOver_injective
  -- Surjectivity in Corollary 3.7.8 lifts the underlying over-morphism, then we repackage it.
  exact hh'.trans (hh.trans rfl)

/-- Helper for Corollary 3.8.12: Corollary 3.7.8 identifies maps of connected covering spaces
with maps of the induced coverings over `Π(B)`, so `Π` is faithful. -/
private theorem fundamentalGroupoidFunctor_faithful [LocPathConnectedSpace B] :
    (fundamentalGroupoidFunctor :
      ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)).Faithful := by
  -- Package the explicit hom-set injectivity above as categorical faithfulness.
  refine { map_injective := ?_ }
  intro X Y f g hfg
  exact toFundamentalGroupoidCoveringHom_injective (B := B) hfg

/-- Helper for Corollary 3.8.12: the same morphism bijection makes `Π` full. -/
private theorem fundamentalGroupoidFunctor_full [LocPathConnectedSpace B] :
    (fundamentalGroupoidFunctor :
      ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)).Full := by
  -- Package the explicit hom-set surjectivity above as categorical fullness.
  refine { map_surjective := ?_ }
  intro X Y F
  exact toFundamentalGroupoidCoveringHom_surjective (B := B) F

/-- Helper for Corollary 3.8.12: the ordinary based image subgroup of a path-connected covering
agrees with the image of the corresponding vertex-group map on the induced fundamental groupoid
covering. -/
private theorem mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range
    {E : Type u} [TopologicalSpace E] {p : C(E, B)}
    (hp : IsPathConnectedCoveringMap p) (e : E) (γ : FundamentalGroup B (p e)) :
    γ ∈ (FundamentalGroup.map p e).range ↔
      γ.toPath ∈
        (Groupoid.CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap
          (FundamentalGroupoid.mk e)).range := by
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ.toPath, rfl⟩
  · rintro ⟨δ, hδ⟩
    refine ⟨FundamentalGroup.fromPath δ, ?_⟩
    simpa using hδ

/-- Helper for Corollary 3.8.12: after passing the quotient covering `E / H → B` to fundamental
groupoids, the image of the upstairs vertex group at the canonical orbit point is still exactly
the subgroup `H`. -/
private theorem universal_cover_orbit_mapVertexGroup_range_eq_subgroup
    {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}
    (hp : IsUniversalCoveringMap p) (e : E) (H : O(FundamentalGroup B (p e))) :
    let hpH := ((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e).obj H).isPathConnectedCoveringMap
    loopSubgroupToEndSubgroup (FundamentalGroupoid.mk (p e))
      (Groupoid.CategoryTheory.Functor.mapVertexGroup
        (IsPathConnectedCoveringMap.fundamentalGroupoidMap hpH)
        (FundamentalGroupoid.mk (IsUniversalCoveringMap.universalCoverOrbitPoint hp e H))).range =
        (H : Subgroup (FundamentalGroup B (p e))) := by
  dsimp only
  ext γ
  -- Convert the vertex-group statement back to the ordinary based fundamental-group image.
  exact
    (mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range
      (hp := ((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e).obj H).isPathConnectedCoveringMap)
      (e := IsUniversalCoveringMap.universalCoverOrbitPoint hp e H)
      (γ := γ)).symm.trans <| by
        -- Lemma 3.8.11 computes that ordinary subgroup at the canonical orbit point.
        change γ ∈ (FundamentalGroup.map
          (IsUniversalCoveringMap.universalCoverOrbitProjection hp e H)
          (IsUniversalCoveringMap.universalCoverOrbitPoint hp e H)).range ↔ γ ∈ H
        rw [IsUniversalCoveringMap.universalCoverOrbitProjection_associatedSubgroup_eq hp e H]
        rfl

/-- Helper for Corollary 3.8.12: the orbit-model cover over `Π(B)` realizes the subgroup `H`
at its canonical identity-class basepoint. -/
private theorem orbit_model_mapVertexGroup_range_eq_subgroup
    [CategoryTheory.IsConnected (FundamentalGroupoid B)]
    (b : FundamentalGroupoid B) (H : O(End b)) :
    loopSubgroupToEndSubgroup b
      (Groupoid.CategoryTheory.Functor.mapVertexGroup
        ((orbitCategoryToConnectedCovering b).obj H).obj.hom
        (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) (𝟙 b))).range =
        (H : Subgroup (End b)) := by
  ext γ
  -- Unfold the orbit-cover model just enough to reuse the standard basepoint classifier.
  simpa [orbitCategoryToConnectedCovering] using
    orbitCategoryAssociatedAction_basepoint_mem_mapVertexGroup_range_iff_mem (b := b) H γ

/-- Helper for Corollary 3.8.12: once two chosen fiber points over the same base object realize
the same subgroup `H`, the transported vertex-group classifiers are equal. -/
private theorem transport_mapVertexGroup_range_eq_of_eq_subgroup
    {X Y : ConnectedCovering (FundamentalGroupoid B)} {b : FundamentalGroupoid B}
    (ξ : X.obj.hom.Fiber b) (η : Y.obj.hom.Fiber b)
    (H : Subgroup (End b))
    (hξ : loopSubgroupToEndSubgroup b
      (ξ.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup X.obj.hom ξ.1).range) = H)
    (hη : loopSubgroupToEndSubgroup b
      (η.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup Y.obj.hom η.1).range) = H) :
    ξ.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup X.obj.hom ξ.1).range =
      η.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup Y.obj.hom η.1).range := by
  apply loopSubgroupToEndSubgroup_injective b
  exact hξ.trans hη.symm

/-- Helper for Corollary 3.8.12: for a fixed subgroup `H`, the quotient universal-cover model and
the orbit-model cover over `Π(B)` are isomorphic because they determine the same subgroup at the
same base object. -/
private noncomputable def universal_cover_orbit_groupoid_covering_iso_orbit_model
    {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}
    [CategoryTheory.IsConnected (FundamentalGroupoid B)]
    (hp : IsUniversalCoveringMap p) (e : E) (H : O(End (FundamentalGroupoid.mk (p e)))) :
    fundamentalGroupoidFunctor.obj
        ((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e).obj
          (show O(FundamentalGroup B (p e)) from H)) ≅
      (orbitCategoryToConnectedCovering (FundamentalGroupoid.mk (p e))).obj H := by
  classical
  let X : ConnectedCovering (FundamentalGroupoid B) :=
    fundamentalGroupoidFunctor.obj
      ((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e).obj
        (show O(FundamentalGroup B (p e)) from H))
  let Y : ConnectedCovering (FundamentalGroupoid B) :=
    (orbitCategoryToConnectedCovering (FundamentalGroupoid.mk (p e))).obj H
  let ξ : X.obj.hom.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk
        (IsUniversalCoveringMap.universalCoverOrbitPoint hp e
          (show O(FundamentalGroup B (p e)) from H)),
      rfl⟩
  let η : Y.obj.hom.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨orbitSubgroupCoveringObjOfHom
        (FundamentalGroupoid.mk (p e))
        (H : Subgroup (End (FundamentalGroupoid.mk (p e))))
        (𝟙 (FundamentalGroupoid.mk (p e))),
      rfl⟩
  let _ : CategoryTheory.IsConnected X.obj.left := ConnectedCovering.isConnected X
  let _ : IsPreconnected Y.obj.left := (ConnectedCovering.isConnected Y).toIsPreconnected
  have hsource :
      loopSubgroupToEndSubgroup (FundamentalGroupoid.mk (p e))
        (Groupoid.CategoryTheory.Functor.mapVertexGroup X.obj.hom ξ.1).range =
        (H : Subgroup (End (FundamentalGroupoid.mk (p e)))) := by
    -- The quotient-cover model keeps the same subgroup after applying `Π`.
    simpa [X, ξ] using
      universal_cover_orbit_mapVertexGroup_range_eq_subgroup hp e
        (show O(FundamentalGroup B (p e)) from H)
  have htarget :
      loopSubgroupToEndSubgroup (FundamentalGroupoid.mk (p e))
        (Groupoid.CategoryTheory.Functor.mapVertexGroup Y.obj.hom η.1).range =
        (H : Subgroup (End (FundamentalGroupoid.mk (p e)))) := by
    -- The orbit-cover model realizes `H` at the identity coset.
    simpa [Y, η] using orbit_model_mapVertexGroup_range_eq_subgroup
      (B := B) (FundamentalGroupoid.mk (p e)) H
  have hEq :
      ξ.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup X.obj.hom ξ.1).range =
        η.2 ▸ (Groupoid.CategoryTheory.Functor.mapVertexGroup Y.obj.hom η.1).range := by
    -- Both classifiers reduce to the same literal subgroup `H`.
    exact
      transport_mapVertexGroup_range_eq_of_eq_subgroup
        (X := X) (Y := Y) ξ η
        (H := (H : Subgroup (End (FundamentalGroupoid.mk (p e)))))
        hsource htarget
  have hex :=
    (CategoryTheory.Functor.IsCovering.existsUnique_map_iff_mapVertexGroup_range_le
      (ConnectedCovering.isCovering Y)
      (FundamentalGroupoid.mk (p e))
      ξ η).2 hEq.le
  let h := Classical.choose hex
  have hex' := Classical.choose_spec hex
  let hh := hex'.1
  have hIso : IsIso h :=
    (CategoryTheory.Functor.IsCovering.isIso_map_iff_mapVertexGroup_range_eq
      (ConnectedCovering.isCovering X)
      (ConnectedCovering.isCovering Y)
      (FundamentalGroupoid.mk (p e))
      ξ η h hh).2 hEq
  -- Package the owner-level isomorphism into the full subcategory of connected coverings.
  let _ : IsIso h := hIso
  let h' : X.obj ⟶ Y.obj := GroupoidFunctorOver.homMk h.left.toFunctor
    (congrArg (fun F => F.toFunctor) (Over.w h))
  let i' : Y.obj ⟶ X.obj := GroupoidFunctorOver.homMk (inv h).left.toFunctor
    (congrArg (fun F => F.toFunctor) (Over.w (inv h)))
  let e' : X.obj ≅ Y.obj :=
    { hom := h'
      inv := i'
      hom_inv_id := by
        apply GroupoidFunctorOver.Hom.ext
        exact congrArg (fun k => k.left.toFunctor) (IsIso.hom_inv_id h)
      inv_hom_id := by
        apply GroupoidFunctorOver.Hom.ext
        exact congrArg (fun k => k.left.toFunctor) (IsIso.inv_hom_id h) }
  exact ObjectProperty.isoMk _ e'

/-- Helper for Corollary 3.8.12: after fixing a universal cover and basepoint, every connected
covering of `Π(B)` comes from the corresponding orbit object because the orbit-model cover and the
universal-cover quotient realize the same subgroup at the chosen basepoint. -/
private theorem universal_cover_orbit_comp_essSurj
    [ConnectedSpace B] [LocPathConnectedSpace B]
    {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}
    (hp : IsUniversalCoveringMap p) (e : E) :
    (((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) ⋙
        fundamentalGroupoidFunctor :
          O(FundamentalGroup B (p e)) ⥤ ConnectedCovering (FundamentalGroupoid B))).EssSurj := by
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace (X := B)
  let b : FundamentalGroupoid B := FundamentalGroupoid.mk (p e)
  let _ : CategoryTheory.IsConnected (FundamentalGroupoid B) := FundamentalGroupoid.isConnected B
  let _ : Functor.IsEquivalence (orbitCategoryToConnectedCovering b) :=
    orbitCategoryToConnectedCovering_isEquivalence (B := FundamentalGroupoid B) (b := b)
  let _ : (orbitCategoryToConnectedCovering b).EssSurj := inferInstance
  refine { mem_essImage := ?_ }
  intro Y
  rcases (inferInstance : (orbitCategoryToConnectedCovering b).EssSurj).mem_essImage Y with
    ⟨H, ⟨iY⟩⟩
  let H' : O(FundamentalGroup B (p e)) := show O(FundamentalGroup B (p e)) from H
  have hcompare :
      ((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) ⋙
          fundamentalGroupoidFunctor).obj H' ≅
        (orbitCategoryToConnectedCovering b).obj H := by
    -- Compare the two source-faithful orbit realizations at the literal owner `End b`.
    simpa [Functor.comp_obj, b] using
      universal_cover_orbit_groupoid_covering_iso_orbit_model
        (B := B) hp e H
  -- Compose the objectwise comparison with essential surjectivity of the orbit-model equivalence.
  exact ⟨H', ⟨hcompare ≪≫ iY⟩⟩

/-- Helper for Corollary 3.8.12: once the universal-cover orbit functor is fixed, the comparison
functor to connected coverings of `Π(B)` is an equivalence because it is full, faithful, and the
source-faithful orbit comparison above is essentially surjective. -/
private theorem universal_cover_orbit_comp_isEquivalence
    [ConnectedSpace B] [LocPathConnectedSpace B]
    {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Functor.IsEquivalence
      (((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) ⋙
          fundamentalGroupoidFunctor :
            O(FundamentalGroup B (p e)) ⥤ ConnectedCovering (FundamentalGroupoid B))) := by
  let _ : Functor.IsEquivalence (IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) :=
    IsUniversalCoveringMap.universalCoverOrbitFunctor_isEquivalence hp e
  let _ : (fundamentalGroupoidFunctor :
      ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)).Faithful :=
    fundamentalGroupoidFunctor_faithful (B := B)
  let _ : (fundamentalGroupoidFunctor :
      ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)).Full :=
    fundamentalGroupoidFunctor_full (B := B)
  let _ :
      (((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) ⋙
          fundamentalGroupoidFunctor :
            O(FundamentalGroup B (p e)) ⥤ ConnectedCovering (FundamentalGroupoid B))).EssSurj :=
    universal_cover_orbit_comp_essSurj (B := B) hp e
  -- The composite functor is now certified by its three standard equivalence components.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Corollary 3.8.12: after fixing a universal cover and a point above the chosen
base object, cancel the known orbit-category equivalence on the left to conclude that `Π`
itself is an equivalence. -/
private theorem fundamentalGroupoidFunctor_isEquivalence_of_universalCover
    [ConnectedSpace B] [LocPathConnectedSpace B]
    {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Functor.IsEquivalence
      (fundamentalGroupoidFunctor :
        ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)) := by
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace (X := B)
  let _ : CategoryTheory.IsConnected (FundamentalGroupoid B) :=
    FundamentalGroupoid.isConnected B
  let _ : Functor.IsEquivalence (IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) :=
    IsUniversalCoveringMap.universalCoverOrbitFunctor_isEquivalence hp e
  let _ :
      Functor.IsEquivalence
        (((IsUniversalCoveringMap.universalCoverOrbitFunctor hp e) ⋙
            fundamentalGroupoidFunctor :
              O(FundamentalGroup B (p e)) ⥤ ConnectedCovering (FundamentalGroupoid B))) :=
    universal_cover_orbit_comp_isEquivalence (B := B) hp e
  -- Route correction: isolate the orbit-category cancellation step so the main corollary only
  -- has to choose the universal cover and its basepoint.
  simpa using
    (Functor.isEquivalence_of_comp_left
      (IsUniversalCoveringMap.universalCoverOrbitFunctor hp e)
      fundamentalGroupoidFunctor :
        Functor.IsEquivalence fundamentalGroupoidFunctor)

/-- Corollary 3.8.12: the functor from connected covering spaces over `B` to connected covering
functors over `Π(B)` induced by the fundamental groupoid construction is an equivalence of
categories. -/
-- Proof sketch: by Theorem 3.8.2 the hypotheses on `B` provide a universal covering.
-- Theorem 3.8.10 identifies `ConnectedCoveringSpace B` with the orbit category of `π₁(B, b)`,
-- while Theorem 3.6.1 identifies `ConnectedCovering (Π(B))` with the same orbit category. The
-- comparison functor above matches these two orbit-category realizations, so it is an
-- equivalence.
theorem fundamentalGroupoidFunctor_isEquivalence [ConnectedSpace B] [LocPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    Functor.IsEquivalence
      (fundamentalGroupoidFunctor :
        ConnectedCoveringSpace B ⥤ ConnectedCovering (FundamentalGroupoid B)) := by
  classical
  obtain ⟨X, hX⟩ := exists_universalCoveringMap (B := B)
  let E : Type u := X.left
  let _ : TopologicalSpace E := by infer_instance
  let p : C(E, B) := show C(E, B) from TopCat.Hom.hom X.hom
  have hp : IsUniversalCoveringMap p := by
    simpa [p] using hX
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace (X := B)
  obtain ⟨e, _⟩ := hp.surjective (Classical.choice (show Nonempty B from inferInstance))
  let _ : LocPathConnectedSpace E :=
    IsUniversalCoveringMap.IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
      hp.isPathConnectedCoveringMap
  -- Route correction: the main proof now stops after producing the universal cover, and the
  -- orbit-category cancellation itself is handled by the dedicated helper above.
  exact fundamentalGroupoidFunctor_isEquivalence_of_universalCover (B := B) hp e

end ConnectedCoveringSpace
