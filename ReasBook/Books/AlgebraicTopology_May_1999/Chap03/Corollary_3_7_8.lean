/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Proposition_3_3_4
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_6
import AlgebraicTopology_May_1999.Chap03.Theorem_3_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open CategoryTheory.Functor.IsCovering
open scoped FundamentalGroup

universe u

namespace IsPathConnectedCoveringMap

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {p' : C(E', B)}

/-- The induced morphism on fundamental groupoids of a morphism of covering spaces over `B`. -/
noncomputable def fundamentalGroupoidMapHom
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    Cat.of (FundamentalGroupoid E) ⟶ Cat.of (FundamentalGroupoid E') :=
  (FundamentalGroupoid.map h.left.hom).toCatHom

/-- A path-connected covering space over `B`, viewed as the induced functor over `Π(B)`. -/
noncomputable def toFundamentalGroupoidCovering (hp : IsPathConnectedCoveringMap p) :
    Over (Cat.of (FundamentalGroupoid B)) :=
  Over.mk hp.fundamentalGroupoidMap.toCatHom

/-- The induced morphism on fundamental groupoids from a morphism of covering spaces over `B`
commutes with the covering projections to `Π(B)`. -/
-- Proof sketch: apply `TopCat.Hom.hom` to the commutative triangle `Over.w h`, then use the
-- functoriality of `FundamentalGroupoid.map` and finally pass to `Cat` via `Functor.toCatHom`.
theorem fundamentalGroupoidMapHom_comm
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    fundamentalGroupoidMapHom h ≫ hp'.fundamentalGroupoidMap.toCatHom =
      hp.fundamentalGroupoidMap.toCatHom := by
  -- First rewrite the over-category commutative triangle as an equality of continuous maps.
  have hcomm : p'.comp h.left.hom = p := by
    ext x
    have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hx
  have hcomp :
      fundamentalGroupoidMapHom h ≫ hp'.fundamentalGroupoidMap.toCatHom =
        (FundamentalGroupoid.map (p'.comp h.left.hom)).toCatHom := by
    -- Functoriality of `FundamentalGroupoid.map` turns composition of maps into composition of functors.
    simpa [fundamentalGroupoidMapHom, IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg Functor.toCatHom (FundamentalGroupoid.map_comp p' h.left.hom).symm
  have hmap :
      (FundamentalGroupoid.map (p'.comp h.left.hom)).toCatHom =
        hp.fundamentalGroupoidMap.toCatHom := by
    -- Replacing `p' ∘ h` by `p` finishes the comparison on the base groupoid.
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg Functor.toCatHom (congrArg FundamentalGroupoid.map hcomm)
  exact hcomp.trans hmap

/-- A morphism of covering spaces over `B` induces a morphism of the associated coverings over
`Π(B)`. -/
noncomputable def toFundamentalGroupoidCoveringHom
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    hp.toFundamentalGroupoidCovering ⟶ hp'.toFundamentalGroupoidCovering :=
  Over.homMk (fundamentalGroupoidMapHom h) (fundamentalGroupoidMapHom_comm hp hp' h)

/-- Helper for Corollary 3.7.8: when the target basepoint is definitionally unchanged, the
fundamental-group map agrees with `mapOfEq`. -/
private theorem fundamental_group_map_eq_mapOfEq_rfl_local {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- Reduce both descriptions to the same formula on loop representatives.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Corollary 3.7.8: membership in the topological image subgroup at the chosen source
basepoint implies membership in the corresponding transported categorical subgroup. -/
private theorem fundamental_groupoid_source_mem_of_mapOfEq_mem
    (hp : IsPathConnectedCoveringMap p) (e₀ : E)
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ (FundamentalGroup.mapOfEq p rfl).range) :
    let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
      ⟨FundamentalGroupoid.mk e₀, rfl⟩
    γ ∈ ξ.2 ▸ (hp.fundamentalGroupoidMap.mapVertexGroup ξ.1).range := by
  -- Rewrite transported membership to the literal basepoint and use the same loop witness.
  dsimp
  have hγ' :
      eqToHom rfl ≫ γ ≫ eqToHom rfl.symm ∈
        (hp.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk e₀)).range := by
    rcases MonoidHom.mem_range.mp hγ with ⟨δ, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨δ, by
      change ((FundamentalGroupoid.map p).mapVertexGroup (FundamentalGroupoid.mk e₀)) δ =
        eqToHom rfl ≫ (FundamentalGroup.mapOfEq p rfl) δ ≫ eqToHom rfl.symm
      rw [← fundamental_group_map_eq_mapOfEq_rfl_local (f := p) (x := e₀)]
      simp⟩
  exact
    (mapVertexGroup_range_transport_iff
      (p := hp.fundamentalGroupoidMap) (e := FundamentalGroupoid.mk e₀) (h := rfl) γ).2 hγ'

/-- Helper for Corollary 3.7.8: membership in the transported categorical subgroup at a target
fiber point implies membership in the topological image subgroup at the corresponding lifted point.
-/
private theorem mapOfEq_mem_of_fundamental_groupoid_target_mem
    (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ ξ'.2 ▸ (hp'.fundamentalGroupoidMap.mapVertexGroup ξ'.1).range) :
    γ ∈ (FundamentalGroup.mapOfEq p'
      (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  -- Unpack the categorical fiber point and conjugate the witness through the transport equality.
  rcases ξ' with ⟨⟨x⟩, hx⟩
  have hx' : p' x = p e₀ := by
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using congrArg FundamentalGroupoid.as hx
  have hγ' :
      eqToHom hx ≫ γ ≫ eqToHom hx.symm ∈
        (hp'.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk x)).range := by
    exact
      (mapVertexGroup_range_transport_iff
        (p := hp'.fundamentalGroupoidMap) (e := FundamentalGroupoid.mk x) (h := hx) γ).1 hγ
  rcases MonoidHom.mem_range.mp hγ' with ⟨δ, hδ⟩
  refine MonoidHom.mem_range.mpr ⟨δ, ?_⟩
  have hmk : congrArg FundamentalGroupoid.mk hx' = hx := by
    apply Subsingleton.elim
  change eqToHom (congrArg FundamentalGroupoid.mk hx').symm ≫
      (hp'.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk x)) δ ≫
      eqToHom (congrArg FundamentalGroupoid.mk hx') = γ
  rw [hmk]
  simpa [Category.assoc] using congrArg (fun η ↦ eqToHom hx.symm ≫ η ≫ eqToHom hx) hδ

/-- Helper for Corollary 3.7.8: the subgroup inclusion produced by the covering-groupoid lift
criterion rewrites to the corresponding inclusion on ordinary fundamental groups at the matching
topological fiber point. -/
theorem subgroup_condition_topological_of_groupoid
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (k : Over.mk hp.fundamentalGroupoidMap.toCatHom ⟶ Over.mk hp'.fundamentalGroupoidMap.toCatHom)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (hξ : ξ'.1 = k.left.toFunctor.obj (FundamentalGroupoid.mk e₀)) :
    (FundamentalGroup.mapOfEq p rfl).range ≤
      (FundamentalGroup.mapOfEq p' (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
    ⟨FundamentalGroupoid.mk e₀, rfl⟩
  have hk :
      k.left.toFunctor ⋙ hp'.fundamentalGroupoidMap = hp.fundamentalGroupoidMap := by
    -- The over-category relation says the induced functors commute with the projection to `Π(B)`.
    simpa using congrArg (fun F ↦ F.toFunctor) (Over.w k)
  have hsub_groupoid :
      ξ.2 ▸ (hp.fundamentalGroupoidMap.mapVertexGroup ξ.1).range ≤
        ξ'.2 ▸ (hp'.fundamentalGroupoidMap.mapVertexGroup ξ'.1).range := by
    -- Apply the covering-groupoid lifting criterion at the chosen source point `ξ`.
    simpa [ξ, hξ] using
      (Functor.mapVertexGroup_range_le_of_lift
        (p := hp'.fundamentalGroupoidMap) (f := hp.fundamentalGroupoidMap)
        (g := k.left.toFunctor) ξ.1 ξ' hk hξ.symm)
  intro γ hγ
  have hγ_source :
      γ ∈ ξ.2 ▸ (hp.fundamentalGroupoidMap.mapVertexGroup ξ.1).range :=
    fundamental_groupoid_source_mem_of_mapOfEq_mem hp e₀ γ hγ
  have hγ_target :
      γ ∈ ξ'.2 ▸ (hp'.fundamentalGroupoidMap.mapVertexGroup ξ'.1).range :=
    hsub_groupoid hγ_source
  -- Convert the transported categorical target membership back into the topological subgroup.
  exact mapOfEq_mem_of_fundamental_groupoid_target_mem hp' e₀ ξ' γ hγ_target

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- Corollary 3.7.8: the fundamental groupoid functor induces a bijection between morphisms of
covering spaces over `B` and morphisms of the induced covering functors over `Π(B)`. -/
-- Proof sketch: map a covering-space morphism `h` to `toFundamentalGroupoidCoveringHom hp hp' h`.
-- For any chosen `e : E`, both Theorem 3.7.6 and Theorem 3.5.6 classify morphisms sending `e` to
-- a prescribed point of the target fiber by the same subgroup-inclusion condition, using
-- Proposition 3.3.4 to view `hp.fundamentalGroupoidMap` and `hp'.fundamentalGroupoidMap` as
-- covering functors. Hence the induced map on morphism sets is both injective and surjective.
theorem toFundamentalGroupoidCoveringHom_bijective
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') :
    Function.Bijective (toFundamentalGroupoidCoveringHom hp hp') := by
  constructor
  · intro h₁ h₂ hk
    apply Over.OverMorphism.ext
    ext x
    -- Equality of induced groupoid maps forces equality on every object `mk x`.
    have hobj :
        (toFundamentalGroupoidCoveringHom hp hp' h₁).left.toFunctor.obj
            (FundamentalGroupoid.mk x) =
          (toFundamentalGroupoidCoveringHom hp hp' h₂).left.toFunctor.obj
            (FundamentalGroupoid.mk x) := by
      simpa using
        congrArg
          (fun k : hp.toFundamentalGroupoidCovering ⟶ hp'.toFundamentalGroupoidCovering ↦
            k.left.toFunctor.obj (FundamentalGroupoid.mk x))
          hk
    exact congrArg FundamentalGroupoid.as hobj
  · intro k
    -- Work at one chosen point of the source cover and compare the two classification theorems there.
    letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
      refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
      intro α F x y
      ext
      exact CategoryTheory.Discrete.eq_of_hom <|
        F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
    obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
    let e : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩
    let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
      ⟨FundamentalGroupoid.mk e₀, rfl⟩
    let ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) := by
      refine ⟨k.left.toFunctor.obj ξ.1, ?_⟩
      -- The over-category relation for `k` shows that the image still lies over `mk (p e₀)`.
      have hobj := congrArg
        (fun F : FundamentalGroupoid E ⥤ FundamentalGroupoid B ↦ F.obj ξ.1)
        (congrArg (fun F => F.toFunctor) (Over.w k))
      exact hobj
    let e' : p' ⁻¹' {p e₀} := hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ'
    have hsub_groupoid :=
      -- The given morphism of covering functors is already a lift, so it yields the subgroup inclusion.
      Functor.mapVertexGroup_range_le_of_lift
        (p := hp'.fundamentalGroupoidMap) (f := hp.fundamentalGroupoidMap)
        (g := k.left.toFunctor) ξ.1 ξ' (by
          exact congrArg (fun F => F.toFunctor) (Over.w k)) rfl
    rcases
        (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
          hp hp' (p e₀) e e').mpr
          (subgroup_condition_topological_of_groupoid hp hp' e₀ k ξ' (by
            change k.left.toFunctor.obj ξ.1 = k.left.toFunctor.obj (FundamentalGroupoid.mk e₀)
            simpa [ξ])) with
      ⟨h, hh, _⟩
    refine ⟨h, ?_⟩
    have hξ' : FundamentalGroupoid.mk e'.1 = ξ'.1 := by
      -- Re-expanding the fiber equivalence identifies the target categorical point with `ξ'`.
      have hξ'_eq :
          (hp'.fundamentalGroupoidMapFiberEquiv (p e₀)).symm e' = ξ' := by
        simpa [e']
      exact congrArg Subtype.val hξ'_eq
    have hh_groupoid :
        (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor.obj ξ.1 = ξ'.1 := by
      -- The constructed topological map hits the prescribed fiber point, so its induced functor does too.
      have hh_to_target :
          (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor.obj ξ.1 =
            FundamentalGroupoid.mk e'.1 := by
        change FundamentalGroupoid.mk (h.left.hom e.1) = FundamentalGroupoid.mk e'.1
        exact congrArg FundamentalGroupoid.mk hh
      exact hh_to_target.trans hξ'
    rcases
        (existsUnique_map_iff_mapVertexGroup_range_le
          (p := hp.fundamentalGroupoidMap) (p' := hp'.fundamentalGroupoidMap)
          hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e₀)) ξ ξ').mpr
          (by simpa using hsub_groupoid) with
      ⟨g, hg, huniqg⟩
    have hk_eq : k = g := huniqg k (by simpa [ξ'] using rfl)
    have hh_eq : toFundamentalGroupoidCoveringHom hp hp' h = g := by
      exact huniqg _ (by simpa using hh_groupoid)
    exact hh_eq.trans hk_eq.symm

end

end IsPathConnectedCoveringMap
