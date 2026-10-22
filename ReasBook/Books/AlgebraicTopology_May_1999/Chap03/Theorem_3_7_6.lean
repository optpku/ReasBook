/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5
import AlgebraicTopology_May_1999.Chap03.Definition_3_7_4
import AlgebraicTopology_May_1999.Chap03.Theorem_3_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FundamentalGroup
open CategoryTheory

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [PathConnectedSpace E] [LocPathConnectedSpace E]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)} {p' : C(E', B)}

/-- Helper for Theorem 3.7.6: when the target basepoint is definitionally unchanged, the ordinary
fundamental-group map agrees with `mapOfEq`. -/
private theorem fundamental_group_map_eq_map_of_eq_rfl {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- Reduce both maps to the same path-level representative formula.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Theorem 3.7.6: the induced map on fundamental groups respects composition of
continuous maps. -/
private theorem fundamental_group_map_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- On loop representatives, composition is definitionally functorial.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  rfl

/-- Helper for Theorem 3.7.6: `mapOfEq` also respects composition once the intermediate basepoint
is transported by an explicit equality. -/
private theorem fundamental_group_map_of_eq_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) :
    FundamentalGroup.mapOfEq (g.comp f) (by simpa [ContinuousMap.comp_apply, hf] using hg) =
      (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) := by
  -- First normalize all endpoint equalities to the definitional `rfl` case.
  cases hf
  cases hg
  let hy : g (f x) = g (f x) := rfl
  have hleft :
      FundamentalGroup.mapOfEq (g.comp f) hy = FundamentalGroup.map (g.comp f) x := by
    simpa [hy] using
      (fundamental_group_map_eq_map_of_eq_rfl (f := g.comp f) (x := x)).symm
  have hrightg : FundamentalGroup.mapOfEq g rfl = FundamentalGroup.map g (f x) := by
    simpa using
      (fundamental_group_map_eq_map_of_eq_rfl (f := g) (x := f x)).symm
  have hrightf : FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f x := by
    simpa using
      (fundamental_group_map_eq_map_of_eq_rfl (f := f) (x := x)).symm
  have hmain :
      FundamentalGroup.mapOfEq (g.comp f) hy =
        (FundamentalGroup.mapOfEq g rfl).comp (FundamentalGroup.map f x) := by
    -- Replace both `mapOfEq` terms by ordinary functorial maps and use composition.
    have hcomp :
        FundamentalGroup.mapOfEq (g.comp f) hy =
          (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) :=
      hleft.trans (fundamental_group_map_comp f g x)
    simpa [hrightg] using hcomp
  simpa [hrightf] using hmain

/-- Helper for Theorem 3.7.6: equal continuous maps induce the same `mapOfEq` after identifying
their endpoint proofs. -/
private theorem fundamental_group_map_of_eq_eq_of_eq {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (hfg : f = g) {x : X} {y : Y} (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Once the maps coincide, proof irrelevance identifies the endpoint transports.
  cases hfg
  exact congrArg (FundamentalGroup.mapOfEq f) (Subsingleton.elim _ _)

/-- Helper for Theorem 3.7.6: a morphism of covering spaces carrying `e` to `e'` forces the image
subgroup over the basepoint to be included in the target image subgroup. -/
private theorem fundamental_group_range_le_of_covering_space_hom
    {p : C(E, B)} {p' : C(E', B)}
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    (FundamentalGroup.mapOfEq p e.2).range ≤
      (FundamentalGroup.mapOfEq p' e'.2).range := by
  rcases e with ⟨e, he⟩
  rcases e' with ⟨e', he'⟩
  subst b
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine MonoidHom.mem_range.mpr ?_
  -- Push the chosen loop class forward along the map of coverings.
  refine ⟨(FundamentalGroup.mapOfEq h.left.hom hh) γ, ?_⟩
  have hbase : (p'.comp h.left.hom) e = p e := by
    simpa using (congrArg p' hh).trans he'
  have hcomp :
      FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase =
        (FundamentalGroup.mapOfEq p' he').comp
          (FundamentalGroup.mapOfEq h.left.hom hh) := by
    simpa [hbase] using
      fundamental_group_map_of_eq_comp h.left.hom p' hh he'
  have hcomm : p'.comp h.left.hom = p := by
    -- The over-category commutative triangle says exactly `p' ∘ h = p`.
    ext y
    have hy := congrArg (fun f : TopCat.of E ⟶ TopCat.of B => f.hom y) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hy
  have hEq :
      FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase =
        FundamentalGroup.mapOfEq p rfl :=
    fundamental_group_map_of_eq_eq_of_eq hcomm hbase rfl
  -- Identify the pushed-forward class with the original one in the target subgroup.
  calc
    (FundamentalGroup.mapOfEq p' he') ((FundamentalGroup.mapOfEq h.left.hom hh) γ) =
        (FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase) γ := by
      simpa using congrArg (fun F ↦ F γ) hcomp.symm
    _ = (FundamentalGroup.mapOfEq p rfl) γ := by
      simpa using congrArg (fun F ↦ F γ) hEq

/-- Theorem 3.7.6: for covers `p : E → B` and `p' : E' → B`, and chosen fiber points
`e : p ⁻¹' {b}` and `e' : p' ⁻¹' {b}` over the same basepoint `b`, there exists a unique
morphism of covering spaces over `B` sending `e` to `e'` if and only if the image subgroup
`p_*(π₁(E,e))` is contained in `p'_*(π₁(E',e'))` inside `π₁(B,b)`. -/
-- Proof sketch: apply Theorem 3.7.1 to the covering map `p' : E' → B` and the continuous map
-- `p : E → B`, with source space `E` and chosen basepoint `e.1`. The lift produced there is
-- exactly a morphism in `Over (TopCat.of B)` by Definition 3.7.4, and uniqueness of the lift is
-- uniqueness of the point-preserving morphism of coverings.
theorem existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    (∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left.hom e.1 = e'.1) ↔
      (FundamentalGroup.mapOfEq p e.2).range ≤
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  let _ := hp
  rcases e with ⟨e, he⟩
  rcases e' with ⟨e', he'⟩
  subst b
  constructor
  · rintro ⟨h, hh, -⟩
    -- A point-preserving morphism yields the subgroup inclusion by functoriality on loops.
    exact
      fundamental_group_range_le_of_covering_space_hom
        (p e) ⟨e, rfl⟩ ⟨e', he'⟩ h hh
  · intro hsub
    have hsub' :
        (FundamentalGroup.map p e).range ≤
          (FundamentalGroup.mapOfEq p' he').range := by
      -- Rewrite the source subgroup into the form required by the lifting theorem.
      simpa [fundamental_group_map_eq_map_of_eq_rfl] using hsub
    -- Apply the covering-space lifting theorem to `p : E → B` viewed as a map into the base.
    rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
        (cov := hp'.isCoveringMap) (f := p) (a₀ := e) (e₀ := e') (he := he') hsub' with
      ⟨F, hF, huniq⟩
    have hcommF : p' ∘ F = p := hF.2
    refine ⟨Over.homMk (TopCat.ofHom F) ?_, ?_, ?_⟩
    · -- The lifted continuous map is exactly a morphism in the over-category.
      ext y
      exact congrArg (fun k ↦ k y) hcommF
    · simpa using hF.1
    · intro h hh
      -- Uniqueness of lifts is uniqueness of point-preserving morphisms over `B`.
      have hcommh : p' ∘ h.left.hom = p := by
        funext y
        have hy := congrArg (fun f : TopCat.of E ⟶ TopCat.of B => f.hom y) (Over.w h)
        simpa [ContinuousMap.comp_apply] using hy
      have hleft : h.left.hom = F := huniq h.left.hom ⟨by simpa using hh, hcommh⟩
      apply Over.OverMorphism.ext
      simpa using congrArg TopCat.ofHom hleft

section ReverseDirection

variable [PathConnectedSpace E'] [LocPathConnectedSpace E']

/-- Helper for Theorem 3.7.6: the inverse of an isomorphism of covering spaces sends the chosen
target basepoint back to the chosen source basepoint. -/
private theorem covering_space_iso_inv_maps_basepoint
    {p : C(E, B)} {p' : C(E', B)}
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) [IsIso h]
    (hh : h.left.hom e.1 = e'.1) :
    (inv h).left.hom e'.1 = e.1 := by
  -- Evaluate the identity `h ≫ inv h = 𝟙` at the chosen source point.
  have hcomp := congrArg (fun f : TopCat.of E ⟶ TopCat.of E => f.hom e.1)
    (Over.hom_left_inv_left (asIso h))
  calc
    (inv h).left.hom e'.1 = (inv h).left.hom (h.left.hom e.1) := by rw [hh]
    _ = e.1 := hcomp

/-- A point-preserving morphism of covering spaces over `B` is an isomorphism in
`Over (TopCat.of B)` exactly when the associated image subgroups in `π₁(B, b)` coincide. -/
-- Proof sketch: if `h` is an isomorphism of coverings, compose with its inverse to obtain the
-- reverse point-preserving morphism and hence the opposite subgroup inclusion. Conversely, if the
-- image subgroups are equal, apply the main theorem in the reverse direction to construct a
-- point-preserving morphism `E' → E`; uniqueness from the main theorem forces the two composites
-- to be identities, so `h` is an isomorphism in the over-category.
theorem coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    IsIso h ↔
      (FundamentalGroup.mapOfEq p e.2).range =
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  constructor
  · intro hIso
    -- An isomorphism gives subgroup inclusions in both directions, hence equality.
    have hle := fundamental_group_range_le_of_covering_space_hom b e e' h hh
    have hhi : (inv h).left.hom e'.1 = e.1 :=
      covering_space_iso_inv_maps_basepoint b e e' h hh
    have hge :
        (FundamentalGroup.mapOfEq p' e'.2).range ≤
          (FundamentalGroup.mapOfEq p e.2).range :=
      fundamental_group_range_le_of_covering_space_hom b e' e (inv h) hhi
    exact le_antisymm hle hge
  · intro hEq
    -- Equality gives a reverse morphism `g : E' → E` fixing the chosen basepoints.
    rcases
        (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
          hp' hp b e' e).mpr hEq.ge with
      ⟨g, hg, hguniq⟩
    have hself :
        ∃! k : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p),
          k.left.hom e.1 = e.1 :=
      (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
        hp hp b e e).mpr le_rfl
    rcases hself with ⟨k, hk, hkunique⟩
    have hhg : (h ≫ g).left.hom e.1 = e.1 := by
      -- The composite `h ≫ g` fixes `e`, so uniqueness forces it to be the identity.
      calc
        (h ≫ g).left.hom e.1 = g.left.hom (h.left.hom e.1) := rfl
        _ = g.left.hom e'.1 := by rw [hh]
        _ = e.1 := hg
    have hcomp_id : h ≫ g = 𝟙 _ := by
      exact (hkunique (h ≫ g) hhg).trans (hkunique (𝟙 _) rfl).symm
    have hself' :
        ∃! k : Over.mk (TopCat.ofHom p') ⟶ Over.mk (TopCat.ofHom p'),
          k.left.hom e'.1 = e'.1 :=
      (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
        hp' hp' b e' e').mpr le_rfl
    rcases hself' with ⟨k', hk', hk'unique⟩
    have hghh : (g ≫ h).left.hom e'.1 = e'.1 := by
      -- The same uniqueness argument on the other side gives `g ≫ h = 𝟙`.
      calc
        (g ≫ h).left.hom e'.1 = h.left.hom (g.left.hom e'.1) := rfl
        _ = h.left.hom e.1 := by rw [hg]
        _ = e'.1 := hh
    have hcomp'_id : g ≫ h = 𝟙 _ := by
      exact (hk'unique (g ≫ h) hghh).trans (hk'unique (𝟙 _) rfl).symm
    exact IsIso.mk ⟨g, hcomp_id, hcomp'_id⟩

/-- The underlying map of a point-preserving isomorphism of covering spaces is a homeomorphism
exactly when the associated image subgroups in `π₁(B, b)` coincide. -/
theorem coveringSpaceMorphism_isHomeomorph_iff_fundamentalGroup_range_eq
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    IsHomeomorph h.left ↔
      (FundamentalGroup.mapOfEq p e.2).range =
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  have hforget : IsIso h.left ↔ IsIso h := by
    simpa using isIso_iff_of_reflects_iso h (Over.forget (TopCat.of B))
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact hforget.trans <|
    coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq hp hp' b e e' h hh

end ReverseDirection

end IsPathConnectedCoveringMap
