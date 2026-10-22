/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_6
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_7_10
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_5
import AlgebraicTopology_May_1999.Chap03.Theorem_3_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory FundamentalGroupoid
open CategoryTheory.Groupoid.CategoryTheory
open scoped FundamentalGroup QuotientGroup

universe u

variable {E B : Type u}
  [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)}

/-- Helper for Corollary 3.7.11: restricting the identity covering-space endomorphism to a fiber
gives the identity map. -/
theorem coveringSpaceHomToFiberFun_id (b : B) :
    coveringSpaceHomToFiberFun (p := p) (p' := p) b (𝟙 (Over.mk (TopCat.ofHom p))) = id := by
  funext x
  -- The identity over-morphism acts trivially on the chosen fiber point.
  apply Subtype.ext
  rfl

/-- Helper for Corollary 3.7.11: restricting a composite covering-space endomorphism to a fiber
composes the induced fiber maps in the same order. -/
theorem coveringSpaceHomToFiberFun_comp (b : B)
    (h₁ h₂ : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p)) :
    coveringSpaceHomToFiberFun (p := p) (p' := p) b (h₁ ≫ h₂) =
      coveringSpaceHomToFiberFun (p := p) (p' := p) b h₂ ∘
        coveringSpaceHomToFiberFun (p := p) (p' := p) b h₁ := by
  funext x
  -- Composition in the over-category composes the underlying maps on fiber points.
  apply Subtype.ext
  rfl

/-- The fiber map induced by a covering-space automorphism is bijective. -/
-- Proof sketch: the inverse automorphism of the covering induces the inverse map on the fiber
-- over `p e`, and the two composites are identities because `α.hom ≫ α.inv = 𝟙 _` and
-- `α.inv ≫ α.hom = 𝟙 _`.
theorem coveringSpaceAutFiberMap_bijective
    (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    Function.Bijective (coveringSpaceHomToFiberFun (p e) α.hom) := by
  let f := coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) α.hom
  let g := coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) α.inv
  have hleft : Function.LeftInverse g f := by
    intro x
    have hcomp : g ∘ f = id := by
      -- Restricting `α.hom ≫ α.inv = 𝟙` to the fiber gives a left inverse.
      calc
        g ∘ f =
            coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) (α.hom ≫ α.inv) := by
              symm
              exact coveringSpaceHomToFiberFun_comp (p := p) (p e) α.hom α.inv
        _ = id := by
              simpa [coveringSpaceHomToFiberFun_id (p := p)] using
                congrArg
                  (coveringSpaceHomToFiberFun (p := p) (p' := p) (p e))
                  α.hom_inv_id
    simpa [f, g] using congrFun hcomp x
  have hright : Function.RightInverse g f := by
    intro x
    have hcomp : f ∘ g = id := by
      -- Restricting `α.inv ≫ α.hom = 𝟙` to the fiber gives a right inverse.
      calc
        f ∘ g =
            coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) (α.inv ≫ α.hom) := by
              symm
              exact coveringSpaceHomToFiberFun_comp (p := p) (p e) α.inv α.hom
        _ = id := by
              simpa [coveringSpaceHomToFiberFun_id (p := p)] using
                congrArg
                  (coveringSpaceHomToFiberFun (p := p) (p' := p) (p e))
                  α.inv_hom_id
    simpa [f, g] using congrFun hcomp x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The permutation of the fiber over `p e` induced by a covering-space automorphism. -/
noncomputable def coveringSpaceAutFiberPerm
    (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    Equiv.Perm (p ⁻¹' {p e}) :=
  Equiv.ofBijective
    (coveringSpaceHomToFiberFun (p e) α.hom)
    (coveringSpaceAutFiberMap_bijective e α)

/-- The identity covering-space automorphism induces the identity permutation on the fiber. -/
-- Proof sketch: unfold `coveringSpaceAutFiberPerm`; the identity morphism of
-- `Over.mk (TopCat.ofHom p)` restricts to the identity map on each fiber.
theorem coveringSpaceAutFiberPerm_one (e : E) :
    coveringSpaceAutFiberPerm e (1 : Aut (Over.mk (TopCat.ofHom p))) = 1 := by
  ext x
  -- The identity covering automorphism restricts to the identity on the fiber.
  rfl

/-- The permutation induced on the fiber is multiplicative in the covering-space automorphism. -/
-- Proof sketch: restriction to the fiber respects composition of morphisms in the over-category,
-- so the permutation attached to `α * β` is the composite of the permutations attached to `α` and
-- `β`.
theorem coveringSpaceAutFiberPerm_mul
    (e : E) (α β : Aut (Over.mk (TopCat.ofHom p))) :
    coveringSpaceAutFiberPerm e (α * β) =
      coveringSpaceAutFiberPerm e α * coveringSpaceAutFiberPerm e β := by
  ext x
  -- Restriction to the fiber respects composition of covering automorphisms.
  rfl

/-- Helper for Corollary 3.7.11: membership in the ordinary image subgroup is equivalent to
membership of the corresponding loop morphism in the image of the induced functor on vertex
groups. -/
private theorem mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range
    (hp : IsPathConnectedCoveringMap p) (e : E) (γ : FundamentalGroup B (p e)) :
    γ ∈ (FundamentalGroup.map p e).range ↔
      γ.toPath ∈
        (hp.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk e)).range := by
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ.toPath, rfl⟩
  · rintro ⟨δ, hδ⟩
    refine ⟨FundamentalGroup.fromPath δ, ?_⟩
    simpa using hδ

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- The monodromy action of `π₁(B, p e)` on the fiber over `p e` is pretransitive for a
path-connected covering space. -/
-- Proof sketch: given two points in the fiber over `p e`, choose a path in the path-connected
-- total space joining them. Projecting that path to `B` gives a loop at `p e`, and monodromy
-- along that loop sends the first point to the second.
theorem fiberMonodromyMulAction_isPretransitive
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    MulAction.IsPretransitive (FundamentalGroup B (p e)) (p ⁻¹' {p e}) := by
  letI := fiberMonodromyMulAction hp (p e)
  letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  letI : MulAction.IsPretransitive
      (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction_isPretransitive
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  let x₀ : p ⁻¹' {p e} := hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀
  refine (MulAction.isPretransitive_iff_base (G := FundamentalGroup B (p e)) x₀).2 ?_
  intro x
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    (hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x
  rcases (MulAction.isPretransitive_iff_base
      (G := FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀).mp
      inferInstance ξ with ⟨δ, hδ⟩
  refine ⟨FundamentalGroup.fromPath δ⁻¹, ?_⟩
  have hsmul :
      δ • ξ₀ =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀ := by
    change δ • ξ₀ =
      (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
        hp.fundamentalGroupoidMap_isCovering).map δ⁻¹ ξ₀
    exact CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
      (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
        hp.fundamentalGroupoidMap_isCovering)
      (b := FundamentalGroupoid.mk (p e)) δ ξ₀
  have htransport :
      hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀) =
        hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀ := by
    change hp.fundamentalGroupoidMapFiberEquiv (p e)
        (CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering ((FundamentalGroup.fromPath δ⁻¹).toPath) ξ₀) =
      hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀
    exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e)
      (FundamentalGroup.fromPath δ⁻¹) ξ₀
  calc
    (FundamentalGroup.fromPath δ⁻¹) • x₀ =
        hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀ := by
          rfl
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀) := htransport.symm
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e) (δ • ξ₀) := by
          exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul.symm
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ := by rw [hδ]
    _ = x := by simp [ξ]

/-- The stabilizer of the distinguished fiber point `e` under monodromy is exactly the image of
`p_* : π₁(E, e) → π₁(B, p e)`. -/
-- Proof sketch: a loop in `B` fixes `e` under monodromy precisely when it lifts to a loop in `E`
-- based at `e`, which is the defining membership condition for the image subgroup
-- `(FundamentalGroup.map p e).range`.
theorem fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    MulAction.stabilizer (FundamentalGroup B (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) =
      (FundamentalGroup.map p e).range := by
  letI := fiberMonodromyMulAction hp (p e)
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let x₀ : p ⁻¹' {p e} := ⟨e, rfl⟩
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  have hstab_groupoid :
      MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ =
        (hp.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk e)).range := by
    -- The categorical fiber-translation stabilizer is the image of the upstairs vertex group.
    simpa [ξ₀] using
      (CategoryTheory.Functor.IsCovering.fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range
        hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk e))
  ext γ
  let δ : FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e) := γ.toPath
  constructor
  · intro hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    have hsmul :
        δ⁻¹ • ξ₀ =
          CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ ξ₀ := by
      change δ⁻¹ • ξ₀ =
        (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering).map δ ξ₀
      simpa using CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := FundamentalGroupoid.mk (p e)) δ⁻¹ ξ₀
    have htransport :
        hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) =
          hp.fiberTranslationMap γ.toPath x₀ := by
      change hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering γ.toPath ξ₀) =
        hp.fiberTranslationMap γ.toPath x₀
      exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e) γ ξ₀
    have hfixed_groupoid : δ⁻¹ • ξ₀ = ξ₀ := by
      apply (hp.fundamentalGroupoidMapFiberEquiv (p e)).injective
      calc
        hp.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ₀) =
            hp.fundamentalGroupoidMapFiberEquiv (p e)
              (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                hp.fundamentalGroupoidMap_isCovering δ ξ₀) := by
                  exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul
        _ = hp.fiberTranslationMap γ.toPath x₀ := htransport
        _ = γ • x₀ := by rfl
        _ = x₀ := hγ
        _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀ := by rfl
    have hmem_stab : δ⁻¹ ∈
        MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ := by
      -- Fixing the distinguished categorical fiber point is stabilizer membership.
      rwa [MulAction.mem_stabilizer_iff]
    have hmem_groupoid_inv : δ⁻¹ ∈
        (hp.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk e)).range := by
      -- Rewrite categorical stabilizer membership using the standard basepoint theorem.
      simpa [hstab_groupoid] using hmem_stab
    have hmem_ordinary_inv : γ⁻¹ ∈ (FundamentalGroup.map p e).range :=
      (mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range hp e (γ⁻¹)).2
        hmem_groupoid_inv
    -- Inverting the subgroup witness returns membership for `γ` itself.
    simpa using Subgroup.inv_mem ((FundamentalGroup.map p e).range) hmem_ordinary_inv
  · intro hγ
    rw [MulAction.mem_stabilizer_iff]
    have hmem_ordinary_inv : γ⁻¹ ∈ (FundamentalGroup.map p e).range := by
      -- The image subgroup is closed under inversion.
      simpa using Subgroup.inv_mem ((FundamentalGroup.map p e).range) hγ
    have hmem_groupoid_inv : δ⁻¹ ∈
        (hp.fundamentalGroupoidMap.mapVertexGroup (FundamentalGroupoid.mk e)).range :=
      (mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range hp e (γ⁻¹)).1
        hmem_ordinary_inv
    have hmem_stab : δ⁻¹ ∈
        MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ := by
      -- Transport the subgroup-membership statement back to the categorical stabilizer.
      simpa [hstab_groupoid] using hmem_groupoid_inv
    have hfixed_groupoid : δ⁻¹ • ξ₀ = ξ₀ := by
      rwa [MulAction.mem_stabilizer_iff] at hmem_stab
    have hsmul :
        δ⁻¹ • ξ₀ =
          CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ ξ₀ := by
      change δ⁻¹ • ξ₀ =
        (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering).map δ ξ₀
      simpa using CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := FundamentalGroupoid.mk (p e)) δ⁻¹ ξ₀
    have htransport :
        hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) =
          hp.fiberTranslationMap γ.toPath x₀ := by
      change hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering γ.toPath ξ₀) =
        hp.fiberTranslationMap γ.toPath x₀
      exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e) γ ξ₀
    -- Transport the categorical fixed-point statement back to the ordinary monodromy action.
    calc
      γ • x₀ = hp.fiberTranslationMap γ.toPath x₀ := by rfl
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) := htransport.symm
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ₀) := by
            exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul.symm
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀ := by rw [hfixed_groupoid]
      _ = x₀ := by rfl

/-- The permutation induced on the fiber by a covering-space automorphism is equivariant for the
monodromy action of `π₁(B, p e)`. -/
-- Proof sketch: `coveringSpaceHomToFiberFun_comm` from Theorem 3.7.9 gives the required
-- commutation relation with monodromy, which is exactly membership in the subgroup `gSetAut`.
theorem coveringSpaceAutFiberPerm_mem_gSetAut
    (hp : IsPathConnectedCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI := fiberMonodromyMulAction hp (p e)
    coveringSpaceAutFiberPerm e α ∈ gSetAut (FundamentalGroup B (p e)) (p ⁻¹' {p e}) := by
  letI := fiberMonodromyMulAction hp (p e)
  change coveringSpaceAutFiberPerm e α ∈
    Subgroup.centralizer
      (((MulAction.toPermHom (FundamentalGroup B (p e)) (p ⁻¹' {p e})).range :
        Set (Equiv.Perm (p ⁻¹' {p e}))))
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  rcases hτ with ⟨γ, rfl⟩
  ext x
  -- Pointwise centralizer equality is exactly monodromy equivariance from Theorem 3.7.9.
  simpa [coveringSpaceAutFiberPerm] using
    congrArg Subtype.val (coveringSpaceHomToFiberFun_comm hp hp (p e) α.hom γ x).symm

/-- The canonical homomorphism from covering-space automorphisms to automorphisms of the fiber as
a `π₁(B, p e)`-set. -/
noncomputable def coveringSpaceAutToFiberAutHom
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut (Over.mk (TopCat.ofHom p)) →*
      Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
  letI := fiberMonodromyMulAction hp (p e)
  ((autMulEquivGSetAut (FundamentalGroup B (p e)) (p ⁻¹' {p e})).symm.toMonoidHom).comp
    { toFun := fun α ↦
        ⟨coveringSpaceAutFiberPerm e α, coveringSpaceAutFiberPerm_mem_gSetAut hp e α⟩
      map_one' := Subtype.ext (coveringSpaceAutFiberPerm_one e)
      map_mul' := fun α β ↦ Subtype.ext (coveringSpaceAutFiberPerm_mul e α β) }

/-- The canonical homomorphism to fiber `π₁(B, p e)`-set automorphisms is bijective. -/
-- Proof sketch: Theorem 3.7.9 identifies all morphisms of covering spaces `p ⟶ p` with
-- equivariant fiber maps. Restricting to invertible morphisms on both sides gives bijectivity on
-- the corresponding automorphism groups.
theorem coveringSpaceAutToFiberAutHom_bijective
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Function.Bijective (coveringSpaceAutToFiberAutHom hp e) := by
  letI := fiberMonodromyMulAction hp (p e)
  constructor
  · intro α β hαβ
    apply Iso.ext
    apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
    apply MulActionHom.ext
    intro x
    have hx :
        (coveringSpaceAutToFiberAutHom hp e α).hom.hom x =
          (coveringSpaceAutToFiberAutHom hp e β).hom.hom x := by
      simpa using
        congrArg
          (fun φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ↦ φ.hom.hom x)
          hαβ
    -- Equality of fiber automorphisms gives equality of the restricted covering maps.
    simpa [coveringSpaceAutToFiberAutHom, coveringSpaceAutFiberPerm, coveringSpaceHomToFiber] using
      hx
  · intro φ
    -- Route correction: lift the inverse fiber automorphism through Theorem 3.7.9 instead of
    -- rebuilding the Weyl-group argument directly.
    have hφ_hom_smul :
        ∀ (γ : FundamentalGroup B (p e)) (x : p ⁻¹' {p e}),
          φ.hom.hom (γ • x) = γ • (show p ⁻¹' {p e} from φ.hom.hom x) := by
      intro γ x
      -- The forward fiber automorphism is equivariant by definition.
      simpa [Action.ofMulAction_apply] using
        congrArg (fun k ↦ k.hom x) (φ.hom.comm γ)
    let φhom : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) :=
      { toFun := φ.hom.hom
        map_smul' := hφ_hom_smul }
    have hφ_inv_smul :
        ∀ (γ : FundamentalGroup B (p e)) (x : p ⁻¹' {p e}),
          φ.inv.hom (γ • x) = γ • (show p ⁻¹' {p e} from φ.inv.hom x) := by
      intro γ x
      -- The inverse fiber automorphism is equivariant for the same monodromy action.
      simpa [Action.ofMulAction_apply] using
        congrArg (fun k ↦ k.hom x) (φ.inv.comm γ)
    let φinv : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) :=
      { toFun := φ.inv.hom
        map_smul' := hφ_inv_smul }
    obtain ⟨h, hh⟩ := (coveringSpaceHomToFiber_bijective hp hp (p e)).2 φhom
    obtain ⟨i, hi⟩ := (coveringSpaceHomToFiber_bijective hp hp (p e)).2 φinv
    have hh_apply (x : p ⁻¹' {p e}) :
        coveringSpaceHomToFiberFun (p e) h x = φ.hom.hom x := by
      -- The lifted endomorphism `h` restricts to the given fiber automorphism `φ.hom`.
      simpa [coveringSpaceHomToFiber] using
        congrArg
          (fun ψ : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) ↦ ψ x)
          hh
    have hi_apply (x : p ⁻¹' {p e}) :
        coveringSpaceHomToFiberFun (p e) i x = φ.inv.hom x := by
      -- Likewise, `i` restricts to the inverse fiber automorphism `φ.inv.hom`.
      simpa [coveringSpaceHomToFiber] using
        congrArg
          (fun ψ : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) ↦ ψ x)
          hi
    have hhi : h ≫ i = 𝟙 (Over.mk (TopCat.ofHom p)) := by
      apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
      apply MulActionHom.ext
      intro x
      -- The lifted maps compose to the identity because `φ.hom` and `φ.inv.hom` are inverse.
      have hcompose :
          coveringSpaceHomToFiberFun (p e) (h ≫ i) x =
            φ.inv.hom (φ.hom.hom x) := by
        calc
          coveringSpaceHomToFiberFun (p e) (h ≫ i) x =
              coveringSpaceHomToFiberFun (p e) i
                (coveringSpaceHomToFiberFun (p e) h x) := by
                  simpa [Function.comp] using
                    congrFun (coveringSpaceHomToFiberFun_comp (p := p) (p e) h i) x
          _ = φ.inv.hom (φ.hom.hom x) := by
                rw [hh_apply x, hi_apply (φ.hom.hom x)]
      have hidentity : φ.inv.hom (φ.hom.hom x) = x := by
        exact congrArg (fun k ↦ k.hom x) (Action.hom_inv_hom φ)
      exact hcompose.trans hidentity
    have hih : i ≫ h = 𝟙 (Over.mk (TopCat.ofHom p)) := by
      apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
      apply MulActionHom.ext
      intro x
      -- The opposite composite is also the identity because `φ.inv.hom` and `φ.hom` are inverse.
      have hcompose :
          coveringSpaceHomToFiberFun (p e) (i ≫ h) x =
            φ.hom.hom (φ.inv.hom x) := by
        calc
          coveringSpaceHomToFiberFun (p e) (i ≫ h) x =
              coveringSpaceHomToFiberFun (p e) h
                (coveringSpaceHomToFiberFun (p e) i x) := by
                  simpa [Function.comp] using
                    congrFun (coveringSpaceHomToFiberFun_comp (p := p) (p e) i h) x
          _ = φ.hom.hom (φ.inv.hom x) := by
                rw [hi_apply x, hh_apply (φ.inv.hom x)]
      have hidentity : φ.hom.hom (φ.inv.hom x) = x := by
        exact congrArg (fun k ↦ k.hom x) (Action.inv_hom_hom φ)
      exact hcompose.trans hidentity
    have hIso : IsIso h := IsIso.mk ⟨i, hhi, hih⟩
    refine ⟨asIso h, ?_⟩
    ext x
    -- The reconstructed covering automorphism acts on the fiber as the original automorphism `φ`.
    simpa [coveringSpaceAutToFiberAutHom, coveringSpaceAutFiberPerm, coveringSpaceHomToFiber,
      CategoryTheory.asIso_hom, φhom] using hh_apply x

/-- The automorphism group of a covering space is canonically isomorphic to the automorphism group
of its fiber over `p e` as a `π₁(B, p e)`-set. -/
noncomputable def coveringSpaceAutMulEquivFiberAut
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut (Over.mk (TopCat.ofHom p)) ≃*
      Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
  letI := fiberMonodromyMulAction hp (p e)
  MulEquiv.ofBijective
    (coveringSpaceAutToFiberAutHom hp e)
    (coveringSpaceAutToFiberAutHom_bijective hp e)

/-- The automorphism group of the fiber monodromy `π₁(B, p e)`-set is canonically identified with
the Weyl group of the image subgroup `(FundamentalGroup.map p e).range`. -/
noncomputable def fiberAutMulEquivWeylGroup_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ≃*
      Subgroup.weylGroup ((FundamentalGroup.map p e).range) :=
  letI := fiberMonodromyMulAction hp (p e)
  letI : MulAction.IsPretransitive (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
    fiberMonodromyMulAction_isPretransitive hp e
  let x₀ : p ⁻¹' {p e} := ⟨e, rfl⟩
  let eW :
      Subgroup.weylGroup (MulAction.stabilizer (FundamentalGroup B (p e)) x₀) ≃*
        Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
    weylGroup_stabilizer_mulEquiv_aut x₀
  show Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ≃*
      Subgroup.weylGroup ((FundamentalGroup.map p e).range) from
    eW.symm.trans
      (MulEquiv.cast (fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange hp e))

/-- Corollary 3.7.11 (1): if `G = π₁(B, p e)` and `H = p_*(π₁(E, e))`, then the automorphism
group of the covering space `p` is canonically isomorphic to the Weyl group `W H`. -/
noncomputable def coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    Aut (Over.mk (TopCat.ofHom p)) ≃* Subgroup.weylGroup ((FundamentalGroup.map p e).range) :=
  (coveringSpaceAutMulEquivFiberAut hp e).trans
    (fiberAutMulEquivWeylGroup_fundamentalGroupRange hp e)

/-- Evaluating the first clause identifies a covering-space automorphism with its Weyl-group
class through the fiber `π₁(B, p e)`-set. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange`; the value is
-- the composite of the covering-automorphism/fiber-action equivalence and the bundled
-- fiber-action Weyl-group bridge.
theorem coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange_apply
    (hp : IsPathConnectedCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI := fiberMonodromyMulAction hp (p e)
    coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange hp e α =
      fiberAutMulEquivWeylGroup_fundamentalGroupRange hp e
        (coveringSpaceAutMulEquivFiberAut hp e α) := rfl

end

end IsPathConnectedCoveringMap

namespace IsRegularCoveringMap

variable {p : C(E, B)} {e : E}

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- Corollary 3.7.11 (2): if `p` is regular at `e`, then the automorphism group of the covering
space `p` is canonically isomorphic to `π₁(B, p e) / p_*(π₁(E, e))`. -/
noncomputable def coveringSpaceAutMulEquivQuotientFundamentalGroupRange
    (hp : IsRegularCoveringMap p e) :
    letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
    Aut (Over.mk (TopCat.ofHom p)) ≃*
      (FundamentalGroup B (p e) ⧸ (FundamentalGroup.map p e).range) :=
  letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
  (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
      hp.isPathConnectedCoveringMap e).trans
    (Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range))

/-- Evaluating the second clause factors through the Weyl-group description and then the quotient
by the normal image subgroup. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivQuotientFundamentalGroupRange`; its value is the
-- application of `weylGroupMulEquivQuotientOfNormal` to the Weyl-group class from the first
-- clause.
theorem coveringSpaceAutMulEquivQuotientFundamentalGroupRange_apply
    (hp : IsRegularCoveringMap p e) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
    coveringSpaceAutMulEquivQuotientFundamentalGroupRange hp α =
      Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)
        (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
          hp.isPathConnectedCoveringMap e α) := rfl

end

end IsRegularCoveringMap

namespace IsUniversalCoveringMap

variable [LocPathConnectedSpace E] {p : C(E, B)}

/-- Helper for Corollary 3.7.11: a universal covering has trivial image subgroup in the base
fundamental group at every chosen basepoint. -/
private theorem fundamentalGroup_map_range_eq_bot_of_universal
    (hp : IsUniversalCoveringMap p) (e : E) :
    (FundamentalGroup.map p e).range = ⊥ := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- A simply connected source has subsingleton fundamental group, so the induced map is trivial.
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact congrArg (FundamentalGroup.fromPath (X := E) (x := e))
      (Subsingleton.elim (FundamentalGroup.toPath γ) ⟦Path.refl e⟧)
  rw [hγ, map_one, MonoidHom.one_apply]

/-- A universal covering map is regular at every chosen basepoint. -/
-- Proof sketch: the image subgroup `p_*(π₁(E, e))` is trivial for a universal covering, hence
-- normal, so the regularity condition follows immediately.
theorem isRegularCoveringMap (hp : IsUniversalCoveringMap p) (e : E) :
    IsRegularCoveringMap p e := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  have hbot : (FundamentalGroup.map p e).range = ⊥ :=
    fundamentalGroup_map_range_eq_bot_of_universal hp e
  refine
    { toIsPathConnectedCoveringMap := hp.isPathConnectedCoveringMap
      normal_fundamentalGroup_map_range := ?_ }
  -- The trivial subgroup is normal, so the regularity condition is automatic.
  exact hbot ▸ Subgroup.normal_bot

/-- For a universal covering, the image subgroup `p_*(π₁(E, e))` is trivial. -/
-- Proof sketch: a simply connected total space has trivial fundamental group at every basepoint,
-- so the image of `FundamentalGroup.map p e` is the bottom subgroup.
theorem fundamentalGroup_map_range_eq_bot (hp : IsUniversalCoveringMap p) (e : E) :
    (FundamentalGroup.map p e).range = ⊥ :=
  fundamentalGroup_map_range_eq_bot_of_universal hp e

/-- Corollary 3.7.11 (3): if `p` is universal, then the automorphism group of the covering space
`p` is canonically isomorphic to `π₁(B, p e)`. -/
noncomputable def coveringSpaceAutMulEquivFundamentalGroup
    (hp : IsUniversalCoveringMap p) (e : E) :
    Aut (Over.mk (TopCat.ofHom p)) ≃* FundamentalGroup B (p e) :=
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  let h_regular := isRegularCoveringMap hp e
  letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
  (IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange h_regular).trans
    ((QuotientGroup.quotientMulEquivOfEq (fundamentalGroup_map_range_eq_bot hp e)).trans
      QuotientGroup.quotientBot)

/-- Evaluating the third clause specializes the quotient description along the equality
`p_*(π₁(E, e)) = ⊥`. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivFundamentalGroup`; its value is the regular-case
-- quotient class, followed by the quotient identifications for the trivial subgroup.
theorem coveringSpaceAutMulEquivFundamentalGroup_apply
    (hp : IsUniversalCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    let h_regular := isRegularCoveringMap hp e
    letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
    coveringSpaceAutMulEquivFundamentalGroup hp e α =
      ((QuotientGroup.quotientMulEquivOfEq (fundamentalGroup_map_range_eq_bot hp e)).trans
        QuotientGroup.quotientBot)
        (IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange
          h_regular α) := rfl

end IsUniversalCoveringMap
