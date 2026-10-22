/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_11
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_4
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_5
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v u₁ u₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped QuotientGroup

namespace CategoryTheory.Functor.IsCovering

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B]
variable {p : E ⥤ B}

noncomputable section

/-- Helper for Corollary 3.5.10: restricting the identity over-morphism of `p` to a fiber gives
the identity map. -/
theorem mapOfCoveringsToFiberFun_id (b : B) :
    mapOfCoveringsToFiberFun (p := p) b (𝟙 (Over.mk p.toCatHom)) = id := by
  funext x
  -- The identity over-morphism acts trivially on the chosen fiber point.
  apply Subtype.ext
  rfl

/-- Helper for Corollary 3.5.10: restricting a composite over-morphism to a fiber composes the
restricted fiber maps in the same order. -/
theorem mapOfCoveringsToFiberFun_comp (b : B)
    (h₁ h₂ : Over.mk p.toCatHom ⟶ Over.mk p.toCatHom) :
    mapOfCoveringsToFiberFun (p := p) b (h₁ ≫ h₂) =
      mapOfCoveringsToFiberFun (p := p) b h₂ ∘ mapOfCoveringsToFiberFun (p := p) b h₁ := by
  funext x
  -- Composition in the over-category composes the underlying functors on fiber points.
  apply Subtype.ext
  rfl

/-- The induced map on the fiber over `p.obj e` coming from a covering automorphism is bijective. -/
-- Proof sketch: the inverse automorphism of `α` induces the inverse fiber map, and the two
-- composites are identities because `α.hom ≫ α.inv = 𝟙 _` and `α.inv ≫ α.hom = 𝟙 _`.
theorem coveringAutFiberMap_bijective (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    Function.Bijective
      (mapOfCoveringsToFiberFun (p.obj e) α.hom) := by
  let f := mapOfCoveringsToFiberFun (p := p) (p.obj e) α.hom
  let g := mapOfCoveringsToFiberFun (p := p) (p.obj e) α.inv
  have hleft : Function.LeftInverse g f := by
    intro x
    have hcomp : g ∘ f = id := by
      -- Restricting `α.hom ≫ α.inv = 𝟙` to the fiber gives a left inverse.
      calc
        g ∘ f = mapOfCoveringsToFiberFun (p := p) (p.obj e) (α.hom ≫ α.inv) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) α.hom α.inv
        _ = id := by
          simpa [mapOfCoveringsToFiberFun_id (p := p)] using
            congrArg (mapOfCoveringsToFiberFun (p := p) (p.obj e)) α.hom_inv_id
    simpa [f, g] using congrFun hcomp x
  have hright : Function.RightInverse g f := by
    intro x
    have hcomp : f ∘ g = id := by
      -- Restricting `α.inv ≫ α.hom = 𝟙` to the fiber gives a right inverse.
      calc
        f ∘ g = mapOfCoveringsToFiberFun (p := p) (p.obj e) (α.inv ≫ α.hom) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) α.inv α.hom
        _ = id := by
          simpa [mapOfCoveringsToFiberFun_id (p := p)] using
            congrArg (mapOfCoveringsToFiberFun (p := p) (p.obj e)) α.inv_hom_id
    simpa [f, g] using congrFun hcomp x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The permutation of the fiber over `p.obj e` induced by a covering automorphism. -/
noncomputable def coveringAutFiberPerm (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) : Equiv.Perm (p.Fiber (p.obj e)) :=
  Equiv.ofBijective
    (mapOfCoveringsToFiberFun (p.obj e) α.hom)
    (coveringAutFiberMap_bijective hp e α)

/-- The permutation induced on the fiber by a covering automorphism is equivariant for the
fiber-translation `π(B, p.obj e)`-action. -/
-- Proof sketch: `mapOfCoveringsToFiberFun_comm` gives the required commutation relation with the
-- canonical fiber-translation action, and this is exactly membership in the centralizer subgroup
-- `gSetAut`.
theorem coveringAutFiberPerm_mem_gSetAut (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    letI := fiberTranslationMulAction hp (p.obj e)
    coveringAutFiberPerm hp e α ∈ gSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  change coveringAutFiberPerm hp e α ∈
    Subgroup.centralizer
      (((MulAction.toPermHom (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))).range :
        Set (Equiv.Perm (p.Fiber (p.obj e)))))
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  rcases hτ with ⟨γ, rfl⟩
  ext x
  -- Evaluating the centralizer condition pointwise is exactly the equivariance relation from
  -- Theorem 3.5.8.
  simpa [coveringAutFiberPerm] using
    (mapOfCoveringsToFiberFun_comm hp hp (p.obj e) α.hom γ x).symm

/-- The permutation induced by the identity covering automorphism is the identity on the fiber. -/
-- Proof sketch: unfold `coveringAutFiberPerm` and use that the identity morphism of
-- `Over.mk p.toCatHom` restricts to the identity map on every fiber.
theorem coveringAutFiberPerm_one (hp : Functor.IsCovering p) (e : E) :
    coveringAutFiberPerm hp e (1 : Aut (Over.mk p.toCatHom)) = 1 := by
  ext x
  -- The identity over-morphism restricts to the identity on the fiber.
  change mapOfCoveringsToFiberFun (p := p) (p.obj e) (𝟙 (Over.mk p.toCatHom)) x = x
  simpa [mapOfCoveringsToFiberFun_id (p := p)]

/-- The permutation induced on the fiber is multiplicative in the covering automorphism. -/
-- Proof sketch: restriction to the fiber respects composition of maps of coverings, so the
-- permutation attached to `α * β` is the composite of the permutations attached to `α` and `β`.
theorem coveringAutFiberPerm_mul (hp : Functor.IsCovering p) (e : E)
    (α β : Aut (Over.mk p.toCatHom)) :
    coveringAutFiberPerm hp e (α * β) =
      coveringAutFiberPerm hp e α * coveringAutFiberPerm hp e β := by
  ext x
  -- Restriction to the fiber respects composition of covering automorphisms.
  change mapOfCoveringsToFiberFun (p := p) (p.obj e) ((α * β).hom) x =
    mapOfCoveringsToFiberFun (p := p) (p.obj e) α.hom
      (mapOfCoveringsToFiberFun (p := p) (p.obj e) β.hom x)
  rw [show (α * β).hom = β.hom ≫ α.hom by rfl]
  simpa [Function.comp] using
    congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) β.hom α.hom) x

/-- The canonical homomorphism from covering automorphisms to automorphisms of the fiber as a
`π(B, p.obj e)`-set. -/
noncomputable def coveringAutToFiberAutHom (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut (Over.mk p.toCatHom) →* Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ((autMulEquivGSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))).symm.toMonoidHom).comp
    { toFun := fun α ↦ ⟨coveringAutFiberPerm hp e α, coveringAutFiberPerm_mem_gSetAut hp e α⟩
      map_one' := Subtype.ext (coveringAutFiberPerm_one hp e)
      map_mul' := fun α β ↦ Subtype.ext (coveringAutFiberPerm_mul hp e α β) }

/-- The canonical homomorphism from covering automorphisms to `G`-set automorphisms of the fiber
is bijective when the total groupoid is connected. -/
-- Proof sketch: Theorem 3.5.8 identifies all endomorphisms of the covering with equivariant
-- endomorphisms of the fiber. Restricting to invertible endomorphisms on both sides gives
-- bijectivity on the corresponding automorphism groups.
theorem coveringAutToFiberAutHom_bijective [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Function.Bijective (coveringAutToFiberAutHom hp e) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro α β hαβ
    apply Iso.ext
    apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
    apply MulActionHom.ext
    intro x
    have hx :
        (coveringAutToFiberAutHom hp e α).hom.hom x =
          (coveringAutToFiberAutHom hp e β).hom.hom x := by
      simpa using
        congrArg
          (fun φ : Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ↦ φ.hom.hom x)
          hαβ
    -- Equality of fiber automorphisms gives equality of the restricted covering maps.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber] using hx
  · intro φ
    -- Route correction: lift the inverse fiber automorphism through Theorem 3.5.8 instead of
    -- rebuilding the Weyl-group argument directly.
    have hφ_hom_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.hom.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.hom.hom x) := by
      intro γ x
      -- The forward automorphism of the fiber is equivariant by definition.
      simpa [Action.ofMulAction_apply] using
        congrArg (fun k ↦ k.hom x) (φ.hom.comm γ)
    let φhom : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.hom.hom
        map_smul' := hφ_hom_smul }
    have hφ_inv_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.inv.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.inv.hom x) := by
      intro γ x
      -- The inverse automorphism is equivariant for the same fiber action.
      simpa [Action.ofMulAction_apply] using
        congrArg (fun k ↦ k.hom x) (φ.inv.comm γ)
    let φinv : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.inv.hom
        map_smul' := hφ_inv_smul }
    obtain ⟨h, hh⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φhom
    obtain ⟨i, hi⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φinv
    have hh_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p := p) (p.obj e) h x = φ.hom.hom x := by
      -- The lifted morphism `h` restricts to the given equivariant automorphism `φ.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hh
    have hi_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p := p) (p.obj e) i x = φ.inv.hom x := by
      -- Likewise, `i` restricts to the inverse equivariant automorphism `φ.inv.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hi
    have hhi : h ≫ i = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The lifted maps compose to the identity because `φ.hom` and `φ.inv.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (h ≫ i) x =
            φ.inv.hom (φ.hom.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (h ≫ i) x =
              mapOfCoveringsToFiberFun (p := p) (p.obj e) i
                (mapOfCoveringsToFiberFun (p := p) (p.obj e) h x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) h i) x
          _ = φ.inv.hom (φ.hom.hom x) := by
                rw [hh_apply x, hi_apply (φ.hom.hom x)]
      have hidentity : φ.inv.hom (φ.hom.hom x) = x := by
        exact congrArg (fun k ↦ k.hom x) (Action.hom_inv_hom φ)
      exact hcompose.trans hidentity
    have hih : i ≫ h = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The opposite composite is also the identity because `φ.inv.hom` and `φ.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (i ≫ h) x =
            φ.hom.hom (φ.inv.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (i ≫ h) x =
              mapOfCoveringsToFiberFun (p := p) (p.obj e) h
                (mapOfCoveringsToFiberFun (p := p) (p.obj e) i x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) i h) x
          _ = φ.hom.hom (φ.inv.hom x) := by
                rw [hi_apply x, hh_apply (φ.inv.hom x)]
      have hidentity : φ.hom.hom (φ.inv.hom x) = x := by
        exact congrArg (fun k ↦ k.hom x) (Action.inv_hom_hom φ)
      exact hcompose.trans hidentity
    have hIso : IsIso h := IsIso.mk ⟨i, hhi, hih⟩
    refine ⟨asIso h, ?_⟩
    ext x
    -- The reconstructed covering automorphism acts on the fiber as the original automorphism `φ`.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber,
      CategoryTheory.asIso_hom, φhom] using hh_apply x

/-- Corollary 3.5.10 (1): for a connected covering functor `p : E ⥤ B`, the automorphism group
of the covering is canonically isomorphic to the automorphism group of the fiber over `p.obj e`
as a `π(B, p.obj e)`-set. -/
noncomputable def coveringAutMulEquivFiberAut [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut (Over.mk p.toCatHom) ≃* Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
  MulEquiv.ofBijective
    (coveringAutToFiberAutHom hp e)
    (coveringAutToFiberAutHom_bijective hp e)

/-- Evaluating the first clause agrees with the canonical homomorphism
`coveringAutToFiberAutHom`. -/
-- Proof sketch: unfold `coveringAutMulEquivFiberAut`; `MulEquiv.ofBijective` keeps the same
-- underlying function.
theorem coveringAutMulEquivFiberAut_apply [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) (α : Aut (Over.mk p.toCatHom)) :
    coveringAutMulEquivFiberAut hp e α = coveringAutToFiberAutHom hp e α := rfl

/-- The first clause is realized by the canonical homomorphism
`coveringAutToFiberAutHom`. -/
@[simp] theorem coveringAutMulEquivFiberAut_toMonoidHom [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    (coveringAutMulEquivFiberAut hp e).toMonoidHom = coveringAutToFiberAutHom hp e := rfl

/-- The automorphism group of the fiber-translation action is canonically identified with the Weyl
group of the image subgroup `p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def fiberAutMulEquivWeylGroupMapVertexGroupRange [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ≃*
      Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction_isPretransitive hp (p.obj e)
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let eW :
      Subgroup.weylGroup (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀) ≃*
        Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    weylGroup_stabilizer_mulEquiv_aut x₀
  show Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ≃*
      Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) from
    (eW.symm).trans
      (MulEquiv.cast (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e))

/-- Corollary 3.5.10 (2): for a connected covering functor, the automorphism group of the
covering is canonically isomorphic to the Weyl group of the image subgroup
`p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def coveringAutMulEquivWeylGroupMapVertexGroupRange
    [IsConnected E] (hp : Functor.IsCovering p) (e : E) :
    Aut (Over.mk p.toCatHom) ≃* Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  (coveringAutMulEquivFiberAut hp e).trans
    (fiberAutMulEquivWeylGroupMapVertexGroupRange hp e)

/-- Evaluating the second clause identifies a covering automorphism with its induced Weyl-group
class through the fiber `π(B, p.obj e)`-set. -/
-- Proof sketch: unfold `coveringAutMulEquivWeylGroupMapVertexGroupRange`; the value is the
-- composite of the fiber-action equivalence and the bundled fiber-action Weyl-group bridge.
theorem coveringAutMulEquivWeylGroupMapVertexGroupRange_apply
    [IsConnected E] (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    coveringAutMulEquivWeylGroupMapVertexGroupRange hp e α =
      fiberAutMulEquivWeylGroupMapVertexGroupRange hp e
        (coveringAutMulEquivFiberAut hp e α) := rfl

/-- Corollary 3.5.10 (3): for a connected regular covering functor, the automorphism group of the
covering is canonically isomorphic to the quotient `π(B, p.obj e) / p(π(E, e))`. -/
noncomputable def regularCoveringAutMulEquivQuotientMapVertexGroupRange
    [IsConnected E] {e : E} (hp : Functor.IsRegularCovering p e) :
    letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
    Aut (Over.mk p.toCatHom) ≃* ((p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :=
  letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
  (coveringAutMulEquivWeylGroupMapVertexGroupRange
    hp.isCovering e).trans
    (Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range))

/-- Evaluating the third clause factors through the Weyl-group description and then the quotient
by the normal image subgroup. -/
-- Proof sketch: unfold
-- `regularCoveringAutMulEquivQuotientMapVertexGroupRange`; its value is the application of
-- `weylGroupMulEquivQuotientOfNormal` to the Weyl-group class from the second clause.
theorem regularCoveringAutMulEquivQuotientMapVertexGroupRange_apply
    [IsConnected E] {e : E} (hp : Functor.IsRegularCovering p e)
    (α : Aut (Over.mk p.toCatHom)) :
    letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
    regularCoveringAutMulEquivQuotientMapVertexGroupRange hp α =
      Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range)
        (coveringAutMulEquivWeylGroupMapVertexGroupRange
          hp.isCovering e α) := rfl

/-- Corollary 3.5.10 (4): for a connected universal covering functor, the automorphism group of
the covering is canonically isomorphic to `π(B, p.obj e)`. -/
noncomputable def universalCoveringAutMulEquivVertexGroup
    [IsConnected E] {e : E} (hp : Functor.IsUniversalCovering p e) :
    Aut (Over.mk p.toCatHom) ≃* (p.obj e ⟶ p.obj e) :=
  letI : (Functor.mapVertexGroup p e).range.Normal :=
    hp.isRegularCovering.normal_mapVertexGroup_range
  (regularCoveringAutMulEquivQuotientMapVertexGroupRange
    hp.isRegularCovering).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hp.mapVertexGroup_range_eq_bot)).trans
      QuotientGroup.quotientBot)

/-- Evaluating the fourth clause specializes the quotient description along the equality
`p(π(E, e)) = ⊥`. -/
-- Proof sketch: unfold `universalCoveringAutMulEquivVertexGroup`; its value is the regular-case
-- quotient class, followed by the quotient identifications for the trivial subgroup.
theorem universalCoveringAutMulEquivVertexGroup_apply
    [IsConnected E] {e : E} (hp : Functor.IsUniversalCovering p e)
    (α : Aut (Over.mk p.toCatHom)) :
    letI : (Functor.mapVertexGroup p e).range.Normal :=
      hp.isRegularCovering.normal_mapVertexGroup_range
    universalCoveringAutMulEquivVertexGroup hp α =
      QuotientGroup.quotientBot
        ((QuotientGroup.quotientMulEquivOfEq
          (hp.mapVertexGroup_range_eq_bot))
          (regularCoveringAutMulEquivQuotientMapVertexGroupRange
            hp.isRegularCovering α)) := rfl

end

end CategoryTheory.Functor.IsCovering
