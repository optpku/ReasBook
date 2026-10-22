/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Theorem_1_2_9
import AlgebraicTopology_May_1999.Chap03.Corollary_3_7_8
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_9
import AlgebraicTopology_May_1999.Chap03.Example_3_3_9
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory FundamentalGroupoid
open CategoryTheory.Functor.IsCovering
open scoped FundamentalGroup

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)} {p' : C(E', B)}

/-- A morphism of covering spaces over `B` sends the fiber of `p` over `b` into the fiber of `p'`
over `b`. -/
-- Proof sketch: apply the commutative-triangle relation `Over.w h` to the chosen point of the
-- fiber and rewrite with the defining equation of that fiber point.
theorem coveringSpaceHom_obj_mem_fiber {b : B}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    p' (h.left.hom e.1) = b := by
  -- Evaluate the over-category commutative triangle on the chosen fiber point.
  have hcomm : p'.comp h.left.hom = p := by
    ext x
    have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hx
  have hObj : p' (h.left.hom e.1) = p e.1 := by
    simpa [ContinuousMap.comp_apply] using congrArg (fun f : C(E, B) ↦ f e.1) hcomm
  exact hObj.trans e.2

/-- Restriction of a morphism of covering spaces over `B` to the fiber over `b`. -/
def coveringSpaceHomToFiberFun (b : B) :
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      p ⁻¹' {b} → p' ⁻¹' {b} :=
  fun h e ↦ ⟨h.left.hom e.1, coveringSpaceHom_obj_mem_fiber h e⟩

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]
variable [PathConnectedSpace E'] [LocPathConnectedSpace E']

/-- The identity loop acts trivially on the fiber over `b` via monodromy. -/
-- Proof sketch: this is the identity law for the monodromy functor of the covering map.
theorem fiberMonodromy_one (hp : IsPathConnectedCoveringMap p) (b : B) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (1 : FundamentalGroup B b).toPath x = x := by
  -- The constant loop has trivial monodromy.
  simpa using congrFun (hp.isCoveringMap.monodromy_refl (x := b)) x

/-- Monodromy along loops in `π₁(B, b)` defines a left action on the fiber over `b`. -/
-- Proof sketch: `monodromyFunctor` is a functor, so it turns composition in
-- `FundamentalGroupoid B` into function composition on the fiber, while
-- `loop_homotopy_mul_eq_trans` identifies multiplication in `π₁(B,b)` with the corresponding
-- loop-class composition order.
theorem fiberMonodromy_mul (hp : IsPathConnectedCoveringMap p) (b : B)
    (γ₁ γ₂ : FundamentalGroup B b) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (γ₁ * γ₂).toPath x =
      hp.isCoveringMap.monodromy γ₁.toPath
        (hp.isCoveringMap.monodromy γ₂.toPath x) := by
  -- Route correction: `FundamentalGroup B b` uses the `End`-based multiplication on loop classes,
  -- so the correct ordinary-fiber action is by direct monodromy, not by inverse loops.
  change hp.isCoveringMap.monodromy
      ((γ₁.toPath * γ₂.toPath : Path.Homotopic.Quotient b b)) x =
    hp.isCoveringMap.monodromy γ₁.toPath
      (hp.isCoveringMap.monodromy γ₂.toPath x)
  -- Rewrite the group product as path-class concatenation, then apply monodromy functoriality.
  rw [loop_homotopy_mul_eq_trans]
  simpa using hp.isCoveringMap.monodromy_trans_apply γ₂.toPath γ₁.toPath x

/-- The monodromy action of `π₁(B, b)` on the fiber over `b`, obtained by transporting the
canonical fiber-translation action of the induced covering functor on `Π(B)` across the fiber
equivalence of Proposition 3.3.4. -/
@[reducible] noncomputable def fiberMonodromyMulAction
    (hp : IsPathConnectedCoveringMap p) (b : B) :
    MulAction (FundamentalGroup B b) (p ⁻¹' {b}) where
  smul γ x := hp.fiberTranslationMap γ.toPath x
  one_smul := by
    intro x
    -- The identity element acts by monodromy along the constant loop.
    change hp.fiberTranslationMap (1 : FundamentalGroup B b).toPath x = x
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_one hp b x
  mul_smul := by
    intro γ₁ γ₂ x
    -- Multiplication in `π₁(B, b)` matches composition of the direct monodromy maps.
    change hp.fiberTranslationMap (γ₁ * γ₂).toPath x =
      hp.fiberTranslationMap γ₁.toPath (hp.fiberTranslationMap γ₂.toPath x)
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_mul hp b γ₁ γ₂ x

/-- Helper for Theorem 3.7.9: restriction to the ordinary fiber agrees pointwise with the
categorical restriction map on the induced covering functors over `Π(B)`, transported across the
canonical fiber equivalence. -/
theorem coveringSpaceHomToFiberFun_eq_groupoidFiberMap
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    coveringSpaceHomToFiberFun b h e =
      hp'.fundamentalGroupoidMapFiberEquiv b
        (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
          (hp.toFundamentalGroupoidCoveringHom hp' h)
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm e)) := by
  -- Both sides are the image of `e.1` under the same underlying map of total spaces.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 3.7.9: transporting categorical fiber translation along the loop `γ`
through the canonical fiber equivalence recovers the ordinary fiber translation map. -/
theorem fundamentalGroupoidMapFiberEquiv_fiberTranslation
    (hp : IsPathConnectedCoveringMap p) (b : B) (γ : FundamentalGroup B b)
    (ξ : hp.fundamentalGroupoidMap.Fiber (mk b)) :
    hp.fundamentalGroupoidMapFiberEquiv b
        (CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) =
      hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
  -- This is exactly how `fiberTranslationMap` was defined in Example 3.3.9.
  apply Subtype.ext
  rfl

/-- Restriction to the fiber over `b` commutes with the monodromy action of `π₁(B, b)`. -/
-- Proof sketch: apply `mapOfCoveringsToFiberFun_comm` to the induced morphism of covering
-- functors on fundamental groupoids from Corollary 3.7.8, then transport the resulting
-- equivariance statement across the fiber equivalences of Proposition 3.3.4 and identify fiber
-- translation with monodromy using Example 3.3.9.
theorem coveringSpaceHomToFiberFun_comm
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (γ : FundamentalGroup B b)
    (e : p ⁻¹' {b}) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    coveringSpaceHomToFiberFun b h (γ • e) = γ • coveringSpaceHomToFiberFun b h e := by
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp'.fundamentalGroupoidMap_isCovering (mk b)
  let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
  let δ : mk b ⟶ mk b := (γ⁻¹).toPath
  have hinv_toPath :
      δ⁻¹ = γ.toPath := by
    -- Undoing the inverse-loop scalar recovers the direct loop class on `Π(B)`.
    change Path.Homotopic.Quotient.symm ((γ⁻¹).toPath) = γ.toPath
    change Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.symm γ.toPath) = γ.toPath
    refine Quotient.inductionOn γ.toPath ?_
    intro p
    change Path.Homotopic.Quotient.mk (p.symm.symm) = Path.Homotopic.Quotient.mk p
    simp
  have hsource :
      δ • ξ =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- The source-facing categorical action uses inverse loops, so acting by `γ⁻¹` translates
    -- exactly by the direct loop `γ`.
    simpa [hinv_toPath] using
      (CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := mk b) δ ξ)
  have htarget :
      (δ •
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering γ.toPath
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
    -- The same inverse-loop convention governs the target categorical fiber.
    simpa [hinv_toPath] using
      (CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp'.fundamentalGroupoidMap_isCovering)
        (b := mk b) δ
        (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
          (hp.toFundamentalGroupoidCoveringHom hp' h) ξ))
  have hξsmul :
      (hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e) =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- Transport the monodromy action back through the canonical fiber equivalence.
    apply (hp.fundamentalGroupoidMapFiberEquiv b).injective
    calc
      hp.fundamentalGroupoidMapFiberEquiv b
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e)) = γ • e := by
            simp
      _ = hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fiberTranslationMap γ.toPath e =
              hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            simp [ξ]
      _ =
          hp.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) := by
            simpa [ξ] using
              (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b γ ξ).symm
  -- Apply equivariance on categorical fibers and transport the result back to ordinary fibers.
  calc
    coveringSpaceHomToFiberFun b h (γ • e) =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e))) := by
          simpa using coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h (γ • e)
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ)) := by
          rw [hξsmul]
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering γ.toPath
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          rw [← hsource]
          rw [CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun_comm
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) δ ξ]
          exact congrArg (hp'.fundamentalGroupoidMapFiberEquiv b) htarget
    _ =
        hp'.fiberTranslationMap γ.toPath
          (hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b γ
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)
    _ = γ • coveringSpaceHomToFiberFun b h e := by
          rw [coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e]
          rfl

/-- Restriction to the fiber over `b` as a bundled `π₁(B, b)`-equivariant map. -/
def coveringSpaceHomToFiber
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      (p ⁻¹' {b}) →[FundamentalGroup B b] (p' ⁻¹' {b}) :=
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  fun h ↦
    { toFun := coveringSpaceHomToFiberFun b h
      map_smul' := coveringSpaceHomToFiberFun_comm hp hp' b h }

/-- Theorem 3.7.9: for path-connected covering spaces `p : E → B` and `p' : E' → B`, restriction
to the fiber over `b` gives a bijection between morphisms of covering spaces over `B` and
`π₁(B, b)`-equivariant maps `(p ⁻¹' {b}) → (p' ⁻¹' {b})`. -/
-- Proof sketch: Corollary 3.7.8 identifies morphisms of covering spaces with morphisms of the
-- induced covering functors on fundamental groupoids. Then `mapOfCoveringsToFiber_bijective`,
-- applied to those induced covering functors at `mk b`, gives the canonical bijection on groupoid
-- fibers. Transport that bijection across `fundamentalGroupoidMapFiberEquiv` and use Example 3.3.9
-- to identify the transported action with monodromy on the topological fibers.
theorem coveringSpaceHomToFiber_bijective
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    Function.Bijective (coveringSpaceHomToFiber hp hp' b) := by
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp'.fundamentalGroupoidMap_isCovering (mk b)
  have hTop := toFundamentalGroupoidCoveringHom_bijective hp hp'
  have hGroupoid :=
    CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber_bijective
      hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
  constructor
  · intro h₁ h₂ hEq
    have hFiberEq :
        CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₁) =
          CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₂) := by
      apply MulActionHom.ext
      intro ξ
      let e : p ⁻¹' {b} := hp.fundamentalGroupoidMapFiberEquiv b ξ
      -- Equality on ordinary fibers transports to equality on categorical fibers.
      apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
      calc
        hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h₁) ξ) =
            coveringSpaceHomToFiber hp hp' b h₁ e := by
              simpa [coveringSpaceHomToFiber, e] using
                (coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₁ e).symm
        _ = coveringSpaceHomToFiber hp hp' b h₂ e := by
              exact congrArg (fun φ ↦ φ e) hEq
        _ =
            hp'.fundamentalGroupoidMapFiberEquiv b
              (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
                (hp.toFundamentalGroupoidCoveringHom hp' h₂) ξ) := by
              simpa [coveringSpaceHomToFiber, e] using
                coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₂ e
    exact hTop.1 (hGroupoid.1 hFiberEq)
  · intro φ
    let φcat :
        hp.fundamentalGroupoidMap.Fiber (mk b) →[(mk b ⟶ mk b)]
          hp'.fundamentalGroupoidMap.Fiber (mk b) :=
      { toFun := fun ξ ↦
          (hp'.fundamentalGroupoidMapFiberEquiv b).symm
            (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))
        map_smul' := fun γ ξ ↦ by
          -- Transport equivariance of `φ` through the canonical fiber equivalences.
          have htransport :
              hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ) =
                (fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fundamentalGroupoidMapFiberEquiv b
                (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                  hp.fundamentalGroupoidMap_isCovering γ⁻¹ ξ) =
              hp.fiberTranslationMap γ⁻¹ (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b
              (γ := (γ⁻¹ : FundamentalGroup B b)) ξ
          have htransport' :
              (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
            change hp'.fiberTranslationMap γ⁻¹
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
              hp'.fundamentalGroupoidMapFiberEquiv b
                (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                  hp'.fundamentalGroupoidMap_isCovering γ⁻¹
                  ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))))
            exact (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b
              (γ := (γ⁻¹ : FundamentalGroup B b))
              ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)))).symm
          apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
          calc
            hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)))) =
                φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)) := by
                  simp
            _ = φ ((fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact congrArg φ htransport
            _ = (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact φ.map_smul' (γ⁻¹ : FundamentalGroup B b)
                    (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            _ =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
                  exact htransport' }
    obtain ⟨k, hk⟩ := hGroupoid.2 φcat
    obtain ⟨h, hh⟩ := hTop.2 k
    refine ⟨h, ?_⟩
    apply MulActionHom.ext
    intro e
    let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
    have hkξ :
        CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ =
          φcat ξ := by
      simpa [hh] using congrArg (fun ψ ↦ ψ ξ) hk
    -- The categorical surjection lifts back to the required topological covering map.
    calc
      coveringSpaceHomToFiber hp hp' b h e =
          hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
              hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
            simpa [coveringSpaceHomToFiber, ξ] using
              coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e
      _ = hp'.fundamentalGroupoidMapFiberEquiv b (φcat ξ) := by
            rw [hkξ]
      _ = φ e := by
            change hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) = φ e
            simp [ξ]

end

end IsPathConnectedCoveringMap
