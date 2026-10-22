/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_6
import AlgebraicTopology_May_1999.Chap02.Proposition_2_8_6
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TopCat

universe u v u₁ v₁ u₂ v₂

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {E₁ : Type u₁} {B₁ : Type v₁} {E₂ : Type u₂} {B₂ : Type v₂}
variable [TopologicalSpace E₁] [TopologicalSpace B₁] [TopologicalSpace E₂] [TopologicalSpace B₂]

namespace IsEvenlyCovered

/-- The product of two evenly covered neighborhoods is evenly covered for the product map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsEvenlyCovered p b₁ (p ⁻¹' ({b₁} : Set B₁)))
    (hq : IsEvenlyCovered q b₂ (q ⁻¹' ({b₂} : Set B₂))) :
    IsEvenlyCovered (Prod.map p q) (b₁, b₂)
      (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hqU₂, H₂, hH₂⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    letI : DiscreteTopology (p ⁻¹' ({b₁} : Set B₁)) := hpdisc
    letI : DiscreteTopology (q ⁻¹' ({b₂} : Set B₂)) := hqdisc
    letI : DiscreteTopology
        ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) := inferInstance
    exact hFiber.discreteTopology
  let H :
      ↑(Prod.map p q ⁻¹' (U₁ ×ˢ U₂)) ≃ₜ
        ↑(U₁ ×ˢ U₂) × (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.setCongr hpre).trans <|
      (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
        (H₁.prodCongr H₂).trans <|
          (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
            (q ⁻¹' ({b₂} : Set B₂))).trans <|
            Homeomorph.prodCongr
              (Homeomorph.Set.prod U₁ U₂).symm
              hFiber
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, ?_, H, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [H, Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [H, Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsEvenlyCovered

namespace IsPathConnectedEvenlyCovered

/-- Path-connected evenly covered neighborhoods are stable under products. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂} {b₁ : B₁} {b₂ : B₂}
    (hp : IsPathConnectedEvenlyCovered p b₁)
    (hq : IsPathConnectedEvenlyCovered q b₂) :
    IsPathConnectedEvenlyCovered (Prod.map p q) (b₁, b₂) := by
  rcases hp with ⟨hpdisc, U₁, hb₁U₁, hU₁, hU₁Path, hpU₁, H₁, hH₁⟩
  rcases hq with ⟨hqdisc, U₂, hb₂U₂, hU₂, hU₂Path, hqU₂, H₂, hH₂⟩
  have hUProd : IsPathConnected (U₁ ×ˢ U₂) := by
    rw [isPathConnected_iff]
    refine ⟨hU₁Path.nonempty.prod hU₂Path.nonempty, ?_⟩
    intro x hx y hy
    let hx₁ := (isPathConnected_iff.mp hU₁Path).2 x.1 hx.1 y.1 hy.1
    let hx₂ := (isPathConnected_iff.mp hU₂Path).2 x.2 hx.2 y.2 hy.2
    exact ⟨hx₁.somePath.prod hx₂.somePath, fun t ↦ ⟨hx₁.somePath_mem t, hx₂.somePath_mem t⟩⟩
  have hpre :
      Prod.map p q ⁻¹' (U₁ ×ˢ U₂) = (p ⁻¹' U₁) ×ˢ (q ⁻¹' U₂) := by
    ext x
    simp [Prod.map]
  have hfiber :
      Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂)) =
        (p ⁻¹' ({b₁} : Set B₁)) ×ˢ (q ⁻¹' ({b₂} : Set B₂)) := by
    ext x
    simp [Prod.map]
  let hFiber :
      ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) ≃ₜ
        (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) :=
    (Homeomorph.Set.prod (p ⁻¹' ({b₁} : Set B₁)) (q ⁻¹' ({b₂} : Set B₂))).symm.trans
      (Homeomorph.setCongr hfiber.symm)
  have hdisc : DiscreteTopology (Prod.map p q ⁻¹' ({(b₁, b₂)} : Set (B₁ × B₂))) := by
    letI : DiscreteTopology (p ⁻¹' ({b₁} : Set B₁)) := hpdisc
    letI : DiscreteTopology (q ⁻¹' ({b₂} : Set B₂)) := hqdisc
    letI : DiscreteTopology
        ((p ⁻¹' ({b₁} : Set B₁)) × (q ⁻¹' ({b₂} : Set B₂))) := inferInstance
    exact hFiber.discreteTopology
  refine ⟨hdisc, U₁ ×ˢ U₂, ⟨hb₁U₁, hb₂U₂⟩, hU₁.prod hU₂, hUProd, ?_, ?_, ?_⟩
  · simpa [Prod.map] using hpU₁.prod hqU₂
  · exact
      (Homeomorph.setCongr hpre).trans <|
        (Homeomorph.Set.prod (p ⁻¹' U₁) (q ⁻¹' U₂)).trans <|
          (H₁.prodCongr H₂).trans <|
            (Homeomorph.prodProdProdComm U₁ (p ⁻¹' ({b₁} : Set B₁)) U₂
              (q ⁻¹' ({b₂} : Set B₂))).trans <|
              Homeomorph.prodCongr
                (Homeomorph.Set.prod U₁ U₂).symm
                hFiber
  · intro x
    have hx₁ : p x.1.1 ∈ U₁ := by
      simpa [Prod.map] using x.2.1
    have hx₂ : q x.1.2 ∈ U₂ := by
      simpa [Prod.map] using x.2.2
    ext
    · simpa [Prod.map] using hH₁ ⟨x.1.1, hx₁⟩
    · simpa [Prod.map] using hH₂ ⟨x.1.2, hx₂⟩

end IsPathConnectedEvenlyCovered

namespace Homeomorph

/-- Example 3.1.7 (1): every homeomorphism is a covering map. -/
-- Proof sketch: a homeomorphism identifies the source with the target, so every point has an open
-- neighborhood over which the map is trivial with singleton fiber.
theorem isCoveringMap (h : X ≃ₜ Y) : IsCoveringMap h := by
  have hf : Continuous (fun x : X ↦ ((h x, ()) : Y × Unit)) := by
    simpa using
      h.continuous.prodMk (continuous_const : Continuous fun _ : X ↦ (() : Unit))
  have hg : Continuous (fun yp : Y × Unit ↦ h.symm yp.1) := by
    fun_prop
  let t : Bundle.Trivialization Unit h := by
    refine
      { toFun := fun x ↦ (h x, ())
        invFun := fun yp : Y × Unit ↦ h.symm yp.1
        source := (_root_.Set.univ : Set X)
        target := (_root_.Set.univ : Set Y) ×ˢ (_root_.Set.univ : Set Unit)
        map_source' := ?_
        map_target' := ?_
        left_inv' := ?_
        right_inv' := ?_
        open_source := isOpen_univ
        open_target := isOpen_univ.prod isOpen_univ
        continuousOn_toFun := Continuous.continuousOn hf
        continuousOn_invFun := Continuous.continuousOn hg
        baseSet := (_root_.Set.univ : Set Y)
        open_baseSet := isOpen_univ
        source_eq := rfl
        target_eq := rfl
        proj_toFun := by intro x hx; rfl }
    · intro x hx
      simp [Set.mem_univ]
    · intro yp hyp
      simp [Set.mem_univ]
    · intro x hx
      simp
    · rintro ⟨y, u⟩ hyp
      cases u
      simp
  exact IsCoveringMap.mk h (fun _ ↦ Unit) (fun _ ↦ t) fun _ ↦ by simp [t]

/-- Example 3.1.7 (1), source-facing form: on a locally path-connected target, every
homeomorphism is a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap [LocPathConnectedSpace Y] (h : X ≃ₜ Y) :
    IsPathConnectedCoveringMap h :=
  h.isCoveringMap.isPathConnectedCoveringMap h.surjective

end Homeomorph

namespace IsCoveringMap

/-- Example 3.1.7 (2): the product of two covering maps is again a covering map. -/
-- Proof sketch: take evenly covered neighborhoods for the two factors and use the product of the
-- corresponding local trivializations to trivialize the product map.
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) :
    IsCoveringMap (Prod.map p q) := by
  rintro ⟨b₁, b₂⟩
  simpa using (hp b₁).prodMap (hq b₂)

end IsCoveringMap

namespace IsPathConnectedCoveringMap

/-- Example 3.1.7 (2), source-facing form: the product of two path-connected covering maps is
again a path-connected covering map. -/
theorem prodMap {p : E₁ → B₁} {q : E₂ → B₂}
    (hp : IsPathConnectedCoveringMap p) (hq : IsPathConnectedCoveringMap q) :
    IsPathConnectedCoveringMap (Prod.map p q) := by
  refine ⟨?_, fun b ↦ ?_⟩
  · simpa using hp.surjective.prodMap hq.surjective
  · rcases b with ⟨b₁, b₂⟩
    simpa using (hp.2 b₁).prodMap (hq.2 b₂)

end IsPathConnectedCoveringMap

/- Example 3.1.7 (3): the map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by
`Real.fourierChar`, is a covering map. -/
recall real_fourierChar_isCoveringMap : IsCoveringMap Real.fourierChar

namespace Circle

private instance : LocPathConnectedSpace Circle := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := inferInstance
  let _ : LocPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) := inferInstance
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle

end Circle

/- The map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by `Real.fourierChar`, is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem real_fourierChar_isPathConnectedCoveringMap :
    IsPathConnectedCoveringMap Real.fourierChar := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have hsurjExp : Function.Surjective Circle.exp := by
    intro z
    rcases Circle.surjOn_exp_neg_pi_pi (by simp : z ∈ (Set.univ : Set Circle)) with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hsurj : Function.Surjective Real.fourierChar := by
    simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
      hsurjExp.comp (Homeomorph.smulOfNeZero (2 * Real.pi) h2pi).surjective
  exact real_fourierChar_isCoveringMap.isPathConnectedCoveringMap hsurj

namespace Circle

/-- Example 3.1.7 (4): for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a covering map. -/
-- Proof sketch: `Circle.isQuotientCoveringMap_npow n` gives the stronger quotient-covering
-- statement, and `IsQuotientCoveringMap.isCoveringMap` forgets the quotient-action data.
theorem isCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsCoveringMap ((· ^ n) : Circle → Circle) := by
  letI : NeZero n := ⟨hn⟩
  exact (isQuotientCoveringMap_npow n).isCoveringMap

/-- Example 3.1.7 (4), source-facing form: for `n ≠ 0`, the power map `z ↦ z ^ n` on `S¹` is a
path-connected covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap_npow (n : ℕ) (hn : n ≠ 0) :
    IsPathConnectedCoveringMap ((· ^ n) : Circle → Circle) := by
  letI : NeZero n := ⟨hn⟩
  exact
      (isCoveringMap_npow n hn).isPathConnectedCoveringMap
      (isQuotientCoveringMap_npow n).surjective

end Circle

/-- Helper for Example 3.1.7: the internal subtype model of `S^n` as the unit sphere in
`ℝ^(n+1)`. -/
private abbrev SphereModel (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Example 3.1.7: the textbook sphere `𝕊 n` is the `ULift` of the concrete sphere
model. -/
private abbrev sphereModelHomeomorph (n : ℕ) : 𝕊 n ≃ₜ SphereModel n := Homeomorph.ulift

/-- Helper for Example 3.1.7: the sphere model is Hausdorff. -/
private instance sphere_t2Space (n : ℕ) : T2Space (𝕊 n) :=
  (sphereModelHomeomorph n).symm.t2Space

/-- Helper for Example 3.1.7: the sphere model is locally compact. -/
private instance sphere_locallyCompactSpace (n : ℕ) : LocallyCompactSpace (𝕊 n) :=
  (sphereModelHomeomorph n).isOpenEmbedding.locallyCompactSpace

/-- Helper for Example 3.1.7: the antipodal map on `𝕊 n`. -/
private def sphereAntipode (n : ℕ) (x : 𝕊 n) : 𝕊 n :=
  ULift.up (-x.down)

/-- The antipodal map gives the canonical negation on `S^n`. -/
instance (n : ℕ) : Neg (𝕊 n) where
  neg := sphereAntipode n

/-- Helper for Example 3.1.7: points on the concrete unit sphere are nonzero. -/
private theorem sphereModel_ne_zero (n : ℕ) (x : SphereModel n) :
    x.1 ≠ (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
  -- Read the subtype condition as the norm-one equation in the ambient Euclidean space.
  intro hx
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [SphereModel, Metric.mem_sphere, dist_eq_norm] using x.2
  simp [hx] at hxnorm

/-- Helper for Example 3.1.7: the antipodal map has no fixed points on `S^n`. -/
private theorem sphereAntipode_ne_self (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n x ≠ x := by
  -- Route correction: avoid the broken later owner and prove freeness of the antipodal action
  -- directly from the concrete sphere model.
  intro hx
  have hx' : -(x.down.1) = x.down.1 := by
    simpa [sphereAntipode] using
      congrArg (fun y : 𝕊 n ↦ y.down.1) hx
  have hsum : x.down.1 + x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    calc
      x.down.1 + x.down.1 = -x.down.1 + x.down.1 := by
        simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z + x.down.1) hx'.symm
      _ = 0 := by simp
  have htwo : (2 : ℝ) • x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [two_smul] using hsum
  have hx0 : x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  exact sphereModel_ne_zero n x.down hx0

/-- The antipodal involution has no fixed points on `S^n`. -/
theorem sphere_neg_ne_self (n : ℕ) (x : 𝕊 n) : (-x : 𝕊 n) ≠ x :=
  sphereAntipode_ne_self n x

/-- Helper for Example 3.1.7: the antipodal map is an involution. -/
private theorem sphereAntipode_involutive (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n (sphereAntipode n x) = x := by
  -- Unfold the `ULift` model of the sphere and compute.
  apply ULift.ext
  apply Subtype.ext
  simp [sphereAntipode]

/-- Helper for Example 3.1.7: the two-element symmetry group generated by the antipodal map. -/
private inductive AntipodalSymmetry where
  | one
  | neg
deriving DecidableEq, Fintype

/-- Helper for Example 3.1.7: `AntipodalSymmetry` has an identity element. -/
private instance : One AntipodalSymmetry := ⟨AntipodalSymmetry.one⟩

/-- Helper for Example 3.1.7: multiplying antipodal symmetries composes them. -/
private instance : Mul AntipodalSymmetry where
  mul g h :=
    match g, h with
    | .one, h => h
    | .neg, .one => .neg
    | .neg, .neg => .one

/-- Helper for Example 3.1.7: each antipodal symmetry is its own inverse. -/
private instance : Inv AntipodalSymmetry where
  inv g := g

/-- Helper for Example 3.1.7: the antipodal symmetries form a group. -/
private instance : Group AntipodalSymmetry where
  one_mul g := by cases g <;> rfl
  mul_one g := by cases g <;> rfl
  mul_assoc g h k := by cases g <;> cases h <;> cases k <;> rfl
  inv_mul_cancel g := by cases g <;> rfl

/-- Helper for Example 3.1.7: the antipodal symmetry group acts on `S^n`. -/
private def sphereAntipodalSMul (n : ℕ) (g : AntipodalSymmetry) (x : 𝕊 n) : 𝕊 n :=
  match g with
  | .one => x
  | .neg => sphereAntipode n x

/-- Helper for Example 3.1.7: `AntipodalSymmetry` acts on `S^n`. -/
private instance sphereAntipodalSMulInst (n : ℕ) : SMul AntipodalSymmetry (𝕊 n) where
  smul := sphereAntipodalSMul n

/-- Helper for Example 3.1.7: the antipodal symmetry action is a group action. -/
private instance sphereAntipodalMulAction (n : ℕ) : MulAction AntipodalSymmetry (𝕊 n) where
  one_smul x := by
    rfl
  mul_smul g h x := by
    -- There are only four group-element cases, and the nontrivial one uses involutivity.
    change sphereAntipodalSMul n (g * h) x =
      sphereAntipodalSMul n g (sphereAntipodalSMul n h x)
    cases g <;> cases h <;> simp [sphereAntipodalSMul, sphereAntipode_involutive]

/-- Helper for Example 3.1.7: each antipodal symmetry acts continuously on `S^n`. -/
private instance sphereAntipodalContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul AntipodalSymmetry (𝕊 n) where
  continuous_const_smul g := by
    -- The only nontrivial action map is the continuous antipodal map.
    cases g
    · simpa [sphereAntipodalSMul] using
        (continuous_id : Continuous fun x : 𝕊 n ↦ x)
    · simpa [sphereAntipodalSMul, sphereAntipode] using
        (continuous_uliftUp.comp (continuous_neg.comp continuous_uliftDown) :
          Continuous fun x : 𝕊 n ↦ ULift.up (-x.down))

/-- Helper for Example 3.1.7: the antipodal action is free, hence cancellative. -/
private instance sphereAntipodalIsCancelSMul (n : ℕ) :
    IsCancelSMul AntipodalSymmetry (𝕊 n) where
  right_cancel' g h x hgh := by
    -- The only potentially nontrivial equalities would force a fixed point of the antipode.
    change sphereAntipodalSMul n g x = sphereAntipodalSMul n h x at hgh
    cases g <;> cases h
    · rfl
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh.symm)
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh)
    · rfl

/-- Helper for Example 3.1.7: quotient equality is exactly equality up to the antipodal map. -/
private theorem sphere_eq_or_neg_eq_iff_orbitRel (n : ℕ) {x y : 𝕊 n} :
    x = y ∨ x = -y ↔ MulAction.orbitRel AntipodalSymmetry (𝕊 n) x y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro hxy
    rcases hxy with rfl | hxy
    · exact ⟨1, by simp⟩
    · exact ⟨AntipodalSymmetry.neg, by simpa [sphereAntipodalSMul] using hxy.symm⟩
  · rintro ⟨g, hg⟩
    cases g
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr (by simpa [sphereAntipodalSMul] using hg.symm)

/-- Helper for Example 3.1.7: the quotient of `S^n` by the antipodal action, used as a model of
`RP^n`. -/
abbrev RealProjectiveSpace (n : ℕ) := MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)

/-- Helper for Example 3.1.7: the canonical quotient map from `S^n` to `RP^n`. -/
def sphereToRealProjectiveSpace (n : ℕ) : 𝕊 n → RealProjectiveSpace n :=
  Quotient.mk''

@[simp] theorem sphereToRealProjectiveSpace_eq_iff (n : ℕ) {x y : 𝕊 n} :
    sphereToRealProjectiveSpace n x = sphereToRealProjectiveSpace n y ↔ x = y ∨ x = -y := by
  change Quotient.mk'' x = (Quotient.mk'' y : MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)) ↔
    x = y ∨ x = -y
  rw [Quotient.eq'']
  exact (sphere_eq_or_neg_eq_iff_orbitRel n).symm

/- Example 3.1.7 (5): the antipodal quotient map `S^n → RP^n` is a covering map. -/
-- Proof sketch: express `RP^n` as the orbit quotient by the free antipodal action and apply the
-- general quotient-covering theorem for properly discontinuous actions.
theorem sphereToRealProjectiveSpace_isCoveringMap (n : ℕ) :
    IsCoveringMap (sphereToRealProjectiveSpace n) := by
  -- The quotient criterion applies once the sphere carries the free antipodal action data above.
  simpa [RealProjectiveSpace, sphereToRealProjectiveSpace] using
    ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := AntipodalSymmetry) (E := 𝕊 n)).isCoveringMap)
