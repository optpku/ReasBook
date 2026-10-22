/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

-- Proof sketch: Fact 6.14(6) identifies `ri C` with `qri C` in finite dimension, and
-- Fact 6.14(13) then sends `qri C` through the continuous linear image `L`.
/-- Corollary 6.15 (1): for a nonempty convex subset `C` of a finite-dimensional real Hilbert
space and a continuous linear map `L : H →L[ℝ] K` into a finite-dimensional real Hilbert space,
the relative interior of `L '' C` is the image of the relative interior of `C`. -/
theorem relativeInterior_image_eq_image_relativeInterior_of_finiteDimensional
    (L : H →L[ℝ] K) (C : Set H) (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) :
    ri (L '' C) = L '' ri C := by
  -- First identify `ri C` with `qri C` and use nonemptiness of `ri C` to trigger Fact 6.14 (13).
  have hri_nonempty : (ri C).Nonempty :=
    relativeInterior_nonempty_of_finiteDimensional hC_nonempty hC_convex
  have hqri_nonempty : (qri C).Nonempty := by
    rw [← relativeInterior_eq_quasiRelativeInterior_of_finiteDimensional hC_convex]
    exact hri_nonempty
  -- Then send the generalized relative interior through the linear image and rewrite back to `ri`.
  calc
    ri (L '' C) = L '' qri C :=
      relativeInterior_image_eq_image_quasiRelativeInterior L hC_convex hqri_nonempty
    _ = L '' ri C := by
      rw [← relativeInterior_eq_quasiRelativeInterior_of_finiteDimensional hC_convex]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Helper for Corollary 6.15: the affine span of a nonempty product is the product of the affine
spans. -/
lemma affineSpan_prod_eq_prod_affineSpan {C D : Set H} (hC_nonempty : C.Nonempty)
    (hD_nonempty : D.Nonempty) :
    (affineSpan ℝ (C ×ˢ D : Set (H × H)) : Set (H × H)) =
      (affineSpan ℝ C : Set H) ×ˢ (affineSpan ℝ D : Set H) := by
  let S : AffineSubspace ℝ (H × H) := affineSpan ℝ (C ×ˢ D : Set (H × H))
  have hsubset : (S : Set (H × H)) ⊆ (affineSpan ℝ C : Set H) ×ˢ (affineSpan ℝ D : Set H) := by
    intro p hp
    constructor
    · -- Project the product affine span to the first factor.
      have hfst_map : AffineSubspace.map (AffineMap.fst : H × H →ᵃ[ℝ] H) S = affineSpan ℝ C := by
        simp [S, AffineSubspace.map_span, Set.fst_image_prod _ hD_nonempty]
      have hpmap : p.1 ∈ AffineSubspace.map (AffineMap.fst : H × H →ᵃ[ℝ] H) S := by
        exact ⟨p, hp, rfl⟩
      simpa [hfst_map] using hpmap
    · -- Project the product affine span to the second factor.
      have hsnd_map : AffineSubspace.map (AffineMap.snd : H × H →ᵃ[ℝ] H) S = affineSpan ℝ D := by
        simp [S, AffineSubspace.map_span, Set.snd_image_prod hC_nonempty _]
      have hpmap : p.2 ∈ AffineSubspace.map (AffineMap.snd : H × H →ᵃ[ℝ] H) S := by
        exact ⟨p, hp, rfl⟩
      simpa [hsnd_map] using hpmap
  have hsupset : (affineSpan ℝ C : Set H) ×ˢ (affineSpan ℝ D : Set H) ⊆ (S : Set (H × H)) := by
    rcases hC_nonempty with ⟨c0, hc0⟩
    rcases hD_nonempty with ⟨d0, hd0⟩
    intro p hp
    rcases hp with ⟨hpC, hpD⟩
    have hleft : (p.1, d0) ∈ (S : Set (H × H)) := by
      -- Hold the second coordinate fixed at `d0` and span the first coordinate inside `C`.
      let P : ∀ x, x ∈ affineSpan ℝ C → Prop := fun x _ ↦ (x, d0) ∈ (S : Set (H × H))
      have hmem : ∀ y (hy : y ∈ C), P y (subset_affineSpan ℝ C hy) := by
        intro y hy
        exact subset_affineSpan ℝ (C ×ˢ D : Set (H × H)) ⟨hy, hd0⟩
      have hstep :
          ∀ (c : ℝ) (u) (hu : u ∈ affineSpan ℝ C) (v) (hv : v ∈ affineSpan ℝ C) (w)
            (hw : w ∈ affineSpan ℝ C), P u hu → P v hv → P w hw →
            P (c • (u - v) + w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw) := by
        intro c u hu v hv w hw huP hvP hwP
        simpa [P, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_sub, Prod.smul_mk,
          Prod.mk_add_mk] using (AffineSubspace.smul_vsub_vadd_mem S c huP hvP hwP)
      exact affineSpan_induction' (s := C) (p := P) hmem hstep hpC
    have hright : (c0, p.2) ∈ (S : Set (H × H)) := by
      -- Hold the first coordinate fixed at `c0` and span the second coordinate inside `D`.
      let P : ∀ y, y ∈ affineSpan ℝ D → Prop := fun y _ ↦ (c0, y) ∈ (S : Set (H × H))
      have hmem : ∀ y (hy : y ∈ D), P y (subset_affineSpan ℝ D hy) := by
        intro y hy
        exact subset_affineSpan ℝ (C ×ˢ D : Set (H × H)) ⟨hc0, hy⟩
      have hstep :
          ∀ (c : ℝ) (u) (hu : u ∈ affineSpan ℝ D) (v) (hv : v ∈ affineSpan ℝ D) (w)
            (hw : w ∈ affineSpan ℝ D), P u hu → P v hv → P w hw →
            P (c • (u - v) + w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw) := by
        intro c u hu v hv w hw huP hvP hwP
        simpa [P, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_sub, Prod.smul_mk,
          Prod.mk_add_mk] using (AffineSubspace.smul_vsub_vadd_mem S c huP hvP hwP)
      exact affineSpan_induction' (s := D) (p := P) hmem hstep hpD
    have hbase : (c0, d0) ∈ (S : Set (H × H)) :=
      subset_affineSpan ℝ (C ×ˢ D : Set (H × H)) ⟨hc0, hd0⟩
    -- Recombine the two one-sided spanning facts inside the affine subspace.
    have hcombine : (1 : ℝ) • ((p.1, d0) - (c0, d0)) + (c0, p.2) ∈ (S : Set (H × H)) := by
      simpa using AffineSubspace.smul_vsub_vadd_mem S (1 : ℝ) hleft hbase hright
    simpa [Prod.smul_mk, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcombine
  exact Set.Subset.antisymm hsubset hsupset

/-- Helper for Corollary 6.15: the intrinsic interior of a nonempty product is the product of the
intrinsic interiors. -/
lemma bauschke_intrinsicInterior_prod_eq_prod_intrinsicInterior {C D : Set H}
    (hC_nonempty : C.Nonempty)
    (hD_nonempty : D.Nonempty) :
    intrinsicInterior ℝ (C ×ˢ D : Set (H × H)) =
      intrinsicInterior ℝ C ×ˢ intrinsicInterior ℝ D := by
  let hspan :
      (affineSpan ℝ (C ×ˢ D : Set (H × H)) : Set (H × H)) =
        (affineSpan ℝ C : Set H) ×ˢ (affineSpan ℝ D : Set H) :=
    affineSpan_prod_eq_prod_affineSpan hC_nonempty hD_nonempty
  let e : affineSpan ℝ (C ×ˢ D : Set (H × H)) ≃ₜ (affineSpan ℝ C) × (affineSpan ℝ D) :=
    (Homeomorph.setCongr hspan).trans
      (Homeomorph.Set.prod (affineSpan ℝ C : Set H) (affineSpan ℝ D : Set H))
  have hpre :
      e '' ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
        Set (affineSpan ℝ (C ×ˢ D : Set (H × H)))) =
        (((↑) ⁻¹' C : Set (affineSpan ℝ C)) ×ˢ ((↑) ⁻¹' D : Set (affineSpan ℝ D))) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [Homeomorph.Set.prod, Homeomorph.setCongr] using hq
    · intro hp
      refine ⟨e.symm p, ?_, ?_⟩
      · simpa [Homeomorph.Set.prod, Homeomorph.setCongr] using hp
      · simpa using Homeomorph.apply_symm_apply e p
  have hinterior :
      e '' interior ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
        Set (affineSpan ℝ (C ×ˢ D : Set (H × H)))) =
        interior ((((↑) ⁻¹' C : Set (affineSpan ℝ C)) ×ˢ ((↑) ⁻¹' D : Set (affineSpan ℝ D)))) := by
    calc
      e '' interior ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
        Set (affineSpan ℝ (C ×ˢ D : Set (H × H)))) =
          interior (e '' ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
            Set (affineSpan ℝ (C ×ˢ D : Set (H × H))))) := by
              simpa using
                e.image_interior ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
                  Set (affineSpan ℝ (C ×ˢ D : Set (H × H))))
      _ = interior ((((↑) ⁻¹' C : Set (affineSpan ℝ C)) ×ˢ ((↑) ⁻¹' D : Set (affineSpan ℝ D)))) := by
            rw [hpre]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    -- Push the intrinsic-interior witness through the product homeomorphism.
    have hq' :
        e q ∈ interior ((((↑) ⁻¹' C : Set (affineSpan ℝ C)) ×ˢ ((↑) ⁻¹' D : Set (affineSpan ℝ D)))) := by
      rw [← hinterior]
      exact ⟨q, hq, rfl⟩
    rw [interior_prod_eq] at hq'
    exact ⟨⟨(e q).1, hq'.1, rfl⟩, ⟨(e q).2, hq'.2, rfl⟩⟩
  · rintro ⟨hpC, hpD⟩
    rcases hpC with ⟨qC, hqC, hqC_eq⟩
    rcases hpD with ⟨qD, hqD, hqD_eq⟩
    -- Combine the two intrinsic-interior witnesses inside the product affine span.
    have hpair :
        (qC, qD) ∈ interior ((((↑) ⁻¹' C : Set (affineSpan ℝ C)) ×ˢ ((↑) ⁻¹' D : Set (affineSpan ℝ D)))) := by
      rw [interior_prod_eq]
      exact ⟨hqC, hqD⟩
    have hback :
        e.symm (qC, qD) ∈ interior ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
          Set (affineSpan ℝ (C ×ˢ D : Set (H × H)))) := by
      have himage :
          (qC, qD) ∈ e '' interior ((↑) ⁻¹' (C ×ˢ D : Set (H × H)) :
            Set (affineSpan ℝ (C ×ˢ D : Set (H × H)))) := by
        rw [hinterior]
        exact hpair
      rcases himage with ⟨q, hq, hqe⟩
      have hqeq : q = e.symm (qC, qD) := by
        apply e.injective
        simpa using hqe
      exact hqeq ▸ hq
    refine ⟨e.symm (qC, qD), hback, ?_⟩
    calc
      (((e.symm (qC, qD)) : affineSpan ℝ (C ×ˢ D : Set (H × H))) : H × H)
          = ((qC : H), (qD : H)) := by
              exact congrArg
                (fun z : (affineSpan ℝ C) × (affineSpan ℝ D) => ((z.1 : H), (z.2 : H)))
                (Homeomorph.apply_symm_apply e (qC, qD))
      _ = p := by
            exact Prod.ext hqC_eq hqD_eq

/-- Helper for Corollary 6.15: in finite dimensions, an affine equivalence sends intrinsic
interior to intrinsic interior. -/
lemma affineEquiv_image_intrinsicInterior_of_finiteDimensional
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : E ≃ᵃ[ℝ] F) (s : Set E) :
    intrinsicInterior ℝ (φ '' s) = φ '' intrinsicInterior ℝ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [intrinsicInterior]
  haveI : Nonempty s := hs.to_subtype
  haveI : Nonempty (affineSpan ℝ s) := by
    rcases hs with ⟨x, hx⟩
    exact ⟨⟨x, subset_affineSpan ℝ s hx⟩⟩
  haveI : Nonempty (affineSpan ℝ (φ '' s)) := by
    rcases hs with ⟨x, hx⟩
    exact ⟨⟨φ x, subset_affineSpan ℝ (φ '' s) ⟨x, hx, rfl⟩⟩⟩
  let e₀ : affineSpan ℝ s ≃ᵃ[ℝ] (affineSpan ℝ s).map φ.toAffineMap :=
    (affineSpan ℝ s).equivMapOfInjective φ.toAffineMap φ.injective
  let e₁ : (affineSpan ℝ s).map φ.toAffineMap ≃ᵃ[ℝ] affineSpan ℝ (φ '' s) :=
    AffineEquiv.ofEq _ _ (AffineSubspace.map_span (f := φ.toAffineMap) s)
  let e : affineSpan ℝ s ≃ₜ affineSpan ℝ (φ '' s) :=
    AffineEquiv.toHomeomorphOfFiniteDimensional (e₀.trans e₁)
  have hpre :
      e '' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) =
        ((↑) ⁻¹' (φ '' s) : Set (affineSpan ℝ (φ '' s))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [e, e₀, e₁]
    · intro hy
      refine ⟨e.symm y, ?_, Homeomorph.apply_symm_apply e y⟩
      rcases hy with ⟨x, hx, hxy⟩
      have hy_val : φ ((e.symm y : affineSpan ℝ s) : E) = y := by
        change (((e₀.trans e₁) ((e₀.trans e₁).symm y) : affineSpan ℝ (φ '' s)) : F) = y
        exact congrArg Subtype.val (AffineEquiv.apply_symm_apply (e₀.trans e₁) y)
      have hxe : ((e.symm y : affineSpan ℝ s) : E) = x := by
        apply φ.injective
        simpa [hxy] using hy_val
      simpa [hxe] using hx
  have hinterior :
      e '' interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) =
        interior (((↑) ⁻¹' (φ '' s)) : Set (affineSpan ℝ (φ '' s))) := by
    rw [e.image_interior, hpre]
  ext y
  constructor
  · intro hy
    rw [mem_intrinsicInterior] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz' : z ∈ e '' interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
      rw [hinterior]
      exact hz
    rcases hz' with ⟨x, hx, hxe⟩
    refine ⟨x, ?_, ?_⟩
    · rw [mem_intrinsicInterior]
      exact ⟨x, hx, rfl⟩
    · simpa [e, e₀, e₁] using congrArg Subtype.val hxe
  · rintro ⟨x, hx, rfl⟩
    rw [mem_intrinsicInterior] at hx ⊢
    rcases hx with ⟨z, hz, rfl⟩
    refine ⟨e z, ?_, ?_⟩
    · have hz' : e z ∈ e '' interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := ⟨z, hz, rfl⟩
      rw [hinterior] at hz'
      exact hz'
    · simp [e, e₀, e₁]

-- Proof sketch: apply part (1) to the subtraction map `(x, y) ↦ x - y` on `H × H`, using that
-- `ri (C ×ˢ D) = ri C ×ˢ ri D` for nonempty convex sets in finite dimension, then rewrite the
-- image of the product under this map as the Minkowski difference.
/-- Corollary 6.15 (2): for nonempty convex subsets `C` and `D` of a finite-dimensional real
Hilbert space, the relative interior of the Minkowski difference `C - D` is
`(ri C) - (ri D)`. -/
theorem relativeInterior_sub_eq_sub_relativeInterior_of_finiteDimensional
    (C D : Set H) (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D) :
    ri (C - D) = ri C - ri D := by
  -- Route correction: the actual product `H × H` carries the max norm in this workspace, so we
  -- move only the image theorem to the `WithLp 2` Hilbert model and transport the product set
  -- back by an affine equivalence.
  let e : WithLp 2 (H × H) ≃L[ℝ] H × H := WithLp.prodContinuousLinearEquiv 2 ℝ H H
  let S : Set (WithLp 2 (H × H)) := e.symm '' (C ×ˢ D : Set (H × H))
  let L : WithLp 2 (H × H) →L[ℝ] H :=
    (ContinuousLinearMap.fst ℝ H H - ContinuousLinearMap.snd ℝ H H).comp e.toContinuousLinearMap
  have hS_nonempty : S.Nonempty := by
    -- The transported product set is nonempty because `C ×ˢ D` is.
    simpa [S] using Set.Nonempty.image e.symm (hC_nonempty.prod hD_nonempty)
  have hS_convex : Convex ℝ S := by
    -- Linear equivalences preserve convexity of the product set.
    simpa [S] using Convex.linear_image (hC_convex.prod hD_convex) e.symm.toLinearMap
  have himage_prod_sub (T U : Set H) :
      L '' (e.symm '' (T ×ˢ U : Set (H × H))) = T - U := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      rw [Set.mem_sub]
      refine ⟨p.1, hp.1, p.2, hp.2, ?_⟩
      simp [L, e]
    · intro hx
      rw [Set.mem_sub] at hx
      rcases hx with ⟨t, ht, u, hu, rfl⟩
      refine ⟨e.symm (t, u), ?_, ?_⟩
      · exact ⟨(t, u), ⟨ht, hu⟩, rfl⟩
      · simp [L, e]
  have hriS : ri S = e.symm '' (ri C ×ˢ ri D : Set (H × H)) := by
    -- Transport the product intrinsic interior across the `WithLp` affine equivalence and then
    -- rewrite the factors back to relative interiors on `H`.
    calc
      ri S = intrinsicInterior ℝ S := by
        rw [relativeInterior_eq_intrinsicInterior_of_finiteDimensional hS_convex]
      _ = e.symm.toAffineEquiv '' intrinsicInterior ℝ (C ×ˢ D : Set (H × H)) := by
        simpa [S] using
          (affineEquiv_image_intrinsicInterior_of_finiteDimensional
            (φ := e.symm.toAffineEquiv) (s := (C ×ˢ D : Set (H × H))))
      _ = e.symm.toAffineEquiv '' (intrinsicInterior ℝ C ×ˢ intrinsicInterior ℝ D) := by
        rw [bauschke_intrinsicInterior_prod_eq_prod_intrinsicInterior hC_nonempty hD_nonempty]
      _ = e.symm '' (ri C ×ˢ ri D : Set (H × H)) := by
        rw [← relativeInterior_eq_intrinsicInterior_of_finiteDimensional hC_convex,
          ← relativeInterior_eq_intrinsicInterior_of_finiteDimensional hD_convex]
        rfl
  -- Apply part (1) to the subtraction map on the Hilbert product model, then identify its image
  -- of the transported product set with the Minkowski difference.
  calc
    ri (C - D) = ri (L '' S) := by
      rw [himage_prod_sub C D]
    _ = L '' ri S :=
      relativeInterior_image_eq_image_relativeInterior_of_finiteDimensional L S hS_nonempty
        hS_convex
    _ = L '' (e.symm '' (ri C ×ˢ ri D : Set (H × H))) := by
      rw [hriS]
    _ = ri C - ri D := by
      rw [himage_prod_sub (ri C) (ri D)]

end
