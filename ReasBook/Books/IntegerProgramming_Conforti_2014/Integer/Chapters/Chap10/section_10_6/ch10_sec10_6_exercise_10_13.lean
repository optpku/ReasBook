/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Exposed
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_3_theorem_10_10

open scoped Matrix LovaszSchrijverNotation

-- Primary domain: faces of polytopes inside the one-step Lovasz-Schrijver relaxation.
-- Owner abstractions reused here:
-- * `prefix_unit_box` from Chapter 5 for the ambient box `[0,1]^n`
-- * `Set.IsPolytope` from Chapter 3 for the canonical polytope owner
-- * `homogenized_point`, `homogenized_cone`, `lifted_basis`,
--   `IsLovaszSchrijverMatrix`, and `N(P)` from Section 10.3
-- * `IsExposed` for the repository face owner
-- This file keeps only the source-facing face statement, bridged through the canonical chapter
-- owners for the ambient box and polytope hypotheses.

section Exercise1013

variable {n : ℕ}

/-- Helper for Exercise 10.13: a valid face inequality on `P` stays valid on every vector of the
homogenized cone of `P` after dehomogenizing the tail coordinates. -/
lemma faceInequality_le_onHomogenizedCone
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    {y : Fin (n + 1) → ℝ}
    (hvalid : is_valid_inequality P c δ)
    (hy : y ∈ homogenized_cone P) :
    c ⬝ᵥ (fun i ↦ y i.succ) ≤ δ * y 0 := by
  -- Extend the valid inequality from `P` to `convexHull ℝ P`, then unfold the cone witness.
  have hvalidHull : is_valid_inequality (convexHull ℝ P) c δ :=
    (is_valid_inequality_convexHull_iff).2 hvalid
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  have htail : (fun i ↦ (t • homogenized_point x) i.succ) = t • x := by
    funext i
    simp [homogenized_point]
  have hy0 : (t • homogenized_point x) 0 = t := by
    simp [homogenized_point]
  -- The lifted inequality scales with the homogenizing coefficient `t`.
  calc
    c ⬝ᵥ (fun i ↦ (t • homogenized_point x) i.succ) = t * (c ⬝ᵥ x) := by
      rw [htail, dotProduct_smul]
      simp [smul_eq_mul]
    _ ≤ t * δ := by
      exact mul_le_mul_of_nonneg_left (hvalidHull hx) ht
    _ = δ * (t • homogenized_point x) 0 := by
      rw [hy0]
      ring

/-- Helper for Exercise 10.13: if a homogenized cone point of `P` makes the exposing inequality
tight, then it already lies in the homogenized cone of the exposed face `face_set P c δ`. -/
lemma mem_homogenizedCone_faceSet_of_eq
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    {y : Fin (n + 1) → ℝ}
    (hvalid : is_valid_inequality P c δ)
    (hface_nonempty : (face_set P c δ).Nonempty)
    (hy : y ∈ homogenized_cone P)
    (hyEq : c ⬝ᵥ (fun i ↦ y i.succ) = δ * y 0) :
    y ∈ homogenized_cone (face_set P c δ) := by
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  by_cases ht_zero : t = 0
  · obtain ⟨x₀, hx₀⟩ := hface_nonempty
    -- When the homogenizing scalar vanishes, reuse any point of the nonempty face.
    refine ⟨0, le_rfl, x₀, subset_convexHull ℝ (face_set P c δ) hx₀, ?_⟩
    simp [ht_zero]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    have htail : (fun i ↦ (t • homogenized_point x) i.succ) = t • x := by
      funext i
      simp [homogenized_point]
    have hy0 : (t • homogenized_point x) 0 = t := by
      simp [homogenized_point]
    have hx_eq : c ⬝ᵥ x = δ := by
      have hyEq' : t * (c ⬝ᵥ x) = δ * t := by
        rw [htail, dotProduct_smul, smul_eq_mul] at hyEq
        simpa [hy0] using hyEq
      nlinarith
    have hhalfspace :
        P ⊆ (dotProductStrongDual c).toLinearMap ⁻¹' Set.Iic δ := by
      intro u hu
      simpa [dotProductStrongDual_apply] using hvalid hu
    have hxFaceHull : x ∈ convexHull ℝ (face_set P c δ) := by
      have hxSlice :
          x ∈ convexHull ℝ P ∩ (dotProductStrongDual c).toLinearMap ⁻¹' ({δ} : Set ℝ) := by
        refine ⟨hxHull, ?_⟩
        simp [dotProductStrongDual_apply, hx_eq]
      have hface_preimage :
          P ∩ (dotProductStrongDual c).toLinearMap ⁻¹' ({δ} : Set ℝ) = face_set P c δ := by
        ext u
        simp [face_set, linear_hyperplane, dotProductStrongDual_apply]
      have hslice :
          convexHull ℝ P ∩ (dotProductStrongDual c).toLinearMap ⁻¹' ({δ} : Set ℝ) =
            convexHull ℝ (P ∩ (dotProductStrongDual c).toLinearMap ⁻¹' ({δ} : Set ℝ)) := by
        exact
          convexHull_inter_hyperplane_eq P (dotProductStrongDual c).toLinearMap δ hhalfspace
      rw [hslice] at hxSlice
      rw [hface_preimage] at hxSlice
      exact hxSlice
    -- Replace the ambient convex-hull witness with a face-convex-hull witness.
    exact ⟨t, ht, x, hxFaceHull, rfl⟩

/-- Helper for Exercise 10.13: an `IsLovaszSchrijverMatrix P Y` witness whose first column lands
on `face_set P c δ` already satisfies the Lovasz-Schrijver constraints for that face. -/
lemma isLovaszSchrijverMatrix_faceSet
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    {x : Fin n → ℝ}
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hvalid : is_valid_inequality P c δ)
    (hface_nonempty : (face_set P c δ).Nonempty)
    (hx : x ∈ face_set P c δ)
    (hY : IsLovaszSchrijverMatrix P Y)
    (hcol : Y *ᵥ lifted_basis 0 = homogenized_point x) :
    IsLovaszSchrijverMatrix (face_set P c δ) Y := by
  rw [isLovaszSchrijverMatrix_iff] at hY ⊢
  rcases hY with ⟨hSymm, h0, hrest, hdiag⟩
  rcases mem_face_set_iff.mp hx with ⟨-, hx_eq⟩
  let phi : (Fin (n + 1) → ℝ) → ℝ := fun y ↦ c ⬝ᵥ (fun j ↦ y j.succ) - δ * y 0
  have phi_add :
      ∀ y z : Fin (n + 1) → ℝ, phi (y + z) = phi y + phi z := by
    intro y z
    dsimp [phi]
    simp [dotProduct, Finset.sum_add_distrib, mul_add, sub_eq_add_neg]
    ring
  refine ⟨hSymm, ?_, ?_, hdiag⟩
  · -- The first column is exactly the homogenized point of a face point.
    rw [hcol]
    exact homogenized_point_mem_homogenized_cone (face_set P c δ) <|
      subset_convexHull ℝ (face_set P c δ) hx
  · intro i
    rcases hrest i with ⟨hi, hdiff⟩
    let yi : Fin (n + 1) → ℝ := Y *ᵥ lifted_basis i.succ
    let ydi : Fin (n + 1) → ℝ := Y *ᵥ (lifted_basis 0 - lifted_basis i.succ)
    have hphi_col0 : phi (Y *ᵥ lifted_basis 0) = 0 := by
      -- The first column already satisfies the exposing equality because `x ∈ face_set P c δ`.
      rw [hcol]
      have htail_col0 : c ⬝ᵥ (fun j ↦ homogenized_point x j.succ) = δ := by
        simpa [homogenized_point] using hx_eq
      dsimp [phi]
      rw [htail_col0]
      simp [homogenized_point]
    have hphi_yi_nonpos : phi yi ≤ 0 := by
      -- Apply the exposing inequality to the ambient cone witness for the `i`th split column.
      dsimp [phi, yi]
      linarith [faceInequality_le_onHomogenizedCone hvalid hi]
    have hphi_ydi_nonpos : phi ydi ≤ 0 := by
      -- The difference column satisfies the same ambient cone inequality.
      dsimp [phi, ydi]
      linarith [faceInequality_le_onHomogenizedCone hvalid hdiff]
    have hy_sum : yi + ydi = Y *ᵥ lifted_basis 0 := by
      -- The split columns decompose the first column by linearity of `mulVec`.
      calc
        yi + ydi = Y *ᵥ lifted_basis i.succ + (Y *ᵥ lifted_basis 0 - Y *ᵥ lifted_basis i.succ) := by
          simp [yi, ydi, Matrix.mulVec_sub]
        _ = Y *ᵥ lifted_basis 0 := by
          ext j
          have hcoord :
              (Y *ᵥ lifted_basis i.succ) j +
                  ((Y *ᵥ lifted_basis 0) j - (Y *ᵥ lifted_basis i.succ) j) =
                (Y *ᵥ lifted_basis 0) j := by
            ring
          exact hcoord
    have hphi_sum : phi yi + phi ydi = 0 := by
      -- The exposing functional is additive across the column decomposition.
      calc
        phi yi + phi ydi = phi (yi + ydi) := by
          symm
          exact phi_add yi ydi
        _ = phi (Y *ᵥ lifted_basis 0) := by rw [hy_sum]
        _ = 0 := hphi_col0
    have hphi_yi_zero : phi yi = 0 := by
      linarith
    have hphi_ydi_zero : phi ydi = 0 := by
      linarith
    refine ⟨?_, ?_⟩
    · -- Tightness of the exposing inequality upgrades the ambient witness to the face witness.
      exact mem_homogenizedCone_faceSet_of_eq hvalid hface_nonempty hi <| by
        dsimp [phi, yi] at hphi_yi_zero
        linarith
    · -- The same tightness argument applies to the complementary split column.
      exact mem_homogenizedCone_faceSet_of_eq hvalid hface_nonempty hdiff <| by
        dsimp [phi, ydi] at hphi_ydi_zero
        linarith

/-- Exercise 10.13. If `F` is a face of a polytope `P ⊆ [0,1]^n`, then the Lovasz-Schrijver
operator commutes with restricting to that face: `N(F) = N(P) ∩ F`. -/
theorem lovasz_schrijver_N_face_eq_inter
    (P F : Set (Fin n → ℝ))
    (hP_polytope : P.IsPolytope ℝ)
    (hP_box : P ⊆ prefix_unit_box (Nat.le_refl n))
    (hF_face : IsExposed ℝ P F) :
    N(F) = N(P) ∩ F := by
  have hP_convex : Convex ℝ P := by
    -- A polytope is a convex hull of finitely many points, hence convex.
    rcases hP_polytope with ⟨V, -, rfl⟩
    exact convex_convexHull ℝ V
  have hF_convex : Convex ℝ F := hF_face.convex hP_convex
  by_cases hF_empty : F = ∅
  · -- If the face is empty, both sides are empty because `N(∅) ⊆ ∅`.
    have hN_empty : N((∅ : Set (Fin n → ℝ))) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (lovasz_schrijver_N_subset (∅ : Set (Fin n → ℝ)) convex_empty hx)
      · intro hx
        simp at hx
    rw [hF_empty, hN_empty]
    simp
  · have hF_nonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_empty
    obtain ⟨c, δ, hvalid, hF_eq⟩ := hF_face.exists_eq_face_set_of_nonempty hF_nonempty
    have hface_nonempty : (face_set P c δ).Nonempty := by
      simpa [hF_eq] using hF_nonempty
    ext x
    constructor
    · intro hx
      -- The forward inclusion is abstract: `N` is monotone and remains inside a convex set.
      refine ⟨lovasz_schrijver_N_mono hF_face.subset hx, ?_⟩
      exact lovasz_schrijver_N_subset F hF_convex hx
    · intro hx
      -- Rewrite the exposed face as a concrete equality face and upgrade the ambient witness.
      rw [hF_eq] at hx ⊢
      rcases hx with ⟨hxN, hxFace⟩
      rw [mem_lovasz_schrijver_N_iff] at hxN ⊢
      rcases hxN with ⟨Y, hY, hcol⟩
      exact ⟨Y, isLovaszSchrijverMatrix_faceSet hvalid hface_nonempty hxFace hY hcol, hcol⟩

end Exercise1013
