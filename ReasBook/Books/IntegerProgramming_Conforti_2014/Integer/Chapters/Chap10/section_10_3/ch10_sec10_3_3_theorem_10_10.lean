/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Order.Iterate
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open Function
open scoped LovaszSchrijverNotation
open scoped CoordinateLiftProjectNotation

section Theorem1010

variable {n : ℕ}

private theorem homogenized_cone_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q) :
    homogenized_cone P ⊆ homogenized_cone Q := by
  intro y hy
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  exact ⟨t, ht, x, convexHull_mono hPQ hx, rfl⟩

private theorem isLovaszSchrijverMatrix_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q)
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsLovaszSchrijverMatrix P Y) :
    IsLovaszSchrijverMatrix Q Y := by
  rw [isLovaszSchrijverMatrix_iff] at hY ⊢
  rcases hY with ⟨h_symm, h0, hrest, hdiag⟩
  refine ⟨h_symm, homogenized_cone_mono hPQ h0, ?_, hdiag⟩
  intro i
  rcases hrest i with ⟨hi, hdiff⟩
  exact ⟨homogenized_cone_mono hPQ hi, homogenized_cone_mono hPQ hdiff⟩

private theorem top_nonneg_of_mem_homogenized_cone
    {P : Set (Fin n → ℝ)}
    {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    0 ≤ y 0 := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  simpa [homogenized_point] using ht

private theorem exists_convexHull_eq_top_smul_homogenized_point_of_mem_homogenized_cone
    {P : Set (Fin n → ℝ)}
    {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    ∃ x : Fin n → ℝ, x ∈ convexHull ℝ P ∧ y = y 0 • homogenized_point x := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  refine ⟨x, hxHull, ?_⟩
  simp [homogenized_point]

private theorem homogenized_point_succ_apply
    (x : Fin n → ℝ)
    (i : Fin n) :
    homogenized_point x i.succ = x i :=
  rfl

private theorem mem_convexHull_coordinate_zero_slice
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n))
    (j : Fin n)
    {x : Fin n → ℝ}
    (hxHull : x ∈ convexHull ℝ P)
    (hxj : x j = 0) :
    x ∈ convexHull ℝ (P ∩ {y : Fin n → ℝ | y j = 0}) := by
  let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hP_nonpos : P ⊆ (-πj) ⁻¹' Set.Iic (0 : ℝ) := by
    intro y hy
    have hyBox : y ∈ prefix_unit_box (Nat.le_refl n) := hP_subset hy
    have hyj_nonneg : 0 ≤ y j := (mem_prefix_unit_box_iff (Nat.le_refl n) y).1 hyBox j |>.1
    simpa [πj, LinearMap.proj_apply] using neg_nonpos.mpr hyj_nonneg
  have hxHyper :
      x ∈ convexHull ℝ P ∩ (-πj) ⁻¹' ({0} : Set ℝ) := by
    refine ⟨hxHull, ?_⟩
    simp [πj, hxj]
  rw [convexHull_inter_hyperplane_eq P (-πj) (0 : ℝ) hP_nonpos] at hxHyper
  have hslice :
      P ∩ (-πj) ⁻¹' ({0} : Set ℝ) = P ∩ {y : Fin n → ℝ | y j = 0} := by
    ext y
    simp [πj]
  rw [hslice] at hxHyper
  exact hxHyper

private theorem mem_convexHull_coordinate_one_slice
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n))
    (j : Fin n)
    {x : Fin n → ℝ}
    (hxHull : x ∈ convexHull ℝ P)
    (hxj : x j = 1) :
    x ∈ convexHull ℝ (P ∩ {y : Fin n → ℝ | y j = 1}) := by
  let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hP_le_one : P ⊆ πj ⁻¹' Set.Iic (1 : ℝ) := by
    intro y hy
    have hyBox : y ∈ prefix_unit_box (Nat.le_refl n) := hP_subset hy
    exact (mem_prefix_unit_box_iff (Nat.le_refl n) y).1 hyBox j |>.2
  have hxHyper :
      x ∈ convexHull ℝ P ∩ πj ⁻¹' ({1} : Set ℝ) := by
    refine ⟨hxHull, ?_⟩
    simp [πj, hxj]
  rw [convexHull_inter_hyperplane_eq P πj (1 : ℝ) hP_le_one] at hxHyper
  have hslice :
      P ∩ πj ⁻¹' ({1} : Set ℝ) = P ∩ {y : Fin n → ℝ | y j = 1} := by
    ext y
    simp [πj]
  rw [hslice] at hxHyper
  exact hxHyper

/-- The Lovász-Schrijver operator is monotone with respect to set inclusion. -/
theorem lovasz_schrijver_N_mono :
    Monotone (lovasz_schrijver_N : Set (Fin n → ℝ) → Set (Fin n → ℝ)) := by
  intro P Q hPQ x hx
  change x ∈ N(P) at hx
  rw [mem_lovasz_schrijver_N_iff] at hx ⊢
  rcases hx with ⟨Y, hY, hcol⟩
  exact ⟨Y, isLovaszSchrijverMatrix_mono hPQ hY, hcol⟩

/-- Under the unit-box assumption on `P`, the one-step Lovász-Schrijver relaxation is contained
in each coordinate lift-and-project hull `(P)_{j}`. -/
theorem lovasz_schrijver_N_subset_coordinate_lift_project_hull
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n))
    (j : Fin n) :
    N(P) ⊆ (P)_{j} := by
  intro x hx
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hSymm, hcone0, hrest, hdiag⟩
  have hxHull : x ∈ convexHull ℝ P := by
    rw [hcol0] at hcone0
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone P hcone0
  have hsymmEntry : ∀ a b : Fin (n + 1), Y a b = Y b a := by
    intro a b
    simpa using congr_fun (congr_fun hSymm b) a
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hYj0 : Y j.succ 0 = x j := by
    simpa [mulVec_lifted_basis, homogenized_point_succ_apply] using congr_fun hcol0 j.succ
  have hY0j : Y 0 j.succ = x j := by
    rw [hsymmEntry 0 j.succ]
    exact hYj0
  have hcol0' : Matrix.mulVec Y (lifted_basis 0) = homogenized_point x := by
    simpa using hcol0
  have hcolCone : Matrix.mulVec Y (lifted_basis j.succ) ∈ homogenized_cone P := by
    simpa using (hrest j).1
  have hdiffCone :
      Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) ∈ homogenized_cone P := by
    simpa using (hrest j).2
  have hxj_nonneg : 0 ≤ x j := by
    simpa [mulVec_lifted_basis, hY0j] using top_nonneg_of_mem_homogenized_cone hcolCone
  have hxj_le_one : x j ≤ 1 := by
    have hdiff_nonneg : 0 ≤ Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) 0 :=
      top_nonneg_of_mem_homogenized_cone hdiffCone
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hdiff_nonneg
  by_cases hxj_zero : x j = 0
  · rw [coordinate_lift_project_hull_def]
    exact
      (convexHull_mono <| by
        intro y hy
        exact Or.inl hy)
        (mem_convexHull_coordinate_zero_slice P hP_subset j hxHull hxj_zero)
  by_cases hxj_one : x j = 1
  · rw [coordinate_lift_project_hull_def]
    exact
      (convexHull_mono <| by
        intro y hy
        exact Or.inr hy)
        (mem_convexHull_coordinate_one_slice P hP_subset j hxHull hxj_one)
  · have hone_sub_nonneg : 0 ≤ 1 - x j := sub_nonneg.mpr hxj_le_one
    rcases exists_convexHull_eq_top_smul_homogenized_point_of_mem_homogenized_cone hcolCone with
      ⟨xOne, hxOneHull, hcolEq⟩
    rcases exists_convexHull_eq_top_smul_homogenized_point_of_mem_homogenized_cone hdiffCone with
      ⟨xZero, hxZeroHull, hdiffEq⟩
    have hdiagj : Y j.succ j.succ = Y j.succ 0 := hdiag j
    have hcolEq' :
        Matrix.mulVec Y (lifted_basis j.succ) = (x j) • homogenized_point xOne := by
      simpa [mulVec_lifted_basis, hY0j] using hcolEq
    have hdiffEq' :
        Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) =
          (1 - x j) • homogenized_point xZero := by
      simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hdiffEq
    have hxOneFace : xOne j = 1 := by
      have hxj_ne_zero : x j ≠ 0 := hxj_zero
      have hcoord : x j = x j * xOne j := by
        simpa [mulVec_lifted_basis, homogenized_point, hdiagj, hYj0] using
          congr_fun hcolEq' j.succ
      have hmul : x j * (xOne j - 1) = 0 := by
        nlinarith [hcoord]
      rcases mul_eq_zero.mp hmul with hzero | hface
      · exact False.elim (hxj_ne_zero hzero)
      · linarith
    have hxZeroFace : xZero j = 0 := by
      have hcoord : 1 - x j = 0 ∨ xZero j = 0 := by
        simpa [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hdiagj, hYj0] using
          congr_fun hdiffEq' j.succ
      rcases hcoord with hzero | hface
      · have hxj_eq_one : x j = 1 := by
          linarith
        exact False.elim (hxj_one hxj_eq_one)
      · exact hface
    have hxZeroCoord : xZero ∈ (P)_{j} := by
      rw [coordinate_lift_project_hull_def]
      exact
        (convexHull_mono <| by
          intro y hy
          exact Or.inl hy)
          (mem_convexHull_coordinate_zero_slice P hP_subset j hxZeroHull hxZeroFace)
    have hxOneCoord : xOne ∈ (P)_{j} := by
      rw [coordinate_lift_project_hull_def]
      exact
        (convexHull_mono <| by
          intro y hy
          exact Or.inr hy)
          (mem_convexHull_coordinate_one_slice P hP_subset j hxOneHull hxOneFace)
    have hsumCols :
        Matrix.mulVec Y (lifted_basis j.succ) +
            Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) =
          Matrix.mulVec Y (lifted_basis 0) := by
      ext k
      simp [Matrix.mulVec_sub, mulVec_lifted_basis]
    have hcomb :
        x = (x j) • xOne + (1 - x j) • xZero := by
      have hsumVec :
          homogenized_point x =
            (x j) • homogenized_point xOne + (1 - x j) • homogenized_point xZero := by
        calc
          homogenized_point x = Matrix.mulVec Y (lifted_basis 0) := hcol0'.symm
          _ =
              Matrix.mulVec Y (lifted_basis j.succ) +
                Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) := by
            symm
            exact hsumCols
          _ = (x j) • homogenized_point xOne + (1 - x j) • homogenized_point xZero := by
            rw [hcolEq', hdiffEq']
      funext i
      have hcoord := congr_fun hsumVec i.succ
      simpa [homogenized_point] using hcoord
    have hconvCoord : Convex ℝ ((P)_{j}) := by
      rw [coordinate_lift_project_hull_def]
      exact convex_convexHull ℝ _
    have hcombMem : (x j) • xOne + (1 - x j) • xZero ∈ (P)_{j} := by
      exact hconvCoord hxOneCoord hxZeroCoord hxj_nonneg hone_sub_nonneg (by ring)
    exact hcomb ▸ hcombMem

private theorem coordinate_lift_project_hull_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q)
    (j : Fin n) :
    (P)_{j} ⊆ (Q)_{j} := by
  rw [coordinate_lift_project_hull_def, coordinate_lift_project_hull_def]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hPQ hx.1, hx.2⟩
    · exact Or.inr ⟨hPQ hx.1, hx.2⟩

/-- For a convex set `P`, the Lovász-Schrijver iterates form an antitone sequence in the subset
order. -/
theorem lovasz_schrijver_iterates_antitone
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P) :
    Antitone (fun t : ℕ ↦ (lovasz_schrijver_N^[t]) P) :=
  Monotone.antitone_iterate_of_map_le lovasz_schrijver_N_mono
    (lovasz_schrijver_N_subset P hP_convex)

/-- For a convex set `P`, every Lovász-Schrijver iterate remains contained in `P`. -/
theorem lovasz_schrijver_iterate_subset_self
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P)
    (t : ℕ) :
    (lovasz_schrijver_N^[t]) P ⊆ P := by
  simpa using lovasz_schrijver_iterates_antitone P hP_convex (Nat.zero_le t)

/-- For a convex set `P`, the Lovász-Schrijver iterates form a descending chain
`P ⊇ N(P) ⊇ N(N(P)) ⊇ ⋯`; equivalently,
`(lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P` for every `t`. -/
theorem lovasz_schrijver_iterates_descend
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P)
    (t : ℕ) :
    (lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P := by
  simpa using lovasz_schrijver_iterates_antitone P hP_convex (Nat.le_succ t)

/-- Theorem 10.10 (1). For a polyhedron `P`, the Lovász-Schrijver iterates form a descending
chain `P ⊇ N(P) ⊇ N(N(P)) ⊇ ⋯`; equivalently,
`(lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P` for every `t`. -/
theorem lovasz_schrijver_iterates_descend_of_is_polyhedron
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (t : ℕ) :
    (lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P :=
  lovasz_schrijver_iterates_descend P (convex_of_is_polyhedron hP_polyhedron) t

private theorem convexHull_zero_one_points_subset_lovasz_schrijver_iterate
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    ∀ t : ℕ,
      convexHull ℝ (zero_one_points (Nat.le_refl n) P) ⊆ (lovasz_schrijver_N^[t]) P
  | 0 => by
      have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
      refine convexHull_min ?_ hP_convex
      intro x hx
      exact (mem_zero_one_points_iff (Nat.le_refl n) P x).1 hx |>.1
  | t + 1 => by
      let S := zero_one_points (Nat.le_refl n) P
      calc
        convexHull ℝ S ⊆
            convexHull ℝ (zero_one_points (Nat.le_refl n) ((lovasz_schrijver_N^[t]) P)) := by
              refine convexHull_mono ?_
              intro x hx
              rw [mem_zero_one_points_iff (Nat.le_refl n) ((lovasz_schrijver_N^[t]) P) x]
              refine ⟨?_, ?_⟩
              · exact convexHull_zero_one_points_subset_lovasz_schrijver_iterate P
                  hP_polyhedron t (subset_convexHull ℝ S hx)
              · exact (mem_zero_one_points_iff (Nat.le_refl n) P x).1 hx |>.2
        _ ⊆ N₊((lovasz_schrijver_N^[t]) P) :=
          convexHull_zero_one_points_subset_lovasz_schrijver_N_plus ((lovasz_schrijver_N^[t]) P)
        _ ⊆ N((lovasz_schrijver_N^[t]) P) :=
          lovasz_schrijver_N_plus_subset_N ((lovasz_schrijver_N^[t]) P)
        _ = (lovasz_schrijver_N^[t + 1]) P := by
          simp [Function.iterate_succ_apply']

private theorem lovasz_schrijver_iterate_subset_sequential_convexification
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n)) :
    ∀ {t : ℕ}, (ht : t ≤ n) →
      (lovasz_schrijver_N^[t]) P ⊆ sequential_convexification_iter (Nat.le_refl n) P ht
  | 0, ht => by
      simp [sequential_convexification_iter_zero (Nat.le_refl n) P]
  | t + 1, ht => by
      have ht_prev : t ≤ n := Nat.le_of_succ_le ht
      calc
        (lovasz_schrijver_N^[t + 1]) P
            = N((lovasz_schrijver_N^[t]) P) := by
                simp [Function.iterate_succ_apply']
        _ ⊆ ((lovasz_schrijver_N^[t]) P)_{
              Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩} :=
            lovasz_schrijver_N_subset_coordinate_lift_project_hull ((lovasz_schrijver_N^[t]) P)
              (by
                intro x hx
                exact hP_subset <|
                  lovasz_schrijver_iterate_subset_self P
                    (convex_of_is_polyhedron hP_polyhedron) t hx)
              (Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩)
        _ ⊆ (sequential_convexification_iter (Nat.le_refl n) P ht_prev)_{
              Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩} :=
            coordinate_lift_project_hull_mono
              (lovasz_schrijver_iterate_subset_sequential_convexification P hP_polyhedron
                hP_subset ht_prev)
              (Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩)
        _ = sequential_convexification_iter (Nat.le_refl n) P ht := by
            rw [sequential_convexification_iter_succ (Nat.le_refl n) P ht]

/-- Theorem 10.10 (2). Let `P ⊆ [0,1]^n`, let
`S = {x ∈ P : x_j ∈ {0,1} for j = 1, …, n}`, and let `N` denote the Lovász-Schrijver iterate
operator. Then `Nⁿ(P) = conv(S)`. Here `S` is formalized as
`zero_one_points (Nat.le_refl n) P`. -/
theorem lovasz_schrijver_nth_iterate_eq_convexHull_zero_one_points
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n)) :
    (lovasz_schrijver_N^[n]) P = convexHull ℝ (zero_one_points (Nat.le_refl n) P) := by
  refine Set.Subset.antisymm ?_ ?_
  · calc
      (lovasz_schrijver_N^[n]) P ⊆
          sequential_convexification_iter (Nat.le_refl n) P (Nat.le_refl n) :=
        lovasz_schrijver_iterate_subset_sequential_convexification P hP_polyhedron hP_subset
          (Nat.le_refl n)
      _ = convexHull ℝ (zero_one_points (Nat.le_refl n) P) :=
        sequential_convexification_iter_eq_convexHull_zero_one_points
          (Nat.le_refl n) P hP_polyhedron hP_subset
  · exact convexHull_zero_one_points_subset_lovasz_schrijver_iterate P hP_polyhedron n

end Theorem1010
