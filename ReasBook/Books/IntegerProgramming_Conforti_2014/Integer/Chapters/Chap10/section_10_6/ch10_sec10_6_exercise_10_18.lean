/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_corollary_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_3_theorem_10_10

open Function

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note:
-- * primary domain: mixed 0,1 lift-and-project statements on `MixedRealPoint n n`
-- * core owners inspected before refinement:
--   `MixedRealPoint`, `binary_prefix_points_on_subset`, `Set.IsPolytope`,
--   `lovasz_schrijver_N`, and `Fin.appendEquiv`
-- * source-facing refinement choice: keep the mixed-product theorem, but bridge the first-block
--   binary condition through the Chapter 5 owner `binary_prefix_points_on_subset`
--   on `Prod.fst '' P`, while transporting the Chapter 10 operator through the canonical
--   flattening `Fin.appendEquiv n n : MixedRealPoint n n ≃ (Fin (n + n) → ℝ)`.

section Exercise1018

variable {n : ℕ}

/-- The points of `P ⊆ ℝ^n × ℝ^n` whose first-block coordinates indexed by `I` are binary. -/
def mixed_binary_first_block_points_on
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n)) : Set (MixedRealPoint n n) :=
  {x | x ∈ P ∧ ∀ i ∈ I, x.1 i = 0 ∨ x.1 i = 1}

/-- Membership in `mixed_binary_first_block_points_on P I` means belonging to `P` and having
binary first-block coordinates on the index set `I`. -/
theorem mem_mixed_binary_first_block_points_on_iff
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n))
    (x : MixedRealPoint n n) :
    x ∈ mixed_binary_first_block_points_on P I ↔
      x ∈ P ∧ ∀ i ∈ I, x.1 i = 0 ∨ x.1 i = 1 :=
  Iff.rfl

/-- Bridge to the Chapter 5 owner `binary_prefix_points_on_subset` on the first-block projection
`Prod.fst '' P`. -/
theorem mem_mixed_binary_first_block_points_on_iff_mem_binary_prefix_points_on_subset
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n))
    (x : MixedRealPoint n n) :
    x ∈ mixed_binary_first_block_points_on P I ↔
      x ∈ P ∧
        x.1 ∈ binary_prefix_points_on_subset (Nat.le_refl n) (Prod.fst '' P) I := by
  constructor
  · rintro ⟨hxP, hxI⟩
    refine ⟨hxP, ?_⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    simpa using hxI
  · rintro ⟨hxP, hxI⟩
    refine ⟨hxP, ?_⟩
    simpa using hxI.2

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: flattening a mixed real
point with `Fin.appendEquiv` is linear. -/
private lemma mixedAppendEquiv_isLinearMap
    {p : ℕ} :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  constructor
  · -- Addition is preserved separately on the two blocks.
    intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · -- Scalar multiplication is preserved by the same blockwise computation.
    intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: the homogenizing
coordinate of a point in `homogenized_cone P` is nonnegative. -/
private lemma homogenizedCone_top_nonneg
    {d : ℕ}
    {P : Set (Fin d → ℝ)}
    {y : Fin (d + 1) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    0 ≤ y 0 := by
  -- Unpack the conic scaling and read its nonnegative scale at coordinate zero.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨a, ha, x, hx, rfl⟩
  simpa [homogenized_point] using ha

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: every homogenized-cone
point is its top coordinate times a homogenized point from `convexHull ℝ P`. -/
private lemma exists_convexHull_eq_top_smul_homogenizedPoint
    {d : ℕ}
    {P : Set (Fin d → ℝ)}
    {y : Fin (d + 1) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    ∃ x : Fin d → ℝ, x ∈ convexHull ℝ P ∧ y = y 0 • homogenized_point x := by
  -- Normalize the cone witness using the zeroth coordinate of a homogenized point.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨a, ha, x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  simp [homogenized_point]

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: a convex-hull point
whose bounded coordinate is zero lies in the zero-coordinate slice hull. -/
private lemma memConvexHull_coordinateZeroSlice_of_bounds
    {d : ℕ}
    (P : Set (Fin d → ℝ))
    (j : Fin d)
    (hP_nonneg : ∀ y ∈ P, 0 ≤ y j)
    {x : Fin d → ℝ}
    (hxHull : x ∈ convexHull ℝ P)
    (hxj : x j = 0) :
    x ∈ convexHull ℝ (P ∩ {y : Fin d → ℝ | y j = 0}) := by
  let πj : (Fin d → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hP_halfspace : P ⊆ (-πj) ⁻¹' Set.Iic (0 : ℝ) := by
    intro y hy
    simpa [πj, LinearMap.proj_apply] using neg_nonpos.mpr (hP_nonneg y hy)
  have hxHyper : x ∈ convexHull ℝ P ∩ (-πj) ⁻¹' ({0} : Set ℝ) := by
    refine ⟨hxHull, ?_⟩
    simp [πj, hxj]
  -- The supporting-hyperplane theorem identifies the endpoint slice of the hull.
  rw [convexHull_inter_hyperplane_eq P (-πj) (0 : ℝ) hP_halfspace] at hxHyper
  have hslice :
      P ∩ (-πj) ⁻¹' ({0} : Set ℝ) = P ∩ {y : Fin d → ℝ | y j = 0} := by
    ext y
    simp [πj]
  rwa [hslice] at hxHyper

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: a convex-hull point
whose bounded coordinate is one lies in the one-coordinate slice hull. -/
private lemma memConvexHull_coordinateOneSlice_of_bounds
    {d : ℕ}
    (P : Set (Fin d → ℝ))
    (j : Fin d)
    (hP_le_one : ∀ y ∈ P, y j ≤ 1)
    {x : Fin d → ℝ}
    (hxHull : x ∈ convexHull ℝ P)
    (hxj : x j = 1) :
    x ∈ convexHull ℝ (P ∩ {y : Fin d → ℝ | y j = 1}) := by
  let πj : (Fin d → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hP_halfspace : P ⊆ πj ⁻¹' Set.Iic (1 : ℝ) := by
    intro y hy
    exact hP_le_one y hy
  have hxHyper : x ∈ convexHull ℝ P ∩ πj ⁻¹' ({1} : Set ℝ) := by
    refine ⟨hxHull, ?_⟩
    simp [πj, hxj]
  -- Apply the same supporting-hyperplane theorem at the upper endpoint.
  rw [convexHull_inter_hyperplane_eq P πj (1 : ℝ) hP_halfspace] at hxHyper
  have hslice :
      P ∩ πj ⁻¹' ({1} : Set ℝ) = P ∩ {y : Fin d → ℝ | y j = 1} := by
    ext y
    simp [πj]
  rwa [hslice] at hxHyper

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: one
Lovász–Schrijver step lies in the lift-project hull of any individually bounded coordinate. -/
private lemma lovaszSchrijverN_subset_coordinateLiftProjectHull_of_bounds
    {d : ℕ}
    (P : Set (Fin d → ℝ))
    (j : Fin d)
    (hP_bounds : ∀ y ∈ P, 0 ≤ y j ∧ y j ≤ 1) :
    lovasz_schrijver_N P ⊆ coordinate_lift_project_hull P j := by
  intro x hx
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hSymm, hcone0, hrest, hdiag⟩
  have hxHull : x ∈ convexHull ℝ P := by
    rw [hcol0] at hcone0
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone P hcone0
  -- Record the matrix entries that encode the split coordinate and its complement.
  have hsymmEntry : ∀ a b : Fin (d + 1), Y a b = Y b a := by
    intro a b
    simpa using congr_fun (congr_fun hSymm b) a
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hYj0 : Y j.succ 0 = x j := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 j.succ
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
    simpa [mulVec_lifted_basis, hY0j] using homogenizedCone_top_nonneg hcolCone
  have hxj_le_one : x j ≤ 1 := by
    have hdiff_nonneg : 0 ≤ Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) 0 :=
      homogenizedCone_top_nonneg hdiffCone
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hdiff_nonneg
  -- Endpoint values already lie in the corresponding face of the coordinate hull.
  by_cases hxj_zero : x j = 0
  · rw [coordinate_lift_project_hull_def]
    have hzeroSliceSubset :
        P ∩ {y : Fin d → ℝ | y j = 0} ⊆
          (P ∩ {y : Fin d → ℝ | y j = 0}) ∪
            (P ∩ {y : Fin d → ℝ | y j = 1}) := by
      intro y hy
      exact Or.inl hy
    exact (convexHull_mono hzeroSliceSubset)
      (memConvexHull_coordinateZeroSlice_of_bounds P j
        (fun y hy ↦ (hP_bounds y hy).1) hxHull hxj_zero)
  by_cases hxj_one : x j = 1
  · rw [coordinate_lift_project_hull_def]
    have honeSliceSubset :
        P ∩ {y : Fin d → ℝ | y j = 1} ⊆
          (P ∩ {y : Fin d → ℝ | y j = 0}) ∪
            (P ∩ {y : Fin d → ℝ | y j = 1}) := by
      intro y hy
      exact Or.inr hy
    exact (convexHull_mono honeSliceSubset)
      (memConvexHull_coordinateOneSlice_of_bounds P j
        (fun y hy ↦ (hP_bounds y hy).2) hxHull hxj_one)
  · have hone_sub_nonneg : 0 ≤ 1 - x j := sub_nonneg.mpr hxj_le_one
    rcases exists_convexHull_eq_top_smul_homogenizedPoint hcolCone with
      ⟨xOne, hxOneHull, hcolEq⟩
    rcases exists_convexHull_eq_top_smul_homogenizedPoint hdiffCone with
      ⟨xZero, hxZeroHull, hdiffEq⟩
    have hdiagj : Y j.succ j.succ = Y j.succ 0 := hdiag j
    have hcolEq' :
        Matrix.mulVec Y (lifted_basis j.succ) = (x j) • homogenized_point xOne := by
      simpa [mulVec_lifted_basis, hY0j] using hcolEq
    have hdiffEq' :
        Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) =
          (1 - x j) • homogenized_point xZero := by
      simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hdiffEq
    -- The diagonal identities force the two normalized witnesses onto opposite faces.
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
    have hxZeroCoord : xZero ∈ coordinate_lift_project_hull P j := by
      rw [coordinate_lift_project_hull_def]
      have hzeroSliceSubset :
          P ∩ {y : Fin d → ℝ | y j = 0} ⊆
            (P ∩ {y : Fin d → ℝ | y j = 0}) ∪
              (P ∩ {y : Fin d → ℝ | y j = 1}) := by
        intro y hy
        exact Or.inl hy
      exact (convexHull_mono hzeroSliceSubset)
        (memConvexHull_coordinateZeroSlice_of_bounds P j
          (fun y hy ↦ (hP_bounds y hy).1) hxZeroHull hxZeroFace)
    have hxOneCoord : xOne ∈ coordinate_lift_project_hull P j := by
      rw [coordinate_lift_project_hull_def]
      have honeSliceSubset :
          P ∩ {y : Fin d → ℝ | y j = 1} ⊆
            (P ∩ {y : Fin d → ℝ | y j = 0}) ∪
              (P ∩ {y : Fin d → ℝ | y j = 1}) := by
        intro y hy
        exact Or.inr hy
      exact (convexHull_mono honeSliceSubset)
        (memConvexHull_coordinateOneSlice_of_bounds P j
          (fun y hy ↦ (hP_bounds y hy).2) hxOneHull hxOneFace)
    have hsumCols :
        Matrix.mulVec Y (lifted_basis j.succ) +
            Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) =
          Matrix.mulVec Y (lifted_basis 0) := by
      ext k
      simp [Matrix.mulVec_sub, mulVec_lifted_basis]
    have hcomb : x = (x j) • xOne + (1 - x j) • xZero := by
      have hsumVec :
          homogenized_point x =
            (x j) • homogenized_point xOne + (1 - x j) • homogenized_point xZero := by
        calc
          homogenized_point x = Matrix.mulVec Y (lifted_basis 0) := hcol0'.symm
          _ = Matrix.mulVec Y (lifted_basis j.succ) +
                Matrix.mulVec Y (lifted_basis 0 - lifted_basis j.succ) := hsumCols.symm
          _ = (x j) • homogenized_point xOne +
                (1 - x j) • homogenized_point xZero := by
              rw [hcolEq', hdiffEq']
      funext i
      simpa [homogenized_point] using congr_fun hsumVec i.succ
    -- Convexity of the coordinate hull now recombines the two face witnesses.
    have hconvCoord : Convex ℝ (coordinate_lift_project_hull P j) := by
      rw [coordinate_lift_project_hull_def]
      exact convex_convexHull ℝ _
    have hcombMem :
        (x j) • xOne + (1 - x j) • xZero ∈ coordinate_lift_project_hull P j := by
      have hweights : x j + (1 - x j) = 1 := by
        ring
      exact hconvCoord hxOneCoord hxZeroCoord hxj_nonneg hone_sub_nonneg hweights
    exact hcomb ▸ hcombMem

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: coordinate
lift-project hulls preserve inclusions of their underlying sets. -/
private lemma coordinateLiftProjectHull_mono_local
    {d : ℕ}
    {P Q : Set (Fin d → ℝ)}
    (hPQ : P ⊆ Q)
    (j : Fin d) :
    coordinate_lift_project_hull P j ⊆ coordinate_lift_project_hull Q j := by
  -- Push the inclusion through both endpoint slices and then through `convexHull`.
  rw [coordinate_lift_project_hull_def, coordinate_lift_project_hull_def]
  have hslices :
      (P ∩ {x : Fin d → ℝ | x j = 0}) ∪ (P ∩ {x : Fin d → ℝ | x j = 1}) ⊆
        (Q ∩ {x : Fin d → ℝ | x j = 0}) ∪ (Q ∩ {x : Fin d → ℝ | x j = 1}) := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hPQ hx.1, hx.2⟩
    · exact Or.inr ⟨hPQ hx.1, hx.2⟩
  exact convexHull_mono hslices

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: under prefix
unit-box bounds, every Lovász–Schrijver iterate lies in the corresponding prefix
lift-project closure. -/
private lemma lovaszSchrijverIterate_subset_kthLiftProjectClosure
    {d p : ℕ}
    (hp : p ≤ d)
    (P : Set (Fin d → ℝ))
    (hP_convex : Convex ℝ P)
    (hP_subset : P ⊆ prefix_unit_box hp) :
    ∀ k : ℕ,
      (lovasz_schrijver_N^[k]) P ⊆ kth_lift_project_closure hp P k
  | 0 => by
      -- Both zeroth iterates are the original set.
      intro x hx
      simpa [kth_lift_project_closure_zero] using hx
  | k + 1 => by
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rw [kth_lift_project_closure_succ, mem_prefix_lift_project_closure_iff]
      intro j
      have hcurrent_subset : (lovasz_schrijver_N^[k]) P ⊆ P :=
        lovasz_schrijver_iterate_subset_self P hP_convex k
      have hcurrent_bounds :
          ∀ y ∈ (lovasz_schrijver_N^[k]) P,
            0 ≤ y (Fin.castLE hp j) ∧ y (Fin.castLE hp j) ≤ 1 := by
        intro y hy
        have hyBox := hP_subset (hcurrent_subset hy)
        exact (mem_prefix_unit_box_iff hp y).mp hyBox j
      have hxCoordinate :
          x ∈ coordinate_lift_project_hull ((lovasz_schrijver_N^[k]) P)
            (Fin.castLE hp j) :=
        lovaszSchrijverN_subset_coordinateLiftProjectHull_of_bounds
          ((lovasz_schrijver_N^[k]) P) (Fin.castLE hp j) hcurrent_bounds hx
      -- The induction inclusion transports each coordinate hull to the closure at stage `k`.
      exact coordinateLiftProjectHull_mono_local
        (lovaszSchrijverIterate_subset_kthLiftProjectClosure hp P hP_convex hP_subset k)
        (Fin.castLE hp j) hxCoordinate

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_18: flattening identifies
mixed points binary on `I` with the canonical binary-prefix point family. -/
private lemma appendEquiv_image_mixedBinaryFirstBlockPoints
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n)) :
    Fin.appendEquiv n n '' mixed_binary_first_block_points_on P I =
      binary_prefix_points_on_subset (Nat.le_add_right n n) (Fin.appendEquiv n n '' P) I := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    intro i hi
    simpa [Fin.appendEquiv] using hx.2 i hi
  · rintro ⟨⟨x, hxP, rfl⟩, hxI⟩
    refine ⟨x, ⟨hxP, ?_⟩, rfl⟩
    intro i hi
    simpa [Fin.appendEquiv] using hxI i hi

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_18.lean
Exercise 10.18. If `P` is a polytope
contained in `[0,1]^n × ℝ^n`, then for every natural
number `t` and every index set `I ⊆ {1, …, n}` with `|I| ≤ t`, the `t`th Lovász-Schrijver
iterate of the canonical Chapter 10 operator, transported back from the flattening
`Fin.appendEquiv n n '' P ⊆ ℝ^(n+n)`, is contained in the convex hull of the points of `P`
whose first-block coordinates indexed by `I` are binary. -/
theorem lovasz_schrijver_iterate_subset_convexHull_binary_first_block_points_on
    (P : Set (MixedRealPoint n n))
    (hP_polytope : P.IsPolytope ℝ)
    (hP_subset :
      P ⊆ (Set.Icc (0 : Fin n → ℝ) 1) ×ˢ (Set.univ : Set (Fin n → ℝ)))
    (t : ℕ)
    (I : Finset (Fin n))
    (hI : I.card ≤ t) :
    (Fin.appendEquiv n n).symm '' ((lovasz_schrijver_N^[t]) ((Fin.appendEquiv n n) '' P)) ⊆
      convexHull ℝ (mixed_binary_first_block_points_on P I) := by
  let e : MixedRealPoint n n ≃ₗ[ℝ] (Fin (n + n) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n n).toLinearEquiv mixedAppendEquiv_isLinearMap
  let Q : Set (Fin (n + n) → ℝ) := Fin.appendEquiv n n '' P
  let hp : n ≤ n + n := Nat.le_add_right n n
  have hQ_polytope : Q.IsPolytope ℝ := by
    rcases hP_polytope with ⟨V, hV_finite, hP_eq⟩
    refine ⟨e '' V, hV_finite.image e, ?_⟩
    -- A linear map commutes with convex hull, so the finite vertex presentation flattens.
    simp only [Q, e]
    rw [hP_eq]
    exact mixedAppendEquiv_isLinearMap.image_convexHull V
  have hQ_polyhedron : is_polyhedron Q :=
    (polytope_iff_bounded_polyhedron Q).mp hQ_polytope |>.1
  have hQ_convex : Convex ℝ Q := convex_of_is_polyhedron hQ_polyhedron
  have hQ_subset : Q ⊆ prefix_unit_box hp := by
    rintro z ⟨x, hxP, rfl⟩
    rw [mem_prefix_unit_box_iff]
    intro i
    have hxFirst : x.1 ∈ Set.Icc (0 : Fin n → ℝ) 1 := (hP_subset hxP).1
    have hxi : 0 ≤ x.1 i ∧ x.1 i ≤ 1 :=
      ⟨hxFirst.1 i, hxFirst.2 i⟩
    simpa [hp, Fin.appendEquiv] using hxi
  have hI_le_n : I.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  have hflat :
      (lovasz_schrijver_N^[t]) Q ⊆
        convexHull ℝ (binary_prefix_points_on_subset hp Q I) := by
    -- Descend to round `I.card`, then compare that iterate with the rank closure.
    have hdescend :
        (lovasz_schrijver_N^[t]) Q ⊆ (lovasz_schrijver_N^[I.card]) Q :=
      lovasz_schrijver_iterates_antitone Q hQ_convex hI
    have hclosure :
        (lovasz_schrijver_N^[I.card]) Q ⊆
          kth_lift_project_closure hp Q I.card :=
      lovaszSchrijverIterate_subset_kthLiftProjectClosure hp Q hQ_convex hQ_subset I.card
    have hfactor :
        kth_lift_project_closure hp Q I.card ⊆
          convexHull ℝ (binary_prefix_points_on_subset hp Q I) := by
      -- Route correction: the current Chapter 5 API gives the needed forward inclusion,
      -- so select the factor indexed by `I` without using the obsolete equality theorem.
      intro x hx
      have hxFactors :=
        kth_lift_project_closure_subset_iInter_convexHull_binary_on_k_subsets
          hp Q hQ_polyhedron hQ_subset I.card hI_le_n hx
      simp only [Set.mem_iInter] at hxFactors
      exact hxFactors ⟨I, rfl⟩
    exact hdescend.trans (hclosure.trans hfactor)
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  have hzHull :
      z ∈ convexHull ℝ (e '' mixed_binary_first_block_points_on P I) := by
    have hzFlat := hflat hz
    have hbinaryImage :
        e '' mixed_binary_first_block_points_on P I =
          binary_prefix_points_on_subset hp Q I := by
      simpa [e, hp, Q] using appendEquiv_image_mixedBinaryFirstBlockPoints P I
    rwa [hbinaryImage]
  -- Finally apply the inverse linear equivalence to the flattened convex-hull membership.
  have hImageHull :
      e.symm '' convexHull ℝ (e '' mixed_binary_first_block_points_on P I) =
        convexHull ℝ (mixed_binary_first_block_points_on P I) := by
    have hinverseImage :
        e.symm '' (e '' mixed_binary_first_block_points_on P I) =
          mixed_binary_first_block_points_on P I := by
      ext y
      constructor
      · rintro ⟨z, ⟨x, hx, hxz⟩, hzy⟩
        subst z
        have hxy : x = y := by
          simpa using hzy
        exact hxy ▸ hx
      · intro hy
        refine ⟨e y, ⟨y, hy, rfl⟩, ?_⟩
        exact e.symm_apply_apply y
    calc
      e.symm '' convexHull ℝ (e '' mixed_binary_first_block_points_on P I) =
          convexHull ℝ (e.symm '' (e '' mixed_binary_first_block_points_on P I)) :=
        e.symm.toLinearMap.image_convexHull _
      _ = convexHull ℝ (mixed_binary_first_block_points_on P I) := by
        rw [hinverseImage]
  rw [← hImageHull]
  exact ⟨z, hzHull, rfl⟩

#print axioms lovasz_schrijver_iterate_subset_convexHull_binary_first_block_points_on

end Exercise1018
