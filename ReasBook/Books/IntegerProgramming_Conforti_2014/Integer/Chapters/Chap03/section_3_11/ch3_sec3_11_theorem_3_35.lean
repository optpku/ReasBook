/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_theorem_3_11
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1

open scoped BigOperators Matrix

-- This source-facing file keeps the matrix presentation in part (1), while part (2) is now the
-- matrix specialization of the Section 3.11 cone-level owner theorem.

section Theorem335

variable {m n : ℕ}

/-- Helper for Theorem 3.35: the row-sum functional obtained by summing all rows of `A`. -/
def rowSumFunctional (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  fun j ↦ ∑ i : Fin m, A i j

/-- Helper for Theorem 3.35: the homogeneous cone `matrix_polyhedral_cone A` contains the zero
vector. -/
lemma matrix_polyhedral_cone_zero_mem (A : Matrix (Fin m) (Fin n) ℝ) :
    (0 : Fin n → ℝ) ∈ matrix_polyhedral_cone A := by
  -- The homogeneous system `A *ᵥ x ≤ 0` is satisfied by the zero vector.
  refine (mem_matrix_polyhedral_cone A 0).2 ?_
  simp

/-- Helper for Theorem 3.35: the homogeneous cone `matrix_polyhedral_cone A` is closed under
addition. -/
lemma matrix_polyhedral_cone_add_mem
    (A : Matrix (Fin m) (Fin n) ℝ)
    {x y : Fin n → ℝ}
    (hx : x ∈ matrix_polyhedral_cone A)
    (hy : y ∈ matrix_polyhedral_cone A) :
    x + y ∈ matrix_polyhedral_cone A := by
  -- Add the two rowwise nonpositive inequality certificates.
  refine (mem_matrix_polyhedral_cone A (x + y)).2 ?_
  intro i
  have hx_i := (mem_matrix_polyhedral_cone A x).mp hx i
  have hy_i := (mem_matrix_polyhedral_cone A y).mp hy i
  simpa [Matrix.mulVec_add] using add_le_add hx_i hy_i

/-- Helper for Theorem 3.35: the homogeneous cone `matrix_polyhedral_cone A` is closed under
nonnegative scaling. -/
lemma matrix_polyhedral_cone_nonneg_smul_mem
    (A : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ matrix_polyhedral_cone A)
    {a : ℝ}
    (ha : 0 ≤ a) :
    a • x ∈ matrix_polyhedral_cone A := by
  -- Scale each homogeneous inequality by the same nonnegative factor.
  refine (mem_matrix_polyhedral_cone A (a • x)).2 ?_
  intro i
  have hx_i := (mem_matrix_polyhedral_cone A x).mp hx i
  simpa [Matrix.mulVec_smul, Pi.smul_apply, mul_comm] using
    mul_le_mul_of_nonneg_left hx_i ha

/-- Helper for Theorem 3.35: the homogeneous system `A *ᵥ x ≤ 0` is canonically a cone. -/
def matrix_polyhedral_cone_pointedCone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    PointedCone ℝ (Fin n → ℝ) where
  carrier := matrix_polyhedral_cone A
  zero_mem' := matrix_polyhedral_cone_zero_mem A
  add_mem' := fun {x y} ↦ matrix_polyhedral_cone_add_mem A
  smul_mem' := fun a x hx ↦ matrix_polyhedral_cone_nonneg_smul_mem A hx a.2

/-- Helper for Theorem 3.35: pairing the row-sum functional with `x` is the sum of all row
evaluations `(A *ᵥ x) i`. -/
lemma rowSumFunctional_dotProduct_eq_sum_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    rowSumFunctional A ⬝ᵥ x = ∑ i : Fin m, (A *ᵥ x) i := by
  -- Expand both sides and commute the finite sums.
  calc
    rowSumFunctional A ⬝ᵥ x = ∑ j : Fin n, (∑ i : Fin m, A i j) * x j := by
      simp [rowSumFunctional, dotProduct]
    _ = ∑ j : Fin n, ∑ i : Fin m, A i j * x j := by
      simp [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, A i j * x j := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin m, (A *ᵥ x) i := by
      simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 3.35: the normalizing slice matrix adjoins the single row
`-rowSumFunctional A` to the original system `A *ᵥ x ≤ 0`. -/
def normalizingSliceMatrix
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + 1)) (Fin n) ℝ :=
  fun i ↦ Fin.lastCases (-rowSumFunctional A) (fun i' ↦ A i') i

/-- Helper for Theorem 3.35: the right-hand side for the normalizing slice is `0` on the original
rows and `1` on the added row. -/
def normalizingSliceRhs : Fin (m + 1) → ℝ :=
  Fin.snoc (fun _ : Fin m ↦ (0 : ℝ)) 1

/-- Helper for Theorem 3.35: multiplying the normalizing slice matrix by `x` records the original
slacks `A *ᵥ x` together with the extra coordinate `-(rowSumFunctional A ⬝ᵥ x)`. -/
lemma normalizingSliceMatrix_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    normalizingSliceMatrix A *ᵥ x =
      Fin.snoc (A *ᵥ x) (-(rowSumFunctional A ⬝ᵥ x)) := by
  -- Evaluate the augmented system row by row.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [normalizingSliceMatrix, Matrix.mulVec, dotProduct, rowSumFunctional,
        Fin.sum_univ_castSucc, Fin.snoc_last, mul_comm, mul_left_comm, mul_assoc]
  | cast i =>
      simp [normalizingSliceMatrix, Matrix.mulVec, dotProduct, Fin.snoc_castSucc]

/-- Helper for Theorem 3.35: membership in the normalizing slice is equivalent to belonging to the
cone and satisfying the extra inequality `rowSumFunctional A ⬝ᵥ x ≥ -1`. -/
lemma mem_normalizingSlice_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs ↔
      x ∈ matrix_polyhedral_cone A ∧ rowSumFunctional A ⬝ᵥ x ≥ -1 := by
  -- Split the augmented inequalities into the original homogeneous block and the final slice row.
  change normalizingSliceMatrix A *ᵥ x ≤ normalizingSliceRhs ↔
    x ∈ matrix_polyhedral_cone A ∧ rowSumFunctional A ⬝ᵥ x ≥ -1
  rw [normalizingSliceMatrix_mulVec]
  constructor
  · intro hx
    refine ⟨(mem_matrix_polyhedral_cone A x).2 ?_, ?_⟩
    · intro i
      simpa [normalizingSliceRhs] using hx i.castSucc
    · have hlast := hx (Fin.last m)
      have hlast' : -(rowSumFunctional A ⬝ᵥ x) ≤ 1 := by
        simpa [normalizingSliceRhs] using hlast
      linarith
  · rintro ⟨hx, hslice⟩
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa [normalizingSliceRhs] using neg_le.mpr hslice
    · simpa [normalizingSliceRhs] using (mem_matrix_polyhedral_cone A x).mp hx i

/-- Helper for Theorem 3.35: on a pointed homogeneous cone, the row-sum functional is strictly
negative on every nonzero cone point. -/
lemma row_sum_strictly_negative_of_mem_matrix_polyhedral_cone_ne_zero
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hC_pointed : is_pointed (matrix_polyhedral_cone A))
    {x : Fin n → ℝ}
    (hx : x ∈ matrix_polyhedral_cone A)
    (hx_ne_zero : x ≠ 0) :
    rowSumFunctional A ⬝ᵥ x < 0 := by
  -- First note that the row sum is never positive because each individual inequality is
  -- nonpositive on a cone point.
  have hx_nonpos : ∀ i : Fin m, (A *ᵥ x) i ≤ 0 := (mem_matrix_polyhedral_cone A x).mp hx
  have hsum_nonpos : rowSumFunctional A ⬝ᵥ x ≤ 0 := by
    rw [rowSumFunctional_dotProduct_eq_sum_mulVec]
    exact Finset.sum_nonpos fun i _ ↦ hx_nonpos i
  by_contra hnot_lt
  have hsum_zero : rowSumFunctional A ⬝ᵥ x = 0 :=
    le_antisymm hsum_nonpos (le_of_not_gt hnot_lt)
  have hAx_zero : A *ᵥ x = 0 := by
    -- If the sum of nonpositive row evaluations is zero, then every row evaluation vanishes.
    ext i
    have hzero_all :
        ∀ j : Fin m, (A *ᵥ x) j = 0 := by
      have hsum_eval : ∑ j : Fin m, (A *ᵥ x) j = 0 := by
        simpa [rowSumFunctional_dotProduct_eq_sum_mulVec A x] using hsum_zero
      intro j
      exact
        (Finset.sum_eq_zero_iff_of_nonpos fun k _ ↦ hx_nonpos k).mp hsum_eval j (Finset.mem_univ j)
    exact hzero_all i
  have h_nonempty : Set.Nonempty (polyhedron_le_set A 0) := ⟨0, by simp [polyhedron_le_set]⟩
  have hx_lineality : x ∈ linealitySpace (matrix_polyhedral_cone A) := by
    rw [polyhedron_linealitySpace_eq_kernel_set A 0 h_nonempty]
    simpa [matrix_polyhedral_cone] using hAx_zero
  -- Pointedness now forces the supposed nonzero cone point to vanish.
  exact hx_ne_zero ((is_pointed_iff_eq_zero_of_mem_linealitySpace.mp hC_pointed) x hx_lineality)

/-- Helper for Theorem 3.35: on the normalized slice `rowSumFunctional A ⬝ᵥ x = -1`, proper conic
decompositions of the cone ray generated by `x` are equivalent to open-segment decompositions of
`x` inside the slice polyhedron. -/
lemma exists_openSegment_decomposition_iff_proper_conic_combination_on_normalized_slice
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hC_pointed : is_pointed (matrix_polyhedral_cone A))
    {x : Fin n → ℝ}
    (hx : x ∈ matrix_polyhedral_cone A)
    (hx_norm : rowSumFunctional A ⬝ᵥ x = -1) :
    ProperConicCombinationOfDistinctConeRays (matrix_polyhedral_cone A) x ↔
      ∃ x' ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs,
        ∃ x'' ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs,
          x' ≠ x'' ∧ x ∈ openSegment ℝ x' x'' := by
  constructor
  · rintro ⟨r₁, r₂, hr₁, hr₂, hr₁_ne, hr₂_ne, hnot_sameRay, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
    let s₁ : ℝ := -(rowSumFunctional A ⬝ᵥ r₁)
    let s₂ : ℝ := -(rowSumFunctional A ⬝ᵥ r₂)
    let x₁ : Fin n → ℝ := s₁⁻¹ • r₁
    let x₂ : Fin n → ℝ := s₂⁻¹ • r₂
    have hs₁_pos : 0 < s₁ := by
      dsimp [s₁]
      linarith [row_sum_strictly_negative_of_mem_matrix_polyhedral_cone_ne_zero
        A hC_pointed hr₁ hr₁_ne]
    have hs₂_pos : 0 < s₂ := by
      dsimp [s₂]
      linarith [row_sum_strictly_negative_of_mem_matrix_polyhedral_cone_ne_zero
        A hC_pointed hr₂ hr₂_ne]
    have hs₁_ne : s₁ ≠ 0 := ne_of_gt hs₁_pos
    have hs₂_ne : s₂ ≠ 0 := ne_of_gt hs₂_pos
    have hx₁_mem_cone : x₁ ∈ matrix_polyhedral_cone A := by
      -- Normalize the first summand by the strictly positive row sum.
      exact
        matrix_polyhedral_cone_nonneg_smul_mem A hr₁
          (by positivity)
    have hx₂_mem_cone : x₂ ∈ matrix_polyhedral_cone A := by
      -- Normalize the second summand by the strictly positive row sum.
      exact
        matrix_polyhedral_cone_nonneg_smul_mem A hr₂
          (by positivity)
    have hx₁_norm : rowSumFunctional A ⬝ᵥ x₁ = -1 := by
      -- The normalization is chosen precisely so that the slice equation becomes `-1`.
      calc
        rowSumFunctional A ⬝ᵥ x₁ = s₁⁻¹ * (rowSumFunctional A ⬝ᵥ r₁) := by
          simp [x₁, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        _ = s₁⁻¹ * (-s₁) := by simp [s₁]
        _ = -(s₁⁻¹ * s₁) := by ring
        _ = -1 := by simp [hs₁_ne]
    have hx₂_norm : rowSumFunctional A ⬝ᵥ x₂ = -1 := by
      -- The same normalization works for the second summand.
      calc
        rowSumFunctional A ⬝ᵥ x₂ = s₂⁻¹ * (rowSumFunctional A ⬝ᵥ r₂) := by
          simp [x₂, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        _ = s₂⁻¹ * (-s₂) := by simp [s₂]
        _ = -(s₂⁻¹ * s₂) := by ring
        _ = -1 := by simp [hs₂_ne]
    have hx₁_mem_slice : x₁ ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs := by
      -- Once the first summand is normalized, it lies on the slice boundary.
      exact (mem_normalizingSlice_iff A x₁).2 ⟨hx₁_mem_cone, by simpa [hx₁_norm]⟩
    have hx₂_mem_slice : x₂ ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs := by
      -- The same argument puts the second summand on the same boundary slice.
      exact (mem_normalizingSlice_iff A x₂).2 ⟨hx₂_mem_cone, by simpa [hx₂_norm]⟩
    have hr₁_scaled : r₁ = s₁ • x₁ := by
      dsimp [x₁]
      rw [smul_smul, mul_inv_cancel₀ hs₁_ne, one_smul]
    have hr₂_scaled : r₂ = s₂ • x₂ := by
      dsimp [x₂]
      rw [smul_smul, mul_inv_cancel₀ hs₂_ne, one_smul]
    let a : ℝ := μ₁ * s₁
    let b : ℝ := μ₂ * s₂
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have hb_pos : 0 < b := by
      dsimp [b]
      positivity
    have hx_convex : x = a • x₁ + b • x₂ := by
      -- Rewrite the proper conic decomposition in terms of the normalized slice points.
      calc
        x = μ₁ • r₁ + μ₂ • r₂ := hdecomp
        _ = μ₁ • (s₁ • x₁) + μ₂ • (s₂ • x₂) := by rw [hr₁_scaled, hr₂_scaled]
        _ = a • x₁ + b • x₂ := by simp [a, b, smul_smul, mul_assoc]
    have hab : a + b = 1 := by
      -- Applying the row-sum functional to the convex decomposition forces the coefficients to
      -- add up to `1`.
      have hα := congrArg (fun z : Fin n → ℝ ↦ rowSumFunctional A ⬝ᵥ z) hx_convex
      have hα' :
          rowSumFunctional A ⬝ᵥ x =
            a * (rowSumFunctional A ⬝ᵥ x₁) + b * (rowSumFunctional A ⬝ᵥ x₂) := by
        simpa [dotProduct_add, dotProduct_smul, mul_comm, mul_left_comm, mul_assoc] using hα
      have hsum : rowSumFunctional A ⬝ᵥ x = -a - b := by
        calc
          rowSumFunctional A ⬝ᵥ x = a * (-1 : ℝ) + b * (-1 : ℝ) := by
            simpa [hx₁_norm, hx₂_norm] using hα'
          _ = -a - b := by ring
      linarith [hx_norm, hsum]
    have hx₁_ne_x₂ : x₁ ≠ x₂ := by
      intro hxeq
      have hsame₁ : SameRay ℝ r₁ x₁ := by
        rw [hr₁_scaled]
        exact SameRay.sameRay_pos_smul_left x₁ hs₁_pos
      have hsame₂ : SameRay ℝ x₁ r₂ := by
        rw [hxeq, hr₂_scaled]
        exact SameRay.sameRay_pos_smul_right x₂ hs₂_pos
      have hsame : SameRay ℝ r₁ r₂ := by
        refine SameRay.trans hsame₁ hsame₂ ?_
        intro hx₁_zero
        left
        rw [hr₁_scaled, hx₁_zero, smul_zero]
      exact hnot_sameRay hsame
    have hx_open : x ∈ openSegment ℝ x₁ x₂ := by
      -- The normalized conic decomposition is now an honest open-segment decomposition.
      refine (mem_openSegment_iff_div).2 ⟨a, b, ha_pos, hb_pos, ?_⟩
      simpa [hab] using hx_convex.symm
    exact ⟨x₁, hx₁_mem_slice, x₂, hx₂_mem_slice, hx₁_ne_x₂, hx_open⟩
  · rintro ⟨x', hx'_slice, x'', hx''_slice, hne, hseg⟩
    rcases (mem_openSegment_iff_div).mp hseg with ⟨a, b, ha, hb, hx_decomp⟩
    rcases (mem_normalizingSlice_iff A x').mp hx'_slice with ⟨hx'_cone, hx'_slice_ineq⟩
    rcases (mem_normalizingSlice_iff A x'').mp hx''_slice with ⟨hx''_cone, hx''_slice_ineq⟩
    let lam : ℝ := a / (a + b)
    let mu : ℝ := b / (a + b)
    have hlam_pos : 0 < lam := by
      dsimp [lam]
      positivity
    have hmu_pos : 0 < mu := by
      dsimp [mu]
      positivity
    have hlammu : lam + mu = 1 := by
      dsimp [lam, mu]
      have hab_ne : a + b ≠ 0 := by linarith
      field_simp [hab_ne]
    have hα_decomp := congrArg (fun z : Fin n → ℝ ↦ rowSumFunctional A ⬝ᵥ z) hx_decomp
    have hα_decomp' :
        lam * (rowSumFunctional A ⬝ᵥ x') + mu * (rowSumFunctional A ⬝ᵥ x'') = -1 := by
      simpa [lam, mu, hx_norm, dotProduct_add, dotProduct_smul, mul_comm, mul_left_comm, mul_assoc]
        using hα_decomp
    have hx'_norm : rowSumFunctional A ⬝ᵥ x' = -1 := by
      -- A convex combination of two slice points can hit the boundary `-1` only if both points
      -- already lie on that same boundary.
      have hx'_le : rowSumFunctional A ⬝ᵥ x' ≤ -1 := by
        by_contra hx'_gt
        have hx'_gt' : -1 < rowSumFunctional A ⬝ᵥ x' := lt_of_not_ge hx'_gt
        nlinarith [hα_decomp', hx''_slice_ineq, hx'_gt', hlam_pos, hmu_pos]
      linarith
    have hx''_norm : rowSumFunctional A ⬝ᵥ x'' = -1 := by
      -- The same argument applies symmetrically to the second endpoint.
      have hx''_le : rowSumFunctional A ⬝ᵥ x'' ≤ -1 := by
        by_contra hx''_gt
        have hx''_gt' : -1 < rowSumFunctional A ⬝ᵥ x'' := lt_of_not_ge hx''_gt
        nlinarith [hα_decomp', hx'_slice_ineq, hx''_gt', hlam_pos, hmu_pos]
      linarith
    have hx'_ne_zero : x' ≠ 0 := by
      intro hx'_zero
      simpa [hx'_zero] using hx'_norm
    have hx''_ne_zero : x'' ≠ 0 := by
      intro hx''_zero
      simpa [hx''_zero] using hx''_norm
    have hnot_sameRay : ¬ SameRay ℝ x' x'' := by
      intro hsame
      rcases SameRay.exists_pos hsame hx'_ne_zero hx''_ne_zero with ⟨u, v, hu, hv, huv⟩
      have hα_scaled := congrArg (fun z : Fin n → ℝ ↦ rowSumFunctional A ⬝ᵥ z) huv
      have huv_eq : u = v := by
        simpa [hx'_norm, hx''_norm, dotProduct_smul, mul_comm, mul_left_comm, mul_assoc]
          using hα_scaled
      have hscaled_eq : u • x' = u • x'' := by simpa [huv_eq] using huv
      have hsub_zero : x' - x'' = 0 := by
        have : u • (x' - x'') = 0 := by
          simpa [smul_sub] using sub_eq_zero.mpr hscaled_eq
        exact (smul_eq_zero.mp this).resolve_left (show u ≠ 0 from ne_of_gt hu)
      exact hne (sub_eq_zero.mp hsub_zero)
    exact ⟨x', x'', hx'_cone, hx''_cone, hx'_ne_zero, hx''_ne_zero, hnot_sameRay,
      lam, mu, hlam_pos, hmu_pos, hx_decomp.symm⟩

/-- Helper for Theorem 3.35: appending the always-active normalizing row converts `n - 1` active
independent original rows into `n` active independent rows of the augmented slice system. -/
lemma exists_augmented_active_linearlyIndependent_rows_of_exists_original_active_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin n → ℝ}
    (hx_norm : rowSumFunctional A ⬝ᵥ x = -1)
    (hrows :
      ∃ I : Fin (n - 1) ↪ Fin m,
        (∀ i : Fin (n - 1), (A *ᵥ x) (I i) = 0) ∧
          LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i))) :
    ∃ J : Fin n ↪ Fin (m + 1),
      (∀ j : Fin n, (normalizingSliceMatrix A *ᵥ x) (J j) = normalizingSliceRhs (J j)) ∧
        LinearIndependent ℝ (fun j : Fin n ↦ normalizingSliceMatrix A (J j)) := by
  rcases hrows with ⟨I, hactive, hlin⟩
  by_cases hn : n = 0
  · -- The slice equation `rowSumFunctional A ⬝ᵥ x = -1` rules out the degenerate zero-dimensional
    -- case, so this branch is contradictory.
    subst hn
    exfalso
    have hx_zero : x = 0 := by
      ext i
      exact Fin.elim0 i
    simpa [hx_zero] using hx_norm
  · have hn_cast : (n - 1) + 1 = n := by
      omega
    let rowsTail : Fin (n - 1) → Fin n → ℝ := fun i ↦ A (I i)
    have hrowsTail_ann :
        ∀ i : Fin (n - 1), rowsTail i ⬝ᵥ x = 0 := by
      intro i
      simpa [rowsTail, Matrix.mulVec, dotProduct] using hactive i
    have hspan_ann :
        ∀ v ∈ Submodule.span ℝ (Set.range rowsTail), v ⬝ᵥ x = 0 := by
      intro v hv
      -- Every row in the span of the chosen active rows still annihilates `x`.
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hrowsTail_ann i
      · simp
      · intro u w _ _ hu hw
        rw [add_dotProduct, hu, hw]
        simp
      · intro a v _ hv
        rw [smul_dotProduct, hv]
        simp
    have hnot_mem_span :
        -rowSumFunctional A ∉ Submodule.span ℝ (Set.range rowsTail) := by
      intro hmem
      have hzero := hspan_ann (-rowSumFunctional A) hmem
      have hone : (-rowSumFunctional A) ⬝ᵥ x = 1 := by
        have hneg :
            (-rowSumFunctional A) ⬝ᵥ x = -(rowSumFunctional A ⬝ᵥ x) := by
          simp [dotProduct, Finset.sum_neg_distrib]
        linarith [hx_norm, hneg]
      linarith
    have hrows_head :
        LinearIndependent ℝ (Fin.cons (-rowSumFunctional A) rowsTail :
          Fin ((n - 1) + 1) → Fin n → ℝ) := by
      -- The added normalizing row is independent from the rows that already vanish on `x`.
      exact hlin.finCons hnot_mem_span
    let e : Fin n ≃ Fin ((n - 1) + 1) := (Fin.castOrderIso hn_cast.symm).toEquiv
    let J' : Fin ((n - 1) + 1) ↪ Fin (m + 1) :=
      ⟨Fin.cons (Fin.last m) (fun i : Fin (n - 1) ↦ (I i).castSucc),
        (Fin.cons_injective_iff).2 ⟨by
          rintro ⟨i, hi⟩
          exact Fin.castSucc_ne_last (I i) hi,
        fun i i' hij ↦ I.injective (Fin.castSucc_injective _ hij)⟩⟩
    let J : Fin n ↪ Fin (m + 1) :=
      ⟨fun i ↦ J' (e i), fun i i' hij ↦ e.injective (J'.injective hij)⟩
    have hJ'_active :
        ∀ i : Fin ((n - 1) + 1),
          (normalizingSliceMatrix A *ᵥ x) (J' i) = normalizingSliceRhs (J' i) := by
      intro i
      cases i using Fin.cases with
      | zero =>
          -- The prepended row is the always-active normalizing equation.
          simpa [J', normalizingSliceMatrix_mulVec, normalizingSliceRhs, hx_norm]
      | succ i =>
          -- The tail rows are exactly the original active homogeneous rows.
          simpa [J', normalizingSliceMatrix_mulVec, normalizingSliceRhs] using hactive i
    have hJ'_linearIndependent :
        LinearIndependent ℝ (fun i : Fin ((n - 1) + 1) ↦ normalizingSliceMatrix A (J' i)) := by
      -- Reindex the prepended row family through the explicit embedding `J'`.
      have hrows_eq :
          (fun i : Fin ((n - 1) + 1) ↦ normalizingSliceMatrix A (J' i)) =
            Fin.cons (-rowSumFunctional A) rowsTail := by
        funext i
        cases i using Fin.cases with
        | zero =>
            simp [J', normalizingSliceMatrix]
        | succ i =>
            simp [J', rowsTail, normalizingSliceMatrix]
      simpa [hrows_eq] using hrows_head
    have hJ_linearIndependent :
        LinearIndependent ℝ (fun i : Fin n ↦ normalizingSliceMatrix A (J i)) := by
      simpa [J, e] using (linearIndependent_equiv e).2 hJ'_linearIndependent
    refine ⟨J, ?_, hJ_linearIndependent⟩
    intro i
    -- Transport the active equalities from the `(n - 1) + 1` indexing to `Fin n`.
    simpa [J, e] using hJ'_active (e i)

/-- Helper for Theorem 3.35: any active independent `n`-tuple of augmented slice rows must use
the added normalizing row, and deleting it yields `n - 1` active independent original rows. -/
lemma exists_original_active_linearlyIndependent_rows_of_exists_augmented_active_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ matrix_polyhedral_cone A)
    (hx_ne_zero : x ≠ 0)
    (hx_norm : rowSumFunctional A ⬝ᵥ x = -1)
    (hrows :
      ∃ J : Fin n ↪ Fin (m + 1),
        (∀ j : Fin n, (normalizingSliceMatrix A *ᵥ x) (J j) = normalizingSliceRhs (J j)) ∧
          LinearIndependent ℝ (fun j : Fin n ↦ normalizingSliceMatrix A (J j))) :
    ∃ I : Fin (n - 1) ↪ Fin m,
      (∀ i : Fin (n - 1), (A *ᵥ x) (I i) = 0) ∧
        LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  rcases hrows with ⟨J, hJ_active, hJ_linearIndependent⟩
  by_cases hn : n = 0
  · -- A nonzero vector cannot live in the zero-dimensional ambient space.
    subst hn
    exfalso
    apply hx_ne_zero
    ext i
    exact Fin.elim0 i
  · have haux_present : ∃ k : Fin n, J k = Fin.last m := by
      by_contra haux_absent
      have hJ_notlast : ∀ k : Fin n, J k ≠ Fin.last m := by
        intro k hk
        exact haux_absent ⟨k, hk⟩
      let tail : Fin n → Fin m := fun k ↦ Fin.castPred (J k) (hJ_notlast k)
      have htail_row :
          ∀ k : Fin n, normalizingSliceMatrix A (J k) = A (tail k) := by
        intro k
        -- If the auxiliary row never appears, every chosen augmented row is really an original row.
        have hcast : (tail k).castSucc = J k :=
          Fin.castSucc_castPred (J k) (hJ_notlast k)
        rw [← hcast]
        simp [normalizingSliceMatrix]
      have htail_linearIndependent :
          LinearIndependent ℝ (fun k : Fin n ↦ A (tail k)) := by
        simpa [htail_row] using hJ_linearIndependent
      have htail_ann :
          ∀ k : Fin n, A (tail k) ⬝ᵥ x = 0 := by
        intro k
        have hk_active := hJ_active k
        rw [show J k = (tail k).castSucc by
          exact Fin.castSucc_castPred (J k) (hJ_notlast k)] at hk_active
        have hk_row : (A *ᵥ x) (tail k) = 0 := by
          simpa [normalizingSliceMatrix_mulVec, normalizingSliceRhs] using hk_active
        simpa [Matrix.mulVec, dotProduct] using hk_row
      -- Without the auxiliary row, all `n` chosen original rows annihilate `x`, forcing `x = 0`.
      exact hx_ne_zero (eq_zero_of_linearIndependent_rows_annihilate htail_linearIndependent htail_ann)
    obtain ⟨kAux, hkAux⟩ := haux_present
    have hn_cast : (n - 1) + 1 = n := by
      omega
    let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm kAux
    let skip : Fin (n - 1) → Fin n := fun i ↦ Fin.cast hn_cast (pivot.succAboveEmb i)
    have hskip_ne_aux : ∀ i : Fin (n - 1), skip i ≠ kAux := by
      intro i
      intro hskip
      have :
          pivot.succAboveEmb i = pivot := by
        apply Fin.cast_injective hn_cast
        simpa [skip, pivot] using hskip
      exact Fin.succAbove_ne pivot i this
    have hskip_notlast : ∀ i : Fin (n - 1), J (skip i) ≠ Fin.last m := by
      intro i hij
      exact hskip_ne_aux i (J.injective (hij.trans hkAux.symm))
    let tail : Fin (n - 1) → Fin m := fun i ↦ Fin.castPred (J (skip i)) (hskip_notlast i)
    have htail_eq :
        ∀ i : Fin (n - 1), J (skip i) = (tail i).castSucc := by
      intro i
      exact (Fin.castSucc_castPred (J (skip i)) (hskip_notlast i)).symm
    let I : Fin (n - 1) ↪ Fin m :=
      ⟨tail, by
        intro i i' hij
        apply pivot.succAboveEmb.inj'
        apply Fin.cast_injective hn_cast
        apply J.injective
        calc
          J (skip i) = (tail i).castSucc := htail_eq i
          _ = (tail i').castSucc := by simpa [hij]
          _ = J (skip i') := (htail_eq i').symm⟩
    refine ⟨I, ?_, ?_⟩
    · intro i
      -- After deleting the auxiliary row, the remaining active slice equalities are exactly the
      -- original homogeneous active equalities.
      have hi := hJ_active (skip i)
      rw [htail_eq i] at hi
      have hi' : (A *ᵥ x) (tail i) = 0 := by
        simpa [normalizingSliceMatrix_mulVec, normalizingSliceRhs] using hi
      simpa [I, Matrix.mulVec, dotProduct] using hi'
    · have hskip_linearIndependent :
          LinearIndependent ℝ
            (fun i : Fin (n - 1) ↦ normalizingSliceMatrix A (J (skip i))) := by
        exact hJ_linearIndependent.comp skip (by
          intro i i' hij
          apply pivot.succAboveEmb.inj'
          apply Fin.cast_injective hn_cast
          exact hij)
      -- Deleting the unique auxiliary row leaves the original active row family.
      simpa [I, htail_eq, normalizingSliceMatrix] using hskip_linearIndependent

/-- Theorem 3.35 (1). Let `C = {x ∈ ℝ^n | A *ᵥ x ≤ 0}` be a pointed cone, and let `rbar ∈ C` be a
nonzero generator of a ray of `C`. Then `rbar` generates an extreme ray of `C` if and only if
there are `n - 1` distinct inequalities of `A *ᵥ x ≤ 0` that are active at `rbar` and whose row
vectors are linearly independent. -/
theorem matrix_polyhedral_cone_extreme_ray_iff_exists_active_linearlyIndependent_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hC_pointed : is_pointed (matrix_polyhedral_cone A))
    {rbar : Fin n → ℝ}
    (hrbar : rbar ∈ matrix_polyhedral_cone A)
    (hrbar_ne_zero : rbar ≠ 0) :
    IsExtremeRayOfCone (matrix_polyhedral_cone A) rbar ↔
      ∃ I : Fin (n - 1) ↪ Fin m,
        (∀ i : Fin (n - 1), (A *ᵥ rbar) (I i) = 0) ∧
          LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
  let α : Fin n → ℝ := rowSumFunctional A
  let scale : ℝ := -(α ⬝ᵥ rbar)
  let c : ℝ := scale⁻¹
  let rhat : Fin n → ℝ := c • rbar
  have hcone :
      ∃ K : PointedCone ℝ (Fin n → ℝ), (K : Set (Fin n → ℝ)) = matrix_polyhedral_cone A := by
    -- The homogeneous system already carries the canonical cone structure needed by the
    -- cone/extreme-ray criterion.
    exact ⟨matrix_polyhedral_cone_pointedCone A, rfl⟩
  have hα_neg : α ⬝ᵥ rbar < 0 := by
    -- The row-sum functional is strictly negative on every nonzero cone point.
    simpa [α] using
      row_sum_strictly_negative_of_mem_matrix_polyhedral_cone_ne_zero
        A hC_pointed hrbar hrbar_ne_zero
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    linarith
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_ne : c ≠ 0 := by
    exact ne_of_gt hc_pos
  have hrhat_mem : rhat ∈ matrix_polyhedral_cone A := by
    -- Positive scaling keeps the generator on the same cone ray.
    exact matrix_polyhedral_cone_nonneg_smul_mem A hrbar hc_pos.le
  have hrhat_ne_zero : rhat ≠ 0 := by
    -- A positive rescaling of a nonzero generator remains nonzero.
    simpa [rhat] using smul_ne_zero hc_ne hrbar_ne_zero
  have hα_rhat : α ⬝ᵥ rhat = -1 := by
    -- The normalization places `rhat` exactly on the slice `α ⬝ᵥ x = -1`.
    calc
      α ⬝ᵥ rhat = c * (α ⬝ᵥ rbar) := by
        simp [rhat, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = c * (-scale) := by simp [scale]
      _ = -(c * scale) := by ring
      _ = -1 := by
        dsimp [c]
        simp [ne_of_gt hscale_pos]
  have hrhat_sameRay : SameRay ℝ rbar rhat := by
    -- Positive rescaling does not change the generated ray.
    simpa [rhat] using (SameRay.sameRay_pos_smul_right (R := ℝ) rbar hc_pos)
  have hrhat_mem_slice :
      rhat ∈ polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs := by
    -- The normalized vector still satisfies the original cone inequalities and now lies on the
    -- slice boundary.
    exact (mem_normalizingSlice_iff A rhat).2 ⟨hrhat_mem, by simpa [α, hα_rhat]⟩
  have hrhat_extreme_iff_extremePoint :
      IsExtremeRayOfCone (matrix_polyhedral_cone A) rhat ↔
        rhat ∈
          (polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs).extremePoints ℝ := by
    -- The cone-side "no proper conic combination" criterion matches the slice-side
    -- "no open-segment decomposition" criterion exactly on `α ⬝ᵥ x = -1`.
    rw [isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      hcone hrhat_mem hrhat_ne_zero]
    rw [mem_extremePoints_iff_not_exists_eq_smul_add_smul_of_ne
      (normalizingSliceMatrix A) normalizingSliceRhs hrhat_mem_slice]
    constructor
    · intro hno hseg
      exact hno
        ((exists_openSegment_decomposition_iff_proper_conic_combination_on_normalized_slice
          A hC_pointed hrhat_mem (by simpa [α] using hα_rhat)).mpr hseg)
    · intro hno hproper
      exact hno
        ((exists_openSegment_decomposition_iff_proper_conic_combination_on_normalized_slice
          A hC_pointed hrhat_mem (by simpa [α] using hα_rhat)).mp hproper)
  have hrhat_extremePoint_iff_active :
      rhat ∈ (polyhedron_le_set (normalizingSliceMatrix A) normalizingSliceRhs).extremePoints ℝ ↔
        ∃ I : Fin (n - 1) ↪ Fin m,
          (∀ i : Fin (n - 1), (A *ᵥ rhat) (I i) = 0) ∧
            LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
    constructor
    · intro hrhat_extremePoint
      obtain ⟨J, hJ_active, hJ_linearIndependent⟩ :=
        (mem_extremePoints_iff_exists_active_linearlyIndependent_rows
          (normalizingSliceMatrix A) normalizingSliceRhs hrhat_mem_slice).mp hrhat_extremePoint
      -- Strip the added normalizing row back off the slice witness.
      exact
        exists_original_active_linearlyIndependent_rows_of_exists_augmented_active_rows
          A hrhat_mem hrhat_ne_zero (by simpa [α] using hα_rhat)
          ⟨J, hJ_active, hJ_linearIndependent⟩
    · intro hrows
      have haugmented :
          ∃ J : Fin n ↪ Fin (m + 1),
            (∀ j : Fin n,
              (normalizingSliceMatrix A *ᵥ rhat) (J j) = normalizingSliceRhs (J j)) ∧
              LinearIndependent ℝ (fun j : Fin n ↦ normalizingSliceMatrix A (J j)) :=
        exists_augmented_active_linearlyIndependent_rows_of_exists_original_active_rows
          A (by simpa [α] using hα_rhat) hrows
      -- Theorem 3.34 now converts the augmented active-row witness into a vertex witness.
      exact
        (mem_extremePoints_iff_exists_active_linearlyIndependent_rows
          (normalizingSliceMatrix A) normalizingSliceRhs hrhat_mem_slice).mpr haugmented
  have hrhat_extreme_iff_active :
      IsExtremeRayOfCone (matrix_polyhedral_cone A) rhat ↔
        ∃ I : Fin (n - 1) ↪ Fin m,
          (∀ i : Fin (n - 1), (A *ᵥ rhat) (I i) = 0) ∧
            LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) := by
    exact hrhat_extreme_iff_extremePoint.trans hrhat_extremePoint_iff_active
  have hactive_scale :
      (∃ I : Fin (n - 1) ↪ Fin m,
        (∀ i : Fin (n - 1), (A *ᵥ rbar) (I i) = 0) ∧
          LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i))) ↔
      (∃ I : Fin (n - 1) ↪ Fin m,
        (∀ i : Fin (n - 1), (A *ᵥ rhat) (I i) = 0) ∧
          LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i))) := by
    constructor
    · rintro ⟨I, hI_active, hI_linearIndependent⟩
      refine ⟨I, ?_, hI_linearIndependent⟩
      intro i
      -- Positive scaling preserves the active-equality condition.
      simp [rhat, Matrix.mulVec_smul, hI_active i, mul_comm]
    · rintro ⟨I, hI_active, hI_linearIndependent⟩
      refine ⟨I, ?_, hI_linearIndependent⟩
      intro i
      have hi : c * (A *ᵥ rbar) (I i) = 0 := by
        simpa [rhat, Matrix.mulVec_smul, mul_comm] using hI_active i
      exact (mul_eq_zero.mp hi).resolve_left hc_ne
  constructor
  · intro hrbar_extreme
    have hrhat_extreme :
        IsExtremeRayOfCone (matrix_polyhedral_cone A) rhat := by
      -- Normalize the generator and stay on the same extreme ray.
      exact isExtremeRayOfCone_of_sameRay hrbar_extreme hrhat_sameRay hrhat_ne_zero
    exact hactive_scale.mpr (hrhat_extreme_iff_active.mp hrhat_extreme)
  · intro hrows
    have hrhat_rows :
        ∃ I : Fin (n - 1) ↪ Fin m,
          (∀ i : Fin (n - 1), (A *ᵥ rhat) (I i) = 0) ∧
            LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)) :=
      hactive_scale.mp hrows
    have hrhat_extreme :
        IsExtremeRayOfCone (matrix_polyhedral_cone A) rhat :=
      hrhat_extreme_iff_active.mpr hrhat_rows
    -- Route correction: finish by transporting the extremality witness back along the positive
    -- same-ray normalization instead of reproving extremality directly on `rbar`.
    exact isExtremeRayOfCone_of_sameRay hrhat_extreme hrhat_sameRay.symm hrbar_ne_zero

/-- Theorem 3.35 (2). Let `C = {x ∈ ℝ^n | A *ᵥ x ≤ 0}` and let `rbar ∈ C` be a nonzero generator
of a ray of `C`. Then `rbar` generates an extreme ray of `C` if and only if it is not a proper
conic combination of two distinct rays contained in `C`. This criterion is stated entirely at the
cone/extreme-ray level, so no separate pointedness hypothesis is needed. -/
theorem matrix_polyhedral_cone_extreme_ray_iff_not_proper_conic_combination_of_distinct_rays
    (A : Matrix (Fin m) (Fin n) ℝ)
    {rbar : Fin n → ℝ}
    (hrbar : rbar ∈ matrix_polyhedral_cone A)
    (hrbar_ne_zero : rbar ≠ 0) :
    IsExtremeRayOfCone (matrix_polyhedral_cone A) rbar ↔
      ¬ ProperConicCombinationOfDistinctConeRays (matrix_polyhedral_cone A) rbar := by
  exact
    isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      ⟨matrix_polyhedral_cone_pointedCone A, rfl⟩ hrbar hrbar_ne_zero

end Theorem335
