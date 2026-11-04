/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Matrix.Order
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped Matrix MatrixOrder LovaszSchrijverNotation

-- Domain sampling note:
-- * primary domain: Lovasz-Schrijver `N₊` lift-and-project relaxations for `0/1` polytopes
-- * core/canonical owners reused from the chapter: `IsLovaszSchrijverMatrix`,
--   `homogenized_point`, `lifted_basis`, and `N₊(P)`
-- * source-facing declarations kept here: the equation `(10.8)` matrix inequalities specialized
--   to `polyhedron_le_set A b`, together with the resulting normalized set
--   `equation_10_8_N_plus`

section Exercise1019

variable {m n : ℕ}

/-- Helper for Exercise 10.19: the matrix polyhedron `polyhedron_le_set A b` is convex. -/
lemma polyhedronLeSet_convex
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a c ha hc hac
  -- Rewrite convex combinations directly through the defining matrix inequalities.
  rw [mem_polyhedron_le_set_iff] at hx hy ⊢
  intro i
  calc
    (A *ᵥ (a • x + c • y)) i = a * (A *ᵥ x) i + c * (A *ᵥ y) i := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ ≤ a * b i + c * b i := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 10.19: a vector in the homogenized cone of `polyhedron_le_set A b`
records a nonnegative height and scaled polyhedron inequalities. -/
lemma homogenizedCone_polyhedronLinearData
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone (polyhedron_le_set A b)) :
    0 ≤ y 0 ∧
      A *ᵥ (fun j : Fin n ↦ y j.succ) ≤ (y 0) • b := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hx : x ∈ polyhedron_le_set A b := by
    -- The convex hull step collapses because matrix polyhedra are convex.
    rwa [convexHull_eq_self.2 (polyhedronLeSet_convex A b)] at hxHull
  rw [mem_polyhedron_le_set_iff] at hx
  refine ⟨by simpa [homogenized_point] using ht, ?_⟩
  -- Scale the defining inequalities by the nonnegative homogenizing coordinate.
  have htail :
      (fun j : Fin n ↦ (t • homogenized_point x) j.succ) = t • x := by
    funext j
    simp [homogenized_point]
  intro i
  calc
    (A *ᵥ fun j : Fin n ↦ (t • homogenized_point x) j.succ) i = (A *ᵥ (t • x)) i := by
      rw [htail]
    _ = t * (A *ᵥ x) i := by
      simp [Matrix.mulVec_smul]
    _ ≤ t * b i := mul_le_mul_of_nonneg_left (hx i) ht
    _ = (((t • homogenized_point x) 0) • b) i := by
      simp [homogenized_point]

/-- Helper for Exercise 10.19: positive homogenizing scale and scaled polyhedron inequalities
rebuild a point of `homogenized_cone (polyhedron_le_set A b)`. -/
lemma homogenizedCone_polyhedronOfPosScale
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {t : ℝ}
    {z : Fin n → ℝ}
    (ht : 0 < t)
    (hz : A *ᵥ z ≤ t • b) :
    Fin.cons t z ∈ homogenized_cone (polyhedron_le_set A b) := by
  rw [mem_homogenized_cone_iff]
  refine ⟨t, ht.le, (1 / t) • z, ?_, ?_⟩
  · -- Divide the scaled inequalities by the positive height.
    rw [convexHull_eq_self.2 (polyhedronLeSet_convex A b), mem_polyhedron_le_set_iff]
    intro i
    have hzi : (A *ᵥ z) i ≤ t * b i := by
      simpa using hz i
    have hdiv :
        (1 / t) * (A *ᵥ z) i ≤ (1 / t) * (t * b i) := by
      exact mul_le_mul_of_nonneg_left hzi (by positivity)
    calc
      (A *ᵥ ((1 / t) • z)) i = (1 / t) * (A *ᵥ z) i := by
        simp [Matrix.mulVec_smul, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / t) * (t * b i) := hdiv
      _ = b i := by
        field_simp [ht.ne']
  · -- Reassemble the lifted vector from the normalized point.
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [homogenized_point]
    · intro j
      simp [homogenized_point, div_eq_mul_inv, ht.ne']

/-- Helper for Exercise 10.19: a positive semidefinite real matrix admits a square Gram
factorization `Y = Uᵀ * U`. -/
lemma posSemidef_exists_eq_transpose_mul_self
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hYpsd : Y.PosSemidef) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Y = Uᵀ * U := by
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hYpsd.nonneg with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU

/-- Helper for Exercise 10.19: if the lifted weight `Y 0 i.succ` vanishes, positive
semidefiniteness forces the entire `i`th lifted column to vanish. -/
lemma psdLiftedColumn_eq_zero_of_zeroWeight
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hYpsd : Y.PosSemidef)
    (hYsymm : Yᵀ = Y)
    (hdiag : ∀ i : Fin n, Y i.succ i.succ = Y i.succ 0)
    (i : Fin n)
    (hzero : Y 0 i.succ = 0) :
    Y *ᵥ lifted_basis i.succ = 0 := by
  rcases posSemidef_exists_eq_transpose_mul_self hYpsd with ⟨U, hU⟩
  have hsymmEntry : Y i.succ 0 = Y 0 i.succ := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) i.succ
  have hdiagZero : Y i.succ i.succ = 0 := by
    rw [hdiag i, hsymmEntry, hzero]
  have hdot :
      (U *ᵥ lifted_basis i.succ) ⬝ᵥ (U *ᵥ lifted_basis i.succ) = 0 := by
    -- The squared Euclidean norm of the `i`th column of `U` is the diagonal entry `Y i i`.
    calc
      (U *ᵥ lifted_basis i.succ) ⬝ᵥ (U *ᵥ lifted_basis i.succ) =
          (Uᵀ * U) i.succ i.succ := by
        simp [dotProduct, Matrix.mul_apply, mulVec_lifted_basis]
      _ = Y i.succ i.succ := by
        simpa using congr_fun (congr_fun hU.symm i.succ) i.succ
      _ = 0 := hdiagZero
  have hUcolZero : U *ᵥ lifted_basis i.succ = 0 := by
    exact dotProduct_self_eq_zero.mp hdot
  have hYcolZero : (Uᴴ * U) *ᵥ lifted_basis i.succ = 0 := by
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero U (lifted_basis i.succ)).2 hUcolZero
  -- Transport the zero-column statement back from the Gram factorization.
  simpa [hU, Matrix.conjTranspose_eq_transpose_of_trivial] using hYcolZero

/-- Helper for Exercise 10.19: if the complementary lifted weight `1 - Y 0 i.succ` vanishes,
positive semidefiniteness forces the complementary lifted column to vanish. -/
lemma psdDifferenceColumn_eq_zero_of_unitWeight
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hYpsd : Y.PosSemidef)
    (hYsymm : Yᵀ = Y)
    (hY00 : Y 0 0 = 1)
    (hdiag : ∀ i : Fin n, Y i.succ i.succ = Y i.succ 0)
    (i : Fin n)
    (hunit : Y 0 i.succ = 1) :
    Y *ᵥ (lifted_basis 0 - lifted_basis i.succ) = 0 := by
  rcases posSemidef_exists_eq_transpose_mul_self hYpsd with ⟨U, hU⟩
  let w : Fin (n + 1) → ℝ := U *ᵥ (lifted_basis 0 - lifted_basis i.succ)
  have hsymmEntry : Y i.succ 0 = Y 0 i.succ := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) i.succ
  have hdiagOne : Y i.succ i.succ = 1 := by
    rw [hdiag i, hsymmEntry, hunit]
  have hwdot : w ⬝ᵥ w = 0 := by
    -- Route correction: compute the squared norm of `U *ᵥ (e₀ - eᵢ)` and rewrite it through
    -- the four relevant entries of `Y`.
    calc
      w ⬝ᵥ w =
          ∑ k, (U k 0 - U k i.succ) * (U k 0 - U k i.succ) := by
        simp [w, dotProduct, Matrix.mulVec_sub, mulVec_lifted_basis]
      _ =
          ∑ k,
            (U k 0 * U k 0 - U k 0 * U k i.succ - U k i.succ * U k 0 +
              U k i.succ * U k i.succ) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring
      _ =
          ∑ k, U k 0 * U k 0 -
            ∑ k, U k 0 * U k i.succ -
            ∑ k, U k i.succ * U k 0 +
            ∑ k, U k i.succ * U k i.succ := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (Uᵀ * U) 0 0 - (Uᵀ * U) 0 i.succ - (Uᵀ * U) i.succ 0 + (Uᵀ * U) i.succ i.succ := by
        simp [Matrix.mul_apply]
      _ = Y 0 0 - Y 0 i.succ - Y i.succ 0 + Y i.succ i.succ := by
        simp [hU]
      _ = 0 := by
        rw [hY00, hunit, hsymmEntry, hunit, hdiagOne]
        ring
  have hwZero : w = 0 := by
    exact dotProduct_self_eq_zero.mp hwdot
  have hYdiffZero : (Uᴴ * U) *ᵥ (lifted_basis 0 - lifted_basis i.succ) = 0 := by
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero U
      (lifted_basis 0 - lifted_basis i.succ)).2 (by simpa [w] using hwZero)
  -- Transport the zero-difference statement back from the Gram factorization.
  simpa [hU, Matrix.conjTranspose_eq_transpose_of_trivial] using hYdiffZero

/-- Helper for Exercise 10.19: a normalized equation `(10.8)` witness satisfies the canonical
Lovasz-Schrijver matrix conditions for `polyhedron_le_set A b`. -/
lemma equation10_8Witness_isLovaszSchrijverMatrix
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {x : Fin n → ℝ}
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hYsymm : Yᵀ = Y)
    (hY00 : Y 0 0 = 1)
    (hcol0 : A *ᵥ (fun j : Fin n ↦ Y j.succ 0) ≤ b)
    (hcols : ∀ i : Fin n,
      0 ≤ Y 0 i.succ ∧
        A *ᵥ (fun j : Fin n ↦ Y j.succ i.succ) ≤ (Y 0 i.succ) • b ∧
          0 ≤ 1 - Y 0 i.succ ∧
            A *ᵥ (fun j : Fin n ↦ Y j.succ 0 - Y j.succ i.succ) ≤
              (1 - Y 0 i.succ) • b)
    (hdiag : ∀ i : Fin n, Y i.succ i.succ = Y i.succ 0)
    (hYpsd : Y.PosSemidef)
    (hfirst : Y *ᵥ lifted_basis 0 = homogenized_point x) :
    IsLovaszSchrijverMatrix (polyhedron_le_set A b) Y := by
  have hxPoly : x ∈ polyhedron_le_set A b := by
    -- Read the tail of the first column as `x` and transfer the normalized inequalities.
    rw [mem_polyhedron_le_set_iff]
    have htail : (fun j : Fin n ↦ Y j.succ 0) = x := by
      funext j
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hfirst j.succ
    intro i
    simpa [htail] using hcol0 i
  have hxHull : x ∈ convexHull ℝ (polyhedron_le_set A b) := by
    rw [convexHull_eq_self.2 (polyhedronLeSet_convex A b)]
    exact hxPoly
  rw [isLovaszSchrijverMatrix_iff]
  refine ⟨hYsymm, ?_, ?_, hdiag⟩
  · -- The first column is exactly the homogenized feasible point `(1, x)`.
    simpa [hfirst] using
      homogenized_point_mem_homogenized_cone (polyhedron_le_set A b) hxHull
  · intro i
    rcases hcols i with ⟨hweight_nonneg, hcolIneq, hcomp_nonneg, hcompIneq⟩
    refine ⟨?_, ?_⟩
    · by_cases hzero : Y 0 i.succ = 0
      · -- Zero lifted weight collapses the whole lifted column by positive semidefiniteness.
        rw [psdLiftedColumn_eq_zero_of_zeroWeight hYpsd hYsymm hdiag i hzero]
        simpa using
          homogenizedCone_nonneg_smul_mem (polyhedron_le_set A b)
            (homogenized_point_mem_homogenized_cone (polyhedron_le_set A b) hxHull) le_rfl
      · -- Positive lifted weight lets us dehomogenize directly.
        have hpos : 0 < Y 0 i.succ := lt_of_le_of_ne hweight_nonneg (Ne.symm hzero)
        have hcolVec :
            Y *ᵥ lifted_basis i.succ =
              Fin.cons (Y 0 i.succ) (fun j : Fin n ↦ Y j.succ i.succ) := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [mulVec_lifted_basis]
          · intro j
            simp [mulVec_lifted_basis]
        rw [hcolVec]
        exact homogenizedCone_polyhedronOfPosScale hpos hcolIneq
    · by_cases hunitZero : 1 - Y 0 i.succ = 0
      · -- Zero complementary weight collapses the complementary column by PSD.
        have hunit : Y 0 i.succ = 1 := by linarith
        rw [psdDifferenceColumn_eq_zero_of_unitWeight hYpsd hYsymm hY00 hdiag i hunit]
        simpa using
          homogenizedCone_nonneg_smul_mem (polyhedron_le_set A b)
            (homogenized_point_mem_homogenized_cone (polyhedron_le_set A b) hxHull) le_rfl
      · -- Positive complementary weight also dehomogenizes directly.
        have hpos : 0 < 1 - Y 0 i.succ := lt_of_le_of_ne hcomp_nonneg (Ne.symm hunitZero)
        have hcompVec :
            Y *ᵥ (lifted_basis 0 - lifted_basis i.succ) =
              Fin.cons (1 - Y 0 i.succ) (fun j : Fin n ↦ Y j.succ 0 - Y j.succ i.succ) := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simpa [Matrix.mulVec_sub, mulVec_lifted_basis] using hY00
          · intro j
            simp [Matrix.mulVec_sub, mulVec_lifted_basis]
        rw [hcompVec]
        exact homogenizedCone_polyhedronOfPosScale hpos hcompIneq

namespace IsLovaszSchrijverMatrix

/-- For `K = polyhedron_le_set A b`, the canonical Lovasz-Schrijver matrix conditions imply the
linear inequalities appearing in equation `(10.8)`.

This bridge is deliberately one-way: membership in `homogenized_cone (polyhedron_le_set A b)`
contains more information than the displayed inequalities alone, notably the collapse forced when
the first coordinate is `0`. The normalized equation `(10.8)` presentation is handled separately
below. -/
theorem polyhedron_le_set_linear_conditions
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsLovaszSchrijverMatrix (polyhedron_le_set A b) Y) :
      Yᵀ = Y ∧
        0 ≤ Y 0 0 ∧
        A *ᵥ (fun j : Fin n ↦ Y j.succ 0) ≤ (Y 0 0) • b ∧
        (∀ i : Fin n,
          0 ≤ Y 0 i.succ ∧
            A *ᵥ (fun j : Fin n ↦ Y j.succ i.succ) ≤ (Y 0 i.succ) • b ∧
              0 ≤ Y 0 0 - Y 0 i.succ ∧
                A *ᵥ (fun j : Fin n ↦ Y j.succ 0 - Y j.succ i.succ) ≤
                  (Y 0 0 - Y 0 i.succ) • b) ∧
        (∀ i : Fin n, Y i.succ i.succ = Y i.succ 0) := by
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, hcol0Cone, hcolsCone, hdiag⟩
  have hcol0Data := homogenizedCone_polyhedronLinearData hcol0Cone
  refine ⟨hYsymm, ?_, ?_, ?_, hdiag⟩
  · simpa [mulVec_lifted_basis] using hcol0Data.1
  · simpa [mulVec_lifted_basis] using hcol0Data.2
  · intro i
    rcases hcolsCone i with ⟨hcolCone, hcompCone⟩
    have hcolData := homogenizedCone_polyhedronLinearData hcolCone
    have hcompData := homogenizedCone_polyhedronLinearData hcompCone
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [mulVec_lifted_basis] using hcolData.1
    · simpa [mulVec_lifted_basis] using hcolData.2
    · simpa [Matrix.mulVec_sub, mulVec_lifted_basis] using hcompData.1
    · simpa [Matrix.mulVec_sub, mulVec_lifted_basis] using hcompData.2

end IsLovaszSchrijverMatrix

/-- The normalized equation `(10.8)` presentation of the semidefinite Lovasz-Schrijver lift for
the matrix polyhedron `polyhedron_le_set A b`. This keeps the source-facing `Y 0 0 = 1`
normalization, while the canonical owner remains `N₊(polyhedron_le_set A b)`. Unlike the raw
matrix-owner conditions, this source-facing witness package keeps only the normalized inequalities
used in the textbook equation `(10.8)`. -/
def equation_10_8_N_plus
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      Yᵀ = Y ∧
        Y 0 0 = 1 ∧
        A *ᵥ (fun j : Fin n ↦ Y j.succ 0) ≤ b ∧
        (∀ i : Fin n,
          0 ≤ Y 0 i.succ ∧
            A *ᵥ (fun j : Fin n ↦ Y j.succ i.succ) ≤ (Y 0 i.succ) • b ∧
              0 ≤ 1 - Y 0 i.succ ∧
                A *ᵥ (fun j : Fin n ↦ Y j.succ 0 - Y j.succ i.succ) ≤
                  (1 - Y 0 i.succ) • b) ∧
        (∀ i : Fin n, Y i.succ i.succ = Y i.succ 0) ∧
        Y.PosSemidef ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- Membership in `equation_10_8_N_plus A b` is exactly the existence of a positive-semidefinite
lift matrix satisfying the normalized equation `(10.8)` constraints and having first column
`(1, x)`. -/
theorem mem_equation_10_8_N_plus_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ equation_10_8_N_plus A b ↔
      ∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        Yᵀ = Y ∧
          Y 0 0 = 1 ∧
          A *ᵥ (fun j : Fin n ↦ Y j.succ 0) ≤ b ∧
          (∀ i : Fin n,
            0 ≤ Y 0 i.succ ∧
              A *ᵥ (fun j : Fin n ↦ Y j.succ i.succ) ≤ (Y 0 i.succ) • b ∧
                0 ≤ 1 - Y 0 i.succ ∧
                  A *ᵥ (fun j : Fin n ↦ Y j.succ 0 - Y j.succ i.succ) ≤
                    (1 - Y 0 i.succ) • b) ∧
          (∀ i : Fin n, Y i.succ i.succ = Y i.succ 0) ∧
          Y.PosSemidef ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- Exercise 10.19. For a matrix polyhedron `K = polyhedron_le_set A b`, the normalized
equation `(10.8)` presentation agrees with the canonical Lovasz-Schrijver semidefinite
relaxation `N₊(K)`. The textbook polytope and box hypotheses are redundant for this
presentation-level identification, so the Lean statement keeps only the matrix polyhedron data. -/
theorem exercise_10_19_equation_10_8_N_plus_eq_lovasz_schrijver_N_plus
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    equation_10_8_N_plus A b = N₊(polyhedron_le_set A b) := by
  ext x
  constructor
  · intro hx
    rw [mem_equation_10_8_N_plus_iff] at hx
    rw [mem_lovasz_schrijver_N_plus_iff]
    rcases hx with ⟨Y, hYsymm, hY00, hcol0, hcols, hdiag, hYpsd, hfirst⟩
    -- Reuse the normalized witness directly after rebuilding the canonical owner conditions.
    refine ⟨Y, ?_, hYpsd, hfirst⟩
    exact equation10_8Witness_isLovaszSchrijverMatrix
      hYsymm hY00 hcol0 hcols hdiag hYpsd hfirst
  · intro hx
    rw [mem_lovasz_schrijver_N_plus_iff] at hx
    rw [mem_equation_10_8_N_plus_iff]
    rcases hx with ⟨Y, hY, hYpsd, hfirst⟩
    have hlinear := hY.polyhedron_le_set_linear_conditions
    rcases hlinear with ⟨hYsymm, hY00_nonneg, hcol0, hcols, hdiag⟩
    have hY00 : Y 0 0 = 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hfirst 0
    -- The canonical `N₊` constraints specialize to the normalized equation `(10.8)` system.
    refine ⟨Y, hYsymm, hY00, ?_, ?_, hdiag, hYpsd, hfirst⟩
    · simpa [hY00] using hcol0
    · intro i
      rcases hcols i with ⟨hweight_nonneg, hcolIneq, hcomp_nonneg, hcompIneq⟩
      refine ⟨hweight_nonneg, hcolIneq, ?_, ?_⟩
      · simpa [hY00] using hcomp_nonneg
      · simpa [hY00] using hcompIneq

end Exercise1019
