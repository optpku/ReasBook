/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped Matrix LovaszSchrijverNotation

section Exercise1010

variable {m p : ℕ}

/-- The polyhedron `P = {x ∈ ℝ_+^(2 + p) | A x ≥ b}` from Exercise 10.10. -/
def mixed_zero_one_polyhedron
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) : Set (Fin (p + 2) → ℝ) :=
  {x | b ≤ A *ᵥ x ∧ 0 ≤ x}

/-- Membership in `mixed_zero_one_polyhedron A b` is exactly the conjunction of the inequalities
`A x ≥ b` and coordinatewise nonnegativity. -/
theorem mem_mixed_zero_one_polyhedron_iff
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_polyhedron A b ↔ b ≤ A *ᵥ x ∧ 0 ≤ x :=
  Iff.rfl

/-- The mixed `0,1` linear set `S = {x ∈ {0,1}^2 × ℝ_+^p | A x ≥ b}` from Exercise 10.10. -/
def mixed_zero_one_linear_set
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) : Set (Fin (p + 2) → ℝ) :=
  {x |
    x ∈ mixed_zero_one_polyhedron A b ∧
      (x 0 = 0 ∨ x 0 = 1) ∧
        (x 1 = 0 ∨ x 1 = 1)}

/-- Membership in `mixed_zero_one_linear_set A b` means membership in the polyhedron together with
binary first and second coordinates. -/
theorem mem_mixed_zero_one_linear_set_iff
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_linear_set A b ↔
      x ∈ mixed_zero_one_polyhedron A b ∧
        (x 0 = 0 ∨ x 0 = 1) ∧
          (x 1 = 0 ∨ x 1 = 1) :=
  Iff.rfl

/-- The mixed `0,1` Lovasz-Schrijver lift-matrix conditions from Exercise 10.10: the first two
coordinates are treated as binary, while the remaining `p` coordinates stay continuous. The
homogenized-cone owner is reused from Section 10.3. -/
def IsMixedZeroOneLovaszSchrijverMatrix
    (P : Set (Fin (p + 2) → ℝ))
    (Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ) : Prop :=
  Yᵀ = Y ∧
    (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
      (Y *ᵥ lifted_basis 1) ∈ homogenized_cone P ∧
        (Y *ᵥ lifted_basis 2) ∈ homogenized_cone P ∧
          (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) ∈ homogenized_cone P ∧
            (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) ∈ homogenized_cone P ∧
              Y 1 1 = Y 1 0 ∧
                Y 2 2 = Y 2 0

/-- Unfolding characterization of `IsMixedZeroOneLovaszSchrijverMatrix`. -/
theorem isMixedZeroOneLovaszSchrijverMatrix_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ} :
    IsMixedZeroOneLovaszSchrijverMatrix P Y ↔
      Yᵀ = Y ∧
        (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
          (Y *ᵥ lifted_basis 1) ∈ homogenized_cone P ∧
            (Y *ᵥ lifted_basis 2) ∈ homogenized_cone P ∧
              (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) ∈ homogenized_cone P ∧
                (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) ∈ homogenized_cone P ∧
                  Y 1 1 = Y 1 0 ∧
                    Y 2 2 = Y 2 0 :=
  Iff.rfl

namespace IsLovaszSchrijverMatrix

/-- The full `0/1` Lovasz-Schrijver matrix constraints imply the mixed `0,1` constraints when only
the first two coordinates are singled out as binary. -/
theorem toMixedZeroOne
    {P : Set (Fin (p + 2) → ℝ)}
    {Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ}
    (hY : IsLovaszSchrijverMatrix P Y) :
    IsMixedZeroOneLovaszSchrijverMatrix P Y := by
  rcases hY with ⟨h_symm, hcol0, hcols, hdiag⟩
  refine ⟨h_symm, hcol0, (hcols 0).1, (hcols 1).1, (hcols 0).2, (hcols 1).2, hdiag 0, hdiag 1⟩

end IsLovaszSchrijverMatrix

/-- The mixed `0,1` one-step linear Lovasz-Schrijver operator from Exercise 10.10. -/
def mixed_zero_one_lovasz_schrijver_N
    (P : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {x | ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
      IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- Membership in `mixed_zero_one_lovasz_schrijver_N P` means admitting a mixed `0,1`
Lovasz-Schrijver lift matrix with first column `(1, x)`. -/
theorem mem_mixed_zero_one_lovasz_schrijver_N_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_lovasz_schrijver_N P ↔
      ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
        IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- The mixed `0,1` one-step semidefinite Lovasz-Schrijver operator from Exercise 10.10. -/
def mixed_zero_one_lovasz_schrijver_N_plus
    (P : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {x | ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
      IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
        Y.PosSemidef ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- Membership in `mixed_zero_one_lovasz_schrijver_N_plus P` means admitting a positive
semidefinite mixed `0,1` Lovasz-Schrijver lift matrix with first column `(1, x)`. -/
theorem mem_mixed_zero_one_lovasz_schrijver_N_plus_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_lovasz_schrijver_N_plus P ↔
      ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
        IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
          Y.PosSemidef ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- Dropping positive semidefiniteness sends the mixed `0,1` semidefinite lift to the mixed
`0,1` linear lift. -/
theorem mixed_zero_one_lovasz_schrijver_N_plus_subset_N
    (P : Set (Fin (p + 2) → ℝ)) :
    mixed_zero_one_lovasz_schrijver_N_plus P ⊆
      mixed_zero_one_lovasz_schrijver_N P := by
  intro x hx
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, -, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_iff).2 ⟨Y, hY, hcol⟩

/-- The chapter-wide all-binary Lovasz-Schrijver lift maps into the mixed `0,1` lift when only
the first two coordinates are remembered as binary. -/
theorem lovasz_schrijver_N_subset_mixed_zero_one_lovasz_schrijver_N
    (P : Set (Fin (p + 2) → ℝ)) :
    N(P) ⊆ mixed_zero_one_lovasz_schrijver_N P := by
  intro x hx
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_iff).2 ⟨Y, hY.toMixedZeroOne, hcol⟩

/-- The chapter-wide all-binary semidefinite Lovasz-Schrijver lift maps into the mixed `0,1`
semidefinite lift when only the first two coordinates are remembered as binary. -/
theorem lovasz_schrijver_N_plus_subset_mixed_zero_one_lovasz_schrijver_N_plus
    (P : Set (Fin (p + 2) → ℝ)) :
    N₊(P) ⊆ mixed_zero_one_lovasz_schrijver_N_plus P := by
  intro x hx
  rw [mem_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, hpsd, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_plus_iff).2
    ⟨Y, hY.toMixedZeroOne, hpsd, hcol⟩

/-- Helper for Exercise 10.10: `mixed_zero_one_polyhedron A b` is convex because both the matrix
system `b ≤ A *ᵥ x` and the coordinatewise nonnegativity constraints are preserved by convex
combinations. -/
lemma convex_mixedZeroOnePolyhedron
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (mixed_zero_one_polyhedron A b) := by
  intro x hx y hy a c ha hc hac
  rw [mem_mixed_zero_one_polyhedron_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · -- Combine the row inequalities linearly and use `a + c = 1`.
    intro i
    have hx_i : b i ≤ (A *ᵥ x) i := hx.1 i
    have hy_i : b i ≤ (A *ᵥ y) i := hy.1 i
    calc
      b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
      _ ≤ a * (A *ᵥ x) i + c * (A *ᵥ y) i := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
      _ = (A *ᵥ (a • x + c • y)) i := by
        rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
        calc
          a * ∑ j, A i j * x j + c * ∑ j, A i j * y j
              = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          _ = ∑ j, A i j * (a • x + c • y) j := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [Pi.smul_apply]
                ring
  · -- Coordinatewise nonnegativity is preserved termwise.
    intro j
    exact add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg hc (hy.2 j))

/-- Helper for Exercise 10.10: enlarging the base set enlarges its homogenized cone. -/
lemma homogenizedCone_mono
    {P Q : Set (Fin (p + 2) → ℝ)}
    (hPQ : P ⊆ Q) :
    homogenized_cone P ⊆ homogenized_cone Q := by
  intro y hy
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  exact ⟨t, ht, x, convexHull_mono hPQ hx, rfl⟩

/-- Helper for Exercise 10.10: the mixed linear Lovász-Schrijver relaxation is monotone in the
underlying set. -/
lemma mixedZeroOneLovaszSchrijverN_mono :
    Monotone (fun P : Set (Fin (p + 2) → ℝ) ↦ mixed_zero_one_lovasz_schrijver_N P) := by
  intro P Q hPQ x hx
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx ⊢
  rcases hx with ⟨Y, hY, hcol⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨h_symm, h0, h1, h2, hdiff1, hdiff2, hdiag1, hdiag2⟩
  refine ⟨Y, ?_, hcol⟩
  exact (isMixedZeroOneLovaszSchrijverMatrix_iff).2
    ⟨h_symm, homogenizedCone_mono hPQ h0, homogenizedCone_mono hPQ h1,
      homogenizedCone_mono hPQ h2, homogenizedCone_mono hPQ hdiff1,
      homogenizedCone_mono hPQ hdiff2, hdiag1, hdiag2⟩

/-- Helper for Exercise 10.10: a homogenized cone point with positive first coordinate can be
dehomogenized back to a point of the original convex set. -/
lemma normalizeMemOfMemHomogenizedCone
    {P : Set (Fin (p + 2) → ℝ)}
    (hP_convex : Convex ℝ P)
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P)
    (hy0_pos : 0 < y 0) :
    ∃ x : Fin (p + 2) → ℝ, x ∈ P ∧ y = y 0 • homogenized_point x := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hxP : x ∈ P := by
    have hxHull' : x ∈ convexHull ℝ P := hxHull
    rwa [convexHull_eq_self.2 hP_convex] at hxHull'
  refine ⟨x, hxP, ?_⟩
  -- The cone scalar is exactly the first coordinate of the homogenized vector.
  simp [homogenized_point]

/-- Helper for Exercise 10.10: every point of a homogenized cone has nonnegative top coordinate,
because the cone scalar is exactly that top coordinate. -/
lemma top_nonneg_of_memHomogenizedCone
    {P : Set (Fin (p + 2) → ℝ)}
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    0 ≤ y 0 := by
  -- Unpack the cone witness and read off the top coordinate of `t • homogenized_point x`.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  simpa [homogenized_point] using ht

/-- Helper for Exercise 10.10: a homogenized cone point with zero top coordinate is the zero
vector. -/
lemma eq_zero_of_memHomogenizedCone_of_top_zero
    {P : Set (Fin (p + 2) → ℝ)}
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P)
    (hy0 : y 0 = 0) :
    y = 0 := by
  -- Unpack the cone witness and read the cone scalar off the top coordinate.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  have ht_zero : t = 0 := by
    simpa [homogenized_point] using hy0
  ext j
  simp [ht_zero]

/-- Helper for Exercise 10.10: the mixed witness already forces the first two distinguished
coordinates into the unit interval. -/
lemma firstTwoUnitBounds_of_mem_mixedZeroOneLovaszSchrijverN
    {Q : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N Q) :
    0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  -- Read the top coordinates of the first/second lifted columns and their complements.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, -, hcone1, hcone2, hconeDiff1, hconeDiff2, -, -⟩
  have hY10 : Y 1 0 = x 0 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
  have hY20 : Y 2 0 = x 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
  have hY01_eq : Y 1 0 = Y 0 1 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
  have hY02_eq : Y 2 0 = Y 0 2 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 2
  have hY01 : Y 0 1 = x 0 := by
    calc
      Y 0 1 = Y 1 0 := hY01_eq.symm
      _ = x 0 := hY10
  have hY02 : Y 0 2 = x 1 := by
    calc
      Y 0 2 = Y 2 0 := hY02_eq.symm
      _ = x 1 := hY20
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hx0_nonneg : 0 ≤ x 0 := by
    simpa [mulVec_lifted_basis, hY01] using top_nonneg_of_memHomogenizedCone hcone1
  have hx0_le_one : x 0 ≤ 1 := by
    have hdiff1_nonneg : 0 ≤ (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 :=
      top_nonneg_of_memHomogenizedCone hconeDiff1
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01] using hdiff1_nonneg
  have hx1_nonneg : 0 ≤ x 1 := by
    simpa [mulVec_lifted_basis, hY02] using top_nonneg_of_memHomogenizedCone hcone2
  have hx1_le_one : x 1 ≤ 1 := by
    have hdiff2_nonneg : 0 ≤ (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 :=
      top_nonneg_of_memHomogenizedCone hconeDiff2
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY02] using hdiff2_nonneg
  exact ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_one⟩

/-- Helper for Exercise 10.10: the mixed `0,1` semidefinite Lovasz-Schrijver relaxation is convex.
-/
lemma convex_mixedZeroOneLovaszSchrijverNPlus
    (P : Set (Fin (p + 2) → ℝ)) :
    Convex ℝ (mixed_zero_one_lovasz_schrijver_N_plus P) := by
  intro x hx y hy a b ha hb hab
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff] at hx hy ⊢
  rcases hx with ⟨Yx, hYx, hYx_psd, hcolx⟩
  rcases hy with ⟨Yy, hYy, hYy_psd, hcoly⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hYx hYy
  rcases hYx with ⟨hYx_symm, hYx0, hYx1, hYx2, hYxDiff1, hYxDiff2, hYxDiag1, hYxDiag2⟩
  rcases hYy with ⟨hYy_symm, hYy0, hYy1, hYy2, hYyDiff1, hYyDiff2, hYyDiag1, hYyDiag2⟩
  refine ⟨a • Yx + b • Yy, ?_, ?_, ?_⟩
  · -- Symmetry, cone membership, and the two binary diagonal identities are preserved termwise.
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        (a • Yx + b • Yy)ᵀ = a • Yxᵀ + b • Yyᵀ := by simp
        _ = a • Yx + b • Yy := by rw [hYx_symm, hYy_symm]
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx0 ha)
        (homogenizedCone_nonneg_smul_mem P hYy0 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx1 ha)
        (homogenizedCone_nonneg_smul_mem P hYy1 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx2 ha)
        (homogenizedCone_nonneg_smul_mem P hYy2 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYxDiff1 ha)
        (homogenizedCone_nonneg_smul_mem P hYyDiff1 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYxDiff2 ha)
        (homogenizedCone_nonneg_smul_mem P hYyDiff2 hb)
    · simp [hYxDiag1, hYyDiag1]
    · simp [hYxDiag2, hYyDiag2]
  · -- Positive semidefiniteness is stable under nonnegative scaling and addition.
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hYx_psd ha)
      (Matrix.PosSemidef.smul hYy_psd hb)
  · -- The first column becomes the homogenized lift of the convex combination.
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcolx, hcoly]
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [homogenized_point, hab]
    · intro j
      simp [homogenized_point]

/-- Helper for Exercise 10.10: every mixed binary feasible point has the standard rank-one witness
in the mixed `N₊` relaxation. -/
lemma mem_mixedZeroOneLovaszSchrijverNPlus_of_mem_mixedZeroOneLinearSet
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_linear_set A b) :
    x ∈ mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) := by
  rw [mem_mixed_zero_one_linear_set_iff] at hx
  rcases hx with ⟨hxP, hx01, hx11⟩
  let u : Fin (p + 3) → ℝ := homogenized_point x
  let Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ := Matrix.vecMulVec u u
  have hxHull : x ∈ convexHull ℝ (mixed_zero_one_polyhedron A b) := by
    exact subset_convexHull ℝ (mixed_zero_one_polyhedron A b) hxP
  have hcol0 : Y *ᵥ lifted_basis 0 = u := by
    -- The first column of the rank-one witness is the homogenized lift itself.
    ext j
    rw [mulVec_lifted_basis]
    simp [Y, u, Matrix.vecMulVec, homogenized_point]
  have hsymm : Yᵀ = Y := by
    -- A rank-one matrix `u uᵀ` is symmetric over `ℝ`.
    ext i j
    simp [Y, Matrix.vecMulVec, mul_comm]
  have hpsd : Y.PosSemidef := by
    -- Positive semidefiniteness is the standard `vecMulVec` fact.
    simpa [Y, u] using Matrix.posSemidef_vecMulVec_self_star u
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff]
  refine ⟨Y, ?_, hpsd, ?_⟩
  · -- The mixed matrix constraints only use the first two binary coordinates.
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff]
    refine ⟨hsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcol0]
      simpa [u] using homogenized_point_mem_homogenized_cone
        (mixed_zero_one_polyhedron A b) hxHull
    · have hx0_nonneg : 0 ≤ x 0 := hxP.2 0
      have hcol1 : Y *ᵥ lifted_basis 1 = x 0 • u := by
        rw [mulVec_lifted_basis]
        ext j
        simp [Y, u, Matrix.vecMulVec, homogenized_point, mul_comm]
      rw [hcol1]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hx0_nonneg
    · have hx1_nonneg : 0 ≤ x 1 := hxP.2 1
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      have hcol2 : Y *ᵥ lifted_basis 2 = x 1 • u := by
        rw [mulVec_lifted_basis]
        ext j
        rw [show Y j 2 = u j * u 2 by simp [Y, Matrix.vecMulVec], hu2]
        simp [Pi.smul_apply, mul_comm]
      rw [hcol2]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hx1_nonneg
    · have hone_sub_nonneg : 0 ≤ 1 - x 0 := by
        rcases hx01 with hx0 | hx0 <;> linarith
      have hx0_sq : x 0 * x 0 = x 0 := by
        rcases hx01 with hx0 | hx0 <;> simp [hx0]
      have hcol1 : Y *ᵥ lifted_basis 1 = x 0 • u := by
        rw [mulVec_lifted_basis]
        ext j
        simp [Y, u, Matrix.vecMulVec, homogenized_point, mul_comm]
      have hcolDiff1 :
          Y *ᵥ (lifted_basis 0 - lifted_basis 1) = (1 - x 0) • u := by
        rw [Matrix.mulVec_sub, hcol0, hcol1]
        ext j
        simp [one_sub_mul]
      rw [hcolDiff1]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hone_sub_nonneg
    · have hone_sub_nonneg : 0 ≤ 1 - x 1 := by
        rcases hx11 with hx1 | hx1 <;> linarith
      have hx1_sq : x 1 * x 1 = x 1 := by
        rcases hx11 with hx1 | hx1 <;> simp [hx1]
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      have hcol2 : Y *ᵥ lifted_basis 2 = x 1 • u := by
        rw [mulVec_lifted_basis]
        ext j
        rw [show Y j 2 = u j * u 2 by simp [Y, Matrix.vecMulVec], hu2]
        simp [Pi.smul_apply, mul_comm]
      have hcolDiff2 :
          Y *ᵥ (lifted_basis 0 - lifted_basis 2) = (1 - x 1) • u := by
        rw [Matrix.mulVec_sub, hcol0, hcol2]
        ext j
        simp [one_sub_mul]
      rw [hcolDiff2]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hone_sub_nonneg
    · have hx0_sq : x 0 * x 0 = x 0 := by
        rcases hx01 with hx0 | hx0 <;> simp [hx0]
      simpa [Y, u, Matrix.vecMulVec, homogenized_point] using hx0_sq
    · have hx1_sq : x 1 * x 1 = x 1 := by
        rcases hx11 with hx1 | hx1 <;> simp [hx1]
      have hu0 : u 0 = 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) 0 = 1
        rw [Fin.cons_zero]
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      calc
        Y 2 2 = u 2 * u 2 := by simp [Y, Matrix.vecMulVec]
        _ = x 1 * x 1 := by rfl
        _ = x 1 := hx1_sq
        _ = x 1 * 1 := by ring
        _ = u 2 * u 0 := by simp [hu0, hu2]
        _ = Y 2 0 := by simp [Y, Matrix.vecMulVec]
  · simpa [u] using hcol0

/-- Helper for Exercise 10.10: the convex hull of the mixed `0,1` feasible set lies in the mixed
`N₊` relaxation. -/
lemma convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) :
    convexHull ℝ (mixed_zero_one_linear_set A b) ⊆
      mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) := by
  -- Every mixed binary feasible point already has a PSD rank-one witness, and `N₊` is convex.
  refine convexHull_min ?_
    (convex_mixedZeroOneLovaszSchrijverNPlus (mixed_zero_one_polyhedron A b))
  intro x hx
  exact mem_mixedZeroOneLovaszSchrijverNPlus_of_mem_mixedZeroOneLinearSet hx

/-- Helper for Exercise 10.10: every mixed `N` point already belongs to the underlying polyhedron
because the first lifted column is a homogenized cone point over a convex owner. -/
lemma mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b)) :
    x ∈ mixed_zero_one_polyhedron A b := by
  -- Read the first lifted column as `homogenized_point x` and collapse the convex hull.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨-, hcone0, -, -, -, -, -, -⟩
  have hcone0' : homogenized_point x ∈ homogenized_cone (mixed_zero_one_polyhedron A b) := by
    simpa [hcol0] using hcone0
  have hxHull : x ∈ convexHull ℝ (mixed_zero_one_polyhedron A b) := by
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone
      (mixed_zero_one_polyhedron A b) hcone0'
  rwa [convexHull_eq_self.2 (convex_mixedZeroOnePolyhedron A b)] at hxHull

/-- Helper for Exercise 10.10: a mixed `N` point satisfies the polyhedron inequalities and the
source box bounds on the two binary coordinates. -/
lemma firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b)) :
    0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  -- Combine polyhedron membership from the first lifted column with the external box hypothesis.
  have hxP : x ∈ mixed_zero_one_polyhedron A b :=
    mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
  have hxBox : x 0 ≤ 1 ∧ x 1 ≤ 1 := hbox hxP
  rw [mem_mixed_zero_one_polyhedron_iff] at hxP
  exact ⟨hxP.2 0, hxBox.1, hxP.2 1, hxBox.2⟩

/-- Helper for Exercise 10.10: if the first binary coordinate is strictly between `0` and `1`,
the mixed witness splits `x` into normalized points on the first-coordinate faces `x 0 = 1` and
`x 0 = 0`. -/
lemma splitOnFirstBinaryCoordinateOfInterior
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    (Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ)
    (hY : IsMixedZeroOneLovaszSchrijverMatrix (mixed_zero_one_polyhedron A b) Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point x)
    (hx0_pos : 0 < x 0)
    (hx0_lt : x 0 < 1) :
    ∃ xOne xZero : Fin (p + 2) → ℝ,
      xOne ∈ mixed_zero_one_polyhedron A b ∧
        xOne 0 = 1 ∧
          xZero ∈ mixed_zero_one_polyhedron A b ∧
            xZero 0 = 0 ∧
              x 0 * xOne 1 = Y 1 2 ∧
                (1 - x 0) * xZero 1 = x 1 - Y 1 2 ∧
                  0 ≤ 1 - x 0 - x 1 + Y 1 2 ∧
                    0 ≤ x 0 - Y 1 2 ∧
                      0 ≤ x 1 - Y 1 2 ∧
                        0 ≤ Y 1 2 ∧
                          x = x 0 • xOne + (1 - x 0) • xZero := by
  -- Unpack the mixed witness and isolate the first-coordinate column and complementary column.
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, -, hcone1, -, hconeDiff1, -, hdiag1, -⟩
  have hY10 : Y 1 0 = x 0 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
  have hY20 : Y 2 0 = x 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
  have hY01_eq : Y 1 0 = Y 0 1 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
  have hY01 : Y 0 1 = x 0 := by
    calc
      Y 0 1 = Y 1 0 := hY01_eq.symm
      _ = x 0 := hY10
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hcol1_pos : 0 < (Y *ᵥ lifted_basis 1) 0 := by
    simpa [mulVec_lifted_basis, hY01] using hx0_pos
  obtain ⟨xOne, hxOneP, hcol1_eq⟩ :=
    normalizeMemOfMemHomogenizedCone (convex_mixedZeroOnePolyhedron A b) hcone1 hcol1_pos
  have hcol1_top : (Y *ᵥ lifted_basis 1) 0 = x 0 := by
    calc
      (Y *ᵥ lifted_basis 1) 0 = Y 0 1 := by simp [mulVec_lifted_basis]
      _ = x 0 := hY01
  have hcol1_eq' : Y *ᵥ lifted_basis 1 = x 0 • homogenized_point xOne := by
    simpa [hcol1_top] using hcol1_eq
  have hxOne0 : xOne 0 = 1 := by
    -- The first binary diagonal identity forces the normalized upper-face point onto `x 0 = 1`.
    have hcoord : x 0 = x 0 * xOne 0 := by
      calc
        x 0 = (Y *ᵥ lifted_basis 1) 1 := by
          simp [mulVec_lifted_basis, hdiag1, hY10]
        _ = (x 0 • homogenized_point xOne) 1 := by rw [hcol1_eq']
        _ = x 0 * xOne 0 := by simp [homogenized_point]
    nlinarith
  have hdiff1_pos : 0 < (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 := by
    -- The complementary lifted column has height `1 - x 0`, which is positive in the interior.
    have hcoord :
        (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 = 1 - x 0 := by
      simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01]
    rw [hcoord]
    linarith
  obtain ⟨xZero, hxZeroP, hdiff1_eq⟩ :=
    normalizeMemOfMemHomogenizedCone
      (convex_mixedZeroOnePolyhedron A b) hconeDiff1 hdiff1_pos
  have hdiff1_top : (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 = 1 - x 0 := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01]
  have hdiff1_eq' :
      Y *ᵥ (lifted_basis 0 - lifted_basis 1) = (1 - x 0) • homogenized_point xZero := by
    simpa [hdiff1_top] using hdiff1_eq
  have hxZero0 : xZero 0 = 0 := by
    -- The complementary first-face column has vanishing first binary coordinate after
    -- normalization.
    have hcoord :
        (1 - x 0) * xZero 0 = 0 := by
      calc
        (1 - x 0) * xZero 0 = ((1 - x 0) • homogenized_point xZero) 1 := by
          simp [homogenized_point]
        _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 1 := by rw [hdiff1_eq']
        _ = Y 1 0 - Y 1 1 := by
          simp [Matrix.mulVec_sub, mulVec_lifted_basis]
        _ = 0 := by rw [hdiag1, sub_self]
    nlinarith
  have hY21_eq : Y 2 1 = Y 1 2 := by
    -- Symmetry identifies the cross moment seen in the first conditioned column.
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 1) 2
  have hxOne1 : x 0 * xOne 1 = Y 1 2 := by
    -- The second coordinate of the upper-face column is the cross moment.
    have hhom2 : homogenized_point xOne 2 = xOne 1 := by rfl
    calc
      x 0 * xOne 1 = (x 0 • homogenized_point xOne) 2 := by
        simp [hhom2]
      _ = (Y *ᵥ lifted_basis 1) 2 := by rw [← hcol1_eq']
      _ = Y 2 1 := by simp [mulVec_lifted_basis]
      _ = Y 1 2 := hY21_eq
  have hxZero1 : (1 - x 0) * xZero 1 = x 1 - Y 1 2 := by
    -- The complementary column records the remaining second-coordinate moment.
    have hhom2 : homogenized_point xZero 2 = xZero 1 := by rfl
    calc
      (1 - x 0) * xZero 1 = ((1 - x 0) • homogenized_point xZero) 2 := by
        simp [hhom2]
      _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 2 := by rw [← hdiff1_eq']
      _ = Y 2 0 - Y 2 1 := by simp [Matrix.mulVec_sub, mulVec_lifted_basis]
      _ = x 1 - Y 1 2 := by rw [hY20, hY21_eq]
  have hxOne1_bounds := (hbox hxOneP).2
  have hxZero1_bounds := (hbox hxZeroP).2
  have hw00 : 0 ≤ 1 - x 0 - x 1 + Y 1 2 := by
    -- Rewrite the lower-face weight as a product of two nonnegative factors.
    calc
      1 - x 0 - x 1 + Y 1 2 = (1 - x 0) * (1 - xZero 1) := by
        nlinarith [hxZero1]
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr (le_of_lt hx0_lt)) (sub_nonneg.mpr hxZero1_bounds)
  have hw10 : 0 ≤ x 0 - Y 1 2 := by
    -- Rewrite the other upper-face weight using its normalized second coordinate.
    calc
      x 0 - Y 1 2 = x 0 * (1 - xOne 1) := by
        rw [← hxOne1]
        ring
      _ ≥ 0 := mul_nonneg (le_of_lt hx0_pos) (sub_nonneg.mpr hxOne1_bounds)
  have hw01 : 0 ≤ x 1 - Y 1 2 := by
    rw [← hxZero1]
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt hx0_lt)) (hxZeroP.2 1)
  have hw11 : 0 ≤ Y 1 2 := by
    rw [← hxOne1]
    exact mul_nonneg (le_of_lt hx0_pos) (hxOneP.2 1)
  -- Reassemble the original point from the two normalized face columns.
  have hhom :
      homogenized_point x =
        x 0 • homogenized_point xOne + (1 - x 0) • homogenized_point xZero := by
    calc
      homogenized_point x = Y *ᵥ lifted_basis 0 := hcol0.symm
      _ = Y *ᵥ lifted_basis 1 + Y *ᵥ (lifted_basis 0 - lifted_basis 1) := by
        rw [Matrix.mulVec_sub]
        ext j
        simp [Pi.add_apply, sub_eq_add_neg]
      _ = x 0 • homogenized_point xOne + (1 - x 0) • homogenized_point xZero := by
        rw [hcol1_eq', hdiff1_eq']
  have htail :
      x = x 0 • xOne + (1 - x 0) • xZero := by
    have := congrArg (fun y : Fin (p + 3) → ℝ => fun j : Fin (p + 2) ↦ y j.succ) hhom
    simpa [homogenized_point] using this
  exact ⟨xOne, xZero, hxOneP, hxOne0, hxZeroP, hxZero0, hxOne1, hxZero1,
    hw00, hw10, hw01, hw11, htail⟩

/-- Helper for Exercise 10.10: once the first distinguished coordinate is already binary, the
mixed witness only needs a second-coordinate split to land in the mixed binary convex hull. -/
lemma binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b))
    (hx0_binary : x 0 = 0 ∨ x 0 = 1) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hx_bounds := firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN hbox hx
  rcases hx_bounds with ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_one⟩
  by_cases hx1_zero : x 1 = 0
  · -- If the second coordinate is already `0`, the point is itself mixed binary feasible.
    have hxP : x ∈ mixed_zero_one_polyhedron A b :=
      mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
    exact subset_convexHull ℝ (mixed_zero_one_linear_set A b) <|
      (mem_mixed_zero_one_linear_set_iff).2 ⟨hxP, hx0_binary, Or.inl hx1_zero⟩
  by_cases hx1_one : x 1 = 1
  · -- If the second coordinate is already `1`, the point is itself mixed binary feasible.
    have hxP : x ∈ mixed_zero_one_polyhedron A b :=
      mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
    exact subset_convexHull ℝ (mixed_zero_one_linear_set A b) <|
      (mem_mixed_zero_one_linear_set_iff).2 ⟨hxP, hx0_binary, Or.inr hx1_one⟩
  · -- Otherwise normalize the second lifted column and its complement into the two binary faces.
    have hx1_pos : 0 < x 1 := by
      exact lt_of_le_of_ne hx1_nonneg (Ne.symm hx1_zero)
    have hx1_lt : x 1 < 1 := by
      exact lt_of_le_of_ne hx1_le_one hx1_one
    rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
    rcases hx with ⟨Y, hY, hcol0⟩
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
    rcases hY with ⟨hYsymm, -, hcone1, hcone2, hconeDiff1, hconeDiff2, hdiag1, hdiag2⟩
    have hY10 : Y 1 0 = x 0 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
    have hY20 : Y 2 0 = x 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
    have hY01_eq : Y 1 0 = Y 0 1 := by
      simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
    have hY01 : Y 0 1 = x 0 := by
      calc
        Y 0 1 = Y 1 0 := hY01_eq.symm
        _ = x 0 := hY10
    have hY00 : Y 0 0 = 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
    have hY02_eq : Y 2 0 = Y 0 2 := by
      simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 2
    have hY02 : Y 0 2 = x 1 := by
      calc
        Y 0 2 = Y 2 0 := hY02_eq.symm
        _ = x 1 := hY20
    have hcol2_top : (Y *ᵥ lifted_basis 2) 0 = x 1 := by
      calc
        (Y *ᵥ lifted_basis 2) 0 = Y 0 2 := by simp [mulVec_lifted_basis]
        _ = x 1 := hY02
    obtain ⟨xOne, hxOneP, hcol2_eq⟩ :=
      normalizeMemOfMemHomogenizedCone
        (convex_mixedZeroOnePolyhedron A b) hcone2 (by simpa [hcol2_top] using hx1_pos)
    have hcol2_eq' : Y *ᵥ lifted_basis 2 = x 1 • homogenized_point xOne := by
      simpa [hcol2_top] using hcol2_eq
    have hdiff2_top : (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 = 1 - x 1 := by
      simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY02]
    obtain ⟨xZero, hxZeroP, hdiff2_eq⟩ :=
      normalizeMemOfMemHomogenizedCone
        (convex_mixedZeroOnePolyhedron A b) hconeDiff2
        (by simpa [hdiff2_top] using sub_pos.mpr hx1_lt)
    have hdiff2_eq' :
        Y *ᵥ (lifted_basis 0 - lifted_basis 2) = (1 - x 1) • homogenized_point xZero := by
      simpa [hdiff2_top] using hdiff2_eq
    have hY12_mul : Y 1 2 = x 0 * x 1 := by
      rcases hx0_binary with hx0 | hx0
      · -- If `x 0 = 0`, the first lifted column has zero height and vanishes.
        have hcol1_zero : Y *ᵥ lifted_basis 1 = 0 := by
          apply eq_zero_of_memHomogenizedCone_of_top_zero hcone1
          simp [mulVec_lifted_basis, hY01, hx0]
        have hY21_zero : Y 2 1 = 0 := by
          simpa [mulVec_lifted_basis] using congr_fun hcol1_zero 2
        have hY12_zero : Y 1 2 = 0 := by
          calc
            Y 1 2 = Y 2 1 := by
              simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 1) 2).symm
            _ = 0 := hY21_zero
        simp [hx0, hY12_zero]
      · -- If `x 0 = 1`, the complementary first-face column has zero height and vanishes.
        have hdiff1_zero : Y *ᵥ (lifted_basis 0 - lifted_basis 1) = 0 := by
          apply eq_zero_of_memHomogenizedCone_of_top_zero hconeDiff1
          simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01, hx0]
        have hY21_eq : Y 2 1 = x 1 := by
          have hcoord : (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 2 = 0 := by
            simpa using congr_fun hdiff1_zero 2
          have : x 1 - Y 2 1 = 0 := by
            simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY20] using hcoord
          linarith
        have hY12_eq : Y 1 2 = x 1 := by
          calc
            Y 1 2 = Y 2 1 := by
              simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 1) 2).symm
            _ = x 1 := hY21_eq
        nlinarith
    have hxOne0_eq : xOne 0 = x 0 := by
      have hcoord :
          x 1 * xOne 0 = x 0 * x 1 := by
        calc
          x 1 * xOne 0 = (x 1 • homogenized_point xOne) 1 := by
            simp [homogenized_point]
          _ = (Y *ᵥ lifted_basis 2) 1 := by rw [← hcol2_eq']
          _ = Y 1 2 := by simp [mulVec_lifted_basis]
          _ = x 0 * x 1 := hY12_mul
      nlinarith
    have hxOne1 : xOne 1 = 1 := by
      have hcoord :
          x 1 = x 1 * homogenized_point xOne 2 := by
        calc
          x 1 = (Y *ᵥ lifted_basis 2) 2 := by
            simp [mulVec_lifted_basis, hdiag2, hY20]
          _ = (x 1 • homogenized_point xOne) 2 := by rw [hcol2_eq']
          _ = x 1 * homogenized_point xOne 2 := by simp
      have hhom2 : homogenized_point xOne 2 = xOne 1 := by
        rfl
      rw [hhom2] at hcoord
      nlinarith
    have hxZero0_eq : xZero 0 = x 0 := by
      have hcoord :
          (1 - x 1) * xZero 0 = x 0 * (1 - x 1) := by
        calc
          (1 - x 1) * xZero 0 = ((1 - x 1) • homogenized_point xZero) 1 := by
            simp [homogenized_point]
          _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 1 := by rw [← hdiff2_eq']
          _ = Y 1 0 - Y 1 2 := by
            simp [Matrix.mulVec_sub, mulVec_lifted_basis]
          _ = x 0 - x 0 * x 1 := by rw [hY10, hY12_mul]
          _ = x 0 * (1 - x 1) := by ring
      nlinarith
    have hxZero1 : xZero 1 = 0 := by
      have hcoord :
          (1 - x 1) * xZero 1 = 0 := by
        calc
          (1 - x 1) * xZero 1 = (1 - x 1) * homogenized_point xZero 2 := by
            rw [show homogenized_point xZero 2 = xZero 1 by rfl]
          _ = ((1 - x 1) • homogenized_point xZero) 2 := by simp
          _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 2 := by rw [← hdiff2_eq']
          _ = Y 2 0 - Y 2 2 := by
            simp [Matrix.mulVec_sub, mulVec_lifted_basis]
          _ = 0 := by rw [hdiag2, sub_self]
      nlinarith
    have hxOne_mem : xOne ∈ mixed_zero_one_linear_set A b := by
      refine (mem_mixed_zero_one_linear_set_iff).2 ?_
      refine ⟨hxOneP, ?_, ?_⟩
      · rcases hx0_binary with hx0 | hx0
        · left
          simpa [hx0] using hxOne0_eq
        · right
          simpa [hx0] using hxOne0_eq
      · exact Or.inr hxOne1
    have hxZero_mem : xZero ∈ mixed_zero_one_linear_set A b := by
      refine (mem_mixed_zero_one_linear_set_iff).2 ?_
      refine ⟨hxZeroP, ?_, ?_⟩
      · rcases hx0_binary with hx0 | hx0
        · left
          simpa [hx0] using hxZero0_eq
        · right
          simpa [hx0] using hxZero0_eq
      · exact Or.inl hxZero1
    have hhom :
        homogenized_point x =
          x 1 • homogenized_point xOne + (1 - x 1) • homogenized_point xZero := by
      calc
        homogenized_point x = Y *ᵥ lifted_basis 0 := hcol0.symm
        _ = Y *ᵥ lifted_basis 2 + Y *ᵥ (lifted_basis 0 - lifted_basis 2) := by
          rw [Matrix.mulVec_sub]
          ext j
          simp [Pi.add_apply, sub_eq_add_neg]
        _ = x 1 • homogenized_point xOne + (1 - x 1) • homogenized_point xZero := by
          rw [hcol2_eq', hdiff2_eq']
    have hx_lineMap : AffineMap.lineMap xZero xOne (x 1) = x := by
      ext j
      have hcoord := congr_fun hhom j.succ
      simpa [AffineMap.lineMap_apply_module, homogenized_point, add_comm, add_left_comm, add_assoc]
        using hcoord.symm
    have hx_segment : x ∈ segment ℝ xZero xOne := by
      rw [← hx_lineMap]
      exact lineMap_mem_segment ℝ xZero xOne ⟨hx1_nonneg, hx1_le_one⟩
    exact (segment_subset_convexHull hxZero_mem hxOne_mem) hx_segment

/-- Helper for Exercise 10.10: for a convex owner, every mixed `N` point already lies in that
owner because the first lifted column is a homogenized cone point over the owner's convex hull. -/
lemma mem_of_mem_mixedZeroOneLovaszSchrijverN
    {Q : Set (Fin (p + 2) → ℝ)}
    (hQ_convex : Convex ℝ Q)
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N Q) :
    x ∈ Q := by
  -- Read the first lifted column as `homogenized_point x` and collapse the owner's convex hull.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨-, hcone0, -, -, -, -, -, -⟩
  have hcone0' : homogenized_point x ∈ homogenized_cone Q := by
    simpa [hcol0] using hcone0
  have hxHull : x ∈ convexHull ℝ Q := by
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone Q hcone0'
  rwa [convexHull_eq_self.2 hQ_convex] at hxHull

/-- Helper for Exercise 10.10: intersecting the polyhedron with a fixed first-coordinate face
preserves convexity. -/
lemma convex_mixedZeroOnePolyhedron_firstCoordinateFace
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (c : ℝ) :
    Convex ℝ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = c} := by
  intro x hx y hy a d ha hd had
  refine ⟨convex_mixedZeroOnePolyhedron A b hx.1 hy.1 ha hd had, ?_⟩
  -- The fixed first-coordinate equation is preserved because the coefficients sum to `1`.
  calc
    (a • x + d • y) 0 = a * x 0 + d * y 0 := by simp [Pi.smul_apply]
    _ = a * c + d * c := by rw [hx.2, hy.2]
    _ = (a + d) * c := by ring
    _ = c := by rw [had, one_mul]

/-- Helper for Exercise 10.10: a mixed `N` point on the upper first-coordinate face can be viewed
in the ambient owner and then closed by the already proved one-binary hull lemma. -/
lemma upperFirstFace_mem_convexHull_mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    {x : Fin (p + 2) → ℝ}
    (hx :
      x ∈ mixed_zero_one_lovasz_schrijver_N
        {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 1}) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hxAmbient : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) :=
    mixedZeroOneLovaszSchrijverN_mono (by intro u hu; exact hu.1) hx
  have hxFace :
      x ∈ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 1} :=
    mem_of_mem_mixedZeroOneLovaszSchrijverN
      (convex_mixedZeroOnePolyhedron_firstCoordinateFace A b 1) hx
  -- Transport the face witness to the ambient owner, then use the solved one-binary closure step.
  exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hxAmbient (Or.inr hxFace.2)

/-- Helper for Exercise 10.10: the same ambient transport closes the lower first-coordinate face. -/
lemma lowerFirstFace_mem_convexHull_mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    {x : Fin (p + 2) → ℝ}
    (hx :
      x ∈ mixed_zero_one_lovasz_schrijver_N
        {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 0}) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hxAmbient : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) :=
    mixedZeroOneLovaszSchrijverN_mono (by intro u hu; exact hu.1) hx
  have hxFace :
      x ∈ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 0} :=
    mem_of_mem_mixedZeroOneLovaszSchrijverN
      (convex_mixedZeroOnePolyhedron_firstCoordinateFace A b 0) hx
  -- The lower face has first binary coordinate `0`, so the same one-binary closure applies.
  exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hxAmbient (Or.inl hxFace.2)

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: the four weighted binary
atoms give a strictly positive quadratic form when some three atom weights are positive. -/
lemma weightedBinarySquares_pos
    {w00 w10 w01 w11 z0 z1 z2 : ℝ}
    (hw00 : 0 ≤ w00) (hw10 : 0 ≤ w10) (hw01 : 0 ≤ w01) (hw11 : 0 ≤ w11)
    (htriple :
      (0 < w00 ∧ 0 < w10 ∧ 0 < w01) ∨
        (0 < w00 ∧ 0 < w10 ∧ 0 < w11) ∨
          (0 < w00 ∧ 0 < w01 ∧ 0 < w11) ∨
            (0 < w10 ∧ 0 < w01 ∧ 0 < w11))
    (hz : z0 ≠ 0 ∨ z1 ≠ 0 ∨ z2 ≠ 0) :
    0 < w00 * z0 ^ 2 + w10 * (z0 + z1) ^ 2 +
      w01 * (z0 + z2) ^ 2 + w11 * (z0 + z1 + z2) ^ 2 := by
  have hterm00 : 0 ≤ w00 * z0 ^ 2 := mul_nonneg hw00 (sq_nonneg z0)
  have hterm10 : 0 ≤ w10 * (z0 + z1) ^ 2 := mul_nonneg hw10 (sq_nonneg (z0 + z1))
  have hterm01 : 0 ≤ w01 * (z0 + z2) ^ 2 := mul_nonneg hw01 (sq_nonneg (z0 + z2))
  have hterm11 : 0 ≤ w11 * (z0 + z1 + z2) ^ 2 :=
    mul_nonneg hw11 (sq_nonneg (z0 + z1 + z2))
  -- In each triple, the corresponding three binary atoms span all three coordinates.
  rcases htriple with htriple | htriple | htriple | htriple
  · rcases htriple with ⟨hw00_pos, hw10_pos, hw01_pos⟩
    by_cases hz0 : z0 = 0
    · by_cases hz1 : z1 = 0
      · have hz2 : z2 ≠ 0 := by tauto
        have hsum02 : z0 + z2 ≠ 0 := by simpa [hz0] using hz2
        have hpos : 0 < w01 * (z0 + z2) ^ 2 := by
          exact mul_pos hw01_pos (sq_pos_of_ne_zero hsum02)
        nlinarith
      · have hsum01 : z0 + z1 ≠ 0 := by simpa [hz0] using hz1
        have hpos : 0 < w10 * (z0 + z1) ^ 2 := by
          exact mul_pos hw10_pos (sq_pos_of_ne_zero hsum01)
        nlinarith
    · have hpos : 0 < w00 * z0 ^ 2 := mul_pos hw00_pos (sq_pos_of_ne_zero hz0)
      nlinarith
  · rcases htriple with ⟨hw00_pos, hw10_pos, hw11_pos⟩
    by_cases hz0 : z0 = 0
    · by_cases hz1 : z1 = 0
      · have hz2 : z2 ≠ 0 := by tauto
        have hsum012 : z0 + z1 + z2 ≠ 0 := by simpa [hz0, hz1] using hz2
        have hpos : 0 < w11 * (z0 + z1 + z2) ^ 2 := by
          exact mul_pos hw11_pos (sq_pos_of_ne_zero hsum012)
        nlinarith
      · have hsum01 : z0 + z1 ≠ 0 := by simpa [hz0] using hz1
        have hpos : 0 < w10 * (z0 + z1) ^ 2 := by
          exact mul_pos hw10_pos (sq_pos_of_ne_zero hsum01)
        nlinarith
    · have hpos : 0 < w00 * z0 ^ 2 := mul_pos hw00_pos (sq_pos_of_ne_zero hz0)
      nlinarith
  · rcases htriple with ⟨hw00_pos, hw01_pos, hw11_pos⟩
    by_cases hz0 : z0 = 0
    · by_cases hz2 : z2 = 0
      · have hz1 : z1 ≠ 0 := by tauto
        have hsum012 : z0 + z1 + z2 ≠ 0 := by simpa [hz0, hz2] using hz1
        have hpos : 0 < w11 * (z0 + z1 + z2) ^ 2 := by
          exact mul_pos hw11_pos (sq_pos_of_ne_zero hsum012)
        nlinarith
      · have hsum02 : z0 + z2 ≠ 0 := by simpa [hz0] using hz2
        have hpos : 0 < w01 * (z0 + z2) ^ 2 := by
          exact mul_pos hw01_pos (sq_pos_of_ne_zero hsum02)
        nlinarith
    · have hpos : 0 < w00 * z0 ^ 2 := mul_pos hw00_pos (sq_pos_of_ne_zero hz0)
      nlinarith
  · rcases htriple with ⟨hw10_pos, hw01_pos, hw11_pos⟩
    by_cases hsum10 : z0 + z1 = 0
    · by_cases hsum01 : z0 + z2 = 0
      · have hsum11 : z0 + z1 + z2 ≠ 0 := by
          intro hzero
          have hz0_zero : z0 = 0 := by linarith
          have hz1_zero : z1 = 0 := by linarith
          have hz2_zero : z2 = 0 := by linarith
          rcases hz with hz0 | hz1 | hz2
          · exact hz0 hz0_zero
          · exact hz1 hz1_zero
          · exact hz2 hz2_zero
        have hpos : 0 < w11 * (z0 + z1 + z2) ^ 2 :=
          mul_pos hw11_pos (sq_pos_of_ne_zero hsum11)
        nlinarith
      · have hpos : 0 < w01 * (z0 + z2) ^ 2 :=
          mul_pos hw01_pos (sq_pos_of_ne_zero hsum01)
        nlinarith
    · have hpos : 0 < w10 * (z0 + z1) ^ 2 :=
        mul_pos hw10_pos (sq_pos_of_ne_zero hsum10)
      nlinarith

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: a binary two-variable
moment matrix is positive definite when three of its four atom weights are positive. -/
lemma mixedBinaryMomentMatrix_posDef
    {a b c : ℝ}
    (hw00 : 0 ≤ 1 - a - b + c) (hw10 : 0 ≤ a - c)
    (hw01 : 0 ≤ b - c) (hw11 : 0 ≤ c)
    (htriple :
      (0 < 1 - a - b + c ∧ 0 < a - c ∧ 0 < b - c) ∨
        (0 < 1 - a - b + c ∧ 0 < a - c ∧ 0 < c) ∨
          (0 < 1 - a - b + c ∧ 0 < b - c ∧ 0 < c) ∨
            (0 < a - c ∧ 0 < b - c ∧ 0 < c)) :
    (!![1, a, b; a, a, c; b, c, b] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · -- The explicit moment matrix is symmetric.
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro z hz
    have hzcoords : z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 := by
      by_contra hcoords
      push Not at hcoords
      apply hz
      funext i
      fin_cases i
      · exact hcoords.1
      · exact hcoords.2.1
      · exact hcoords.2.2
    have hpositive := weightedBinarySquares_pos hw00 hw10 hw01 hw11 htriple hzcoords
    -- Expand the quadratic form into its four binary-atom squares.
    have hquadratic :
        star z ⬝ᵥ
            ((!![1, a, b; a, a, c; b, c, b] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ z) =
          (1 - a - b + c) * (z 0) ^ 2 + (a - c) * (z 0 + z 1) ^ 2 +
            (b - c) * (z 0 + z 2) ^ 2 + c * (z 0 + z 1 + z 2) ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    rw [hquadratic]
    exact hpositive

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: reindex the first three
homogeneous/binary coordinates ahead of the `p` continuous coordinates. -/
def firstThreeSumEquiv (p : ℕ) : Fin 3 ⊕ Fin p ≃ Fin (p + 3) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 3 p))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_10.lean: the left summand of
`firstThreeSumEquiv` preserves the numerical index of each leading coordinate. -/
lemma firstThreeSumEquiv_apply_inl (p : ℕ) (j : Fin 3) :
    firstThreeSumEquiv p (Sum.inl j) = Fin.castLE (Nat.le_add_left 3 p) j := by
  -- Both sides represent `j` in the enlarged coordinate type.
  apply Fin.ext
  rfl

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: extract the principal
moment block on the homogeneous coordinate and the two binary coordinates. -/
def firstTwoMomentBlock (Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (Y.submatrix (firstThreeSumEquiv p) (firstThreeSumEquiv p)).toBlocks₁₁

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: an interior mixed witness
either has a positive-definite leading moment block or yields a mixed-binary convex decomposition.
-/
lemma conditionOnFirstBinaryCoordinate
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {u : Fin (p + 2) → ℝ},
      u ∈ mixed_zero_one_polyhedron A b → u 0 ≤ 1 ∧ u 1 ≤ 1)
    (Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ)
    (hY : IsMixedZeroOneLovaszSchrijverMatrix (mixed_zero_one_polyhedron A b) Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point x)
    (hx0_pos : 0 < x 0)
    (hx0_lt : x 0 < 1) :
    (firstTwoMomentBlock Y).PosDef ∨
      x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) :=
    (mem_mixed_zero_one_lovasz_schrijver_N_iff).2 ⟨Y, hY, hcol0⟩
  obtain ⟨xOne, xZero, hxOneP, hxOne0, hxZeroP, hxZero0, hxOne1, hxZero1,
      hw00, hw10, hw01, hw11, hsplit⟩ :=
    splitOnFirstBinaryCoordinateOfInterior hbox Y hY hcol0 hx0_pos hx0_lt
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, -, -, -, -, -, hdiag1, hdiag2⟩
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hY10 : Y 1 0 = x 0 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
  have hY20 : Y 2 0 = x 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
  have hY01 : Y 0 1 = x 0 := by
    calc
      Y 0 1 = Y 1 0 := by
        simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 0) 1).symm
      _ = x 0 := hY10
  have hY02 : Y 0 2 = x 1 := by
    calc
      Y 0 2 = Y 2 0 := by
        simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 0) 2).symm
      _ = x 1 := hY20
  have hY21 : Y 2 1 = Y 1 2 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 1) 2
  have hblock :
      firstTwoMomentBlock Y =
        (!![1, x 0, x 1; x 0, x 0, Y 1 2; x 1, Y 1 2, x 1] :
          Matrix (Fin 3) (Fin 3) ℝ) := by
    -- Normalize all nine entries once; later arguments use only this stable moment form.
    ext i j
    fin_cases i <;> fin_cases j
    · simpa only [firstTwoMomentBlock, Matrix.toBlocks₁₁, Matrix.submatrix_apply] using hY00
    · convert hY01 using 1
    · convert hY02 using 1
    · convert hY10 using 1
    · calc
        firstTwoMomentBlock Y 1 1 = Y 1 1 := by
          congr 2
        _ = Y 1 0 := hdiag1
        _ = x 0 := hY10
    · congr 2
    · convert hY20 using 1
    · calc
        firstTwoMomentBlock Y 2 1 = Y 2 1 := by
          congr 2
        _ = Y 1 2 := hY21
    · calc
        firstTwoMomentBlock Y 2 2 = Y 2 2 := by
          congr 2
        _ = Y 2 0 := hdiag2
        _ = x 1 := hY20
  by_cases htriple :
      (0 < 1 - x 0 - x 1 + Y 1 2 ∧ 0 < x 0 - Y 1 2 ∧ 0 < x 1 - Y 1 2) ∨
        (0 < 1 - x 0 - x 1 + Y 1 2 ∧ 0 < x 0 - Y 1 2 ∧ 0 < Y 1 2) ∨
          (0 < 1 - x 0 - x 1 + Y 1 2 ∧ 0 < x 1 - Y 1 2 ∧ 0 < Y 1 2) ∨
            (0 < x 0 - Y 1 2 ∧ 0 < x 1 - Y 1 2 ∧ 0 < Y 1 2)
  · left
    rw [hblock]
    exact mixedBinaryMomentMatrix_posDef hw00 hw10 hw01 hw11 htriple
  · right
    have hUpperZero : x 0 - Y 1 2 = 0 ∨ Y 1 2 = 0 := by
      by_contra hzeros
      push Not at hzeros
      have hw10_pos : 0 < x 0 - Y 1 2 := lt_of_le_of_ne hw10 (Ne.symm hzeros.1)
      have hw11_pos : 0 < Y 1 2 := lt_of_le_of_ne hw11 (Ne.symm hzeros.2)
      by_cases hw00_zero : 1 - x 0 - x 1 + Y 1 2 = 0
      · have hw01_pos : 0 < x 1 - Y 1 2 := by nlinarith
        exact htriple (Or.inr (Or.inr (Or.inr ⟨hw10_pos, hw01_pos, hw11_pos⟩)))
      · have hw00_pos : 0 < 1 - x 0 - x 1 + Y 1 2 :=
          lt_of_le_of_ne hw00 (Ne.symm hw00_zero)
        exact htriple (Or.inr (Or.inl ⟨hw00_pos, hw10_pos, hw11_pos⟩))
    have hLowerZero : 1 - x 0 - x 1 + Y 1 2 = 0 ∨ x 1 - Y 1 2 = 0 := by
      by_contra hzeros
      push Not at hzeros
      have hw00_pos : 0 < 1 - x 0 - x 1 + Y 1 2 :=
        lt_of_le_of_ne hw00 (Ne.symm hzeros.1)
      have hw01_pos : 0 < x 1 - Y 1 2 := lt_of_le_of_ne hw01 (Ne.symm hzeros.2)
      by_cases hw10_zero : x 0 - Y 1 2 = 0
      · have hw11_pos : 0 < Y 1 2 := by nlinarith
        exact htriple (Or.inr (Or.inr (Or.inl ⟨hw00_pos, hw01_pos, hw11_pos⟩)))
      · have hw10_pos : 0 < x 0 - Y 1 2 := lt_of_le_of_ne hw10 (Ne.symm hw10_zero)
        exact htriple (Or.inl ⟨hw00_pos, hw10_pos, hw01_pos⟩)
    have hxOne1_binary : xOne 1 = 0 ∨ xOne 1 = 1 := by
      rcases hUpperZero with hUpperZero | hUpperZero
      · right
        nlinarith
      · left
        nlinarith
    have hxZero1_binary : xZero 1 = 0 ∨ xZero 1 = 1 := by
      rcases hLowerZero with hLowerZero | hLowerZero
      · right
        nlinarith
      · left
        nlinarith
    have hxOne_mem : xOne ∈ mixed_zero_one_linear_set A b :=
      (mem_mixed_zero_one_linear_set_iff).2
        ⟨hxOneP, Or.inr hxOne0, hxOne1_binary⟩
    have hxZero_mem : xZero ∈ mixed_zero_one_linear_set A b :=
      (mem_mixed_zero_one_linear_set_iff).2
        ⟨hxZeroP, Or.inl hxZero0, hxZero1_binary⟩
    have hcomb :
        x 0 • xOne + (1 - x 0) • xZero ∈
          convexHull ℝ (mixed_zero_one_linear_set A b) := by
      -- Convexity now assembles the two genuinely mixed-binary conditioned points.
      refine (convex_convexHull ℝ (mixed_zero_one_linear_set A b))
        (subset_convexHull ℝ (mixed_zero_one_linear_set A b) hxOne_mem)
        (subset_convexHull ℝ (mixed_zero_one_linear_set A b) hxZero_mem)
        (le_of_lt hx0_pos) (sub_nonneg.mpr (le_of_lt hx0_lt)) ?_
      ring
    rwa [← hsplit] at hcomb

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: a symmetric partial
matrix with positive-definite leading block has a positive-semidefinite completion preserving its
leading block columns. -/
lemma exists_posSemidef_completion_of_posDef_toBlocks
    {ι κ : Type*} [Finite ι] [Finite κ]
    (W : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hWsymm : Wᵀ = W)
    (hApos : W.toBlocks₁₁.PosDef) :
    ∃ Z : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ,
      Z.PosSemidef ∧ ∀ i j, Z i (Sum.inl j) = W i (Sum.inl j) := by
  classical
  -- Local instance justification (finite index enumeration): block matrix multiplication needs
  -- explicit `Fintype` witnesses obtained canonically from the `Finite` assumptions.
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  let A : Matrix ι ι ℝ := W.toBlocks₁₁
  let B : Matrix ι κ ℝ := W.toBlocks₁₂
  have hAposLocal : A.PosDef := hApos
  -- Local instance justification (matrix inverse): the Schur-complement API requires the
  -- canonical inverse supplied by positive definiteness.
  letI : Invertible A := hAposLocal.isUnit.invertible
  let D : Matrix κ κ ℝ := Bᴴ * A⁻¹ * B
  let Z : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks A B Bᴴ D
  have hSchur : (D - Bᴴ * A⁻¹ * B).PosSemidef := by
    -- The chosen lower-right block makes the Schur complement identically zero.
    simpa [D] using (Matrix.PosSemidef.zero : (0 : Matrix κ κ ℝ).PosSemidef)
  have hZpsd : Z.PosSemidef := by
    -- Apply the block positive-semidefinite criterion to the zero Schur complement.
    exact (Matrix.PosDef.fromBlocks₁₁ B D hAposLocal).2 hSchur
  refine ⟨Z, hZpsd, ?_⟩
  intro i j
  rcases i with i | i
  · -- The upper block column is copied definitionally.
    rfl
  · -- Symmetry identifies the copied conjugate-transpose block with the old lower block.
    have hentry := congr_fun (congr_fun hWsymm (Sum.inl j)) (Sum.inr i)
    simpa [Z, B, Matrix.transpose_apply, Matrix.conjTranspose_apply] using hentry.symm

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: symmetry and equality of
the first three columns transport all mixed Lovasz-Schrijver matrix constraints. -/
lemma isMixedZeroOneLovaszSchrijverMatrix_of_firstThreeColumns
    {P : Set (Fin (p + 2) → ℝ)}
    {Y Z : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ}
    (hY : IsMixedZeroOneLovaszSchrijverMatrix P Y)
    (hZsymm : Zᵀ = Z)
    (hcol0 : ∀ i, Z i 0 = Y i 0)
    (hcol1 : ∀ i, Z i 1 = Y i 1)
    (hcol2 : ∀ i, Z i 2 = Y i 2) :
    IsMixedZeroOneLovaszSchrijverMatrix P Z := by
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY ⊢
  rcases hY with ⟨-, hcone0, hcone1, hcone2, hconeDiff1, hconeDiff2, hdiag1, hdiag2⟩
  have hmul0 : Z *ᵥ lifted_basis 0 = Y *ᵥ lifted_basis 0 := by
    -- A lifted basis vector reads exactly the corresponding matrix column.
    ext i
    simp [mulVec_lifted_basis, hcol0]
  have hmul1 : Z *ᵥ lifted_basis 1 = Y *ᵥ lifted_basis 1 := by
    ext i
    simp [mulVec_lifted_basis, hcol1]
  have hmul2 : Z *ᵥ lifted_basis 2 = Y *ᵥ lifted_basis 2 := by
    ext i
    simp [mulVec_lifted_basis, hcol2]
  refine ⟨hZsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hmul0]
  · rwa [hmul1]
  · rwa [hmul2]
  · simpa only [Matrix.mulVec_sub, hmul0, hmul1] using hconeDiff1
  · simpa only [Matrix.mulVec_sub, hmul0, hmul2] using hconeDiff2
  · calc
      Z 1 1 = Y 1 1 := hcol1 1
      _ = Y 1 0 := hdiag1
      _ = Z 1 0 := (hcol0 1).symm
  · calc
      Z 2 2 = Y 2 2 := hcol2 2
      _ = Y 2 0 := hdiag2
      _ = Z 2 0 := (hcol0 2).symm

/-- Helper for sorry cleanup existing repo ch10_sec10_6_exercise_10_10: every mixed linear
Lovasz-Schrijver point admits a positive-semidefinite mixed witness. -/
lemma mixedZeroOneLovaszSchrijverN_subset_mixedZeroOneLovaszSchrijverNPlus
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1) :
    mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) ⊆
      mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) := by
  intro x hx
  have hx_bounds := firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN hbox hx
  rcases hx_bounds with ⟨hx0_nonneg, hx0_le_one, -, -⟩
  by_cases hx0_zero : x 0 = 0
  · -- Endpoint points enter `N₊` through their mixed-binary convex hull certificate.
    exact convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus A b <|
      binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hx (Or.inl hx0_zero)
  by_cases hx0_one : x 0 = 1
  · exact convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus A b <|
      binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hx (Or.inr hx0_one)
  · have hx0_pos : 0 < x 0 := lt_of_le_of_ne hx0_nonneg (Ne.symm hx0_zero)
    have hx0_lt : x 0 < 1 := lt_of_le_of_ne hx0_le_one hx0_one
    rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
    rcases hx with ⟨Y, hY, hfirst⟩
    rcases conditionOnFirstBinaryCoordinate hbox Y hY hfirst hx0_pos hx0_lt with
      hleading | hxHull
    · -- In the nondegenerate branch, complete the witness after moving its first three indices
      -- into the leading block.
      let e : Fin 3 ⊕ Fin p ≃ Fin (p + 3) := firstThreeSumEquiv p
      let W : Matrix (Fin 3 ⊕ Fin p) (Fin 3 ⊕ Fin p) ℝ := Y.submatrix e e
      have hYsymm : Yᵀ = Y := (isMixedZeroOneLovaszSchrijverMatrix_iff.mp hY).1
      have hWsymm : Wᵀ = W := by
        ext i j
        have hentry := congr_fun (congr_fun hYsymm (e i)) (e j)
        simpa [W, Matrix.transpose_apply] using hentry
      have hWleading : W.toBlocks₁₁.PosDef := by
        simpa [W, e, firstTwoMomentBlock] using hleading
      obtain ⟨Z, hZpsd, hZcols⟩ :=
        exists_posSemidef_completion_of_posDef_toBlocks W hWsymm hWleading
      let Yplus : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ := Z.submatrix e.symm e.symm
      have hYplusPsd : Yplus.PosSemidef := by
        -- Reindexing a PSD completion back to the original coordinate order preserves PSD.
        exact hZpsd.submatrix e.symm
      have hcopied (i : Fin (p + 3)) (j : Fin 3) :
          Yplus i (e (Sum.inl j)) = Y i (e (Sum.inl j)) := by
        calc
          Yplus i (e (Sum.inl j)) = Z (e.symm i) (Sum.inl j) := by simp [Yplus]
          _ = W (e.symm i) (Sum.inl j) := hZcols (e.symm i) j
          _ = Y i (e (Sum.inl j)) := by simp [W]
      -- The computation rule for `e` turns the copied leading block into the three LS columns.
      have hcol0 (i : Fin (p + 3)) : Yplus i 0 = Y i 0 := by
        simpa [e, firstThreeSumEquiv_apply_inl] using hcopied i 0
      have hcol1 (i : Fin (p + 3)) : Yplus i 1 = Y i 1 := by
        simpa [e, firstThreeSumEquiv_apply_inl] using hcopied i 1
      have hcol2 (i : Fin (p + 3)) : Yplus i 2 = Y i 2 := by
        simpa [e, firstThreeSumEquiv_apply_inl] using hcopied i 2
      have hYplusSymm : Yplusᵀ = Yplus := by
        -- Over the reals, Hermitian symmetry from PSD is ordinary transpose symmetry.
        ext i j
        simpa [Matrix.transpose_apply] using hYplusPsd.1.apply i j
      have hYplus :
          IsMixedZeroOneLovaszSchrijverMatrix (mixed_zero_one_polyhedron A b) Yplus :=
        isMixedZeroOneLovaszSchrijverMatrix_of_firstThreeColumns
          hY hYplusSymm hcol0 hcol1 hcol2
      have hfirstPlus : Yplus *ᵥ lifted_basis 0 = homogenized_point x := by
        calc
          Yplus *ᵥ lifted_basis 0 = Y *ᵥ lifted_basis 0 := by
            ext i
            simp [mulVec_lifted_basis, hcol0]
          _ = homogenized_point x := hfirst
      exact (mem_mixed_zero_one_lovasz_schrijver_N_plus_iff).2
        ⟨Yplus, hYplus, hYplusPsd, hfirstPlus⟩
    · -- Degenerate leading moments give an actual mixed-binary convex decomposition.
      exact convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus A b hxHull

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_10.lean
Exercise 10.10. Let
`P = {x ∈ ℝ_+^(2 + p) | A x ≥ b}` and
`S = {x ∈ {0,1}^2 × ℝ_+^p | A x ≥ b}`. Assuming the first two coordinates of `P` are bounded
above by `1`, the mixed `0,1` semidefinite and linear one-step Lovasz-Schrijver operators
coincide. -/
theorem exercise_10_10_lovasz_schrijver_N_plus_eq_N
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1) :
    mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) =
      mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) := by
  refine Set.Subset.antisymm
    (mixed_zero_one_lovasz_schrijver_N_plus_subset_N (mixed_zero_one_polyhedron A b)) ?_
  -- Route correction: the old global convex-hull strengthening is false; condition on the first
  -- binary coordinate and use PSD completion precisely in the nondegenerate moment branch.
  exact mixedZeroOneLovaszSchrijverN_subset_mixedZeroOneLovaszSchrijverNPlus A b hbox

#print axioms exercise_10_10_lovasz_schrijver_N_plus_eq_N

end Exercise1010
