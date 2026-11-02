import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped BigOperators Matrix

-- Primary domain: Lovasz-Schrijver `N₊` iterates for the Exercise 10.17 polytope.
-- Owner abstractions reused here:
-- * `lovasz_schrijver_N_plus` from Section 10.3 for the one-step PSD lift-and-project operator
-- * `zero_one_points` from Chapter 5 for the canonical `P ∩ {0,1}ⁿ` owner
-- * `Function.iterate` for the textbook iterates `N₊^k`

section Exercise1017

variable {n : ℕ}

/-- The polytope
`P = {x ∈ ℝ^n | ∑_{j ∈ J} x_j + ∑_{j ∉ J} (1 - x_j) ≥ 1 / 2 for all J ⊆ {1, …, n}}`
from Exercise 10.17, encoded by finite index sets `J : Finset (Fin n)`. -/
def exercise_10_17_polytope
    (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ J : Finset (Fin n),
      (1 / 2 : ℝ) ≤
        Finset.sum J (fun j ↦ x j) +
          Finset.sum (Finset.univ \ J) (fun j ↦ (1 - x j))}

/-- Membership in `exercise_10_17_polytope n` means satisfying the subset inequality for every
`J : Finset (Fin n)`. -/
theorem mem_exercise_10_17_polytope_iff
    (n : ℕ)
    (x : Fin n → ℝ) :
    x ∈ exercise_10_17_polytope n ↔
      ∀ J : Finset (Fin n),
        (1 / 2 : ℝ) ≤
          Finset.sum J (fun j ↦ x j) +
            Finset.sum (Finset.univ \ J) (fun j ↦ (1 - x j)) :=
  Iff.rfl

/-- The point `(1 / 2, …, 1 / 2)` in `ℝ^n`. -/
noncomputable def exercise_10_17_half_point
    (n : ℕ) : Fin n → ℝ :=
  fun _ ↦ 1 / 2

/-- Every coordinate of `exercise_10_17_half_point n` is `1 / 2`. -/
theorem exercise_10_17_half_point_apply
    (n : ℕ)
    (i : Fin n) :
    exercise_10_17_half_point n i = 1 / 2 :=
  rfl

/-- The zeroth positive-semidefinite Lovasz-Schrijver iterate of the Exercise 10.17 polytope is
the polytope itself. -/
theorem exercise_10_17_positive_semidefinite_iterate_zero
    (n : ℕ) :
    (lovasz_schrijver_N_plus^[0]) (exercise_10_17_polytope n) = exercise_10_17_polytope n := by
  simp

/-- The successor positive-semidefinite Lovasz-Schrijver iterate is obtained by applying one more
`N₊` step. -/
theorem exercise_10_17_positive_semidefinite_iterate_succ
    (n k : ℕ) :
    (lovasz_schrijver_N_plus^[k + 1]) (exercise_10_17_polytope n) =
      lovasz_schrijver_N_plus ((lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n)) := by
  simp [Function.iterate_succ_apply']

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the Bernoulli second-moment matrix of a point in the unit cube. -/
private def exercise_10_17_roundingWitnessMatrix
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.vecMulVec (homogenized_point x) (homogenized_point x) +
    Matrix.diagonal (Fin.cons 0 (fun i ↦ x i * (1 - x i)))

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the Bernoulli second-moment matrix is symmetric. -/
private lemma exercise_10_17_roundingWitnessMatrix_transpose
    (x : Fin n → ℝ) :
    (exercise_10_17_roundingWitnessMatrix x)ᵀ =
      exercise_10_17_roundingWitnessMatrix x := by
  -- Both the rank-one part and the diagonal correction are symmetric.
  ext i j
  by_cases hij : i = j
  · subst j
    simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec]
  · simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec,
      hij, Ne.symm hij, mul_comm]

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the first column of the Bernoulli second-moment matrix is the homogenized point. -/
private lemma exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_zero
    (x : Fin n → ℝ) :
    exercise_10_17_roundingWitnessMatrix x *ᵥ lifted_basis 0 =
      homogenized_point x := by
  -- Multiplication by the zeroth lifted basis vector exposes the zeroth column.
  rw [mulVec_lifted_basis]
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point]
  · intro j
    simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point]

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the coordinate column of the Bernoulli second-moment matrix is the scaled homogenized
one-update. -/
private lemma exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_succ
    (x : Fin n → ℝ)
    (i : Fin n) :
    exercise_10_17_roundingWitnessMatrix x *ᵥ lifted_basis i.succ =
      x i • homogenized_point (Function.update x i 1) := by
  -- The diagonal correction changes exactly the selected coordinate from `x i` to `1`.
  rw [mulVec_lifted_basis]
  ext j
  refine Fin.cases ?_ ?_ j
  · have hzero_ne : (0 : Fin (n + 1)) ≠ i.succ := by
      exact i.succ_ne_zero.symm
    simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point,
      Matrix.diagonal_apply_ne _ hzero_ne, Function.update_of_ne hzero_ne]
  · intro j
    by_cases hji : j = i
    · subst j
      simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point]
      ring
    · simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point, hji]
      ring

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the complementary coordinate column is the scaled homogenized zero-update. -/
private lemma exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_diff
    (x : Fin n → ℝ)
    (i : Fin n) :
    exercise_10_17_roundingWitnessMatrix x *ᵥ
        (lifted_basis 0 - lifted_basis i.succ) =
      (1 - x i) • homogenized_point (Function.update x i 0) := by
  -- Subtract the computed coordinate column from the first column and normalize pointwise.
  rw [Matrix.mulVec_sub,
    exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_zero,
    exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_succ]
  ext j
  refine Fin.cases ?_ ?_ j
  · have hzero_ne : (0 : Fin (n + 1)) ≠ i.succ := by
      exact i.succ_ne_zero.symm
    simp [homogenized_point, Function.update_of_ne hzero_ne]
  · intro j
    by_cases hji : j = i
    · subst j
      simp [homogenized_point]
    · simp [homogenized_point, hji]
      ring

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the diagonal of the Bernoulli second-moment matrix agrees with its first column. -/
private lemma exercise_10_17_roundingWitnessMatrix_diag_eq_firstColumn
    (x : Fin n → ℝ)
    (i : Fin n) :
    exercise_10_17_roundingWitnessMatrix x i.succ i.succ =
      exercise_10_17_roundingWitnessMatrix x i.succ 0 := by
  -- The correction turns the square `x i ^ 2` into `x i`.
  simp [exercise_10_17_roundingWitnessMatrix, Matrix.vecMulVec, homogenized_point]
  ring

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the Bernoulli second-moment matrix is positive semidefinite for points in the unit cube. -/
private lemma exercise_10_17_roundingWitnessMatrix_posSemidef
    (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (exercise_10_17_roundingWitnessMatrix x).PosSemidef := by
  -- The matrix is a positive rank-one matrix plus a nonnegative diagonal matrix.
  have hdiag :
      ∀ i : Fin (n + 1),
        0 ≤ ((Fin.cons (0 : ℝ) (fun j ↦ x j * (1 - x j)) : Fin (n + 1) → ℝ) i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact le_rfl
    · intro i
      exact mul_nonneg (hx i).1 (sub_nonneg.mpr (hx i).2)
  have hrank :
      (Matrix.vecMulVec (homogenized_point x) (homogenized_point x)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (homogenized_point x)
  exact Matrix.PosSemidef.add hrank (Matrix.PosSemidef.diagonal hdiag)

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean:
the Bernoulli second-moment matrix supplies an `N₊` witness whenever the point and its binary
coordinate updates lie in the preceding convex hull. -/
private lemma exercise_10_17_roundingWitnessMatrix_spec
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ)
    (hxBounds : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hxHull : x ∈ convexHull ℝ P)
    (hxZeroHull : ∀ i, Function.update x i 0 ∈ convexHull ℝ P)
    (hxOneHull : ∀ i, Function.update x i 1 ∈ convexHull ℝ P) :
    IsLovaszSchrijverMatrix P (exercise_10_17_roundingWitnessMatrix x) ∧
      (exercise_10_17_roundingWitnessMatrix x).PosSemidef ∧
      exercise_10_17_roundingWitnessMatrix x *ᵥ lifted_basis 0 =
        homogenized_point x := by
  -- Assemble the Lovasz-Schrijver column conditions from the stable matrix interface above.
  refine ⟨?_, exercise_10_17_roundingWitnessMatrix_posSemidef x hxBounds,
    exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_zero x⟩
  rw [isLovaszSchrijverMatrix_iff]
  refine ⟨exercise_10_17_roundingWitnessMatrix_transpose x, ?_, ?_, ?_⟩
  · rw [exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_zero]
    exact homogenized_point_mem_homogenized_cone P hxHull
  · intro i
    refine ⟨?_, ?_⟩
    · rw [exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_succ]
      exact homogenizedCone_nonneg_smul_mem P
        (homogenized_point_mem_homogenized_cone P (hxOneHull i)) (hxBounds i).1
    · rw [exercise_10_17_roundingWitnessMatrix_mul_liftedBasis_diff]
      exact homogenizedCone_nonneg_smul_mem P
        (homogenized_point_mem_homogenized_cone P (hxZeroHull i))
        (sub_nonneg.mpr (hxBounds i).2)
  · exact exercise_10_17_roundingWitnessMatrix_diag_eq_firstColumn x

/-- Helper for Exercise 10.17 local proof
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean: a ternary point with a
half-integral coordinate belongs to the Exercise 10.17 polytope. -/
private lemma exercise_10_17_mem_polytope_of_halfIntegral_of_exists_half
    (x : Fin n → ℝ)
    (hxValues : ∀ i, x i = 1 / 2 ∨ x i = 0 ∨ x i = 1)
    (hxHalf : ∃ i, x i = 1 / 2) :
    x ∈ exercise_10_17_polytope n := by
  -- Every ternary coordinate lies in the unit interval.
  have hxNonneg : ∀ i, 0 ≤ x i := by
    intro i
    rcases hxValues i with hi | hi | hi
    · rw [hi]
      norm_num
    · rw [hi]
    · rw [hi]
      norm_num
  have hxLeOne : ∀ i, x i ≤ 1 := by
    intro i
    rcases hxValues i with hi | hi | hi
    · rw [hi]
      norm_num
    · rw [hi]
      norm_num
    · rw [hi]
  obtain ⟨i, hiHalf⟩ := hxHalf
  rw [mem_exercise_10_17_polytope_iff]
  intro J
  have hleftNonneg : 0 ≤ Finset.sum J (fun j ↦ x j) :=
    Finset.sum_nonneg fun j _ ↦ hxNonneg j
  have hrightNonneg :
      0 ≤ Finset.sum (Finset.univ \ J) (fun j ↦ 1 - x j) :=
    Finset.sum_nonneg fun j _ ↦ sub_nonneg.mpr (hxLeOne j)
  by_cases hiJ : i ∈ J
  · -- If the half coordinate lies in `J`, it alone supplies the required lower bound.
    have hiLeLeft : x i ≤ Finset.sum J (fun j ↦ x j) :=
      Finset.single_le_sum (fun j _ ↦ hxNonneg j) hiJ
    linarith
  · -- Otherwise its complementary summand supplies the same lower bound.
    have hiCompl : i ∈ Finset.univ \ J := by
      simp [hiJ]
    have hiLeRight :
        1 - x i ≤ Finset.sum (Finset.univ \ J) (fun j ↦ 1 - x j) :=
      Finset.single_le_sum (fun j _ ↦ sub_nonneg.mpr (hxLeOne j)) hiCompl
    linarith

/-- Helper for Exercise 10.17 proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean: updating a coordinate to a
non-half value erases exactly that coordinate from the set of half coordinates. -/
private lemma exercise_10_17_halfCoordinateFilter_update_of_ne
    (x : Fin n → ℝ)
    (i : Fin n)
    (b : ℝ)
    (hb : b ≠ 1 / 2) :
    Finset.univ.filter (fun j ↦ Function.update x i b j = 1 / 2) =
      (Finset.univ.filter (fun j ↦ x j = 1 / 2)).erase i := by
  -- Compare membership pointwise, separating the updated coordinate from all others.
  ext j
  by_cases hji : j = i
  · subst j
    have hb' : b ≠ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using hb
    simp [hb']
  · simp [hji]

/-- Helper for Exercise 10.17 proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean: a ternary point survives
every `N₊` iterate strictly below its number of half coordinates. -/
private lemma exercise_10_17_halfIntegral_mem_positiveSemidefiniteIterate
    (k : ℕ)
    (x : Fin n → ℝ)
    (hxValues : ∀ i, x i = 1 / 2 ∨ x i = 0 ∨ x i = 1)
    (hk : k < (Finset.univ.filter (fun i ↦ x i = 1 / 2)).card) :
    x ∈ (lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n) := by
  induction k generalizing x with
  | zero =>
      -- A positive half-coordinate count gives the half coordinate needed by the base polytope.
      simp only [Function.iterate_zero_apply]
      have hcardPos : 0 < (Finset.univ.filter (fun i ↦ x i = 1 / 2)).card := hk
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardPos
      have hiHalf : x i = 1 / 2 := (Finset.mem_filter.mp hi).2
      have hxHalf : ∃ i, x i = 1 / 2 := Exists.intro i hiHalf
      exact exercise_10_17_mem_polytope_of_halfIntegral_of_exists_half x hxValues hxHalf
  | succ k ih =>
      let Q : Set (Fin n → ℝ) :=
        (lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n)
      have hxBounds : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
        intro i
        rcases hxValues i with hi | hi | hi
        · constructor
          · rw [hi]
            norm_num
          · rw [hi]
            norm_num
        · constructor
          · rw [hi]
          · rw [hi]
            norm_num
        · constructor
          · rw [hi]
            norm_num
          · rw [hi]
      have hupdateValues :
          ∀ i b, b = 0 ∨ b = 1 →
            ∀ j, Function.update x i b j = 1 / 2 ∨
              Function.update x i b j = 0 ∨ Function.update x i b j = 1 := by
        intro i b hb j
        by_cases hji : j = i
        · subst j
          rcases hb with rfl | rfl
          · simp
          · simp
        · simpa [hji] using hxValues j
      have hupdateCard :
          ∀ i b, b ≠ 1 / 2 →
            k < (Finset.univ.filter
              (fun j ↦ Function.update x i b j = 1 / 2)).card := by
        intro i b hb
        rw [exercise_10_17_halfCoordinateFilter_update_of_ne x i b hb]
        by_cases hiHalf : i ∈ Finset.univ.filter (fun j ↦ x j = 1 / 2)
        · rw [Finset.card_erase_of_mem hiHalf]
          omega
        · rw [Finset.erase_eq_of_notMem hiHalf]
          omega
      have hzeroNeHalf : (0 : ℝ) ≠ 1 / 2 := by
        norm_num
      have honeNeHalf : (1 : ℝ) ≠ 1 / 2 := by
        norm_num
      have hzeroMem : ∀ i, Function.update x i 0 ∈ Q := by
        intro i
        apply ih (Function.update x i 0)
        · exact hupdateValues i 0 (Or.inl rfl)
        · exact hupdateCard i 0 hzeroNeHalf
      have honeMem : ∀ i, Function.update x i 1 ∈ Q := by
        intro i
        apply ih (Function.update x i 1)
        · exact hupdateValues i 1 (Or.inr rfl)
        · exact hupdateCard i 1 honeNeHalf
      have hcardPos : 0 < (Finset.univ.filter (fun i ↦ x i = 1 / 2)).card := by
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardPos
      have hiHalf : x i = 1 / 2 := (Finset.mem_filter.mp hi).2
      have hzeroHull : ∀ j, Function.update x j 0 ∈ convexHull ℝ Q := by
        intro j
        exact subset_convexHull ℝ Q (hzeroMem j)
      have honeHull : ∀ j, Function.update x j 1 ∈ convexHull ℝ Q := by
        intro j
        exact subset_convexHull ℝ Q (honeMem j)
      have hcoeffNonneg : (0 : ℝ) ≤ 1 / 2 := by
        norm_num
      have hcoeffSum : (1 / 2 : ℝ) + 1 / 2 = 1 := by
        norm_num
      have hxMidpoint :
          (1 / 2 : ℝ) • Function.update x i 0 +
              (1 / 2 : ℝ) • Function.update x i 1 = x := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [hiHalf]
        · simp [hji]
          ring
      have hxHull : x ∈ convexHull ℝ Q := by
        have hmidpointMem :=
          (convex_convexHull ℝ Q) (hzeroHull i) (honeHull i)
            hcoeffNonneg hcoeffNonneg hcoeffSum
        rwa [hxMidpoint] at hmidpointMem
      -- The Bernoulli witness turns the predecessor updates into one `N₊` step.
      rw [Function.iterate_succ_apply']
      rw [mem_lovasz_schrijver_N_plus_iff]
      exact Exists.intro (exercise_10_17_roundingWitnessMatrix x)
        (exercise_10_17_roundingWitnessMatrix_spec Q x hxBounds hxHull hzeroHull honeHull)

/-- Helper for Exercise 10.17 proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean: the Exercise 10.17 polytope
has no binary points. -/
private lemma exercise_10_17_zeroOnePoints_eq_empty
    (n : ℕ) :
    zero_one_points (Nat.le_refl n) (exercise_10_17_polytope n) = ∅ := by
  -- A binary point violates the inequality indexed by precisely its zero coordinates.
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [mem_zero_one_points_iff] at hx
  rcases hx with ⟨hxPolytope, hxBinaryRaw⟩
  have hxBinary : ∀ i : Fin n, x i = 0 ∨ x i = 1 := by
    simpa using hxBinaryRaw
  let J : Finset (Fin n) := Finset.univ.filter (fun i ↦ x i = 0)
  have hineq := (mem_exercise_10_17_polytope_iff n x).1 hxPolytope J
  have hleft : Finset.sum J (fun j ↦ x j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hright : Finset.sum (Finset.univ \ J) (fun j ↦ 1 - x j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjNot : j ∉ J := (Finset.mem_sdiff.mp hj).2
    rcases hxBinary j with hjZero | hjOne
    · exfalso
      apply hjNot
      simp [J, hjZero]
    · simp [hjOne]
  rw [hleft, hright] at hineq
  norm_num at hineq

/-- Exercise 10.17 (1). For `n ≥ 2`, the point `(1 / 2, …, 1 / 2)` belongs to the
`(n - 1)`st positive-semidefinite Lovasz-Schrijver iterate `N₊^(n - 1)` of the Exercise 10.17
polytope. -/
theorem exercise_10_17_half_point_mem_positive_semidefinite_iterate
    (n : ℕ)
    (hn : 2 ≤ n) :
    exercise_10_17_half_point n ∈
      (lovasz_schrijver_N_plus^[n - 1]) (exercise_10_17_polytope n) := by
  -- All `n` coordinates are half-integral, so the rank invariant reaches step `n - 1`.
  apply exercise_10_17_halfIntegral_mem_positiveSemidefiniteIterate
  · intro i
    exact Or.inl (exercise_10_17_half_point_apply n i)
  · simp [exercise_10_17_half_point_apply]
    omega

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_17.lean
— Exercise 10.17 (2).
For `n ≥ 2` and every `k < n`, the `k`th positive-semidefinite Lovasz-Schrijver iterate `N₊^k`
of the Exercise 10.17 polytope is not the convex hull of `S = P ∩ {0,1}^n`. -/
theorem exercise_10_17_iterate_ne_zero_one_convexHull
    (n k : ℕ)
    (hn : 2 ≤ n)
    (hk : k < n) :
    (lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n) ≠
      convexHull ℝ (zero_one_points (Nat.le_refl n) (exercise_10_17_polytope n)) := by
  -- The half point remains on the left, whereas the binary set and its hull are empty.
  intro heq
  have hhalf :
      exercise_10_17_half_point n ∈
        (lovasz_schrijver_N_plus^[k]) (exercise_10_17_polytope n) := by
    by_cases hkLast : k = n - 1
    · rw [hkLast]
      exact exercise_10_17_half_point_mem_positive_semidefinite_iterate n hn
    · apply exercise_10_17_halfIntegral_mem_positiveSemidefiniteIterate
      · intro i
        exact Or.inl (exercise_10_17_half_point_apply n i)
      · simp [exercise_10_17_half_point_apply]
        omega
  rw [heq, exercise_10_17_zeroOnePoints_eq_empty, convexHull_empty] at hhalf
  exact hhalf

end Exercise1017
