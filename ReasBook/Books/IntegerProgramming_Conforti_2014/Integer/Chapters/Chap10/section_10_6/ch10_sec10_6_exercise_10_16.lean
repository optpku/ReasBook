/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open Function
open scoped BigOperators
open scoped Matrix

-- Primary domain: Lovasz-Schrijver `N₊` iterates on convex sets in `ℝ^n`.
-- Owner abstractions reused here:
-- * `lovasz_schrijver_N_plus` from Section 10.3 for the one-step PSD lift-and-project operator
-- * `pure_integer_hull` from Chapter 5 for the canonical integer-hull owner
-- * `is_iterate_rank_of_polyhedron` from Chapter 5 for the generic iterate-rank owner
-- * `Function.iterate` for textbook iterates `N₊^k`

section Exercise1016

variable {n : ℕ}

/-- The polytope `P = {x ∈ [0,1]^n : ∑_j x_j ≥ 1 / 2}` from Exercise 10.16. -/
def exercise_10_16_polytope
    (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1) ∧ (1 / 2 : ℝ) ≤ ∑ i : Fin n, x i}

/-- Membership in `exercise_10_16_polytope n` is exactly the unit-cube condition together with
the inequality `1 / 2 ≤ ∑_j x_j`. -/
theorem mem_exercise_10_16_polytope_iff
    (n : ℕ)
    (x : Fin n → ℝ) :
    x ∈ exercise_10_16_polytope n ↔
      (∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1) ∧ (1 / 2 : ℝ) ≤ ∑ i : Fin n, x i := Iff.rfl

/-- The point `(1 / (2 n - k), ..., 1 / (2 n - k))` used in Exercise 10.16. -/
noncomputable def exercise_10_16_fractional_point
    (n k : ℕ) : Fin n → ℝ :=
  fun _ ↦ 1 / ((2 * n - k : ℕ) : ℝ)

/-- Every coordinate of `exercise_10_16_fractional_point n k` is `1 / (2 n - k)`. -/
theorem exercise_10_16_fractional_point_apply
    (n k : ℕ)
    (i : Fin n) :
    exercise_10_16_fractional_point n k i = 1 / ((2 * n - k : ℕ) : ℝ) := rfl

/-- The zeroth positive-semidefinite Lovasz-Schrijver iterate of the Exercise 10.16 polytope is
the polytope itself. -/
theorem exercise_10_16_positive_semidefinite_iterate_zero
    (n : ℕ) :
    (lovasz_schrijver_N_plus^[0]) (exercise_10_16_polytope n) = exercise_10_16_polytope n := by
  simp

/-- The successor positive-semidefinite Lovasz-Schrijver iterate is obtained by applying one more
`N₊` step. -/
theorem exercise_10_16_positive_semidefinite_iterate_succ
    (n k : ℕ) :
    (lovasz_schrijver_N_plus^[k + 1]) (exercise_10_16_polytope n) =
      lovasz_schrijver_N_plus ((lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n)) := by
  simp [Function.iterate_succ_apply']

/-- Helper for Exercise 10.16: the defining polytope is convex because both the unit-box
constraints and the lower-bound halfspace are convex. -/
lemma exercise_10_16_polytope_convex
    (n : ℕ) :
    Convex ℝ (exercise_10_16_polytope n) := by
  intro x hx y hy a b ha hb hab
  rw [mem_exercise_10_16_polytope_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · intro i
    rcases hx.1 i with ⟨hxi_nonneg, hxi_le⟩
    rcases hy.1 i with ⟨hyi_nonneg, hyi_le⟩
    refine ⟨by
      simp [Pi.add_apply, Pi.smul_apply, add_nonneg,
        mul_nonneg ha hxi_nonneg, mul_nonneg hb hyi_nonneg], ?_⟩
    calc
      (a • x + b • y) i = a * x i + b * y i := by simp [Pi.add_apply, Pi.smul_apply]
      _ ≤ a * 1 + b * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hxi_le ha)
          (mul_le_mul_of_nonneg_left hyi_le hb)
      _ = 1 := by nlinarith
  · calc
      (1 / 2 : ℝ) = a * (1 / 2 : ℝ) + b * (1 / 2 : ℝ) := by nlinarith
      _ ≤ a * ∑ i : Fin n, x i + b * ∑ i : Fin n, y i := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = ∑ i : Fin n, (a • x + b • y) i := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]

/-- Helper for Exercise 10.16: every `N₊` iterate of the Exercise 10.16 polytope stays convex. -/
lemma exercise_10_16_positiveSemidefiniteIterate_convex
    (n k : ℕ) :
    Convex ℝ ((lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n)) := by
  induction k with
  | zero =>
      simpa using exercise_10_16_polytope_convex n
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        convex_lovaszSchrijverNPlus ((lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n))

/-- Helper for Exercise 10.16: any known point of `Q` gives the zero vector in
`homogenized_cone Q` by taking scalar `0`. -/
lemma exercise_10_16_zero_mem_homogenizedCone_of_mem
    {Q : Set (Fin n → ℝ)}
    {x : Fin n → ℝ}
    (hx : x ∈ Q) :
    (0 : Fin (n + 1) → ℝ) ∈ homogenized_cone Q := by
  rw [mem_homogenized_cone_iff]
  refine ⟨0, le_rfl, x, subset_convexHull ℝ Q hx, ?_⟩
  simp

/-- Helper for Exercise 10.16: the singleton indicator of coordinate `i`. -/
def exercise_10_16_coordinateIndicator
    (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1

/-- The singleton indicator is `1` at its distinguished coordinate and `0` elsewhere. -/
theorem exercise_10_16_coordinateIndicator_apply
    (i j : Fin n) :
    exercise_10_16_coordinateIndicator i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [exercise_10_16_coordinateIndicator]
  · simp [exercise_10_16_coordinateIndicator, h]

/-- Helper for Exercise 10.16: every singleton indicator point is feasible for the source
polytope. -/
lemma exercise_10_16_coordinateIndicator_mem_polytope
    (i : Fin n) :
    exercise_10_16_coordinateIndicator i ∈ exercise_10_16_polytope n := by
  rw [mem_exercise_10_16_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst h
      simp [exercise_10_16_coordinateIndicator]
    · simp [exercise_10_16_coordinateIndicator, h]
  · calc
      (1 / 2 : ℝ) ≤ 1 := by norm_num
      _ = ∑ j : Fin n, exercise_10_16_coordinateIndicator i j := by
        simpa [exercise_10_16_coordinateIndicator] using
          (Finset.sum_ite_eq' i (fun _ ↦ (1 : ℝ))).symm

/-- Helper for Exercise 10.16: singleton indicator points stay in every positive-semidefinite
Lovasz-Schrijver iterate. -/
lemma exercise_10_16_coordinateIndicator_mem_positiveSemidefiniteIterate
    (i : Fin n)
    (k : ℕ) :
    exercise_10_16_coordinateIndicator i ∈
      (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n) := by
  induction k with
  | zero =>
      simpa using exercise_10_16_coordinateIndicator_mem_polytope (n := n) i
  | succ k ih =>
      -- Binary feasible points survive one more `N₊` step.
      simpa [Function.iterate_succ_apply'] using
        mem_lovaszSchrijverNPlus_of_mem_zeroOnePoints
          ((lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n))
          ((mem_zero_one_points_iff (Nat.le_refl n)
            ((lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n))
            (exercise_10_16_coordinateIndicator i)).2
            ⟨ih, by
              intro j
              by_cases h : j = i
              · subst h
                simp [exercise_10_16_coordinateIndicator]
              · simp [exercise_10_16_coordinateIndicator, h]⟩)

/-- Helper for Exercise 10.16: the denominator of the support-indexed sparse point. -/
def exercise_10_16_sparseDenominator
    (n : ℕ)
    (I : Finset (Fin n))
    (k : ℕ) : ℕ :=
  2 * n - k - 2 * I.card

/-- Helper for Exercise 10.16: the support-indexed sparse point used in the induction for part
`(i)`. Coordinates in `I` are forced to `0`, and the remaining coordinates all carry the same
value. -/
noncomputable def exercise_10_16_sparseFractionalPoint
    (n : ℕ)
    (I : Finset (Fin n))
    (k : ℕ) : Fin n → ℝ :=
  fun j ↦
    if j ∈ I then 0 else 1 / ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ)

/-- Coordinates inside the support set vanish on the sparse point. -/
theorem exercise_10_16_sparseFractionalPoint_apply_of_mem
    (I : Finset (Fin n))
    (k : ℕ)
    {j : Fin n}
    (hj : j ∈ I) :
    exercise_10_16_sparseFractionalPoint n I k j = 0 := by
  simp [exercise_10_16_sparseFractionalPoint, hj]

/-- Coordinates outside the support set are constant on the sparse point. -/
theorem exercise_10_16_sparseFractionalPoint_apply_of_not_mem
    (I : Finset (Fin n))
    (k : ℕ)
    {j : Fin n}
    (hj : j ∉ I) :
    exercise_10_16_sparseFractionalPoint n I k j =
      1 / ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
  simp [exercise_10_16_sparseFractionalPoint, hj]

/-- Helper for Exercise 10.16: the sparse denominator is positive whenever the support is not
all of `Fin n` and the iteration budget is feasible. -/
lemma exercise_10_16_sparseDenominator_pos
    (I : Finset (Fin n))
    (k : ℕ)
    (hIk : I.card + k ≤ n)
    (hIlt : I.card < n) :
    0 < exercise_10_16_sparseDenominator n I k := by
  dsimp [exercise_10_16_sparseDenominator]
  omega

/-- Helper for Exercise 10.16: every coordinate of a feasible sparse point is nonnegative. -/
lemma exercise_10_16_sparseFractionalPoint_nonneg
    (I : Finset (Fin n))
    (k : ℕ)
    (hIk : I.card + k ≤ n)
    (hIlt : I.card < n) :
    ∀ j : Fin n, 0 ≤ exercise_10_16_sparseFractionalPoint n I k j := by
  intro j
  -- Split on whether the coordinate is forced to zero by the support set.
  by_cases hj : j ∈ I
  · simpa [exercise_10_16_sparseFractionalPoint, hj]
  · have hden_pos_nat :=
      exercise_10_16_sparseDenominator_pos (n := n) I k hIk hIlt
    have hden_pos : 0 < ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
      exact_mod_cast hden_pos_nat
    rw [exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I k hj]
    positivity

/-- Helper for Exercise 10.16: the total weight of a sparse point is the expected cardinality
ratio. -/
lemma exercise_10_16_sparseFractionalPoint_sum
    (I : Finset (Fin n))
    (k : ℕ) :
    ∑ j : Fin n, exercise_10_16_sparseFractionalPoint n I k j =
      (((Finset.univ \ I).card : ℕ) : ℝ) /
        ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
  classical
  let c : ℝ := 1 / ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ)
  -- Convert the support-based definition into a sum over the complement of `I`.
  calc
    ∑ j : Fin n, exercise_10_16_sparseFractionalPoint n I k j
        = ∑ j : Fin n, if j ∉ I then c else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hji : j ∈ I
            · simp [exercise_10_16_sparseFractionalPoint, c, hji]
            · simp [exercise_10_16_sparseFractionalPoint, c, hji]
    _ = Finset.sum (Finset.univ.filter (fun j : Fin n ↦ j ∉ I)) (fun _ ↦ c) := by
          symm
          simpa using
            (Finset.sum_filter
              (s := Finset.univ)
              (p := fun j : Fin n ↦ j ∉ I)
              (f := fun _ ↦ c))
    _ = ((Finset.univ.filter (fun j : Fin n ↦ j ∉ I)).card : ℝ) * c := by
          simp
    _ = (((Finset.univ \ I).card : ℕ) : ℝ) /
          ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
          simp [c, Finset.sdiff_eq_filter, div_eq_mul_inv, mul_comm]

/-- Helper for Exercise 10.16: the total weight of the sparse point is at most `1` in every
inductive step where the denominator is positive. -/
lemma exercise_10_16_sparseFractionalPoint_sum_le_one
    (I : Finset (Fin n))
    (k : ℕ)
    (hIk : I.card + k ≤ n)
    (hIlt : I.card < n) :
    ∑ j : Fin n, exercise_10_16_sparseFractionalPoint n I k j ≤ 1 := by
  have hden_pos_nat :=
    exercise_10_16_sparseDenominator_pos (n := n) I k hIk hIlt
  have hden_pos : 0 < ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hcard_eq : (Finset.univ \ I).card = n - I.card := by
    simpa [Finset.compl_eq_univ_sdiff, Fintype.card_fin] using
      (Finset.card_compl I)
  have hnum_le_den_nat :
      (Finset.univ \ I).card ≤ exercise_10_16_sparseDenominator n I k := by
    rw [hcard_eq]
    dsimp [exercise_10_16_sparseDenominator]
    omega
  have hnum_le_den :
      (((Finset.univ \ I).card : ℕ) : ℝ) ≤
        ((exercise_10_16_sparseDenominator n I k : ℕ) : ℝ) := by
    exact_mod_cast hnum_le_den_nat
  rw [exercise_10_16_sparseFractionalPoint_sum]
  -- Cross-multiply against the positive denominator.
  refine (div_le_iff₀ hden_pos).2 ?_
  simpa using hnum_le_den

/-- Helper for Exercise 10.16: the base sparse points already lie in the original polytope. -/
lemma exercise_10_16_sparseFractionalPoint_mem_polytope
    (I : Finset (Fin n))
    (hIlt : I.card < n) :
    exercise_10_16_sparseFractionalPoint n I 0 ∈ exercise_10_16_polytope n := by
  have hIk : I.card + 0 ≤ n := by omega
  have hden_pos_nat :=
    exercise_10_16_sparseDenominator_pos (n := n) I 0 hIk hIlt
  have hden_pos : 0 < ((exercise_10_16_sparseDenominator n I 0 : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hden_ge_one : (1 : ℝ) ≤ ((exercise_10_16_sparseDenominator n I 0 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hden_pos_nat
  rw [mem_exercise_10_16_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨exercise_10_16_sparseFractionalPoint_nonneg (n := n) I 0 hIk hIlt j, ?_⟩
    by_cases hj : j ∈ I
    · simpa [exercise_10_16_sparseFractionalPoint, hj]
    · rw [exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I 0 hj]
      have hmul :=
        mul_le_mul_of_nonneg_right hden_ge_one
          (inv_nonneg.mpr (le_of_lt hden_pos))
      have hden_ne : ((exercise_10_16_sparseDenominator n I 0 : ℕ) : ℝ) ≠ 0 :=
        ne_of_gt hden_pos
      simpa [one_div, hden_ne] using hmul
  · have hcard_eq : (Finset.univ \ I).card = n - I.card := by
      simpa [Finset.compl_eq_univ_sdiff, Fintype.card_fin] using
        (Finset.card_compl I)
    have hden_eq_nat :
        exercise_10_16_sparseDenominator n I 0 = 2 * (Finset.univ \ I).card := by
      rw [hcard_eq]
      dsimp [exercise_10_16_sparseDenominator]
      omega
    have hcard_pos_nat : 0 < (Finset.univ \ I).card := by
      rw [hcard_eq]
      omega
    have hcard_pos : 0 < (((Finset.univ \ I).card : ℕ) : ℝ) := by
      exact_mod_cast hcard_pos_nat
    rw [exercise_10_16_sparseFractionalPoint_sum, hden_eq_nat]
    -- At `k = 0` the sparse-point sum is exactly `1 / 2`.
    have hhalf :
        (((Finset.univ \ I).card : ℕ) : ℝ) /
            (((2 * (Finset.univ \ I).card : ℕ) : ℕ) : ℝ) =
          (1 / 2 : ℝ) := by
      rw [Nat.cast_mul]
      field_simp [hcard_pos.ne']
      ring
    linarith [hhalf]

/-- Helper for Exercise 10.16: the homogenized lift preserves convex combinations. -/
lemma exercise_10_16_homogenizedPoint_convexCombination
    {a b : ℝ}
    {x y : Fin n → ℝ}
    (hab : a + b = 1) :
    homogenized_point (a • x + b • y) =
      a • homogenized_point x + b • homogenized_point y := by
  -- Compare the zeroth coordinate and the original coordinates separately.
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [homogenized_point, hab]
  · intro i
    simp [homogenized_point]

/-- Helper for Exercise 10.16: the singleton indicator lift is `e₀ + eᵢ`. -/
lemma exercise_10_16_homogenizedPoint_coordinateIndicator
    (i : Fin n) :
    homogenized_point (exercise_10_16_coordinateIndicator i) =
      lifted_basis 0 + lifted_basis i.succ := by
  -- The homogenized indicator has leading coordinate `1` and a single active original entry.
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [homogenized_point, lifted_basis]
  · intro k
    by_cases hki : k = i
    · subst hki
      simp [homogenized_point, exercise_10_16_coordinateIndicator, lifted_basis]
    · simp [homogenized_point, exercise_10_16_coordinateIndicator, lifted_basis, hki]

/-- Helper for Exercise 10.16: the PSD witness matrix used in the sparse-point induction is the
sum of one `e₀ e₀ᵀ` term and the rank-one terms attached to the active coordinates of `x`. -/
noncomputable def exercise_10_16_sparseWitnessMatrix
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun a b ↦
    Fin.cases
      (Fin.cases 1 (fun j ↦ x j) b)
      (fun i ↦ Fin.cases (x i) (fun j ↦ if i = j then x i else 0) b)
      a

/-- Helper for Exercise 10.16: the witness quadratic form is a weighted sum of squares. -/
lemma exercise_10_16_sparseWitnessMatrix_dotProduct_mulVec
    (x : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) :
    v ⬝ᵥ (exercise_10_16_sparseWitnessMatrix x *ᵥ v) =
      (1 - ∑ j : Fin n, x j) * (v 0)^2 +
        ∑ j : Fin n, x j * (v 0 + v j.succ)^2 := by
  -- Route correction: normalize the quadratic form directly instead of proving the
  -- unused entrywise rank-one decomposition of the witness matrix.
  rw [Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul, dotProduct, exercise_10_16_sparseWitnessMatrix]
  rw [Fin.sum_univ_succ]
  simp_rw [Fin.sum_univ_succ]
  simp
  -- Expand the zeroth-coordinate contribution of the quadratic form.
  have hZero :
      (v 0 + ∑ x_1, v x_1.succ * x x_1) * v 0 =
        v 0 ^ 2 + v 0 * ∑ x_1, v x_1.succ * x x_1 := by
    ring
  rw [hZero]
  -- Normalize each nonzero-coordinate contribution to a short polynomial shape.
  have hSucc :
      ∀ i : Fin n,
        (v 0 * x i + v i.succ * x i) * v i.succ =
          v 0 * x i * v i.succ + x i * v i.succ ^ 2 := by
    intro i
    ring
  simp_rw [hSucc]
  rw [Finset.mul_sum]
  -- Merge the two support sums before rewriting the target weighted-squares expression.
  have hCombine :
      (∑ i : Fin n, v 0 * (v i.succ * x i)) +
        ∑ i : Fin n, (v 0 * x i * v i.succ + x i * v i.succ ^ 2) =
      ∑ i : Fin n, (v 0 * (v i.succ * x i) + (v 0 * x i * v i.succ + x i * v i.succ ^ 2)) := by
    symm
    exact Finset.sum_add_distrib
  rw [show v 0 ^ 2 + ∑ i : Fin n, v 0 * (v i.succ * x i) +
          ∑ i : Fin n, (v 0 * x i * v i.succ + x i * v i.succ ^ 2) =
      v 0 ^ 2 + ((∑ i : Fin n, v 0 * (v i.succ * x i)) +
          ∑ i : Fin n, (v 0 * x i * v i.succ + x i * v i.succ ^ 2)) by ac_rfl]
  rw [hCombine]
  have hLeftTerm :
      ∀ i : Fin n,
        v 0 * (v i.succ * x i) + (v 0 * x i * v i.succ + x i * v i.succ ^ 2) =
          2 * v 0 * x i * v i.succ + x i * v i.succ ^ 2 := by
    intro i
    ring
  simp_rw [hLeftTerm]
  rw [sub_eq_add_neg, add_mul, one_mul, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  have hRightCombine :
      (∑ i : Fin n, -(x i * v 0 ^ 2)) +
        ∑ i : Fin n, x i * (v 0 + v i.succ) ^ 2 =
      ∑ i : Fin n, (-(x i * v 0 ^ 2) + x i * (v 0 + v i.succ) ^ 2) := by
    symm
    exact Finset.sum_add_distrib
  rw [show v 0 ^ 2 + ∑ i : Fin n, -(x i * v 0 ^ 2) +
          ∑ i : Fin n, x i * (v 0 + v i.succ) ^ 2 =
      v 0 ^ 2 + ((∑ i : Fin n, -(x i * v 0 ^ 2)) +
          ∑ i : Fin n, x i * (v 0 + v i.succ) ^ 2) by ac_rfl]
  rw [hRightCombine]
  have hTerm :
      (fun i : Fin n ↦ 2 * v 0 * x i * v i.succ + x i * v i.succ ^ 2) =
        fun i : Fin n ↦ -(x i * v 0 ^ 2) + x i * (v 0 + v i.succ) ^ 2 := by
    funext i
    ring
  simp [hTerm]

/-- Helper for Exercise 10.16: inserting a fresh support index lowers the sparse denominator by
exactly one. -/
lemma exercise_10_16_sparseDenominator_insert_succ
    (I : Finset (Fin n))
    (k : ℕ)
    {j : Fin n}
    (hIk : I.card + (k + 1) ≤ n)
    (hj : j ∉ I) :
    exercise_10_16_sparseDenominator n (insert j I) k + 1 =
      exercise_10_16_sparseDenominator n I (k + 1) := by
  -- Expand both denominators and use the fresh-index cardinality formula.
  dsimp [exercise_10_16_sparseDenominator]
  rw [Finset.card_insert_of_notMem hj]
  omega

/-- Helper for Exercise 10.16: adding a fresh support index rewrites the current sparse point as
the convex combination of the new coordinate indicator and the next sparse point. -/
lemma exercise_10_16_sparseFractionalPoint_step
    (I : Finset (Fin n))
    (k : ℕ)
    {j : Fin n}
    (hIk : I.card + (k + 1) ≤ n)
    (hj : j ∉ I) :
    exercise_10_16_sparseFractionalPoint n I (k + 1) =
      (1 / ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ)) •
          exercise_10_16_coordinateIndicator j +
        (1 - 1 / ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ)) •
          exercise_10_16_sparseFractionalPoint n (insert j I) k := by
  have hIk_insert : (insert j I).card + k ≤ n := by
    rw [Finset.card_insert_of_notMem hj]
    omega
  have hden_insert :=
    exercise_10_16_sparseDenominator_insert_succ (n := n) I k hIk hj
  -- Compare the coordinates inside `I`, at the fresh index `j`, and outside `insert j I`.
  ext t
  by_cases htj : t = j
  · subst htj
    rw [exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I (k + 1) hj]
    simp [Pi.add_apply, Pi.smul_apply, exercise_10_16_coordinateIndicator,
      exercise_10_16_sparseFractionalPoint]
  · by_cases htI : t ∈ I
    · have htInsert_mem : t ∈ insert j I := by
        simp [Finset.mem_insert, htI]
      have hcoord_zero : exercise_10_16_coordinateIndicator j t = 0 := by
        rw [exercise_10_16_coordinateIndicator_apply]
        simp [htj]
      rw [exercise_10_16_sparseFractionalPoint_apply_of_mem (n := n) I (k + 1) htI,
        Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hcoord_zero,
        exercise_10_16_sparseFractionalPoint_apply_of_mem (n := n) (insert j I) k htInsert_mem]
      simp
    · have htInsert : t ∉ insert j I := by
        simp [Finset.mem_insert, htj, htI]
      have hInsertLt : (insert j I).card < n := by
        simpa [Fintype.card_fin] using
          (Finset.card_lt_univ_of_notMem (s := insert j I) htInsert)
      have hIlt : I.card < n := by
        simpa [Fintype.card_fin] using
          (Finset.card_lt_univ_of_notMem (s := I) hj)
      have hden_insert_pos_nat :=
        exercise_10_16_sparseDenominator_pos (n := n) (insert j I) k hIk_insert hInsertLt
      have hden_pos_nat :=
        exercise_10_16_sparseDenominator_pos (n := n) I (k + 1) hIk hIlt
      have hden_insert_pos :
          0 < ((exercise_10_16_sparseDenominator n (insert j I) k : ℕ) : ℝ) := by
        exact_mod_cast hden_insert_pos_nat
      have hden_pos :
          0 < ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast hden_pos_nat
      have hden_insert_cast :
          (((exercise_10_16_sparseDenominator n (insert j I) k : ℕ) : ℝ) + 1) =
            ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast hden_insert
      have hcalc :
          (1 - 1 / ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ)) *
              (1 / ((exercise_10_16_sparseDenominator n (insert j I) k : ℕ) : ℝ)) =
            1 / ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) := by
        have hden_insert_ne :
            (((exercise_10_16_sparseDenominator n (insert j I) k : ℕ) : ℝ)) ≠ 0 :=
          ne_of_gt hden_insert_pos
        have hden_ne :
            (((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ)) ≠ 0 :=
          ne_of_gt hden_pos
        field_simp [hden_insert_cast, hden_insert_ne, hden_ne]
        linarith
      have hcoord_zero : exercise_10_16_coordinateIndicator j t = 0 := by
        rw [exercise_10_16_coordinateIndicator_apply]
        simp [htj]
      rw [exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I (k + 1) htI,
        Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hcoord_zero,
        exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) (insert j I) k htInsert]
      simpa [one_div] using hcalc.symm

/-- Helper for Exercise 10.16: the boundary sparse point at step `1` is exactly the fresh
coordinate indicator. -/
lemma exercise_10_16_sparseFractionalPoint_one_eq_coordinateIndicator_of_card_add_one_eq
    (I : Finset (Fin n))
    {j : Fin n}
    (hj : j ∉ I)
    (hboundary : I.card + 1 = n) :
    exercise_10_16_sparseFractionalPoint n I 1 =
      exercise_10_16_coordinateIndicator j := by
  have hInsert_eq_univ : insert j I = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [Fintype.card_fin, Finset.card_insert_of_notMem hj] using hboundary
  have hden_eq_one : exercise_10_16_sparseDenominator n I 1 = 1 := by
    dsimp [exercise_10_16_sparseDenominator]
    omega
  -- The boundary case leaves exactly the single fresh coordinate active.
  ext t
  by_cases htj : t = j
  · subst htj
    rw [exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I 1 hj]
    simp [exercise_10_16_coordinateIndicator, hden_eq_one]
  · have htI : t ∈ I := by
      have htInsert : t ∈ insert j I := by
        simpa [hInsert_eq_univ]
      simpa [Finset.mem_insert, htj] using htInsert
    rw [exercise_10_16_sparseFractionalPoint_apply_of_mem (n := n) I 1 htI,
      exercise_10_16_coordinateIndicator_apply]
    simp [htj]

/-- Helper for Exercise 10.16: the witness matrix is symmetric. -/
lemma exercise_10_16_sparseWitnessMatrix_transpose
    (x : Fin n → ℝ) :
    (exercise_10_16_sparseWitnessMatrix x)ᵀ =
      exercise_10_16_sparseWitnessMatrix x := by
  -- The explicit witness matrix is symmetric entrywise.
  ext a b
  refine Fin.cases ?_ ?_ a
  · refine Fin.cases ?_ ?_ b
    · simp [exercise_10_16_sparseWitnessMatrix]
    · intro j
      simp [exercise_10_16_sparseWitnessMatrix]
  · intro i
    refine Fin.cases ?_ ?_ b
    · simp [exercise_10_16_sparseWitnessMatrix]
    · intro j
      by_cases hij : i = j
      · subst hij
        simp [exercise_10_16_sparseWitnessMatrix]
      · simp [exercise_10_16_sparseWitnessMatrix, hij, ne_comm.mp hij]

/-- Helper for Exercise 10.16: the first lifted column of the witness is the homogenized point. -/
lemma exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_zero
    (x : Fin n → ℝ) :
    exercise_10_16_sparseWitnessMatrix x *ᵥ lifted_basis 0 = homogenized_point x := by
  -- Multiplication by `lifted_basis 0` extracts the first column.
  rw [mulVec_lifted_basis]
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [exercise_10_16_sparseWitnessMatrix, homogenized_point]
  · intro i
    simp [exercise_10_16_sparseWitnessMatrix, homogenized_point]

/-- Helper for Exercise 10.16: the `j`th lifted column is the scaled singleton lift
`x j • (1, e_j)`. -/
lemma exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_succ
    (x : Fin n → ℝ)
    (j : Fin n) :
    exercise_10_16_sparseWitnessMatrix x *ᵥ lifted_basis j.succ =
      x j • homogenized_point (exercise_10_16_coordinateIndicator j) := by
  -- Multiplication by `lifted_basis j.succ` extracts the `j`th data column.
  rw [mulVec_lifted_basis]
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [exercise_10_16_sparseWitnessMatrix, homogenized_point,
      exercise_10_16_coordinateIndicator]
  · intro k
    by_cases hkj : k = j
    · subst hkj
      simp [exercise_10_16_sparseWitnessMatrix, homogenized_point,
        exercise_10_16_coordinateIndicator]
    · simp [exercise_10_16_sparseWitnessMatrix, homogenized_point,
        exercise_10_16_coordinateIndicator, hkj]

/-- Helper for Exercise 10.16: every difference column of the sparse witness is the first
homogenized column minus the corresponding scaled singleton lift. -/
lemma exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_diff
    (x : Fin n → ℝ)
    (i : Fin n) :
    exercise_10_16_sparseWitnessMatrix x *ᵥ (lifted_basis 0 - lifted_basis i.succ) =
      homogenized_point x - x i • homogenized_point (exercise_10_16_coordinateIndicator i) := by
  -- Normalize difference columns through the already computed zero and successor columns.
  rw [Matrix.mulVec_sub, exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_zero,
    exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_succ]

/-- Helper for Exercise 10.16: each diagonal entry of the witness matches the corresponding
first-column entry. -/
lemma exercise_10_16_sparseWitnessMatrix_diag_eq_firstColumn
    (x : Fin n → ℝ)
    (j : Fin n) :
    exercise_10_16_sparseWitnessMatrix x j.succ j.succ =
      exercise_10_16_sparseWitnessMatrix x j.succ 0 := by
  -- Both entries are the same coordinate weight by definition.
  simp [exercise_10_16_sparseWitnessMatrix]

/-- Helper for Exercise 10.16: the sparse witness matrix is positive semidefinite as soon as the
weights of `x` are nonnegative and sum to at most `1`. -/
lemma exercise_10_16_sparseWitnessMatrix_posSemidef
    {x : Fin n → ℝ}
    (hx_nonneg : ∀ j : Fin n, 0 ≤ x j)
    (hx_sum_le_one : ∑ j : Fin n, x j ≤ 1) :
    (exercise_10_16_sparseWitnessMatrix x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Over `ℝ`, the explicit transpose symmetry is exactly the Hermitian condition.
    simpa using exercise_10_16_sparseWitnessMatrix_transpose x
  · intro v
    -- The quadratic-form normal form turns the PSD check into termwise nonnegativity.
    have hv :
        star v ⬝ᵥ (exercise_10_16_sparseWitnessMatrix x *ᵥ v) =
          (1 - ∑ j : Fin n, x j) * (v 0)^2 +
            ∑ j : Fin n, x j * (v 0 + v j.succ)^2 := by
      simpa using exercise_10_16_sparseWitnessMatrix_dotProduct_mulVec x v
    rw [hv]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (sub_nonneg.mpr hx_sum_le_one) (sq_nonneg (v 0))
    · refine Finset.sum_nonneg ?_
      intro j hj
      exact mul_nonneg (hx_nonneg j) (sq_nonneg (v 0 + v j.succ))

/-- Helper for Exercise 10.16: the support-indexed sparse points belong to the matching
positive-semidefinite Lovasz-Schrijver iterate. -/
lemma exercise_10_16_sparseFractionalPoint_mem_positiveSemidefiniteIterate
    (I : Finset (Fin n))
    (k : ℕ)
    (hIk : I.card + k ≤ n)
    (hIlt : I.card < n) :
    exercise_10_16_sparseFractionalPoint n I k ∈
      (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n) := by
  classical
  induction k generalizing I with
  | zero =>
      -- Base case: the sparse point is already feasible for the original polytope.
      simpa using exercise_10_16_sparseFractionalPoint_mem_polytope (n := n) I hIlt
  | succ k ih =>
      let Q : Set (Fin n → ℝ) := (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n)
      let x : Fin n → ℝ := exercise_10_16_sparseFractionalPoint n I (k + 1)
      have hcard_eq : (Finset.univ \ I).card = n - I.card := by
        simpa [Finset.compl_eq_univ_sdiff, Fintype.card_fin] using (Finset.card_compl I)
      have hcompl_pos : 0 < (Finset.univ \ I).card := by
        rw [hcard_eq]
        omega
      obtain ⟨j, hjmem⟩ := Finset.card_pos.mp hcompl_pos
      have hj : j ∉ I := (Finset.mem_sdiff.mp hjmem).2
      by_cases hboundary : I.card + 1 = n
      · have hk_zero : k = 0 := by
          omega
        have hx_eq : x = exercise_10_16_coordinateIndicator j := by
          simpa [x, hk_zero] using
            exercise_10_16_sparseFractionalPoint_one_eq_coordinateIndicator_of_card_add_one_eq
              (n := n) I hj hboundary
        -- Route correction: when `insert j I = univ`, the successor step collapses to the
        -- already solved singleton-indicator case instead of transporting through `insert j I`.
        simpa [x, hx_eq] using
          exercise_10_16_coordinateIndicator_mem_positiveSemidefiniteIterate (n := n) j (k + 1)
      · have hinterior : I.card + 1 < n := by
          omega
        have hQconvex : Convex ℝ Q := by
          simpa [Q] using exercise_10_16_positiveSemidefiniteIterate_convex n k
        have hden_pos_nat :=
          exercise_10_16_sparseDenominator_pos (n := n) I (k + 1) hIk hIlt
        have hden_pos :
            0 < ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) := by
          exact_mod_cast hden_pos_nat
        let c : ℝ := 1 / ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ)
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          exact one_div_nonneg.mpr (le_of_lt hden_pos)
        have hden_ge_one :
            (1 : ℝ) ≤ ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hden_pos_nat
        have hc_le_one : c ≤ 1 := by
          have hmul :=
            mul_le_mul_of_nonneg_right hden_ge_one
              (inv_nonneg.mpr (le_of_lt hden_pos))
          have hden_ne :
              ((exercise_10_16_sparseDenominator n I (k + 1) : ℕ) : ℝ) ≠ 0 :=
            ne_of_gt hden_pos
          dsimp [c] at *
          simpa [one_div, hden_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
        have hone_sub_nonneg : 0 ≤ 1 - c := by
          linarith
        have hInsert_card : (insert j I).card + k ≤ n := by
          rw [Finset.card_insert_of_notMem hj]
          omega
        have hInsert_lt : (insert j I).card < n := by
          rw [Finset.card_insert_of_notMem hj]
          omega
        have hstep_j :
            x =
              c • exercise_10_16_coordinateIndicator j +
                (1 - c) • exercise_10_16_sparseFractionalPoint n (insert j I) k := by
          simpa [x, c] using
            exercise_10_16_sparseFractionalPoint_step (n := n) I k hIk hj
        have hcoord_j : exercise_10_16_coordinateIndicator j ∈ Q := by
          simpa [Q] using
            exercise_10_16_coordinateIndicator_mem_positiveSemidefiniteIterate (n := n) j k
        have hinsert_mem : exercise_10_16_sparseFractionalPoint n (insert j I) k ∈ Q := by
          simpa [Q] using ih (I := insert j I) hInsert_card hInsert_lt
        have hx_mem : x ∈ Q := by
          -- The interior sparse point is a convex combination of two points already in `Q`.
          rw [hstep_j]
          exact hQconvex hcoord_j hinsert_mem hc_nonneg hone_sub_nonneg (by ring)
        have hx_nonneg : ∀ i : Fin n, 0 ≤ x i := by
          simpa [x] using exercise_10_16_sparseFractionalPoint_nonneg (n := n) I (k + 1) hIk hIlt
        have hx_sum_le_one : ∑ i : Fin n, x i ≤ 1 := by
          simpa [x] using
            exercise_10_16_sparseFractionalPoint_sum_le_one (n := n) I (k + 1) hIk hIlt
        have hcone0 : homogenized_point x ∈ homogenized_cone Q := by
          exact homogenized_point_mem_homogenized_cone Q (subset_convexHull ℝ Q hx_mem)
        rw [exercise_10_16_positive_semidefinite_iterate_succ]
        rw [mem_lovasz_schrijver_N_plus_iff]
        refine ⟨exercise_10_16_sparseWitnessMatrix x, ?_, ?_, ?_⟩
        · rw [isLovaszSchrijverMatrix_iff]
          refine ⟨exercise_10_16_sparseWitnessMatrix_transpose x, ?_, ?_, ?_⟩
          · rw [exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_zero]
            exact hcone0
          · intro i
            have hcoord_i : exercise_10_16_coordinateIndicator i ∈ Q := by
              simpa [Q] using
                exercise_10_16_coordinateIndicator_mem_positiveSemidefiniteIterate (n := n) i k
            have hcone_coord_i :
                homogenized_point (exercise_10_16_coordinateIndicator i) ∈ homogenized_cone Q := by
              exact homogenized_point_mem_homogenized_cone Q
                (subset_convexHull ℝ Q hcoord_i)
            refine ⟨?_, ?_⟩
            · rw [exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_succ]
              exact homogenizedCone_nonneg_smul_mem Q hcone_coord_i (hx_nonneg i)
            · by_cases hiI : i ∈ I
              · have hxi_zero : x i = 0 := by
                  simpa [x] using
                    exercise_10_16_sparseFractionalPoint_apply_of_mem (n := n) I (k + 1) hiI
                rw [exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_diff, hxi_zero]
                simpa [hxi_zero] using hcone0
              · have hInsert_i_card : (insert i I).card + k ≤ n := by
                  rw [Finset.card_insert_of_notMem hiI]
                  omega
                have hInsert_i_lt : (insert i I).card < n := by
                  rw [Finset.card_insert_of_notMem hiI]
                  omega
                have hinsert_i_mem :
                    exercise_10_16_sparseFractionalPoint n (insert i I) k ∈ Q := by
                  simpa [Q] using ih (I := insert i I) hInsert_i_card hInsert_i_lt
                have hcone_insert_i :
                    homogenized_point (exercise_10_16_sparseFractionalPoint n (insert i I) k) ∈
                      homogenized_cone Q := by
                  exact homogenized_point_mem_homogenized_cone Q
                    (subset_convexHull ℝ Q hinsert_i_mem)
                have hxi_eq_c : x i = c := by
                  simpa [x, c] using
                    exercise_10_16_sparseFractionalPoint_apply_of_not_mem (n := n) I (k + 1) hiI
                have hstep_i :
                    x =
                      c • exercise_10_16_coordinateIndicator i +
                        (1 - c) • exercise_10_16_sparseFractionalPoint n (insert i I) k := by
                  simpa [x, c] using
                    exercise_10_16_sparseFractionalPoint_step (n := n) I k hIk hiI
                have hdiff_i :
                    homogenized_point x - x i •
                        homogenized_point (exercise_10_16_coordinateIndicator i) =
                      (1 - c) •
                        homogenized_point (exercise_10_16_sparseFractionalPoint n (insert i I) k) := by
                  rw [hxi_eq_c, hstep_i,
                    exercise_10_16_homogenizedPoint_convexCombination (by ring)]
                  ext m <;> simp [Pi.add_apply, Pi.smul_apply]
                rw [exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_diff, hdiff_i]
                exact homogenizedCone_nonneg_smul_mem Q hcone_insert_i hone_sub_nonneg
          · intro i
            exact exercise_10_16_sparseWitnessMatrix_diag_eq_firstColumn x i
        · exact exercise_10_16_sparseWitnessMatrix_posSemidef hx_nonneg hx_sum_le_one
        · exact exercise_10_16_sparseWitnessMatrix_mul_liftedBasis_zero x

/-- Helper for Exercise 10.16: every pure-integer-hull point satisfies the inequality
`1 ≤ ∑ i, x i`. -/
lemma exercise_10_16_sumGeOneOfMemPureIntegerHull
    (n : ℕ)
    {x : Fin n → ℝ}
    (hx : x ∈ pure_integer_hull (exercise_10_16_polytope n)) :
    1 ≤ ∑ i : Fin n, x i := by
  rw [pure_integer_hull] at hx
  have hhalfspace :
      convexHull ℝ (pure_integer_points (exercise_10_16_polytope n)) ⊆
        {y : Fin n → ℝ | 1 ≤ ∑ i : Fin n, y i} := by
    refine convexHull_min ?_ ?_
    · intro y hy
      rw [mem_pure_integer_points_iff_forall] at hy
      rw [mem_exercise_10_16_polytope_iff] at hy
      rcases hy with ⟨hyP, hyInt⟩
      -- The sum is an integer and already lies above `1 / 2`, hence it is at least `1`.
      choose z hz using hyInt
      have hsum_int :
          ∃ t : ℤ, ∑ i : Fin n, y i = (t : ℝ) := by
        refine ⟨∑ i : Fin n, z i, ?_⟩
        calc
          ∑ i : Fin n, y i = ∑ i : Fin n, ((z i : ℤ) : ℝ) := by simp [hz]
          _ = ((∑ i : Fin n, z i : ℤ) : ℝ) := by simp
      rcases hsum_int with ⟨t, ht⟩
      have ht_ge_one : (1 : ℤ) ≤ t := by
        have ht_half : (1 / 2 : ℝ) ≤ (t : ℝ) := by simpa [ht] using hyP.2
        by_contra ht_lt_one
        have ht_le_zero : t ≤ 0 := by omega
        have ht_le_zero_real : (t : ℝ) ≤ 0 := by
          exact_mod_cast ht_le_zero
        linarith
      have ht_ge_one_real : (1 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast ht_ge_one
      simpa [ht] using ht_ge_one_real
    · intro y hy z hz a b ha hb hab
      -- The halfspace `{y | 1 ≤ ∑ i, y i}` is convex.
      dsimp at hy hz ⊢
      have hcomb : 1 ≤ a * ∑ i : Fin n, y i + b * ∑ i : Fin n, z i := by
        nlinarith
      simpa [Pi.smul_apply, Pi.add_apply, Finset.mul_sum, Finset.sum_add_distrib] using hcomb
  exact hhalfspace hx

/-- Helper for Exercise 10.16: the textbook fractional point has total sum strictly less than
`1` whenever `k < n`. -/
lemma exercise_10_16_fractionalPointSumLtOne
    (n k : ℕ)
    (hk : k < n) :
    ∑ i : Fin n, exercise_10_16_fractional_point n k i < 1 := by
  have hden_pos_nat : 0 < 2 * n - k := by omega
  have hden_pos : 0 < ((2 * n - k : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hnum_lt_den : (n : ℝ) < ((2 * n - k : ℕ) : ℝ) := by
    exact_mod_cast (show n < 2 * n - k by omega)
  calc
    ∑ i : Fin n, exercise_10_16_fractional_point n k i
        = (n : ℝ) / ((2 * n - k : ℕ) : ℝ) := by
            simp [exercise_10_16_fractional_point, Finset.sum_const, Fintype.card_fin,
              div_eq_mul_inv, mul_comm]
    _ < 1 := by
      refine (div_lt_iff₀ hden_pos).2 ?_
      simpa using hnum_lt_den

/-- Exercise 10.16 (1). For `0 < n` and `k ≤ n`, the point
`(1 / (2 n - k), ..., 1 / (2 n - k))` belongs to the `k`th positive-semidefinite
Lovasz-Schrijver iterate `N₊^k` of `P = {x ∈ [0,1]^n : ∑_j x_j ≥ 1 / 2}`. -/
theorem exercise_10_16_fractional_point_mem_positive_semidefinite_iterate
    (n k : ℕ)
    (hn : 0 < n)
    (hk : k ≤ n) :
    exercise_10_16_fractional_point n k ∈
      (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n) := by
  -- The textbook point is the empty-support specialization of the sparse induction.
  simpa [exercise_10_16_fractional_point, exercise_10_16_sparseFractionalPoint,
    exercise_10_16_sparseDenominator] using
    exercise_10_16_sparseFractionalPoint_mem_positiveSemidefiniteIterate
      (n := n) (I := ∅) k (by simpa using hk) (by simpa using hn)

/-- Exercise 10.16 (2). For `k < n`, the `k`th positive-semidefinite Lovasz-Schrijver iterate
`N₊^k` of the Exercise 10.16 polytope is not equal to its pure-integer hull `P_I`. -/
theorem exercise_10_16_positive_semidefinite_iterate_ne_pure_integer_hull
    (n k : ℕ)
    (hk : k < n) :
    (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n) ≠
      pure_integer_hull (exercise_10_16_polytope n) := by
  intro hEq
  have hn : 0 < n := by omega
  let x := exercise_10_16_fractional_point n k
  have hx_iter :
      x ∈ (lovasz_schrijver_N_plus^[k]) (exercise_10_16_polytope n) :=
    exercise_10_16_fractional_point_mem_positive_semidefinite_iterate n k hn (Nat.le_of_lt hk)
  have hx_hull : x ∈ pure_integer_hull (exercise_10_16_polytope n) := by
    simpa [x] using hEq ▸ hx_iter
  have hsum_ge : 1 ≤ ∑ i : Fin n, x i :=
    exercise_10_16_sumGeOneOfMemPureIntegerHull n hx_hull
  have hsum_lt : ∑ i : Fin n, x i < 1 :=
    exercise_10_16_fractionalPointSumLtOne n k hk
  linarith

/-- If `t` is an iteration index at which the positive-semidefinite Lovasz-Schrijver iterates of
the Exercise 10.16 polytope reach the pure-integer hull, then `n ≤ t`. This packages the
source lower bound through the generic iterate-rank owner. -/
theorem exercise_10_16_positive_semidefinite_rank_at_least
    {n t : ℕ}
    (ht : is_iterate_rank_of_polyhedron
      lovasz_schrijver_N_plus
      (exercise_10_16_polytope n) t) :
    n ≤ t := by
  by_contra hnt
  exact exercise_10_16_positive_semidefinite_iterate_ne_pure_integer_hull n t
    (Nat.lt_of_not_ge hnt) ht.eq_integer_hull

end Exercise1016
