/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

open scoped BigOperators Matrix

-- This file keeps the source-facing mixed-integer set and valid `≥` inequality of Exercise 6.10,
-- while exposing the Chapter 5 `is_valid_inequality` formulation as a companion bridge.

section Exercise610

variable {m n : ℕ}

/-- The mixed-integer set `S = {x ∈ ℝ^n_+ | A x ≥ b} ∩ ℤ^n` from Exercise 6.10, recorded through
the Chapter 5 owner `mixed_integer_feasible_set` by rewriting `A x ≥ b` as `(-A) x ≤ -b`. -/
def exercise_6_10_mixed_integer_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  mixed_integer_feasible_set (-A) (-b) Finset.univ ∩ Set.Ici (0 : Fin n → ℝ)

/-- Membership in `exercise_6_10_mixed_integer_set A b` is exactly the source system
`A x ≥ b`, `x ≥ 0`, and integrality of every coordinate. -/
theorem mem_exercise_6_10_mixed_integer_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ exercise_6_10_mixed_integer_set A b ↔
      b ≤ A *ᵥ x ∧ 0 ≤ x ∧ ∀ j : Fin n, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [exercise_6_10_mixed_integer_set, Set.mem_inter_iff, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hx, hx_nonneg⟩
    refine ⟨?_, hx_nonneg, ?_⟩
    · intro i
      have hi : ((-A) *ᵥ x) i ≤ (-b) i := hx.1 i
      have hi' : -((A *ᵥ x) i) ≤ -(b i) := by
        simpa [Matrix.neg_mulVec] using hi
      simpa using neg_le_neg hi'
    · intro j
      simpa using hx.2 j (by simp)
  · rintro ⟨hAx, hx_nonneg, hx_int⟩
    refine ⟨?_, hx_nonneg⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hi : -((A *ᵥ x) i) ≤ -(b i) := neg_le_neg (hAx i)
      simpa [Matrix.neg_mulVec] using hi
    · intro j _
      exact hx_int j

/-- Helper for Exercise 6.10: a matrix-vector product over `ℝ` is the sum of the scaled columns of
the matrix. -/
lemma matrixMulVecEqSumCols
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    A *ᵥ x = ∑ j : Fin n, x j • A.col j := by
  -- Compare both sides coordinatewise and unfold the standard matrix multiplication formula.
  ext i
  simp [Matrix.mulVec_eq_sum, Matrix.col_apply, mul_comm]

/-- Helper for Exercise 6.10: subadditivity bounds the value on a natural scalar multiple by the
corresponding scalar multiple of the value. -/
lemma subadditiveLeNatSmul
    (g : (Fin m → ℝ) → ℝ)
    (hg_zero : g 0 = 0)
    (hg_subadditive : g.Subadditive)
    (r : Fin m → ℝ) :
    ∀ n : ℕ, g ((n : ℝ) • r) ≤ (n : ℝ) * g r
  | 0 => by
      simp [hg_zero]
  | n + 1 => by
      -- Split off one copy of `r` and apply the induction hypothesis to the remaining multiple.
      have hstep :
          g (((n + 1 : ℕ) : ℝ) • r) ≤ g ((n : ℝ) • r) + g r := by
        simpa [Nat.succ_eq_add_one, add_smul] using hg_subadditive ((n : ℝ) • r) r
      have hih := subadditiveLeNatSmul g hg_zero hg_subadditive r n
      calc
        g (((n + 1 : ℕ) : ℝ) • r) ≤ g ((n : ℝ) • r) + g r := hstep
        _ ≤ (n : ℝ) * g r + g r := by gcongr
        _ = ((n + 1 : ℕ) : ℝ) * g r := by
          norm_num [Nat.cast_add]
          ring

/-- Helper for Exercise 6.10: subadditivity bounds the value on a nonnegative integer scalar
multiple by the corresponding scalar multiple of the value. -/
lemma subadditiveLeIntSmul
    (g : (Fin m → ℝ) → ℝ)
    (hg_zero : g 0 = 0)
    (hg_subadditive : g.Subadditive)
    (r : Fin m → ℝ)
    {z : ℤ}
    (hz_nonneg : 0 ≤ z) :
    g ((z : ℝ) • r) ≤ (z : ℝ) * g r := by
  have hz_nat : ((Int.toNat z : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
  have hz_real : ((Int.toNat z : ℕ) : ℝ) = (z : ℝ) := by
    exact_mod_cast hz_nat
  -- Reduce the nonnegative integer coefficient to the natural-number case.
  simpa [hz_real] using
    subadditiveLeNatSmul g hg_zero hg_subadditive r (Int.toNat z)

/-- Helper for Exercise 6.10: subadditivity bounds the value on a nonnegative integral scalar
multiple by the corresponding scalar multiple of the value. -/
lemma subadditiveLeNonnegIntegralSmul
    (g : (Fin m → ℝ) → ℝ)
    (hg_zero : g 0 = 0)
    (hg_subadditive : g.Subadditive)
    {r : Fin m → ℝ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_int : ∃ z : ℤ, t = (z : ℝ)) :
    g (t • r) ≤ t * g r := by
  rcases ht_int with ⟨z, rfl⟩
  -- Convert the real nonnegativity hypothesis into the integer nonnegativity expected by the
  -- reusable integer-smul estimate from Section 6.3.
  have hz_nonneg : 0 ≤ z := by
    exact_mod_cast ht_nonneg
  simpa using
    subadditiveLeIntSmul g hg_zero hg_subadditive r hz_nonneg

/-- Helper for Exercise 6.10: the subadditive cut is already a valid inequality on the underlying
mixed-integer set before passing to the convex hull. -/
lemma subadditiveCutIsValidOnMixedIntegerSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (g : (Fin m → ℝ) → ℝ)
    (hg_mono : Monotone g)
    (hg_subadditive : g.Subadditive)
    (hg_zero : g 0 = 0) :
    is_valid_inequality
      (exercise_6_10_mixed_integer_set A b)
      (fun j ↦ -g (A.col j))
      (-g b) := by
  intro y hy
  rw [mem_exercise_6_10_mixed_integer_set_iff] at hy
  rcases hy with ⟨hAy, hy_nonneg, hy_int⟩
  have hg_zero_le : g 0 ≤ 0 := le_of_eq hg_zero
  have hcolumn_bound :
      ∀ j : Fin n, g (y j • A.col j) ≤ g (A.col j) * y j := by
    intro j
    -- Each coefficient is a nonnegative integer, so the one-column term is controlled by the
    -- integer-smul bound.
    have hterm :=
      subadditiveLeNonnegIntegralSmul g hg_zero hg_subadditive
        (r := A.col j)
        (t := y j)
        (ht_nonneg := hy_nonneg j)
        (ht_int := hy_int j)
    simpa [mul_comm] using hterm
  have hsum_bound :
      ∑ j : Fin n, g (y j • A.col j) ≤ ∑ j : Fin n, g (A.col j) * y j := by
    -- Sum the coordinatewise one-column bounds.
    exact Finset.sum_le_sum (fun j _ ↦ hcolumn_bound j)
  have hcut :
      g b ≤ ∑ j : Fin n, g (A.col j) * y j := by
    -- Normalize `A *ᵥ y` to a column sum, apply monotonicity, then use subadditivity and the
    -- coordinatewise integral-scaling bound.
    calc
      g b ≤ g (A *ᵥ y) := hg_mono hAy
      _ = g (∑ j : Fin n, y j • A.col j) := by
        rw [matrixMulVecEqSumCols]
      _ ≤ ∑ j : Fin n, g (y j • A.col j) := by
        simpa using
          (Finset.le_sum_of_subadditive
            g
            hg_zero_le
            hg_subadditive
            Finset.univ
            (fun j : Fin n ↦ y j • A.col j))
      _ ≤ ∑ j : Fin n, g (A.col j) * y j := hsum_bound
  -- Negating the source-facing inequality packages it into the Chapter 5 `is_valid_inequality`
  -- convention.
  simpa [dotProduct] using neg_le_neg hcut

/-- Exercise 6.10. Let `g : ℝ^m → ℝ` be nondecreasing and subadditive with `g 0 = 0`, and let
`S = {x ∈ ℝ^n_+ | A x ≥ b} ∩ ℤ^n`. Then the inequality
`∑ j, g(a^j) x_j ≥ g(b)` is valid for `conv(S)`, where `a^j` is the `j`th column of `A`. -/
theorem exercise_6_10_subadditive_cut_valid
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (g : (Fin m → ℝ) → ℝ)
    (hg_mono : Monotone g)
    (hg_subadditive : g.Subadditive)
    (hg_zero : g 0 = 0)
    (x : Fin n → ℝ)
    (hx : x ∈ convexHull ℝ (exercise_6_10_mixed_integer_set A b)) :
    g b ≤ ∑ j : Fin n, g (A.col j) * x j := by
  -- First move from the mixed-integer set to its convex hull using the Chapter 5 validity bridge.
  have hvalid :
      is_valid_inequality
        (convexHull ℝ (exercise_6_10_mixed_integer_set A b))
        (fun j ↦ -g (A.col j))
        (-g b) := by
    rw [is_valid_inequality_convexHull_iff]
    exact subadditiveCutIsValidOnMixedIntegerSet A b g hg_mono hg_subadditive hg_zero
  -- Then negate the Chapter 5 inequality to recover the source-facing `≥` form.
  simpa [dotProduct] using neg_le_neg (hvalid hx)

/-- The source-facing inequality of Exercise 6.10 is equivalently the Chapter 5 valid-inequality
owner obtained by negating both sides. -/
theorem exercise_6_10_subadditive_cut_is_valid_inequality
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (g : (Fin m → ℝ) → ℝ)
    (hg_mono : Monotone g)
    (hg_subadditive : g.Subadditive)
    (hg_zero : g 0 = 0) :
    is_valid_inequality
      (convexHull ℝ (exercise_6_10_mixed_integer_set A b))
      (fun j ↦ -g (A.col j))
      (-g b) := by
  intro x hx
  have h := exercise_6_10_subadditive_cut_valid A b g hg_mono hg_subadditive hg_zero x hx
  simpa [dotProduct] using neg_le_neg h

end Exercise610
