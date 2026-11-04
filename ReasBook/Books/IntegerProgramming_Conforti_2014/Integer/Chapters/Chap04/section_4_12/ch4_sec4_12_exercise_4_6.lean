/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section Exercise46

variable {m n : ℕ}

/-- The set `S = {x ∈ ℤ_+^n | A x ≤ b}` from Exercise 4.6, viewed as a subset of `ℝ^n` via the
usual embedding of integer vectors into real vectors. -/
def fractional_rhs_integer_feasible_set
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  integerVectors n ∩ {x | (∀ j, 0 ≤ x j) ∧ ∀ i, ∑ j, (A i j : ℝ) * x j ≤ b i}

/-- Choosing the integer vector underlying a point of `integerVectors n` turns every row sum
`∑ j Aᵢⱼ xⱼ` into an integer. -/
lemma integerVectors_row_sum_eq_int_cast
    (A : Matrix (Fin m) (Fin n) ℤ) {x : Fin n → ℝ} (i : Fin m)
    (hx : x ∈ integerVectors n) :
    ∃ z : ℤ, ∑ j, (A i j : ℝ) * x j = (z : ℝ) := by
  rcases (mem_integerVectors_iff).1 hx with ⟨z, rfl⟩
  refine ⟨∑ j, A i j * z j, ?_⟩
  calc
    ∑ j, (A i j : ℝ) * (z j : ℝ)
        = ∑ j, ((A i j * z j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl (fun j _ ↦ by simp [Int.cast_mul])
    _ = ((∑ j, A i j * z j : ℤ) : ℝ) := by
          simp

/-- Every row sum of an integer vector against an integral matrix is an integer. -/
lemma integerVectors_row_sum_mem_range
    (A : Matrix (Fin m) (Fin n) ℤ) {x : Fin n → ℝ} (i : Fin m)
    (hx : x ∈ integerVectors n) :
    (∑ j, (A i j : ℝ) * x j) ∈ Set.range ((↑) : ℤ → ℝ) := by
  rcases integerVectors_row_sum_eq_int_cast A i hx with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

/-- An integral real number is bounded by `b` exactly when it is bounded by the real cast of
`⌊b⌋`. -/
lemma integral_real_le_floor_iff
    {r b : ℝ} (hr : r ∈ Set.range ((↑) : ℤ → ℝ)) :
    r ≤ b ↔ r ≤ ((⌊b⌋ : ℤ) : ℝ) := by
  rcases hr with ⟨z, rfl⟩
  constructor
  · intro hz
    exact Int.cast_le.2 ((Int.le_floor).2 hz)
  · intro hz
    exact hz.trans (Int.floor_le b)

/-- For integer vectors, the inequalities `A x ≤ b` are equivalent to `A x ≤ ⌊b⌋`, so the set
from Exercise 4.6 is exactly the set of integral points of the floor-rounded nonnegative
polyhedron. -/
theorem mem_fractional_rhs_integer_feasible_set_iff
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℝ} {x : Fin n → ℝ} :
    x ∈ fractional_rhs_integer_feasible_set A b ↔
      x ∈ nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋) ∩ integerVectors n := by
  rw [fractional_rhs_integer_feasible_set, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
    mem_nonnegative_matrix_polyhedron_iff]
  constructor
  · rintro ⟨hxint, hxnonneg, hAx⟩
    refine ⟨?_, hxint⟩
    refine ⟨?_, hxnonneg⟩
    intro i
    have hrow := integerVectors_row_sum_mem_range A i hxint
    exact (integral_real_le_floor_iff hrow).1 (hAx i)
  · rintro ⟨⟨hAx, hxnonneg⟩, hxint⟩
    refine ⟨hxint, hxnonneg, ?_⟩
    intro i
    have hrow := integerVectors_row_sum_mem_range A i hxint
    exact (integral_real_le_floor_iff hrow).2 (hAx i)

/-- Exercise 4.6. Given the integer set `S := {x ∈ ℤ_+^n : A x ≤ b}`, where `A` is totally
unimodular and `b` may have fractional components, the convex hull of `S` is exactly
`{x ∈ ℝ_+^n : A x ≤ ⌊b⌋}`. -/
theorem convexHull_fractional_rhs_integer_feasible_set_eq_floor_rhs_polyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) (hA : A.IsTotallyUnimodular) :
    convexHull ℝ (fractional_rhs_integer_feasible_set A b) =
      nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋) := by
  have hIntegral :
      is_integral (nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋)) :=
    ((nonnegative_matrix_polyhedron_integral_iff_totally_unimodular A).2 hA) (fun i ↦ ⌊b i⌋)
  have hSet :
      fractional_rhs_integer_feasible_set A b =
        nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋) ∩ integerVectors n := by
    ext x
    rw [mem_fractional_rhs_integer_feasible_set_iff]
  calc
    convexHull ℝ (fractional_rhs_integer_feasible_set A b)
        = convexHull ℝ
            (nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋) ∩ integerVectors n) := by
              rw [hSet]
    _ = nonnegative_matrix_polyhedron A (fun i ↦ ⌊b i⌋) := by
          simpa using ((is_integral_iff).1 hIntegral).symm

end Exercise46
