/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic

public section

open scoped BigOperators

namespace SAT
namespace ClauseMatrix

/-- The matrix `A` has signed clause entries when every coefficient is one of `-1`, `0`, or `1`.
-/
def hasSignedEntries {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1

/-- Unfolding `hasSignedEntries A` gives the pointwise condition `A i j ∈ {-1, 0, 1}`. -/
theorem hasSignedEntries_iff {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} :
    hasSignedEntries A ↔ ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1 := by
  -- This theorem is exactly the definitional expansion of `hasSignedEntries`.
  rfl

/-- The rowwise count `n(A)` sums the indicators of the entries equal to `-1`. -/
def negativeCount {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Fin m → ℤ :=
  fun i ↦ ∑ j : Fin n, if A i j = -1 then (1 : ℤ) else 0

/-- Expanding `negativeCount A i` gives the rowwise sum of the `-1` indicators. -/
theorem negativeCount_eq_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) :
    negativeCount A i = ∑ j : Fin n, if A i j = -1 then (1 : ℤ) else 0 := by
  -- Evaluating `negativeCount` at row `i` exposes the defining sum.
  rfl

/-- The source right-hand side vector is the rowwise function `1 - n(A)`. -/
def rhs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Fin m → ℤ :=
  fun i ↦ 1 - negativeCount A i

/-- Expanding `rhs A i` yields the source term `1 - n(A)_i`. -/
theorem rhs_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) :
    rhs A i = 1 - negativeCount A i := by
  -- Evaluating `rhs` at row `i` exposes the defining expression `1 - negativeCount A i`.
  rfl

/-- The clause encoded by row `i` contains the positive literals at the `1`-entries and the
negative literals at the `-1`-entries. -/
def clause {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) :
    SAT.Clause n :=
  ((Finset.univ.filter fun j : Fin n ↦ A i j = 1).image SAT.Literal.pos) ∪
    ((Finset.univ.filter fun j : Fin n ↦ A i j = -1).image SAT.Literal.neg)

/-- A positive literal belongs to the row clause exactly when the matrix entry is `1`. -/
theorem pos_mem_clause_iff {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    (i : Fin m) (j : Fin n) :
    SAT.Literal.pos j ∈ clause A i ↔ A i j = 1 := by
  -- Normalize clause membership to the positive and negative filtered-image branches.
  simp [clause]

/-- A negative literal belongs to the row clause exactly when the matrix entry is `-1`. -/
theorem neg_mem_clause_iff {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    (i : Fin m) (j : Fin n) :
    SAT.Literal.neg j ∈ clause A i ↔ A i j = -1 := by
  -- Normalize clause membership to the two filtered-image branches and discard the wrong sign.
  simp [clause]

/-- The signed matrix `A` determines a SAT instance by interpreting each row as a clause. -/
def toInstance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    SAT.Instance :=
  SAT.Instance.ofClauses fun i ↦ clause A i

/-- The SAT instance built from `A` has the same variable count as the matrix column count. -/
theorem toInstance_n {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (toInstance A).n = n := by
  -- `toInstance` is built through the canonical row-clause constructor.
  simpa [toInstance] using SAT.Instance.ofClauses_n (fun i ↦ clause A i)

/-- The SAT instance built from `A` has the same clause count as the matrix row count. -/
theorem toInstance_m {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (toInstance A).m = m := by
  -- `toInstance` is built through the canonical row-clause constructor.
  simpa [toInstance] using SAT.Instance.ofClauses_m (fun i ↦ clause A i)

end ClauseMatrix
end SAT
