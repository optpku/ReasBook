/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Abs
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_11

open scoped BigOperators

-- Semantic recall: `Matrix.IsSubsetIrreducible` from Definition 1.2.11 is the
-- source-facing irreducibility owner used below, and
-- `det_ne_zero_of_sum_row_lt_diag` in `Mathlib.LinearAlgebra.Matrix.Gershgorin`
-- uses the exact strict rowwise inequality defining strict diagonal dominance.

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup R] [LinearOrder R]

/-- Chapter01 Definition 1.2.12 (1): a square matrix is diagonally dominant when, in each row,
the sum of the absolute values of the off-diagonal entries is bounded by the absolute value of
the diagonal entry. Specializing to `Matrix (Fin n) (Fin n) ℝ` recovers the textbook notion. -/
def IsDiagonallyDominant (A : Matrix ι ι R) : Prop :=
  ∀ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i|

/-- Unfolding formula for `Matrix.IsDiagonallyDominant`. -/
@[simp] theorem isDiagonallyDominant_iff {A : Matrix ι ι R} :
    A.IsDiagonallyDominant ↔ ∀ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i| :=
  Iff.rfl

/-- Chapter01 Definition 1.2.12 (2): a square matrix is strictly diagonally dominant when the
rowwise diagonal-dominance inequality is strict in every row. Specializing to
`Matrix (Fin n) (Fin n) ℝ` recovers the textbook notion. -/
def IsStrictlyDiagonallyDominant (A : Matrix ι ι R) : Prop :=
  ∀ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|

/-- Unfolding formula for `Matrix.IsStrictlyDiagonallyDominant`. -/
@[simp] theorem isStrictlyDiagonallyDominant_iff {A : Matrix ι ι R} :
    A.IsStrictlyDiagonallyDominant ↔ ∀ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i| :=
  Iff.rfl

/-- Chapter01 Definition 1.2.12 (3): a square matrix is irreducibly diagonally dominant when it
is diagonally dominant, irreducible in the sense of `Matrix.IsSubsetIrreducible`, and the strict
rowwise inequality holds for at least one row. Specializing to `Matrix (Fin n) (Fin n) ℝ`
recovers the textbook notion. -/
@[mk_iff] class IsIrreduciblyDiagonallyDominant (A : Matrix ι ι R) : Prop where
  isDiagonallyDominant : A.IsDiagonallyDominant
  isIrreducible : A.IsSubsetIrreducible
  exists_strict_row : ∃ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|

end Matrix
