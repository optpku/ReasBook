/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

-- Domain-style sampling for Theorem 5.6.1:
-- * primary domain: finite-dimensional real matrix positivity for sparse quasi-Newton data;
-- * source-facing layer: the row vectors `s(i)` and the matrix `Q` from `(5.6.14)` and `(5.6.27)`;
-- * core/canonical owners: `Matrix.PosSemidef`, `Matrix.PosDef`,
--   `Matrix.PosSemidef.posDef_iff_det_ne_zero`, `Matrix.hadamard`, and `Matrix.diagonal`;
-- * sampled mathlib declarations in this domain:
--   `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`,
--   `Matrix.PosDef.of_dotProduct_mulVec_pos`,
--   `Matrix.PosSemidef.posDef_iff_det_ne_zero`,
--   `Matrix.PosSemidef.diagonal`,
--   `Matrix.PosSemidef.hadamard`;
-- * primitive data: the sparse-pattern matrix itself, with the row vectors and `Q` derived from it.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The sparse-pattern matrix whose `i`-th row is the row-restricted vector `s(i)` from `(5.6.14)`.
-/
def sparsePatternMatrix (J : Set (Fin n × Fin n)) (s : Point) : MatrixN :=
  Matrix.of fun i j ↦ if (i, j) ∈ J then s j else 0

@[simp] theorem sparsePatternMatrix_apply
    (J : Set (Fin n × Fin n)) (s : Point) (i j : Fin n) :
    sparsePatternMatrix J s i j = if (i, j) ∈ J then s j else 0 :=
  rfl

/-- The row-restricted vector `s(i)` from `(5.6.14)`, obtained from `s` by keeping only the
entries indexed by the sparsity pattern `J` in row `i`. -/
def sparsePatternVector (J : Set (Fin n × Fin n)) (s : Point) (i : Fin n) : Point :=
  WithLp.toLp 2 (sparsePatternMatrix J s i)

@[simp] theorem sparsePatternVector_apply
    (J : Set (Fin n × Fin n)) (s : Point) (i j : Fin n) :
    sparsePatternVector J s i j = if (i, j) ∈ J then s j else 0 :=
  rfl

/-- The sparse quasi-Newton matrix `Q` from `(5.6.27)`, canonically written as the Hadamard
product of the sparse-pattern matrix with its transpose, plus the diagonal matrix of row-square
terms. -/
def sparseQuasiNewtonQ (J : Set (Fin n × Fin n)) (s : Point) : MatrixN :=
  let S := sparsePatternMatrix J s
  S ⊙ Sᵀ + diagonal (fun i ↦ dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i))

/-- Entrywise description of `sparseQuasiNewtonQ`, matching `(5.6.27)`. -/
theorem sparseQuasiNewtonQ_apply
    (J : Set (Fin n × Fin n)) (s : Point) (i j : Fin n) :
    sparseQuasiNewtonQ J s i j =
      sparsePatternVector J s i j * sparsePatternVector J s j i +
        if i = j then
          dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)
        else 0 := by
  by_cases hij : i = j
  · subst hij
    simp [sparseQuasiNewtonQ]
  · simp [sparseQuasiNewtonQ, hij]

/-- Helper for Chapter05 Theorem 5.6.1: the sparse quasi-Newton matrix is symmetric, hence
Hermitian over `ℝ`. -/
lemma sparseQuasiNewtonQ_isHermitian
    (J : Set (Fin n × Fin n)) (s : Point) :
    (sparseQuasiNewtonQ J s).IsHermitian := by
  -- The entrywise formula is symmetric in `(i, j)`, which is the real-valued Hermitian condition.
  rw [isHermitian_iff_isSymm, IsSymm.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [sparseQuasiNewtonQ_apply]
  · simp [sparseQuasiNewtonQ_apply, hij, eq_comm, mul_comm]

/-- Helper for Chapter05 Theorem 5.6.1: the squared row norm of a sparse-pattern vector is the
sum of the squares of its entries. -/
lemma sparsePatternVector_dotProduct_self
    (J : Set (Fin n × Fin n)) (s : Point) (i : Fin n) :
    dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)
      = ∑ j, (sparsePatternVector J s i j) ^ 2 := by
  -- Expand the Euclidean dot product, then rewrite each product as a square.
  calc
    dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)
      = ∑ j, sparsePatternVector J s i j * sparsePatternVector J s i j := by
          rfl
    _ = ∑ j, (sparsePatternVector J s i j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : (i, j) ∈ J
          · simp [pow_two, h]
          · simp [pow_two, h]

/-- Helper for Chapter05 Theorem 5.6.1: the diagonal contribution in the quadratic form equals
twice the sum of the row-square terms from the source proof. -/
lemma diag_sum_eq
    (J : Set (Fin n × Fin n)) (s : Point) (z : Fin n → ℝ) :
    ∑ i, ∑ j,
      (z i * if i = j then dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)
        else 0) * z j * 2 =
    2 * ∑ i, ∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2 := by
  -- Collapse the Kronecker-delta term to the diagonal and then distribute the scalar factors.
  calc
    ∑ i, ∑ j,
        (z i * if i = j then dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)
          else 0) * z j * 2
      = ∑ i,
          (z i * dotProduct (sparsePatternVector J s i) (sparsePatternVector J s i)) * z i * 2 := by
          simp
    _ = ∑ i, (z i * ∑ j, (sparsePatternVector J s i j) ^ 2) * z i * 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [sparsePatternVector_dotProduct_self]
    _ = ∑ i, 2 * ∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            (z i * ∑ j, (sparsePatternVector J s i j) ^ 2) * z i * 2
                = (∑ j, ((z i * sparsePatternVector J s i j ^ 2) * z i)) * 2 := by
                    rw [Finset.mul_sum, Finset.sum_mul]
            _ = (∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2) * 2 := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = 2 * ∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2 := by
                  ring
    _ = 2 * ∑ i, ∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2 := by
          rw [Finset.mul_sum]

/-- Helper for Chapter05 Theorem 5.6.1: the second square-sum in the expansion is the same after
swapping the summation order. -/
lemma square_sum_swap
    (J : Set (Fin n × Fin n)) (s : Point) (z : Fin n → ℝ) :
    (∑ i, ∑ j, z j ^ 2 * (sparsePatternVector J s j i) ^ 2)
      = ∑ i, ∑ j, z i ^ 2 * (sparsePatternVector J s i j) ^ 2 := by
  -- This is just the double sum with the two indices exchanged.
  rw [Finset.sum_comm]

/-- Helper for Chapter05 Theorem 5.6.1: the mixed term in the quadratic-form expansion can be
reordered without changing its value. -/
lemma cross_sum_comm
    (J : Set (Fin n × Fin n)) (s : Point) (z : Fin n → ℝ) :
    (∑ i, ∑ j, z i * sparsePatternVector J s i j * sparsePatternVector J s j i * z j * 2)
      = ∑ i, ∑ j, z i * sparsePatternVector J s i j * z j * sparsePatternVector J s j i * 2 := by
  -- Commute the scalar factors inside each summand to match the square expansion.
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  ring

/-- Helper for Chapter05 Theorem 5.6.1: doubling the quadratic form of `Q` produces the textbook
sum-of-squares identity from `(5.6.29)`. -/
lemma two_mul_dotProduct_sparseQuasiNewtonQ_eq_sum_sq
    (J : Set (Fin n × Fin n)) (s : Point) (z : Fin n → ℝ) :
    2 * dotProduct z ((sparseQuasiNewtonQ J s).mulVec z) =
      ∑ i, ∑ j, (z i * sparsePatternVector J s i j + z j * sparsePatternVector J s j i) ^ 2 := by
  -- Expand `zᵀ Q z` entrywise and normalize the target into the source proof's double sum.
  rw [show dotProduct z ((sparseQuasiNewtonQ J s).mulVec z) =
      ∑ i, z i * ((sparseQuasiNewtonQ J s).mulVec z i) by rfl]
  rw [show (sparseQuasiNewtonQ J s).mulVec z = fun i ↦ ∑ j, sparseQuasiNewtonQ J s i j * z j by rfl]
  simp_rw [sparseQuasiNewtonQ_apply, Finset.mul_sum, pow_two]
  ring_nf
  calc
    (∑ x,
      ∑ x_1,
        (z x * sparsePatternVector J s x x_1 * sparsePatternVector J s x_1 x * z x_1 * 2 +
          (z x * if x = x_1 then dotProduct (sparsePatternVector J s x) (sparsePatternVector J s x)
            else 0) * z x_1 * 2))
        = (∑ x, ∑ x_1, z x * sparsePatternVector J s x x_1 *
            sparsePatternVector J s x_1 x * z x_1 * 2) +
          ∑ x, ∑ x_1,
            (z x * if x = x_1 then
                dotProduct (sparsePatternVector J s x) (sparsePatternVector J s x)
              else 0) * z x_1 * 2 := by
                simp_rw [Finset.sum_add_distrib]
    _ = (∑ x, ∑ x_1, z x * sparsePatternVector J s x x_1 *
            z x_1 * sparsePatternVector J s x_1 x * 2) +
          2 * ∑ x, ∑ x_1, z x ^ 2 * (sparsePatternVector J s x x_1) ^ 2 := by
            rw [cross_sum_comm, diag_sum_eq]
    _ = (∑ x, ∑ x_1, z x * sparsePatternVector J s x x_1 *
            z x_1 * sparsePatternVector J s x_1 x * 2) +
          ((∑ x, ∑ x_1, z x ^ 2 * (sparsePatternVector J s x x_1) ^ 2) +
            ∑ x, ∑ x_1, z x_1 ^ 2 * (sparsePatternVector J s x_1 x) ^ 2) := by
            rw [square_sum_swap]
            ring
    _ = ∑ x,
          ∑ x_1,
            (z x * sparsePatternVector J s x x_1 * z x_1 * sparsePatternVector J s x_1 x * 2 +
              z x ^ 2 * (sparsePatternVector J s x x_1) ^ 2 +
              z x_1 ^ 2 * (sparsePatternVector J s x_1 x) ^ 2) := by
            simp_rw [Finset.sum_add_distrib]
            ring

/-- Helper for Chapter05 Theorem 5.6.1: the quadratic form of `Q` is nonnegative because the
source expansion is a finite sum of squares. -/
lemma sparseQuasiNewtonQ_dotProduct_nonneg
    (J : Set (Fin n × Fin n)) (s : Point) (z : Fin n → ℝ) :
    0 ≤ dotProduct z ((sparseQuasiNewtonQ J s).mulVec z) := by
  -- Apply the sum-of-squares identity and divide away the positive factor `2`.
  have hsum := two_mul_dotProduct_sparseQuasiNewtonQ_eq_sum_sq J s z
  have hnonneg : 0 ≤ 2 * dotProduct z ((sparseQuasiNewtonQ J s).mulVec z) := by
    rw [hsum]
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  nlinarith

/-- Companion positivity fact: the sparse quasi-Newton matrix `Q` from `(5.6.27)` is positive
semidefinite. Equivalently, for every `z : Point`, one has
`0 ≤ dotProduct z ((sparseQuasiNewtonQ J s).mulVec z)`. -/
theorem sparseQuasiNewtonQ_posSemidef
    (J : Set (Fin n × Fin n)) (s : Point) :
    (sparseQuasiNewtonQ J s).PosSemidef := by
  -- The source proof gives nonnegativity of the quadratic form once we package the sum of squares.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (sparseQuasiNewtonQ_isHermitian J s) ?_
  intro z
  simpa using sparseQuasiNewtonQ_dotProduct_nonneg J s z

/-- Since `sparseQuasiNewtonQ J s` is always positive semidefinite, strict positive definiteness
is equivalent to the nondegeneracy condition `det Q ≠ 0`. -/
theorem sparseQuasiNewtonQ_posDef_iff_det_ne_zero
    (J : Set (Fin n × Fin n)) (s : Point) :
    (sparseQuasiNewtonQ J s).PosDef ↔ (sparseQuasiNewtonQ J s).det ≠ 0 := by
  exact (sparseQuasiNewtonQ_posSemidef J s).posDef_iff_det_ne_zero

/-- Chapter05 Theorem 5.6.1: the sparse quasi-Newton matrix `Q` from `(5.6.27)` is positive
definite under the exact owner-level nondegeneracy condition `det Q ≠ 0`. -/
theorem sparseQuasiNewtonQ_posDef
    (J : Set (Fin n × Fin n)) (s : Point)
    (h_det : (sparseQuasiNewtonQ J s).det ≠ 0) :
    (sparseQuasiNewtonQ J s).PosDef := by
  exact (sparseQuasiNewtonQ_posDef_iff_det_ne_zero J s).2 h_det

end
