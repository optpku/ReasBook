/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

open scoped Matrix
open Matrix

-- Declarations for this item will be appended below by the statement pipeline.

/-- The symmetric correlation-coordinate space on `Fin n`, viewed as the canonical linear
subspace of real symmetric matrices. -/
abbrev correlationSpace (n : ℕ) :=
  ↥(selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ))

/-- Correlation-space points act as their underlying symmetric matrices. -/
instance {n : ℕ} : CoeFun (correlationSpace n) fun _ ↦ Fin n → Fin n → ℝ :=
  ⟨fun x ↦ x.1⟩

namespace correlationSpace

/-- The ambient symmetric matrix underlying a correlation-space point. -/
def toMatrix {n : ℕ} (x : correlationSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  x.1

end correlationSpace

/-- The ambient matrix attached to a subset of `Fin n`. -/
def correlation_vertex_matrix {n : ℕ} (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0)

/-- The ambient matrix attached to a correlation vertex is symmetric. -/
theorem correlation_vertex_matrix_isSymm {n : ℕ} (S : Finset (Fin n)) :
    (correlation_vertex_matrix S).IsSymm := by
  -- The defining entry formula is symmetric in the two coordinates.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp [correlation_vertex_matrix, mul_comm]

/-- The ambient matrix attached to a correlation vertex belongs to the symmetric correlation
space. -/
theorem correlation_vertex_matrix_mem_correlationSpace {n : ℕ} (S : Finset (Fin n)) :
    correlation_vertex_matrix S ∈
      selfAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Membership is exactly the self-adjointness condition for real symmetric matrices.
  rw [mem_selfAdjointMatricesSubmodule]
  simpa [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair] using
    correlation_vertex_matrix_isSymm S

/-- The `0/1` rank-one correlation vertex attached to a subset of `Fin n`. -/
def correlation_vertex {n : ℕ} (S : Finset (Fin n)) : correlationSpace n :=
  ⟨correlation_vertex_matrix S, correlation_vertex_matrix_mem_correlationSpace S⟩

/-- The `0/1` rank-one vertices spanning the correlation polytope on `n` vertices. -/
def correlationVertices (n : ℕ) : Set (correlationSpace n) :=
  Set.range fun S : Finset (Fin n) ↦ correlation_vertex S

/-- The correlation polytope on `n` vertices is the convex hull of the `0/1` rank-one symmetric
correlation vertices attached to subsets of `Fin n`. -/
def correlationPolytope (n : ℕ) : Set (correlationSpace n) :=
  convexHull ℝ (correlationVertices n)

/-- The correlation polytope is defined as the convex hull of the `0/1` rank-one symmetric
correlation vertices coming from subsets of `Fin n`. -/
theorem correlationPolytope_eq_convexHull (n : ℕ) :
    correlationPolytope n = convexHull ℝ (correlationVertices n) := by
  -- This theorem is just the defining equation of the polytope.
  rfl

/-- The matrix `2 Diag(a) - aaᵀ` appearing in inequality `(4.38)`. -/
def correlation_cut_matrix {n : ℕ} (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • Matrix.diagonal a - Matrix.vecMulVec a a

/-- Helper for Lemma 4.56: each coordinate of a `0/1` vector is idempotent. -/
lemma zero_one_vector_sq_eq_self
    {n : ℕ} {b : Fin n → ℝ} (hb : is_zero_one_vector b) (i : Fin n) :
    b i ^ 2 = b i := by
  rcases hb i with hbi | hbi
  · rw [hbi]
    norm_num
  · rw [hbi]
    norm_num

/-- Helper for Lemma 4.56: the diagonal part of `2 Diag(a) - aaᵀ` pairs with `bbᵀ`
as `aᵀb`. -/
lemma diagonal_vecMulVec_trace_eq_dotProduct
    {n : ℕ} (a b : Fin n → ℝ) (hb : is_zero_one_vector b) :
    Matrix.trace (Matrix.diagonal a * Matrix.vecMulVec b b) = a ⬝ᵥ b := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  unfold dotProduct
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Matrix.mulVec_diagonal, mul_assoc]
  calc
    a i * (b i * b i) = a i * b i ^ 2 := by rw [pow_two]
    _ = a i * b i := by rw [zero_one_vector_sq_eq_self hb i]

/-- Helper for Lemma 4.56: the trace of `aaᵀbbᵀ` is `(aᵀb)^2`. -/
lemma vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq
    {n : ℕ} (a b : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec a a * Matrix.vecMulVec b b) = (a ⬝ᵥ b) ^ 2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul,
    pow_two]

/-- Bridge from the coordinate-level `vec` pairing to the canonical trace pairing for the cut
matrix. -/
lemma correlation_cut_vec_dot_eq_trace
    {n : ℕ} (a : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) :
    (correlation_cut_matrix a).vec ⬝ᵥ Y.vec = Matrix.trace (correlation_cut_matrix a * Y) := by
  rw [Matrix.vec_dotProduct_vec]
  simp only [correlation_cut_matrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.diagonal_transpose, Matrix.transpose_vecMulVec]

/-- Helper for Lemma 4.56: the cut sublevel set `{Y | ⟪2 Diag(a) - aaᵀ, Y⟫ ≤ 1}`
is convex in the symmetric correlation-coordinate space. -/
lemma correlation_cut_sublevel_convex
    {n : ℕ} (a : Fin n → ℝ) :
    Convex ℝ
      {Y : correlationSpace n |
        Matrix.trace (correlation_cut_matrix a * Y.toMatrix) ≤ 1} := by
  let traceLinear : correlationSpace n →ₗ[ℝ] ℝ :=
    { toFun := fun Y ↦ Matrix.trace (correlation_cut_matrix a * Y.toMatrix)
      map_add' := by
        -- The trace pairing is linear in the correlation-space argument.
        intro Y Z
        simp [correlationSpace.toMatrix, Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        -- Scalar multiplication passes through matrix multiplication and trace.
        intro c Y
        simp [correlationSpace.toMatrix, Matrix.trace_smul] }
  have hsublevel :
      {Y : correlationSpace n |
          Matrix.trace (correlation_cut_matrix a * Y.toMatrix) ≤ 1} =
        traceLinear ⁻¹' Set.Iic (1 : ℝ) := by
    -- The target set is exactly the preimage of the interval `(-∞, 1]`.
    ext Y
    simp [traceLinear, Set.mem_Iic]
  rw [hsublevel]
  exact (convex_Iic (1 : ℝ)).linear_preimage traceLinear

/-- Helper for Lemma 4.56: the subset indicator of a finite set is a `0/1` vector. -/
lemma finset_indicator_is_zero_one_vector
    {n : ℕ} (S : Finset (Fin n)) :
    is_zero_one_vector (fun i : Fin n ↦ if i ∈ S then (1 : ℝ) else 0) := by
  -- Each coordinate is definitionally either `1` on `S` or `0` off `S`.
  intro i
  by_cases hi : i ∈ S
  · right
    simp [hi]
  · left
    simp [hi]

/-- Helper for Lemma 4.56: a correlation vertex matrix is the rank-one matrix of its indicator
vector. -/
lemma correlation_vertex_matrix_eq_vecMulVec_indicator
    {n : ℕ} (S : Finset (Fin n)) :
    correlation_vertex_matrix S =
      Matrix.vecMulVec
        (fun i : Fin n ↦ if i ∈ S then (1 : ℝ) else 0)
        (fun i : Fin n ↦ if i ∈ S then (1 : ℝ) else 0) := by
  -- Both matrices have the same entrywise product formula.
  ext i j
  simp [correlation_vertex_matrix, Matrix.vecMulVec]

/-- Helper for Lemma 4.56: every rank-one correlation vertex satisfies the cut inequality. -/
lemma correlation_vertex_mem_cut_sublevel
    {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n)) :
    correlation_vertex S ∈
      {Y : correlationSpace n |
        Matrix.trace (correlation_cut_matrix a * Y.toMatrix) ≤ 1} := by
  let b : Fin n → ℝ := fun i : Fin n ↦ if i ∈ S then (1 : ℝ) else 0
  have hb : is_zero_one_vector b := finset_indicator_is_zero_one_vector S
  have hmatrix :
      (correlation_vertex S).toMatrix = Matrix.vecMulVec b b := by
    -- The ambient matrix of the subtype vertex is the indicator rank-one matrix.
    ext i j
    simp [correlationSpace.toMatrix, correlation_vertex,
      correlation_vertex_matrix_eq_vecMulVec_indicator, b]
  have hslack :
      1 - Matrix.trace (correlation_cut_matrix a * (correlation_vertex S).toMatrix) =
        (1 - a ⬝ᵥ b) ^ 2 := by
    -- This is the source slack computation specialized to the indicator vector of `S`.
    rw [hmatrix]
    simp only [correlation_cut_matrix]
    rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
      diagonal_vecMulVec_trace_eq_dotProduct a b hb,
      vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq]
    ring
  have hsq : 0 ≤ (1 - a ⬝ᵥ b) ^ 2 := sq_nonneg (1 - a ⬝ᵥ b)
  -- Nonnegativity of the slack rearranges to the desired upper bound.
  have hineq : Matrix.trace (correlation_cut_matrix a * (correlation_vertex S).toMatrix) ≤ 1 := by
    nlinarith [hslack, hsq]
  exact hineq

/-- Lemma 4.56 (1). The textbook statement assumes `a ∈ {0,1}^n`; the same computation proves the
stronger valid inequality for every real vector `a`. -/
theorem correlation_cut_inequality_valid
    {n : ℕ} (a : Fin n → ℝ) {Y : correlationSpace n} (hY : Y ∈ correlationPolytope n) :
    Matrix.trace (correlation_cut_matrix a * Y.toMatrix) ≤ 1 := by
  have hHull : Y ∈ convexHull ℝ (correlationVertices n) := by
    -- The correlation polytope is defined as the convex hull of its rank-one vertices.
    simpa [correlationPolytope_eq_convexHull] using hY
  have hvertices :
      correlationVertices n ⊆
        {Z : correlationSpace n |
          Matrix.trace (correlation_cut_matrix a * Z.toMatrix) ≤ 1} := by
    -- Each generator vertex has nonnegative slack, hence lies in the cut halfspace.
    rintro _ ⟨S, rfl⟩
    exact correlation_vertex_mem_cut_sublevel a S
  -- Convexity of the halfspace lifts the vertexwise inequality to the whole convex hull.
  exact (convexHull_min hvertices (correlation_cut_sublevel_convex a)) hHull

/-- Lemma 4.56 (2). The textbook statement assumes both `a` and `b` are `0/1`; the exact slack
formula only needs `b` to be `0/1`, so the Lean statement keeps the stronger form. -/
theorem correlation_cut_inequality_slack_at_vertex
    {n : ℕ} (a b : Fin n → ℝ) (hb : is_zero_one_vector b) :
    1 - Matrix.trace (correlation_cut_matrix a * Matrix.vecMulVec b b) =
      (1 - a ⬝ᵥ b) ^ 2 := by
  simp only [correlation_cut_matrix]
  rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
    diagonal_vecMulVec_trace_eq_dotProduct a b hb,
    vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq]
  ring
