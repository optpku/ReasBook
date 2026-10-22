/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Order.Filter.Extr

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

/-
Domain sampling for this item:
- primary domain: Hessian-form weighted least-change quasi-Newton updates for the PSB owner on
  real matrix models of `ℝ^n`;
- sampled project declarations in this domain:
  `symmetrizedBroydenLimit`,
  `satisfiesQuasiNewtonEquationHessianForm`,
  `IsMinOn`,
  `weightedFrobeniusNorm`;
- source/core/bridge triage:
  the theorem below is source-facing because it adds the textbook symmetry restriction and
  uniqueness conclusion for the weighted objective, while `symmetrizedBroydenLimit` and
  `satisfiesQuasiNewtonEquationHessianForm` are the Chapter 5 core/canonical owners,
  `IsMinOn` is the canonical minimization owner, and `weightedFrobeniusNorm M` is the Chapter 1
  bridge/view objective;
- primitive data here: the PSB owner, the canonical Hessian-form secant owner, symmetry of the
  minimizer and competitors, and the weighted comparison/uniqueness conclusions;
- owner decision:
  the source theorem keeps its explicit weighted minimization surface under the present symmetric
  nonsingular hypotheses, and its feasible predicate reuses the Chapter 5 canonical secant owner
  together with the canonical minimization owner `IsMinOn` on the symmetric secant feasible set
  instead of an unrestricted least-change wrapper that would erase the source symmetry
  constraint.
-/

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter05 Theorem 5.1.10: the metric secant vector `z := M c` satisfies
`M z = s` once `M c = M⁻¹ s` and `M` is nonsingular. -/
lemma metricSecantVector_mulVec
    (M : MatrixN) (c s : Point) (hMdet : IsUnit M.det)
    (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    M.mulVec (M.mulVec c) = s := by
  -- Rewrite `M c` through the inverse-side secant identity and then cancel `M * M⁻¹`.
  calc
    M.mulVec (M.mulVec c) = (M * M⁻¹).mulVec s := by
          rw [hMc]
          simpa using (Matrix.mulVec_mulVec s.ofLp M M⁻¹)
    _ = s := by
          rw [Matrix.mul_nonsing_inv M hMdet]
          simp

/-- Helper for Chapter05 Theorem 5.1.10: the metric secant vector `z := M c` satisfies
`dotProduct z z = dotProduct c s`. -/
lemma metricSecantVector_dotProductSelf
    (M : MatrixN) (c s : Point) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    dotProduct (M.mulVec c) (M.mulVec c) = dotProduct c s := by
  -- Move one factor of `M` across the bilinear pairing and then use `M (M c) = s`.
  calc
    dotProduct (M.mulVec c) (M.mulVec c)
        = dotProduct c (M.transpose.mulVec (M.mulVec c)) := by
            symm
            exact Matrix.dotProduct_transpose_mulVec M c (M.mulVec c)
    _ = dotProduct c (M.mulVec (M.mulVec c)) := by
          simpa [hM.eq]
    _ = dotProduct c s := by
          rw [metricSecantVector_mulVec M c s hMdet hMc]

/-- Helper for Chapter05 Theorem 5.1.10: the metric secant vector `z := M c` is nonzero when
`dotProduct c s > 0`. -/
lemma metricSecantVector_ne_zero
    (M : MatrixN) (c s : Point) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    M.mulVec c ≠ 0 := by
  -- Positive self-pairing excludes the zero vector.
  have hzsq :
      0 < dotProduct (M.mulVec c) (M.mulVec c) := by
    rw [metricSecantVector_dotProductSelf M c s hM hMdet hMc]
    exact hcs
  intro hz
  simpa [hz] using hzsq.ne'

/-- Helper for Chapter05 Theorem 5.1.10: conjugating the residual by `M` turns the source
pairing against `s` into the Euclidean pairing against `z := M c`. -/
lemma metricResidual_dotProductSecantVector
    (B M : MatrixN) (c s y : Point) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    dotProduct (M.mulVec (y - Matrix.toEuclideanLin B s)) (M.mulVec c) =
      dotProduct (y - Matrix.toEuclideanLin B s) s := by
  -- Move one factor of `M` across the dot product and reuse `M (M c) = s`.
  have hraw :
      dotProduct (M.mulVec (y.ofLp - B.mulVec s.ofLp)) (M.mulVec c) =
        dotProduct (y.ofLp - B.mulVec s.ofLp) s.ofLp := by
    calc
      dotProduct (M.mulVec (y.ofLp - B.mulVec s.ofLp)) (M.mulVec c)
          = dotProduct (M.mulVec c) (M.mulVec (y.ofLp - B.mulVec s.ofLp)) := by
                rw [dotProduct_comm]
      _ = dotProduct (y.ofLp - B.mulVec s.ofLp)
            (M.transpose.mulVec (M.mulVec c)) := by
              exact (Matrix.dotProduct_transpose_mulVec M
                (y.ofLp - B.mulVec s.ofLp) (M.mulVec c)).symm
      _ = dotProduct (y.ofLp - B.mulVec s.ofLp) (M.mulVec (M.mulVec c)) := by
            simp [hM.eq]
      _ = dotProduct (y.ofLp - B.mulVec s.ofLp) s.ofLp := by
            rw [metricSecantVector_mulVec M c s hMdet hMc]
  calc
    dotProduct (M.mulVec (y - Matrix.toEuclideanLin B s)) (M.mulVec c)
        = dotProduct (M.mulVec (y.ofLp - B.mulVec s.ofLp)) (M.mulVec c) := by
            simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    _ = dotProduct (y.ofLp - B.mulVec s.ofLp) s.ofLp := hraw
    _ = dotProduct (y - Matrix.toEuclideanLin B s) s := by
          simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Chapter05 Theorem 5.1.10: the canonical symmetric matrix with prescribed
secant image `r = P z`. -/
def symmetricSecantProjection (r z : Point) : MatrixN :=
  (dotProduct z z)⁻¹ • (Matrix.vecMulVec r z + Matrix.vecMulVec z r) -
    (dotProduct r z * (dotProduct z z)⁻¹ * (dotProduct z z)⁻¹) • Matrix.vecMulVec z z

/-- Helper for Chapter05 Theorem 5.1.10: the canonical symmetric secant projection is symmetric. -/
lemma symmetricSecantProjection_isSymm
    (r z : Point) :
    (symmetricSecantProjection r z).IsSymm := by
  -- The projection formula is manifestly symmetric entrywise.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [symmetricSecantProjection, Matrix.vecMulVec_apply, sub_eq_add_neg,
    add_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Chapter05 Theorem 5.1.10: vectorize a matrix by reindexing its entries by pairs. -/
def matrixEntryVector (A : MatrixN) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 fun ij : Fin n × Fin n ↦ A ij.1 ij.2

/-- Helper for Chapter05 Theorem 5.1.10: the Frobenius norm of a matrix is the Euclidean norm of
its entry vectorization. -/
lemma frobeniusNorm_eq_matrixEntryVectorNorm
    (A : MatrixN) :
    ‖A‖ = ‖matrixEntryVector A‖ := by
  -- Both sides are the `ℓ²` norm of the same family of entries, indexed differently.
  rw [Matrix.frobenius_norm_def, matrixEntryVector, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp [← Finset.univ_product_univ, Finset.sum_product]

/-- Helper for Chapter05 Theorem 5.1.10: conjugating by a nonsingular weight makes the weighted
Frobenius norm detect exactly the zero matrix. -/
lemma weightedFrobeniusNorm_eq_zero_iff
    (M A : MatrixN) (hMdet : IsUnit M.det) :
    weightedFrobeniusNorm M A = 0 ↔ A = 0 := by
  have hMUnit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hMdet
  obtain ⟨U, rfl⟩ := hMUnit
  constructor
  · intro hzero
    have hzero' :
        ‖((↑U : MatrixN) * A * (↑U : MatrixN) : MatrixN)‖ = 0 := by
      simpa [weightedFrobeniusNorm_eq] using hzero
    have hconjZero :
        ((↑U : MatrixN)⁻¹ * (((↑U : MatrixN) * A * (↑U : MatrixN))) * (↑U : MatrixN)⁻¹) = 0 := by
      have hnormZero :
          (((↑U : MatrixN) * A * (↑U : MatrixN)) : MatrixN) = 0 := norm_eq_zero.mp hzero'
      rw [hnormZero]
      simp
    -- Cancel the unit factors to recover the original matrix `A`.
    simpa [weightedFrobeniusNorm_eq, mul_assoc] using hconjZero
  · intro hA
    -- Vanishing is immediate when the argument matrix itself vanishes.
    subst hA
    simp [weightedFrobeniusNorm_eq]

/-- Helper for Chapter05 Theorem 5.1.10: two distinct Frobenius corrections with the same norm
have a strictly smaller midpoint correction norm. -/
lemma frobeniusMidpoint_lt_of_distinct
    {A₁ A₂ B : MatrixN}
    (hNorm : ‖A₁ - B‖ = ‖A₂ - B‖) (hne : A₁ ≠ A₂) :
    ‖(((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂) - B)‖ < ‖A₁ - B‖ := by
  let x : EuclideanSpace ℝ (Fin n × Fin n) := matrixEntryVector (A₁ - B)
  let y : EuclideanSpace ℝ (Fin n × Fin n) := matrixEntryVector (A₂ - B)
  have hNormVec : ‖x‖ = ‖y‖ := by
    simpa [x, y, frobeniusNorm_eq_matrixEntryVectorNorm] using hNorm
  have hcorrNe : x ≠ y := by
    intro hvec
    have hsub : A₁ - B = A₂ - B := by
      ext i j
      simpa [x, y, matrixEntryVector] using congrFun (congrArg WithLp.ofLp hvec) (i, j)
    apply hne
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun M : MatrixN ↦ M + B) hsub
  have hMidVecLt : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ := by
    -- Equal correction norms turn strict convexity of the Euclidean norm into midpoint descent.
    exact (norm_midpoint_lt_iff hNormVec).2 hcorrNe
  have hmidVec :
      matrixEntryVector ((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ - B) = (1 / 2 : ℝ) • (x + y) := by
    ext ij
    rcases ij with ⟨j, i⟩
    simp [matrixEntryVector, x, y]
    ring
  calc
    ‖(((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂) - B)‖
        = ‖matrixEntryVector ((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ - B)‖ := by
            rw [frobeniusNorm_eq_matrixEntryVectorNorm]
    _ = ‖(1 / 2 : ℝ) • (x + y)‖ := by
          rw [hmidVec]
    _ < ‖x‖ := hMidVecLt
    _ = ‖A₁ - B‖ := by
          simpa [x] using (frobeniusNorm_eq_matrixEntryVectorNorm (A₁ - B)).symm

/-- Helper for Chapter05 Theorem 5.1.10: the weighted Frobenius norm inherits the strict midpoint
inequality from the ordinary Frobenius norm after conjugating by `M`. -/
lemma weightedFrobeniusNorm_midpoint_lt_of_distinct
    (M A₁ A₂ B : MatrixN) (hMdet : IsUnit M.det)
    (hNorm :
      weightedFrobeniusNorm M (A₁ - B) =
        weightedFrobeniusNorm M (A₂ - B))
    (hne : A₁ ≠ A₂) :
    weightedFrobeniusNorm M (((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂) - B) <
      weightedFrobeniusNorm M (A₁ - B) := by
  let conj : MatrixN → MatrixN := fun A ↦ M * A * M
  have hNorm' : ‖conj (A₁ - B)‖ = ‖conj (A₂ - B)‖ := by
    simpa [conj, weightedFrobeniusNorm_eq] using hNorm
  have hne' : conj A₁ ≠ conj A₂ := by
    intro hEq
    have hZero :
        weightedFrobeniusNorm M (A₁ - A₂) = 0 := by
      rw [weightedFrobeniusNorm_eq]
      have hSub : conj (A₁ - A₂) = 0 := by
        calc
          conj (A₁ - A₂) = conj A₁ - conj A₂ := by
            simp [conj, sub_eq_add_neg, mul_add, add_mul, mul_assoc]
          _ = 0 := by
                simpa [sub_eq_add_neg] using sub_eq_zero.mpr hEq
      simpa [conj] using congrArg norm hSub
    have hSubZero : A₁ - A₂ = 0 :=
      (weightedFrobeniusNorm_eq_zero_iff M (A₁ - A₂) hMdet).1 hZero
    exact hne (sub_eq_zero.mp hSubZero)
  have hMid :=
    frobeniusMidpoint_lt_of_distinct
      (A₁ := conj A₁) (A₂ := conj A₂) (B := conj B)
      (by simpa [conj, sub_eq_add_neg, mul_add, add_mul, mul_assoc] using hNorm') hne'
  -- Expand the conjugated midpoint once so the strict Frobenius inequality becomes the desired
  -- weighted inequality.
  simpa [conj, weightedFrobeniusNorm_eq, sub_eq_add_neg, mul_add, add_mul, mul_assoc] using hMid

/-- Helper for Chapter05 Theorem 5.1.10: the explicit symmetric secant projection sends `z` to
the prescribed image `r` when `z ≠ 0`. -/
lemma symmetricSecantProjection_mulVec
    (r z : Point) (hz : z ≠ 0) :
    (symmetricSecantProjection r z).mulVec z.ofLp = r.ofLp := by
  have hzLp : z.ofLp ≠ 0 := by
    simpa using hz
  have hzz : dotProduct z z ≠ 0 := by
    intro hzero
    exact hzLp (dotProduct_self_eq_zero.mp hzero)
  have hProjection :
      symmetricSecantProjection r z = symmetrizedBroydenLimit (0 : MatrixN) z r z := by
    -- The zero-base PSB formula is exactly the canonical symmetric projection.
    simp [symmetricSecantProjection, symmetrizedBroydenLimit, Matrix.toEuclideanLin]
  have hSecant :
      Matrix.toEuclideanLin (symmetrizedBroydenLimit (0 : MatrixN) z r z) z = r :=
    symmetrizedBroydenLimit_mulVecSecant (0 : MatrixN) z r z hzz
  -- Unpack the secant equation back to the `mulVec` form used in the comparison proof.
  simpa [hProjection, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg WithLp.ofLp hSecant

/-- Helper for Chapter05 Theorem 5.1.10: entry vectorization converts Frobenius products into
matrix traces. -/
lemma matrixEntryVector_dotProduct
    (A B : MatrixN) :
    dotProduct (matrixEntryVector A) (matrixEntryVector B) = (A.transpose * B).trace := by
  -- Rewrite both sides as the same double sum over matrix entries.
  calc
    dotProduct (matrixEntryVector A) (matrixEntryVector B)
        = ∑ ij : Fin n × Fin n, A ij.1 ij.2 * B ij.1 ij.2 := by
            simp [dotProduct, matrixEntryVector]
    _ = ∑ i, ∑ j, A i j * B i j := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product
              (s := (Finset.univ : Finset (Fin n)))
              (t := (Finset.univ : Finset (Fin n)))
              (f := fun ij : Fin n × Fin n ↦ A ij.1 ij.2 * B ij.1 ij.2))
    _ = ∑ j, ∑ i, A i j * B i j := by
          rw [Finset.sum_comm]
    _ = (A.transpose * B).trace := by
          simp [Matrix.trace, Matrix.mul_apply]

/-- Helper for Chapter05 Theorem 5.1.10: every symmetric error killing `z` is Frobenius-orthogonal
to the canonical symmetric secant projection. -/
lemma symmetricSecantProjection_trace_mul_eq_zero
    {r z : Point} {D : MatrixN}
    (hD : D.IsSymm) (hDz : D.mulVec z.ofLp = 0) :
    (((symmetricSecantProjection r z).transpose) * D).trace = 0 := by
  have hTraceRz :
      (((Matrix.vecMulVec r z).transpose) * D).trace = 0 := by
    -- Cycle the rank-one factor to the right so the trace only sees `D.mulVec z`.
    calc
      (((Matrix.vecMulVec r z).transpose) * D).trace
          = (D * (Matrix.vecMulVec r z).transpose).trace := by
              rw [Matrix.trace_mul_comm]
      _ = (D * Matrix.vecMulVec z r).trace := by
            simp
      _ = (Matrix.vecMulVec (D.mulVec z.ofLp) r).trace := by
            rw [Matrix.mul_vecMulVec]
      _ = dotProduct r (D.mulVec z.ofLp) := by
            simp [Matrix.trace_vecMulVec, dotProduct_comm]
      _ = 0 := by
            simpa [hDz]
  have hTraceZr :
      (((Matrix.vecMulVec z r).transpose) * D).trace = 0 := by
    -- Symmetry of `D` moves the surviving factor back onto the same killed vector `z`.
    calc
      (((Matrix.vecMulVec z r).transpose) * D).trace
          = (D * (Matrix.vecMulVec z r).transpose).trace := by
              rw [Matrix.trace_mul_comm]
      _ = (D * Matrix.vecMulVec r z).trace := by
            simp
      _ = (Matrix.vecMulVec (D.mulVec r.ofLp) z).trace := by
            rw [Matrix.mul_vecMulVec]
      _ = dotProduct z (D.mulVec r.ofLp) := by
            simp [Matrix.trace_vecMulVec, dotProduct_comm]
      _ = dotProduct r (D.mulVec z.ofLp) := by
            simpa [hD.eq] using Matrix.dotProduct_transpose_mulVec D z r
      _ = dotProduct (D.mulVec z.ofLp) r := by
            rw [dotProduct_comm]
      _ = 0 := by
            simpa [hDz]
  have hTraceZz :
      (((Matrix.vecMulVec z z).transpose) * D).trace = 0 := by
    -- The final rank-one term vanishes because both slots hit the killed vector `z`.
    calc
      (((Matrix.vecMulVec z z).transpose) * D).trace
          = (D * (Matrix.vecMulVec z z).transpose).trace := by
              rw [Matrix.trace_mul_comm]
      _ = (D * Matrix.vecMulVec z z).trace := by
            simp
      _ = (Matrix.vecMulVec (D.mulVec z.ofLp) z).trace := by
            rw [Matrix.mul_vecMulVec]
      _ = dotProduct z (D.mulVec z.ofLp) := by
            simp [Matrix.trace_vecMulVec, dotProduct_comm]
      _ = 0 := by
            simpa [hDz]
  let a : ℝ := (dotProduct z z)⁻¹
  let b : ℝ := dotProduct r z * a * a
  let U : MatrixN := Matrix.vecMulVec r z
  let V : MatrixN := Matrix.vecMulVec z r
  let W : MatrixN := Matrix.vecMulVec z z
  have hExpand :
      (((symmetricSecantProjection r z).transpose) * D).trace =
        (a • (U.transpose * D)).trace + (a • (V.transpose * D)).trace +
          ((-b) • (W.transpose * D)).trace := by
    -- Flatten the transpose and trace through the rank-one decomposition once.
    simp [symmetricSecantProjection, a, b, U, V, W, sub_eq_add_neg,
      Matrix.transpose_add, Matrix.transpose_smul, Matrix.smul_mul, Matrix.add_mul,
      Matrix.trace_add, Matrix.trace_smul, add_assoc]
  -- After rewriting the trace through the rank-one decomposition, each scalar multiple vanishes.
  rw [hExpand, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    hTraceRz, hTraceZr, hTraceZz]
  ring

/-- Helper for Chapter05 Theorem 5.1.10: among symmetric matrices sending `z` to `r`, the
canonical symmetric secant projection has minimal Frobenius norm. -/
lemma symmetricSecantProjection_frobenius_le
    {r z : Point} {C : MatrixN}
    (hz : z ≠ 0)
    (hC : C.IsSymm) (hCz : C.mulVec z.ofLp = r.ofLp) :
    ‖symmetricSecantProjection r z‖ ≤ ‖C‖ := by
  let P := symmetricSecantProjection r z
  let D := C - P
  have hP : P.IsSymm := symmetricSecantProjection_isSymm r z
  have hPz : P.mulVec z.ofLp = r.ofLp := symmetricSecantProjection_mulVec r z hz
  have hD : D.IsSymm := hC.sub hP
  have hDz : D.mulVec z.ofLp = 0 := by
    -- The residual lies in the tangent space of the feasible affine set.
    calc
      D.mulVec z.ofLp = C.mulVec z.ofLp - P.mulVec z.ofLp := by
        simp [D, Matrix.sub_mulVec]
      _ = r.ofLp - r.ofLp := by
            rw [hCz, hPz]
      _ = 0 := by
            simp
  have hOrth :
      dotProduct (matrixEntryVector P) (matrixEntryVector D) = 0 := by
    -- The mixed Frobenius term is exactly the trace certificate from the previous lemma.
    simpa [P, matrixEntryVector_dotProduct] using
      symmetricSecantProjection_trace_mul_eq_zero (r := r) (z := z) hD hDz
  have hInner :
      inner ℝ (matrixEntryVector P) (matrixEntryVector D) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using hOrth
  have hVecAdd :
      matrixEntryVector (P + D) = matrixEntryVector P + matrixEntryVector D := by
    -- Entry vectorization is linear in the matrix argument.
    ext ij
    simp [matrixEntryVector]
  have hPyth :
      ‖matrixEntryVector (P + D)‖ * ‖matrixEntryVector (P + D)‖ =
        ‖matrixEntryVector P‖ * ‖matrixEntryVector P‖ +
          ‖matrixEntryVector D‖ * ‖matrixEntryVector D‖ := by
    -- Orthogonality in the entry vectorization gives the Pythagorean identity.
    rw [hVecAdd]
    simpa using
      norm_add_sq_eq_norm_sq_add_norm_sq_real (x := matrixEntryVector P) (y := matrixEntryVector D)
        hInner
  have hSq :
      ‖C‖ * ‖C‖ = ‖P‖ * ‖P‖ + ‖D‖ * ‖D‖ := by
    -- Translate the vectorized Pythagorean identity back to the Frobenius norm.
    calc
      ‖C‖ * ‖C‖ = ‖P + D‖ * ‖P + D‖ := by
        have hSplit : C = P + D := by
          simp [P, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hSplit]
      _ = ‖matrixEntryVector (P + D)‖ * ‖matrixEntryVector (P + D)‖ := by
            rw [frobeniusNorm_eq_matrixEntryVectorNorm]
      _ = ‖matrixEntryVector P‖ * ‖matrixEntryVector P‖ +
            ‖matrixEntryVector D‖ * ‖matrixEntryVector D‖ := hPyth
      _ = ‖P‖ * ‖P‖ + ‖D‖ * ‖D‖ := by
            rw [frobeniusNorm_eq_matrixEntryVectorNorm, frobeniusNorm_eq_matrixEntryVectorNorm]
  have hDsqNonneg : 0 ≤ ‖D‖ * ‖D‖ := by
    nlinarith [norm_nonneg D]
  have hLeSq : ‖P‖ * ‖P‖ ≤ ‖C‖ * ‖C‖ := by
    nlinarith [hSq, hDsqNonneg]
  -- The squared comparison upgrades to the norm comparison because both norms are nonnegative.
  nlinarith [hLeSq, norm_nonneg P, norm_nonneg C]

/-- Helper for Chapter05 Theorem 5.1.10: conjugating the PSB correction by `M` produces the
canonical symmetric secant projection in the transported coordinates. -/
lemma conjugatedSymmetrizedBroydenLimit_eq_symmetricSecantProjection
    (B M : MatrixN) (c s y : Point)
    (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    M * (symmetrizedBroydenLimit B s y c - B) * M =
      symmetricSecantProjection
        (WithLp.toLp 2 (M.mulVec (y - Matrix.toEuclideanLin B s).ofLp))
        (WithLp.toLp 2 (M.mulVec c.ofLp)) := by
  let r : Point := y - Matrix.toEuclideanLin B s
  let z : Point := WithLp.toLp 2 (M.mulVec c.ofLp)
  let u : Point := WithLp.toLp 2 (M.mulVec r.ofLp)
  have hVecMulC : Matrix.vecMul c M = M.mulVec c := by
    simpa [hM.eq] using Matrix.vecMul_transpose M c
  have hVecMulR : Matrix.vecMul r M = M.mulVec r := by
    simpa [hM.eq] using Matrix.vecMul_transpose M r
  have hCorrection :
      symmetrizedBroydenLimit B s y c - B =
        (dotProduct c s)⁻¹ • (Matrix.vecMulVec r c + Matrix.vecMulVec c r) -
          (dotProduct r s * (dotProduct c s)⁻¹ * (dotProduct c s)⁻¹) • Matrix.vecMulVec c c := by
    simp [symmetrizedBroydenLimit, r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hExpand :
      M * (symmetrizedBroydenLimit B s y c - B) * M =
        (dotProduct c s)⁻¹ • Matrix.vecMulVec (M.mulVec r) (Matrix.vecMul c M) +
          (dotProduct c s)⁻¹ • Matrix.vecMulVec (M.mulVec c) (Matrix.vecMul r M) -
          (dotProduct r s * (dotProduct c s)⁻¹ * (dotProduct c s)⁻¹) •
            Matrix.vecMulVec (M.mulVec c) (Matrix.vecMul c M) := by
    -- Expand the conjugated correction term term-by-term before rewriting the pairings.
    rw [hCorrection]
    simp [Matrix.mul_sub, sub_mul, Matrix.mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, mul_assoc, sub_eq_add_neg]
  have hzz : dotProduct z z = dotProduct c s := by
    simpa [z] using metricSecantVector_dotProductSelf M c s hM hMdet hMc
  have huz : dotProduct u z = dotProduct r s := by
    simpa [u, z, r] using metricResidual_dotProductSecantVector B M c s y hM hMdet hMc
  -- Expand the conjugated correction term-by-term and rewrite the scalar pairings through the
  -- transported secant vector `z = M c`.
  rw [hExpand, symmetricSecantProjection]
  rw [hzz, huz, hVecMulC, hVecMulR]
  simp [r, z, u, Matrix.mul_sub, sub_mul, Matrix.mul_add, add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hVecMulC, hVecMulR,
    sub_eq_add_neg, mul_assoc]

/-- Helper for Chapter05 Theorem 5.1.10: the PSB update is no farther than any feasible symmetric
competitor in the weighted Frobenius norm. -/
lemma symmetrizedBroydenLimit_weightedFrobenius_leAux
    (B M : MatrixN) (c s y : Point)
    (hB : B.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s)
    (Bhat : MatrixN)
    (hSymm : Bhat.IsSymm)
    (hsecant : satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y) :
    weightedFrobeniusNorm M (symmetrizedBroydenLimit B s y c - B) ≤
      weightedFrobeniusNorm M (Bhat - B) := by
  let z : Point := WithLp.toLp 2 (M.mulVec c.ofLp)
  let r : Point := WithLp.toLp 2 (M.mulVec (y - Matrix.toEuclideanLin B s).ofLp)
  let C : MatrixN := M * (Bhat - B) * M
  have hz : z ≠ 0 := by
    simpa [z] using metricSecantVector_ne_zero M c s hM hMdet hcs hMc
  have hBhatApply : Bhat.mulVec s.ofLp = y.ofLp :=
    satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp hsecant
  have hC : C.IsSymm := by
    -- Symmetry is preserved by subtracting symmetric matrices and conjugating by a symmetric `M`.
    dsimp [C]
    have hDiff : (Bhat - B).IsSymm := hSymm.sub hB
    rw [Matrix.IsSymm]
    simp [Matrix.transpose_mul, hM.eq, hDiff.eq, mul_assoc]
  have hCz : C.mulVec z.ofLp = r.ofLp := by
    -- Transport the feasible secant equation through the `M`-conjugation.
    have hMz : M.mulVec (M.mulVec c) = s := metricSecantVector_mulVec M c s hMdet hMc
    calc
      C.mulVec z.ofLp = ((M * (Bhat - B)) * M).mulVec (M.mulVec c) := by
        rfl
      _ = (M * (Bhat - B)).mulVec (M.mulVec (M.mulVec c)) := by
            exact (Matrix.mulVec_mulVec (M.mulVec c) (M * (Bhat - B)) M).symm
      _ = (M * (Bhat - B)).mulVec s.ofLp := by
            rw [hMz]
      _ = M.mulVec ((Bhat - B).mulVec s.ofLp) := by
            simpa using Matrix.mulVec_mulVec s.ofLp M (Bhat - B)
      _ = M.mulVec (y.ofLp - B.mulVec s.ofLp) := by
            simp [Matrix.sub_mulVec, hBhatApply]
      _ = r.ofLp := by
            simp [r]
  have hProjection :
      M * (symmetrizedBroydenLimit B s y c - B) * M = symmetricSecantProjection r z :=
    conjugatedSymmetrizedBroydenLimit_eq_symmetricSecantProjection B M c s y hM hMdet hMc
  have hCompare :
      ‖symmetricSecantProjection r z‖ ≤ ‖C‖ :=
    symmetricSecantProjection_frobenius_le (r := r) (z := z) hz hC hCz
  -- Rewrite both transported corrections back into the weighted objective.
  simpa [C, r, z, weightedFrobeniusNorm_eq, hProjection] using hCompare

/-- Chapter05 Theorem 5.1.10: if `B` is symmetric, `M` is symmetric and nonsingular,
`0 < dotProduct c s`, and `M.mulVec c = (M⁻¹).mulVec s`, then `symmetrizedBroydenLimit B s y c`
is feasible for the secant and symmetry constraints and is the unique minimizer of the weighted
Frobenius change `weightedFrobeniusNorm M (Bhat - B)` among symmetric matrices `Bhat`
satisfying the Hessian-form quasi-Newton equation `Bhat.mulVec s = y`. -/
theorem symmetrizedBroydenLimit_isUniqueWeightedFrobeniusMinimizer
    (B M : MatrixN) (c s y : Point)
    (hB : B.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    let Bbar := symmetrizedBroydenLimit B s y c
    let objective : MatrixN → ℝ := fun Bhat ↦ weightedFrobeniusNorm M (Bhat - B)
    let feasibleSet : Set MatrixN :=
      {Bhat | Bhat.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y}
    (Bbar.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Bbar.toEuclideanLin s y) ∧
      IsMinOn objective feasibleSet Bbar ∧
      ∀ Bhat : MatrixN, Bhat ∈ feasibleSet →
        IsMinOn objective feasibleSet Bhat → Bhat = Bbar := by
  let Bbar := symmetrizedBroydenLimit B s y c
  let objective : MatrixN → ℝ := fun Bhat ↦ weightedFrobeniusNorm M (Bhat - B)
  let feasibleSet : Set MatrixN :=
    {Bhat | Bhat.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y}
  have hcs0 : dotProduct c s ≠ 0 := ne_of_gt hcs
  have hFeasible : Bbar.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Bbar.toEuclideanLin s y := by
    -- Package the existing symmetry and secant owners once so the minimization proof stays flat.
    refine ⟨?_, ?_⟩
    · simpa [Bbar] using symmetrizedBroydenLimit_isSymm hB s y c
    · simpa [Bbar, satisfiesQuasiNewtonEquationHessianForm] using
        symmetrizedBroydenLimit_mulVec B s y c hcs0
  have hMin : IsMinOn objective feasibleSet Bbar := by
    -- The comparison lemma gives the pointwise minimization inequality on the feasible set.
    refine isMinOn_iff.mpr ?_
    intro Bhat hBhat
    exact symmetrizedBroydenLimit_weightedFrobenius_leAux
      B M c s y hB hM hMdet hcs hMc Bhat hBhat.1 hBhat.2
  refine ⟨hFeasible, hMin, ?_⟩
  intro Bhat hBhatFeasible hBhatMin
  by_contra hne
  have hEqNorm : objective Bhat = objective Bbar :=
    le_antisymm (hBhatMin hFeasible) (hMin hBhatFeasible)
  have hMidFeasible :
      (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • Bbar).IsSymm ∧
        satisfiesQuasiNewtonEquationHessianForm
          (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • Bbar).toEuclideanLin) s y) := by
    constructor
    · -- Symmetry is preserved by affine combinations.
      exact (hBhatFeasible.1.smul (1 / 2 : ℝ)).add (hFeasible.1.smul (1 / 2 : ℝ))
    · -- The feasible secant set is affine, so midpoint competitors remain feasible.
      rw [satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff]
      calc
        (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • Bbar).mulVec s.ofLp)
            = (1 / 2 : ℝ) • Bhat.mulVec s.ofLp + (1 / 2 : ℝ) • Bbar.mulVec s.ofLp := by
                simp [Matrix.add_mulVec, Matrix.smul_mulVec]
        _ = (1 / 2 : ℝ) • y.ofLp + (1 / 2 : ℝ) • y.ofLp := by
              rw [satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp hBhatFeasible.2,
                satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp hFeasible.2]
        _ = y.ofLp := by
              ext i
              simp
              ring
  have hMidLt : objective (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • Bbar)) < objective Bhat := by
    -- Equal objective values force strict midpoint descent unless the two minimizers coincide.
    simpa [objective] using
      weightedFrobeniusNorm_midpoint_lt_of_distinct M Bhat Bbar B hMdet hEqNorm hne
  have hMidGe : objective Bhat ≤ objective (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • Bbar)) :=
    hBhatMin hMidFeasible
  exact (lt_irrefl _ <| lt_of_lt_of_le hMidLt hMidGe)

/-- Under the theorem hypotheses, `symmetrizedBroydenLimit B s y c` minimizes
`weightedFrobeniusNorm M (Bhat - B)` among symmetric matrices satisfying the canonical
Hessian-form secant equation. -/
theorem symmetrizedBroydenLimit_weightedFrobenius_le
    (B M : MatrixN) (c s y : Point)
    (hB : B.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s)
    (Bhat : MatrixN)
    (hSymm : Bhat.IsSymm)
    (hsecant : satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y) :
    weightedFrobeniusNorm M (symmetrizedBroydenLimit B s y c - B) ≤
      weightedFrobeniusNorm M (Bhat - B) := by
  -- Reuse the dedicated transported comparison lemma proved for the main theorem.
  simpa using
    symmetrizedBroydenLimit_weightedFrobenius_leAux
      B M c s y hB hM hMdet hcs hMc Bhat hSymm hsecant

/-- Among feasible symmetric matrices, equality in the weighted Frobenius objective forces
`Bhat = symmetrizedBroydenLimit B s y c`. -/
theorem symmetrizedBroydenLimit_weightedFrobenius_eq_imp
    (B M : MatrixN) (c s y : Point)
    (hB : B.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s)
    (Bhat : MatrixN) (hSymm : Bhat.IsSymm)
    (hsecant : satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y)
    (heq :
      weightedFrobeniusNorm M (Bhat - B) =
        weightedFrobeniusNorm M (symmetrizedBroydenLimit B s y c - B)) :
    Bhat = symmetrizedBroydenLimit B s y c := by
  let Bbar := symmetrizedBroydenLimit B s y c
  let objective : MatrixN → ℝ := fun A ↦ weightedFrobeniusNorm M (A - B)
  let feasibleSet : Set MatrixN :=
    {A | A.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm A.toEuclideanLin s y}
  have hMain :=
    symmetrizedBroydenLimit_isUniqueWeightedFrobeniusMinimizer B M c s y hB hM hMdet hcs hMc
  have hBhatMin : IsMinOn objective feasibleSet Bhat := by
    -- Equality with the PSB objective value upgrades the feasible competitor to another minimizer.
    refine isMinOn_iff.mpr ?_
    intro A hA
    calc
      objective Bhat = objective Bbar := by
        simpa [objective, Bbar] using heq
      _ ≤ objective A := by
            simpa [Bbar, objective, feasibleSet] using hMain.2.1 hA
  -- The uniqueness clause of the main theorem now forces coincidence with the PSB update.
  exact hMain.2.2 Bhat (by simpa [feasibleSet] using And.intro hSymm hsecant) hBhatMin

/-- Under the theorem hypotheses, `symmetrizedBroydenLimit B s y c` is a minimizer of
`weightedFrobeniusNorm M (Bhat - B)` on the symmetric Hessian-form secant feasible set. -/
theorem symmetrizedBroydenLimit_isMinOn_weightedFrobeniusSymmetricSecantSet
    (B M : MatrixN) (c s y : Point)
    (hB : B.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hcs : 0 < dotProduct c s) (hMc : M.mulVec c = (M⁻¹).mulVec s) :
    let Bbar := symmetrizedBroydenLimit B s y c
    let objective : MatrixN → ℝ := fun Bhat ↦ weightedFrobeniusNorm M (Bhat - B)
    let feasibleSet : Set MatrixN :=
      {Bhat | Bhat.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Bhat.toEuclideanLin s y}
    IsMinOn objective feasibleSet Bbar := by
  -- The minimizer statement is the middle conjunct of the main uniqueness theorem.
  simpa using
    (symmetrizedBroydenLimit_isUniqueWeightedFrobeniusMinimizer
      B M c s y hB hM hMdet hcs hMc).2.1
