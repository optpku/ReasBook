/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3

open Matrix

noncomputable section

-- Semantic recall: this file reuses the Chapter 1 Frobenius norm owner together with the
-- canonical `Matrix.PosDef` API. It keeps the reported `3 × 3` data and the source-stated
-- concrete consequences explicit, without rebuilding the previous modified-factorization setup
-- locally.

section

local notation "Matrix3" => Matrix (Fin 3) (Fin 3) ℝ

/-- Chapter03 Example 3.3.3 (1): the reported value of `β²` is `1.061`. -/
def chapter03Example333ReportedBetaSq : ℝ :=
  (1061 : ℝ) / 1000

/-- The reported constant `β²` is the rational value `1061 / 1000`. -/
@[simp]
theorem chapter03Example333ReportedBetaSq_def :
    chapter03Example333ReportedBetaSq = (1061 : ℝ) / 1000 :=
  rfl

/-- Chapter03 Example 3.3.3 (2): the concrete matrix `G_k` from formula `(3.3.15)`. -/
def chapter03Example333InputMatrix : Matrix3 :=
  Matrix.of fun i j ↦
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => 2
    | 1, 0 => 1
    | 1, 1 => 1 + (1 / (10 : ℝ) ^ (20 : ℕ))
    | 1, 2 => 3
    | 2, 0 => 2
    | 2, 1 => 3
    | 2, 2 => 1
    | _, _ => 0

/-- The lower-triangular factor `L` reported in Example 3.3.3. -/
def chapter03Example333ReportedL : Matrix3 :=
  Matrix.of fun i j ↦
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 0
    | 0, 2 => 0
    | 1, 0 => (2652 : ℝ) / 10000
    | 1, 1 => 1
    | 1, 2 => 0
    | 2, 0 => (5303 : ℝ) / 10000
    | 2, 1 => (4295 : ℝ) / 10000
    | 2, 2 => 1
    | _, _ => 0

/-- The diagonal matrix `D` reported in Example 3.3.3. -/
def chapter03Example333ReportedD : Matrix3 :=
  Matrix.diagonal fun i ↦
    match i.1 with
    | 0 => (3771 : ℝ) / 1000
    | 1 => (5750 : ℝ) / 1000
    | 2 => (1121 : ℝ) / 1000
    | _ => 0

/-- The diagonal correction matrix `E_k` reported in Example 3.3.3. -/
def chapter03Example333ReportedE : Matrix3 :=
  Matrix.diagonal fun i ↦
    match i.1 with
    | 0 => (2771 : ℝ) / 1000
    | 1 => (5016 : ℝ) / 1000
    | 2 => (2243 : ℝ) / 1000
    | _ => 0

/-- The corrected matrix `Ḡ_k = G_k + E_k` attached to the reported data of Example 3.3.3. -/
def chapter03Example333ReportedCorrectedMatrix : Matrix3 :=
  chapter03Example333InputMatrix + chapter03Example333ReportedE

/-- The concrete correction satisfies `Ḡ_k - G_k = E_k`. -/
@[simp] theorem chapter03Example333ReportedCorrectedMatrix_sub_inputMatrix :
    chapter03Example333ReportedCorrectedMatrix - chapter03Example333InputMatrix =
      chapter03Example333ReportedE := by
  funext i
  funext j
  simp [chapter03Example333ReportedCorrectedMatrix]

/-
Source note on the rounded factors: the next part of the example reports `L`, `D`, and the
diagonal correction matrix `E_k`. This file records that concrete data explicitly in
`chapter03Example333ReportedL`, `chapter03Example333ReportedD`, and
`chapter03Example333ReportedE`, without adding an extra rounded-factorization error theorem not
stated in the book.
-/

/-- Chapter03 Example 3.3.3 (3): for the reported correction matrix,
`‖Ḡ_k - G_k‖_F = ‖E_k‖_F`. -/
theorem chapter03Example333_reportedCorrectionFrobeniusNorm_eq :
    ‖chapter03Example333ReportedCorrectedMatrix - chapter03Example333InputMatrix‖_F =
      ‖chapter03Example333ReportedE‖_F := by
  simp

/-- Helper for Chapter03 Example 3.3.3: the squared Frobenius norm of the reported
diagonal correction has the exact rational value coming from its three diagonal entries. -/
lemma chapter03Example333_reportedCorrectionFrobeniusNorm_sq :
    ‖chapter03Example333ReportedE‖_F ^ (2 : ℕ) = (37869746 : ℝ) / 1000000 := by
  -- Expand the Frobenius norm into the sum of squares of the diagonal entries.
  simp [chapter03Example333ReportedE, Matrix.frobenius_norm_def, Fin.sum_univ_three]
  have hsum :
      (2771 / 1000 : ℝ) ^ (2 : ℕ) + (5016 / 1000 : ℝ) ^ (2 : ℕ) +
          (2243 / 1000 : ℝ) ^ (2 : ℕ) =
        (18934873 : ℝ) / 500000 := by
    norm_num
  rw [hsum]
  have hnonneg : 0 ≤ (18934873 : ℝ) / 500000 := by
    norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
  norm_num

/-- Chapter03 Example 3.3.3 (4): the Frobenius norm of the concrete correction
`Ḡ_k - G_k` is reported by the rounded value `6154 / 1000 = 6.154`. -/
theorem chapter03Example333_reportedCorrectionFrobeniusNorm_rounded :
    |‖chapter03Example333ReportedCorrectedMatrix - chapter03Example333InputMatrix‖_F -
      (6154 : ℝ) / 1000| ≤
      (1 : ℝ) / 2000 := by
  -- Reduce the estimate to the reported diagonal correction matrix.
  rw [chapter03Example333_reportedCorrectionFrobeniusNorm_eq]
  have hsq := chapter03Example333_reportedCorrectionFrobeniusNorm_sq
  have hnorm :
      ‖chapter03Example333ReportedE‖_F =
        ((18934873 : ℝ) / 500000) ^ (1 / (2 : ℝ)) := by
    simp [chapter03Example333ReportedE, Matrix.frobenius_norm_def, Fin.sum_univ_three]
    norm_num
  have hnonneg : 0 ≤ ‖chapter03Example333ReportedE‖_F := by
    rw [hnorm]
    apply Real.rpow_nonneg
    norm_num
  have hlower_sq :
      ((12307 : ℝ) / 2000) ^ (2 : ℕ) ≤ ‖chapter03Example333ReportedE‖_F ^ (2 : ℕ) := by
    rw [hsq]
    norm_num
  have hupper_sq :
      ‖chapter03Example333ReportedE‖_F ^ (2 : ℕ) ≤ ((12309 : ℝ) / 2000) ^ (2 : ℕ) := by
    rw [hsq]
    norm_num
  have hlower : (12307 : ℝ) / 2000 ≤ ‖chapter03Example333ReportedE‖_F := by
    nlinarith
  have hupper : ‖chapter03Example333ReportedE‖_F ≤ (12309 : ℝ) / 2000 := by
    nlinarith
  -- These scalar bounds are exactly the `± 0.0005` enclosure around `6.154`.
  rw [abs_le]
  constructor <;> nlinarith

/-- Helper for Chapter03 Example 3.3.3: the rational core of the corrected matrix keeps the
reported rounded entries and drops only the tiny `10^-20` diagonal perturbation. -/
def chapter03Example333ReportedCorrectedMatrixCore : Matrix3 :=
  Matrix.of fun i j ↦
    match i.1, j.1 with
    | 0, 0 => (3771 : ℝ) / 1000
    | 0, 1 => 1
    | 0, 2 => 2
    | 1, 0 => 1
    | 1, 1 => (6016 : ℝ) / 1000
    | 1, 2 => 3
    | 2, 0 => 2
    | 2, 1 => 3
    | 2, 2 => (3243 : ℝ) / 1000
    | _, _ => 0

/-- Helper for Chapter03 Example 3.3.3: the remaining tiny positive diagonal perturbation in the
reported corrected matrix sits only in the `(1,1)` entry. -/
def chapter03Example333ReportedTinyDiagonalCorrection : Matrix3 :=
  Matrix.diagonal fun i ↦
    match i.1 with
    | 1 => 1 / (10 : ℝ) ^ (20 : ℕ)
    | _ => 0

/-- Helper for Chapter03 Example 3.3.3: the corrected matrix splits into the rational core plus
the tiny nonnegative diagonal remainder. -/
theorem chapter03Example333_reportedCorrectedMatrix_decomposition :
    chapter03Example333ReportedCorrectedMatrix =
      chapter03Example333ReportedCorrectedMatrixCore +
        chapter03Example333ReportedTinyDiagonalCorrection := by
  -- Check the explicit `3 × 3` entries one by one.
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chapter03Example333ReportedCorrectedMatrix,
      chapter03Example333InputMatrix, chapter03Example333ReportedE,
      chapter03Example333ReportedCorrectedMatrixCore,
      chapter03Example333ReportedTinyDiagonalCorrection]

/-- Helper for Chapter03 Example 3.3.3: the rational core is symmetric. -/
theorem chapter03Example333_reportedCorrectedMatrixCore_isSymm :
    chapter03Example333ReportedCorrectedMatrixCore.IsSymm := by
  -- The core is the explicit symmetric `3 × 3` matrix recorded by the example.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chapter03Example333ReportedCorrectedMatrixCore]

/-- Helper for Chapter03 Example 3.3.3: if all three coordinates of a vector in `Fin 3 → ℝ`
vanish, then the vector itself is zero. -/
lemma chapter03Example333_fin3_eq_zero_of_coords {x : Fin 3 → ℝ}
    (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) :
    x = 0 := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Helper for Chapter03 Example 3.3.3: the rational core quadratic form admits the exact
two-step square-completion decomposition that mirrors the source's modified-factorization route. -/
lemma chapter03Example333_reportedCorrectedMatrixCore_quadraticForm_split
    (x : Fin 3 → ℝ) :
    dotProduct x (chapter03Example333ReportedCorrectedMatrixCore.mulVec x) =
      (3771 / 1000 : ℝ) *
          (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) +
        ((2710792 : ℝ) / 471375) *
          (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) +
        ((47511304 : ℝ) / 42356125) * (x 2) ^ (2 : ℕ) := by
  -- Expand the explicit `3 × 3` quadratic form and complete squares algebraically.
  simp [chapter03Example333ReportedCorrectedMatrixCore, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, pow_two]
  ring

/-- Helper for Chapter03 Example 3.3.3: the rational core already has a strictly positive
quadratic form on every nonzero vector. -/
lemma chapter03Example333_reportedCorrectedMatrixCore_dotProduct_pos
    {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    0 < dotProduct x (chapter03Example333ReportedCorrectedMatrixCore.mulVec x) := by
  -- Rewrite the quadratic form into the completed-square decomposition.
  rw [chapter03Example333_reportedCorrectedMatrixCore_quadraticForm_split]
  by_cases hx2 : x 2 = 0
  · by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        exact chapter03Example333_fin3_eq_zero_of_coords hx0 hx1 hx2
      have hterm0 :
          0 <
            (3771 / 1000 : ℝ) *
              (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := by
        have hsquare :
            0 <
              (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := by
          simpa [hx1, hx2] using sq_pos_of_ne_zero hx0
        nlinarith
      have hterm1 :
          0 ≤
            ((2710792 : ℝ) / 471375) *
              (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := by
        have hsquare :
            0 ≤ (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := sq_nonneg _
        nlinarith
      have hterm2 :
          0 ≤ ((47511304 : ℝ) / 42356125) * (x 2) ^ (2 : ℕ) := by
        have hsquare : 0 ≤ (x 2) ^ (2 : ℕ) := sq_nonneg _
        nlinarith
      nlinarith
    · have hterm0 :
          0 ≤
            (3771 / 1000 : ℝ) *
              (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := by
        have hsquare :
            0 ≤
              (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := sq_nonneg _
        nlinarith
      have hterm1 :
          0 <
            ((2710792 : ℝ) / 471375) *
              (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := by
        have hsquare :
            0 <
              (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := by
          simpa [hx2] using sq_pos_of_ne_zero hx1
        nlinarith
      have hterm2 :
          0 ≤ ((47511304 : ℝ) / 42356125) * (x 2) ^ (2 : ℕ) := by
        have hsquare : 0 ≤ (x 2) ^ (2 : ℕ) := sq_nonneg _
        nlinarith
      nlinarith
  · have hterm0 :
        0 ≤
          (3771 / 1000 : ℝ) *
            (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := by
      have hsquare :
          0 ≤
            (x 0 + (1000 / 3771 : ℝ) * x 1 + (2000 / 3771 : ℝ) * x 2) ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    have hterm1 :
        0 ≤
          ((2710792 : ℝ) / 471375) *
            (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := by
      have hsquare :
          0 ≤ (x 1 + ((1164125 : ℝ) / 2710792) * x 2) ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    have hterm2 :
        0 < ((47511304 : ℝ) / 42356125) * (x 2) ^ (2 : ℕ) := by
      have hsquare : 0 < (x 2) ^ (2 : ℕ) := sq_pos_of_ne_zero hx2
      nlinarith
    nlinarith

/-- Helper for Chapter03 Example 3.3.3: the rational core matrix is positive definite. -/
lemma chapter03Example333_reportedCorrectedMatrixCore_posDef :
    chapter03Example333ReportedCorrectedMatrixCore.PosDef := by
  -- Combine symmetry with strict positivity of the quadratic form on nonzero vectors.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · simpa [Matrix.isHermitian_iff_isSymm] using
      chapter03Example333_reportedCorrectedMatrixCore_isSymm
  · exact chapter03Example333_reportedCorrectedMatrixCore_dotProduct_pos hx

/-- Helper for Chapter03 Example 3.3.3: the tiny diagonal remainder is positive semidefinite,
so it can be added without destroying positive definiteness. -/
lemma chapter03Example333_reportedTinyDiagonalCorrection_posSemidef :
    chapter03Example333ReportedTinyDiagonalCorrection.PosSemidef := by
  -- The only nonzero diagonal entry is the positive scalar `10^-20`.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.isHermitian_iff_isSymm] using
      (by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [chapter03Example333ReportedTinyDiagonalCorrection] :
          chapter03Example333ReportedTinyDiagonalCorrection.IsSymm)
  · intro x
    simp [chapter03Example333ReportedTinyDiagonalCorrection, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 1)]

/-- Chapter03 Example 3.3.3 (5): the concrete corrected matrix `Ḡ_k = G_k + E_k` attached to
the reported data is positive definite. -/
theorem chapter03Example333_reportedCorrectedMatrix_posDef :
    chapter03Example333ReportedCorrectedMatrix.PosDef := by
  -- Prove positive definiteness on the rational core, then add the tiny nonnegative remainder.
  have hCore : chapter03Example333ReportedCorrectedMatrixCore.PosDef :=
    chapter03Example333_reportedCorrectedMatrixCore_posDef
  have hTiny : chapter03Example333ReportedTinyDiagonalCorrection.PosSemidef :=
    chapter03Example333_reportedTinyDiagonalCorrection_posSemidef
  have hSum :
      (chapter03Example333ReportedCorrectedMatrixCore +
        chapter03Example333ReportedTinyDiagonalCorrection).PosDef :=
    hCore.add_posSemidef hTiny
  simpa [chapter03Example333_reportedCorrectedMatrix_decomposition] using hSum

/-- The rounded factor product `L D Lᵀ` attached to the reported data of Example 3.3.3. -/
def chapter03Example333ReportedRoundedFactorProduct : Matrix3 :=
  chapter03Example333ReportedL * chapter03Example333ReportedD *
    Matrix.transpose chapter03Example333ReportedL

/- Chapter03 Example 3.3.3 (6): the source tail next invokes the preceding Algorithm 3.3.2
setup, where `Ḡ_k` denotes the corrected matrix family produced by the modified factorization.
Under that recalled setup, the source states that these corrected matrices admit a fixed uniform
condition-number bound: there exists `κ ≥ 0` such that `‖Ḡ_k‖ * ‖(Ḡ_k)⁻¹‖ ≤ κ` for all `k`.

This example file keeps that clause as prose recall rather than restating the full
Algorithm 3.3.2 hypotheses as a new standalone Lean theorem with the wrong generality.
-/

/- Chapter03 Example 3.3.3 (7): with the same Algorithm 3.3.2 setup, and with `s_k` the
corresponding modified-Newton search direction for the corrected matrices `Ḡ_k`, the source
obtains the descent estimate `(3.3.16)`:
`-((∇ f (x_k))ᵀ s_k) / ‖s_k‖ ≥ (1 / κ) * ‖∇ f (x_k)‖`.

This clause is likewise kept as prose recall, because its meaning depends on the previous
modified-factorization/search-direction setup rather than on an arbitrary family of vectors.
-/

/- Chapter03 Example 3.3.3 (8): combining the inexact line-search hypothesis `(2.5.19)` from the
preceding Chapter02 setup with the recalled descent estimate `(3.3.16)`, the source concludes
that the gradient sequence `∇ f (x_k)` converges to `0`.

This final tail is recorded as prose recall rather than as a free-standing generic theorem,
since the example cites earlier setup instead of restating all of its hypotheses locally.
-/

end

#print axioms chapter03Example333ReportedBetaSq
#print axioms chapter03Example333ReportedBetaSq_def
#print axioms chapter03Example333InputMatrix
#print axioms chapter03Example333ReportedL
#print axioms chapter03Example333ReportedD
#print axioms chapter03Example333ReportedE
#print axioms chapter03Example333ReportedCorrectedMatrix
#print axioms chapter03Example333ReportedCorrectedMatrix_sub_inputMatrix
#print axioms chapter03Example333ReportedRoundedFactorProduct
#print axioms chapter03Example333_reportedCorrectedMatrix_posDef
#print axioms chapter03Example333_reportedCorrectionFrobeniusNorm_rounded
