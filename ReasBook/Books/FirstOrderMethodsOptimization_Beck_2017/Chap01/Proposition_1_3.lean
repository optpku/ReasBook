/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_34

-- Declarations for this item will be appended below by the statement pipeline.

namespace Matrix

open scoped Matrix

section

variable {m n : ℕ}

/-- The real-valued maximum absolute column sum of a real matrix. This is the source-facing
quantity appearing in Proposition 1.3. -/
def maxAbsColumnSum (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).sup fun j : Fin n ↦
    ∑ i : Fin m, ‖A i j‖₊ : NNReal)

@[simp] theorem maxAbsColumnSum_eq_sup (A : Matrix (Fin m) (Fin n) ℝ) :
    maxAbsColumnSum A =
      ((Finset.univ : Finset (Fin n)).sup fun j : Fin n ↦
        ∑ i : Fin m, ‖A i j‖₊ : NNReal) := rfl

-- Proof sketch: specialize the chapter owner `‖A‖[a,b]` from Definition 1.34 to `a = b = 1`.
-- The upper bound expands `A *ᵥ x` coordinatewise and uses the triangle inequality in the `ℓ¹`
-- norm; the reverse inequality tests the induced operator on a standard basis vector for a column
-- attaining the finite supremum.
/-- Canonical `NNReal` companion for Proposition 1.3 (`bridge/view`): the nonnegative operator
norm of `(A.toLpLin 1 1).toContinuousLinearMap` is the maximum absolute column sum. -/
theorem induced_l1_opNNNorm_eq_max_column_sum (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(A.toLpLin 1 1).toContinuousLinearMap‖₊ =
      ((Finset.univ : Finset (Fin n)).sup fun j : Fin n ↦
        ∑ i : Fin m, ‖A i j‖₊) := by
  -- Work with the nonnegative operator norm so positivity is built into the bounds.
  let φ : WithLp 1 (Fin n → ℝ) →L[ℝ] WithLp 1 (Fin m → ℝ) :=
    (A.toLpLin 1 1).toContinuousLinearMap
  let colSum : Fin n → NNReal := fun j ↦ ∑ i : Fin m, ‖A i j‖₊
  let M : NNReal := (Finset.univ : Finset (Fin n)).sup colSum
  -- Expand the `ℓ¹` norm of `A *ᵥ x`, apply the triangle inequality rowwise,
  -- and then factor out the maximal column sum.
  have h_upper : ∀ x : WithLp 1 (Fin n → ℝ), ‖φ x‖₊ ≤ M * ‖x‖₊ := by
    intro x
    calc
      ‖φ x‖₊ = ∑ i : Fin m, ‖(A *ᵥ x.ofLp) i‖₊ := by
        simp [φ, PiLp.nnnorm_eq_of_L1]
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, ‖A i j * x.ofLp j‖₊ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa [Matrix.mulVec] using
          nnnorm_sum_le (Finset.univ : Finset (Fin n)) (fun j : Fin n ↦ A i j * x.ofLp j)
      _ = ∑ j : Fin n, (∑ i : Fin m, ‖A i j‖₊) * ‖x.ofLp j‖₊ := by
        rw [Finset.sum_comm]
        congr with j
        rw [Finset.sum_mul]
        congr with i
        simp
      _ ≤ ∑ j : Fin n, M * ‖x.ofLp j‖₊ := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have h_col_le : colSum j ≤ M := by
          simpa [M] using
            (Finset.univ : Finset (Fin n)).le_sup (by simp : j ∈ (Finset.univ : Finset (Fin n)))
        simpa using mul_le_mul_left h_col_le ‖x.ofLp j‖₊
      _ = M * ‖x‖₊ := by
        rw [← Finset.mul_sum]
        simp [PiLp.nnnorm_eq_of_L1]
  -- Test the operator on a standard basis vector to recover each column sum.
  have h_lower : M ≤ ‖φ‖₊ := by
    refine Finset.sup_le_iff.mpr ?_
    intro j hj
    let e : WithLp 1 (Fin n → ℝ) := WithLp.toLp 1 (Pi.single j (1 : ℝ))
    have h_image : φ e = WithLp.toLp 1 (A.col j) := by
      simpa [e, φ, Matrix.mulVec_single_one] using
        (Matrix.toLpLin_toLp 1 1 A (Pi.single j (1 : ℝ)))
    have h_col : ‖WithLp.toLp 1 (A.col j)‖₊ = ∑ i : Fin m, ‖A i j‖₊ := by
      simp [PiLp.nnnorm_eq_of_L1, Matrix.col]
    have h_basis : ‖e‖₊ = 1 := by
      simp [e]
    calc
      ∑ i : Fin m, ‖A i j‖₊ = ‖φ e‖₊ := by
        rw [h_image, h_col]
      _ ≤ ‖φ‖₊ * ‖e‖₊ := ContinuousLinearMap.le_opNNNorm φ e
      _ = ‖φ‖₊ := by
        rw [h_basis, mul_one]
  -- The upper and lower bounds identify the exact `ℓ¹` operator norm.
  exact le_antisymm (ContinuousLinearMap.opNNNorm_le_bound φ M h_upper) h_lower

/-- Proposition 1.3 (`source-facing`; `core/canonical` owner: `Matrix.toLpLin`; `bridge/view`:
`induced_l1_opNNNorm_eq_max_column_sum`): the induced `ℓ¹` matrix norm `‖A‖[1,1]` of a real
matrix is the maximum absolute column sum. -/
theorem induced_l1_norm_eq_max_column_sum (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖[1,1] = maxAbsColumnSum A := by
  have h_eq : ‖(A.toLpLin 1 1).toContinuousLinearMap‖₊ =
      ((Finset.univ : Finset (Fin n)).sup fun j : Fin n ↦
        ∑ i : Fin m, ‖A i j‖₊) :=
    induced_l1_opNNNorm_eq_max_column_sum A
  simpa [maxAbsColumnSum] using congrArg (fun t : NNReal ↦ (t : ℝ)) h_eq

end

end Matrix
