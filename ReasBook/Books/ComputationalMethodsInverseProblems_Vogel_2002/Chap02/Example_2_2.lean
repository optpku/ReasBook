/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_2.Instances

public section

open scoped Matrix.Norms.Frobenius

universe u v

namespace Matrix

/-- Example 2.2 (1). The Frobenius inner product on `Matrix m n ℝ` is
`∑ i, ∑ j, A i j * B i j`. -/
theorem frobeniusInner_eq_sum_mul
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A B : Matrix m n ℝ) :
    inner ℝ A B = ∑ i, ∑ j, A i j * B i j := by
  -- Express the Frobenius norm square through the entrywise sum of squares.
  have hentrySquares (C : Matrix m n ℝ) :
      ∑ i, ∑ j, ‖C i j‖ ^ (2 : ℝ) = ∑ i, ∑ j, (C i j) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [sq_abs]
  have hnormMulSelf (C : Matrix m n ℝ) :
      ‖C‖ * ‖C‖ = ∑ i, ∑ j, (C i j) ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ ∑ i, ∑ j, ‖C i j‖ ^ (2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro i _
      refine Finset.sum_nonneg ?_
      intro j _
      simpa [Real.rpow_natCast] using sq_nonneg ‖C i j‖
    -- Convert the Frobenius norm formula from `rpow (1/2)` to `sqrt`, then square it away.
    rw [Matrix.frobenius_norm_def]
    rw [← pow_two]
    rw [← Real.sqrt_eq_rpow (∑ i, ∑ j, ‖C i j‖ ^ (2 : ℝ))]
    rw [Real.sq_sqrt hnonneg, hentrySquares C]
  have hsumAdd :
      ∑ i, ∑ j, ((A + B) i j) ^ (2 : ℕ) =
        ∑ i, ∑ j, ((A i j) ^ (2 : ℕ) + 2 * (A i j * B i j) + (B i j) ^ (2 : ℕ)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.add_apply, pow_two]
    ring
  let sumSqA : ℝ := ∑ i, ∑ j, (A i j) ^ (2 : ℕ)
  let sumMul : ℝ := ∑ i, ∑ j, A i j * B i j
  let sumSqB : ℝ := ∑ i, ∑ j, (B i j) ^ (2 : ℕ)
  have hmiddle :
      ∑ i, ∑ j, 2 * (A i j * B i j) = 2 * sumMul := by
    dsimp [sumMul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
  have hsplit :
      ∑ i, ∑ j, ((A i j) ^ (2 : ℕ) + 2 * (A i j * B i j) + (B i j) ^ (2 : ℕ)) =
        sumSqA + 2 * sumMul + sumSqB := by
    dsimp [sumSqA, sumMul, sumSqB]
    simp_rw [Finset.sum_add_distrib]
    rw [hmiddle]
  -- Polarization reduces the inner product to norm squares, which now compute entrywise.
  calc
    inner ℝ A B = (‖A + B‖ * ‖A + B‖ - ‖A‖ * ‖A‖ - ‖B‖ * ‖B‖) / 2 := by
      simpa using real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two A B
    _ = (((∑ i, ∑ j, ((A + B) i j) ^ (2 : ℕ)) : ℝ) - sumSqA - sumSqB) / 2 := by
      rw [hnormMulSelf (A + B), hnormMulSelf A, hnormMulSelf B]
    _ = (sumSqA + 2 * sumMul + sumSqB - sumSqA - sumSqB) / 2 := by
      rw [hsumAdd, hsplit]
    _ = sumMul := by
      ring
    _ = ∑ i, ∑ j, A i j * B i j := rfl

/-- Example 2.2 (2). The induced Frobenius norm on `Matrix m n ℝ` is
`Real.sqrt (∑ i, ∑ j, (A i j)^2)`. -/
theorem frobeniusNorm_eq_sqrt_sum_sq
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, (A i j) ^ (2 : ℕ)) := by
  have hsum :
      ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) = ∑ i, ∑ j, (A i j) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [sq_abs]
  -- Rewrite the Frobenius norm through the upstream matrix norm formula and then convert to `sqrt`.
  calc
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := Matrix.frobenius_norm_def A
    _ = (∑ i, ∑ j, (A i j) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by rw [hsum]
    _ = Real.sqrt (∑ i, ∑ j, (A i j) ^ (2 : ℕ)) := by
      symm
      rw [Real.sqrt_eq_rpow]

end Matrix
