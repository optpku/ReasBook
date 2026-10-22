/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.RectangularStochastic

public section

open scoped BigOperators

namespace Matrix

/-- The matrix obtained by normalizing each column of `K` by its column sum. -/
noncomputable def columnNormalized {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i j ↦ K i j / ∑ i', K i' j

/-- The entrywise normalization formula for `Matrix.columnNormalized`. -/
theorem columnNormalized_apply {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) (i : ι) (j : κ) :
    columnNormalized K i j = K i j / ∑ i', K i' j := by
  rfl

/-- If every column sum of `K` is nonzero, then every column of `Matrix.columnNormalized K`
sums to `1`. -/
theorem columnNormalized_sum_col_eq_one {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) (hcol : ∀ j, ∑ i, K i j ≠ 0) (j : κ) :
    ∑ i, columnNormalized K i j = 1 := by
  -- Pull the common denominator out of the column sum and cancel it.
  simp_rw [columnNormalized_apply, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simpa [div_eq_mul_inv] using
    (div_self (hcol j) : (∑ i, K i j) / (∑ i, K i j) = (1 : ℝ))

/-- A rectangular real matrix whose columns each sum to `1` preserves total mass under
`Matrix.mulVec`. -/
theorem sum_mulVec_eq_sum_of_sum_col_eq_one {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℝ) (f : κ → ℝ) (hS : ∀ j, ∑ i, S i j = 1) :
    ∑ i, (S *ᵥ f) i = ∑ j, f j := by
  -- Swap the finite sums so each column-sum hypothesis can be applied directly.
  simp_rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_mul, hS j, one_mul]

/-- If every column sum of `K` is nonzero, then `Matrix.columnNormalized K` preserves the total
mass of every real vector under `Matrix.mulVec`. -/
theorem columnNormalized_sum_mulVec_eq_sum {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) (hcol : ∀ j, ∑ i, K i j ≠ 0) (f : κ → ℝ) :
    ∑ i, (columnNormalized K *ᵥ f) i = ∑ j, f j := by
  exact sum_mulVec_eq_sum_of_sum_col_eq_one (S := columnNormalized K) (f := f)
    (fun j ↦ columnNormalized_sum_col_eq_one K hcol j)

/-- Nonnegative entries and positive column sums make `Matrix.columnNormalized K` a rectangular
column-stochastic matrix. -/
theorem columnNormalized_isColStochasticRect {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) (hK_nonneg : ∀ i j, 0 ≤ K i j)
    (hcol_pos : ∀ j, 0 < ∑ i, K i j) :
    (columnNormalized K).IsColStochasticRect := by
  rw [isColStochasticRect_iff]
  constructor
  · intro i j
    rw [columnNormalized_apply]
    exact div_nonneg (hK_nonneg i j) (le_of_lt (hcol_pos j))
  · intro j
    exact columnNormalized_sum_col_eq_one K (fun j ↦ ne_of_gt (hcol_pos j)) j

end Matrix
