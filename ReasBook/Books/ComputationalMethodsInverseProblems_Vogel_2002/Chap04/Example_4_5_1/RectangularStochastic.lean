/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.Matrix.Stochastic

public section

open scoped BigOperators

namespace Matrix

/-- A rectangular real matrix is column stochastic when its entries are nonnegative and each
column sums to `1`. -/
def IsColStochasticRect {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) : Prop :=
  (∀ i j, 0 ≤ K i j) ∧ ∀ j, ∑ i, K i j = 1

/-- The defining conditions for `Matrix.IsColStochasticRect`. -/
theorem isColStochasticRect_iff {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix ι κ ℝ) :
    K.IsColStochasticRect ↔ (∀ i j, 0 ≤ K i j) ∧ ∀ j, ∑ i, K i j = 1 :=
  Iff.rfl

/-- Every entry of a rectangular column-stochastic matrix is nonnegative. -/
theorem IsColStochasticRect.nonneg {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {K : Matrix ι κ ℝ} (hK : K.IsColStochasticRect) (i : ι) (j : κ) : 0 ≤ K i j :=
  hK.1 i j

/-- Every column of a rectangular column-stochastic matrix sums to `1`. -/
theorem IsColStochasticRect.sum_col_eq_one {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {K : Matrix ι κ ℝ} (hK : K.IsColStochasticRect) (j : κ) : ∑ i, K i j = 1 :=
  hK.2 j

/-- In the square case, `Matrix.IsColStochasticRect` is exactly mathlib's canonical
`Matrix.colStochastic` predicate. -/
theorem isColStochasticRect_iff_mem_colStochastic {n : Type u} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) :
    K.IsColStochasticRect ↔ K ∈ Matrix.colStochastic ℝ n := by
  rw [isColStochasticRect_iff, Matrix.mem_colStochastic_iff_sum]

/-- A square rectangular column-stochastic matrix is column stochastic in mathlib's canonical
sense. -/
theorem IsColStochasticRect.mem_colStochastic {n : Type u} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.IsColStochasticRect) :
    K ∈ Matrix.colStochastic ℝ n :=
  (isColStochasticRect_iff_mem_colStochastic K).mp hK

/-- Applying a rectangular column-stochastic matrix to a point of `stdSimplex ℝ κ` produces a
point of `stdSimplex ℝ ι`. -/
theorem IsColStochasticRect.mulVec_mem_stdSimplex
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {K : Matrix ι κ ℝ} {f : κ → ℝ} (hK : K.IsColStochasticRect) (hf : f ∈ stdSimplex ℝ κ) :
    K *ᵥ f ∈ stdSimplex ℝ ι := by
  refine ⟨?_, ?_⟩
  · intro i
    -- Each entry of `K *ᵥ f` is a finite sum of nonnegative terms.
    suffices hsum : 0 ≤ ∑ j, K i j * f j by
      simpa only [Matrix.mulVec, dotProduct] using hsum
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hK.nonneg i j) (hf.1 j)
  · -- Column normalization preserves the total mass of a simplex point.
    simp_rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, K i j * f j = ∑ j, (∑ i, K i j) * f j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [← Finset.sum_mul]
      _ = ∑ j, f j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hK.sum_col_eq_one j, one_mul]
      _ = 1 := hf.2

end Matrix
