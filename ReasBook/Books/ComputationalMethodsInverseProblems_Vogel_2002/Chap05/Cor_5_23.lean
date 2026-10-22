/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_11.Toeplitz
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Theorem_5_22

public section

namespace Matrix

/-- Helper for Corollary 5.23: a wrapped diagonal entry of `Matrix.toeplitzByDiag n t`
depends only on whether the shift by `j` crosses the boundary of `Fin n`. -/
lemma toeplitzByDiag_wrappedDiagonal_split
    {n : ℕ} (t : ℤ → ℝ) (j k : Fin n) :
    toeplitzByDiag n t (k + j) k =
      if (k : ℕ) + (j : ℕ) < n then
        t ((j : ℕ) : ℤ)
      else
        t (((j : ℕ) : ℤ) - (n : ℤ)) := by
  -- Rewrite the shifted row index into its wrapped integer normal form.
  rw [toeplitzByDiag_apply, Fin.coe_int_add_eq_ite]
  by_cases hwrap : (k : ℕ) + (j : ℕ) < n
  · -- Before the wrap, the Toeplitz offset is exactly `j`.
    have hoffset : (((k : ℕ) : ℤ) + (j : ℕ) : ℤ) - (k : ℕ) = ((j : ℕ) : ℤ) := by
      omega
    simp [hwrap, hoffset]
  · -- After the wrap, one full copy of `n` has been subtracted from the offset.
    have hoffset :
        ((((k : ℕ) : ℤ) + (j : ℕ) : ℤ) - (n : ℤ)) - (k : ℕ) =
          ((j : ℕ) : ℤ) - (n : ℤ) := by
      omega
    simpa [hwrap] using congrArg t hoffset

/-- Helper for Corollary 5.23: summing a wrapped Toeplitz diagonal counts `n - j`
unwrapped entries and `j` wrapped entries. -/
lemma sum_toeplitzByDiag_wrappedDiagonal
    {n : ℕ} (t : ℤ → ℝ) (j : Fin n) :
    ∑ k : Fin n, toeplitzByDiag n t (k + j) k =
      (((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
        (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ))) := by
  -- Replace each wrapped diagonal entry by its two-case Toeplitz value.
  calc
    ∑ k : Fin n, toeplitzByDiag n t (k + j) k
        = ∑ k : Fin n,
            if (k : ℕ) + (j : ℕ) < n then
              t ((j : ℕ) : ℤ)
            else
              t (((j : ℕ) : ℤ) - (n : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact toeplitzByDiag_wrappedDiagonal_split t j k
    _ = Finset.sum (Finset.range n) (fun k ↦
          if k + (j : ℕ) < n then
            t ((j : ℕ) : ℤ)
          else
            t (((j : ℕ) : ℤ) - (n : ℤ))) := by
          rw [Fin.sum_univ_eq_sum_range fun k ↦
            if k + (j : ℕ) < n then
              t ((j : ℕ) : ℤ)
            else
              t (((j : ℕ) : ℤ) - (n : ℤ))]
    _ = Finset.sum (Finset.range (n - (j : ℕ)))
          (fun k ↦
            if k + (j : ℕ) < n then
              t ((j : ℕ) : ℤ)
            else
              t (((j : ℕ) : ℤ) - (n : ℤ))) +
          Finset.sum (Finset.range (j : ℕ))
            (fun k ↦
              if (n - (j : ℕ) + k) + (j : ℕ) < n then
                t ((j : ℕ) : ℤ)
              else
                t (((j : ℕ) : ℤ) - (n : ℤ))) := by
          -- Split the natural range at the unique wrap point `n - j`.
          let f : ℕ → ℝ := fun k ↦
            if k + (j : ℕ) < n then
              t ((j : ℕ) : ℤ)
            else
              t (((j : ℕ) : ℤ) - (n : ℤ))
          simpa [f, Nat.sub_add_cancel (Nat.le_of_lt j.2)] using
            (Finset.sum_range_add (f := f) (n - (j : ℕ)) (j : ℕ))
    _ = Finset.sum (Finset.range (n - (j : ℕ))) (fun _ ↦ t ((j : ℕ) : ℤ)) +
          Finset.sum (Finset.range (j : ℕ)) (fun _ ↦ t (((j : ℕ) : ℤ) - (n : ℤ))) := by
          -- Normalize each block to its constant Toeplitz value.
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro k hk
            have hklt : k < n - (j : ℕ) := Finset.mem_range.mp hk
            have hlt : k + (j : ℕ) < n := by
              omega
            simp [hlt]
          · refine Finset.sum_congr rfl ?_
            intro k hk
            have hklt : k < (j : ℕ) := Finset.mem_range.mp hk
            have hnot : ¬ ((n - (j : ℕ) + k) + (j : ℕ) < n) := by
              omega
            simp [hnot]
    _ = (((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
          (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ))) := by
          -- Evaluate the two constant blocks by their cardinalities.
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_comm]

/-- The Toeplitz specialization of
`Matrix.bestCirculantApproximationCoeffs` has the weighted diagonal-average
formula from Chapter 5. -/
theorem bestCirculantApproximationCoeffs_toeplitzByDiag_apply
    {n : ℕ} (t : ℤ → ℝ) (j : Fin n) :
    bestCirculantApproximationCoeffs (toeplitzByDiag n t) j =
      ((((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
          (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ)))) / (n : ℝ) := by
  -- Rewrite the coefficient through the Chapter 5 wrapped diagonal-average formula.
  calc
    bestCirculantApproximationCoeffs (toeplitzByDiag n t) j
        = (1 / (n : ℝ)) * ∑ k : Fin n, toeplitzByDiag n t (k + j) k := by
            simpa using
              bestCirculantApproximationCoeffs_apply_diagonalAverage (toeplitzByDiag n t) j
    _ = (1 / (n : ℝ)) *
          ((((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
            (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ)))) := by
          rw [sum_toeplitzByDiag_wrappedDiagonal]
    _ = ((((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
          (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ)))) / (n : ℝ) := by
          ring

/-- Corollary 5.23. For the Toeplitz matrix `Matrix.toeplitzByDiag n t`, the
Chapter 5 best-circulant approximation is the circulant matrix generated by the
weighted diagonal-average coefficients given by
`Matrix.bestCirculantApproximationCoeffs_toeplitzByDiag_apply`. -/
theorem bestCirculantApproximation_toeplitzByDiag_eq_circulant
    {n : ℕ} (t : ℤ → ℝ) :
    bestCirculantApproximation (toeplitzByDiag n t) =
      circulant
        (fun j : Fin n ↦
          ((((n - (j : ℕ) : ℕ) : ℝ) * t ((j : ℕ) : ℤ)) +
              (((j : ℕ) : ℝ) * t (((j : ℕ) : ℤ) - (n : ℤ)))) / (n : ℝ)) := by
  rw [bestCirculantApproximation_eq_circulant_frobeniusCoeffs, Fin.circulant_inj]
  ext j
  -- Reinterpret the Frobenius coefficient as `bestCirculantApproximationCoeffs`.
  simpa [bestCirculantApproximationCoeffs] using
    bestCirculantApproximationCoeffs_toeplitzByDiag_apply t j

end Matrix
