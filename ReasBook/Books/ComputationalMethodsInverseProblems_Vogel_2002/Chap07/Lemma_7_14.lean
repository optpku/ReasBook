/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.Extr

public section

/-- Lemma 7.14 (1). If `mStar` minimizes `F` on `Set.Icc 0 n` and satisfies
`mStar < n`, then the backward first difference `F mStar - F (mStar - 1)` is
nonpositive. The source's lower-bound hypothesis `0 < mStar` is redundant over
`ℕ`. -/
theorem backwardDiff_nonpos_of_isMinOn
    (F : ℕ → ℝ) (n mStar : ℕ) (hmin : IsMinOn F (Set.Icc 0 n) mStar)
    (hmn : mStar < n) :
    F mStar - F (mStar - 1) ≤ 0 := by
  rw [isMinOn_iff] at hmin
  rw [sub_nonpos]
  exact hmin (mStar - 1) ⟨Nat.zero_le _, le_trans (Nat.pred_le _) (Nat.le_of_lt hmn)⟩

/-- Lemma 7.14 (2). If `mStar` minimizes `F` on `Set.Icc 0 n` and satisfies
`mStar < n`, then the forward first difference `fwdDiff 1 F mStar` is
nonnegative. The source's lower-bound hypothesis `0 < mStar` is redundant over
`ℕ`. -/
theorem forwardDiff_nonneg_of_isMinOn
    (F : ℕ → ℝ) (n mStar : ℕ) (hmin : IsMinOn F (Set.Icc 0 n) mStar)
    (hmn : mStar < n) :
    0 ≤ fwdDiff 1 F mStar := by
  rw [isMinOn_iff] at hmin
  rw [fwdDiff, sub_nonneg]
  exact hmin (mStar + 1) ⟨Nat.zero_le _, Nat.add_one_le_iff.mpr hmn⟩
