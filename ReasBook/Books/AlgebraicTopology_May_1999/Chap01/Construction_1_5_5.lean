/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Construction_1_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The linear lift `\tilde f_n` of the standard loop is the path `s ↦ ns` from `0` to `n` in
`ℝ`. This is the canonical straight-line path `Path.segment 0 n`. -/
def standardLoopLift (n : ℤ) : Path (0 : ℝ) n :=
  Path.segment (0 : ℝ) n

/-- Evaluating the lifted standard loop gives the formula `\tilde f_n(s) = ns`. -/
-- Proof sketch: `Path.segment` is given by the affine line map; for endpoints `0` and `n`, this
-- simplifies to multiplication by `n`.
theorem standardLoopLift_apply (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoopLift n s = (n : ℝ) * (s : ℝ) := by
  rw [standardLoopLift, Path.segment_apply, AffineMap.lineMap_apply_module]
  simp
  ring

/-- Construction 1.5.5: the standard loop `f_n` factors through the canonical covering map
`Real.fourierChar : ℝ → S¹` by the lift `\tilde f_n(s) = ns`. -/
-- Proof sketch: combine `standardLoop_apply` from Construction 1.5.3 with
-- `standardLoopLift_apply`, then identify the resulting expression with `Real.fourierChar`.
theorem standardLoop_factors_through_fourierChar (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoop n s = Real.fourierChar (standardLoopLift n s) := by
  rw [standardLoop_apply, standardLoopLift_apply, Real.fourierChar_apply']
  ring_nf

/-- In textbook notation, the factorization of `f_n` through the covering map reads
`f_n(s) = e^{2πi\tilde f_n(s)}`. -/
theorem standardLoop_factors_through_circle_exp (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoop n s = Circle.exp (2 * Real.pi * standardLoopLift n s) := by
  rw [standardLoop_factors_through_fourierChar]
  simp [Real.fourierChar_apply']
