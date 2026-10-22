/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_11

-- Semantic recall hits verified for this item: `ConvexOn.smul`, `ConvexOn.add`, and the
-- Chapter 1 owner `convexOn_nonneg_finset_sum`.

/-
Chapter01 Exercise 1.19

This exercise is already recorded upstream in `Theorem_1_3_11.lean`. Parts (1) and (2) are
direct recalls of mathlib's owner theorems `ConvexOn.smul` and `ConvexOn.add`, while part (3)
reuses the Chapter 1 theorem `convexOn_nonneg_finset_sum`.
-/
#check fun {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {α : ℝ} (hf : ConvexOn ℝ S f) (hα : 0 ≤ α) ↦
  (hf.smul hα : ConvexOn ℝ S (α • f))
#check fun {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g) ↦
  (hf.add hg : ConvexOn ℝ S (f + g))
#check convexOn_nonneg_finset_sum
