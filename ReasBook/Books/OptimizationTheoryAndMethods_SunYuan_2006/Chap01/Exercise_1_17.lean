/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_11

-- Semantic recall hit verified for this item: `convexOn_nonneg_finset_sum`.

/-
Chapter01 Exercise 1.17

Layer triage:
- source-facing: finite nonnegative sums of convex functions on `ℝ^n`
- core/canonical: `ConvexOn`
- bridge/view: `convexOn_nonneg_finset_sum`

The Chapter 1 theorem `convexOn_nonneg_finset_sum` is the owner abstraction for this exercise.
The source normalization hypothesis `∑ i, α i = 1` is stronger than needed for convexity of a
finite weighted sum, so the refined file reuses the upstream owner directly instead of keeping a
parallel `Fin m`-indexed proof term.
-/
#check convexOn_nonneg_finset_sum
