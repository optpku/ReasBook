/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Combination

-- Semantic recall hits verified for this item: `convexHull_eq` and `convexHull_eq_iInter`.

/-
Chapter01 Exercise 1.16

Core/canonical owner: `convexHull`.

For `S : Set (EuclideanSpace ℝ (Fin n))`, mathlib already provides the two equivalent textbook
descriptions of `convexHull ℝ S`.

- `convexHull_eq`: `convexHull ℝ S` is the set of all finite convex combinations of points of `S`.
- `convexHull_eq_iInter`: `convexHull ℝ S` is the intersection of all convex sets containing `S`.
-/
#check convexHull
#check convexHull_eq
#check convexHull_eq_iInter
