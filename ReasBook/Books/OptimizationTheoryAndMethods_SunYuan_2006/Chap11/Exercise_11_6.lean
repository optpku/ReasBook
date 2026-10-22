/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Theorem_11_3_2

open GeneralizedReducedGradientMethod

/- Chapter11 Exercise 11.6: direct recall of the source-facing generalized reduced-gradient
method owner form of Chapter 11 Theorem 11.3.2. -/
#check
  tendsto_reducedGradientNorm_zero_or_objective_tendsto_atBot
