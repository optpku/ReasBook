/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_6

/- Chapter03 Exercise 3.6: this exercise is exactly the first clause of the Chapter 3.6
inexact-Newton convergence theorem already owned by `Theorem_3_6_6`.

Source/core/bridge triage:
* source-facing: the regular-zero and inexact-Newton owners from Chapter 3.6
* core/canonical: `inexactNewton_tendsto_root_and_eventually_linear_of_forcing_bounded`
* bridge/view: none; the exercise statement matches the existing owner exactly

The previous local `IsRegularZero` and `IsInexactNewtonSequence` declarations duplicated the
Chapter 3.6 owner surface from `Theorem_3_6_2` and `Algorithm_3_6_extra_2`. This file is
therefore recall-only. -/

#check inexactNewton_tendsto_root_and_eventually_linear_of_forcing_bounded
