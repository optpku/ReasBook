/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3

-- Source/core/bridge triage:
-- * source-facing item: the exercise asks for the theorem proved in Chapter05 Theorem 5.4.3;
-- * core/canonical owner: `quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero`;
-- * bridge/view: none is needed here, because the exercise is a pure recall of that theorem.
-- This file therefore reuses the existing Chapter 5 owner directly instead of restating its full
-- telescope locally.

/-
Chapter05 Exercise 5.8: prove Theorem 5.4.3.

This exercise is a canonical recall item. The result is already formalized as
`quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero` in
`SunYuanOptimizationTheoryMethods.Chap05.Theorem_5_4_3`, so the exercise reuses that owner
directly and introduces no duplicate local theorem surface.
-/
#check quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero
