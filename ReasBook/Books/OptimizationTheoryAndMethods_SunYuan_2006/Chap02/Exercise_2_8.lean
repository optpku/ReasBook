/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_5_4

-- Domain sampling:
-- * source-facing Step 3 owner: `InexactLineSearchAcceptance`;
-- * chapter iterate package: `InexactLineSearchMethod`;
-- * derived Step 3 expansion: `InexactLineSearchMethod.stepSpec`;
-- * theorem owner for the exercise outline: `inexactLineSearch_globalConvergence`.
-- Primitive data live in the inexact-line-search acceptance/method owners above; the exercise
-- itself is recall-only and should therefore point to the chapter theorem rather than restate a
-- narrower Armijo-backtracking ingredient list.

/- Chapter02 Exercise 2.8

The source item is expository: it asks for the outline of Chapter02 Theorem 2.5.4 rather than for
new source-facing mathematical data. The correct public layer is therefore the existing chapter
theorem `inexactLineSearch_globalConvergence`, with `InexactLineSearchAcceptance` and
`InexactLineSearchMethod.stepSpec` as the nearby source-facing Step 3 owners that unpack its
accepted inexact line-search hypothesis.
-/
#check InexactLineSearchAcceptance
#check InexactLineSearchMethod.stepSpec
#check inexactLineSearch_globalConvergence
