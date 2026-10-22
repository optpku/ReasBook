/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_3

-- Domain sampling:
-- * primary domain: Beale's three-term conjugate-gradient method on `ℝ^n`;
-- * inspected project declarations:
--   `bealeThreeTermBeta`,
--   `bealeThreeTermGamma`,
--   `ConjugateGradientRun`,
--   `BealeThreeTermConjugateGradientMethod`;
-- * owner choice: `BealeThreeTermConjugateGradientMethod` is the
--   `source-facing` owner for the textbook formulas `(4.2.38)` and `(4.2.39)`,
--   while the generic iterate/gradient/direction/step data are inherited from
--   the Chapter 4 owner `ConjugateGradientRun`;
-- * primitive data vs derived API: `ConjugateGradientRun` owns the common run
--   data, while the denominator-nonzero statements and the textbook Beale
--   coefficient formulas are Beale-specific method-level API and should be
--   reused directly rather than restated as parallel local theorems.

/- Chapter04 Exercise 4.5 belongs to the recall layer: the stronger owner
`BealeThreeTermConjugateGradientMethod` already provides the exact denominator
and formula fields for `(4.2.38)` and the two branches of `(4.2.39)`, so this
file reuses those canonical declarations directly instead of restating them over
the inherited generic run data. -/

#check BealeThreeTermConjugateGradientMethod.betaDenominatorNonzero
#check BealeThreeTermConjugateGradientMethod.betaFormula
#check BealeThreeTermConjugateGradientMethod.gammaFormula_of_recentRestart
#check BealeThreeTermConjugateGradientMethod.gammaDenominatorNonzero
#check BealeThreeTermConjugateGradientMethod.gammaFormula
