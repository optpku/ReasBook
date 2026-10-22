/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_2_1

-- Domain sampling:
-- * primary domain: linear conjugate-gradient recurrences for quadratic objectives;
-- * inspected project declarations: `ConjugateGradientIterativeScheme`,
--   `quadraticObjective`, `IsMinOn`, `LinearConjugateGradientMethod`,
--   `LinearConjugateGradientMethod.nonterminalStep`;
-- * source/core/bridge triage:
--   `ConjugateGradientIterativeScheme` is the chapter's core owner,
--   `LinearConjugateGradientMethod` is the source-facing quadratic specialization on top of it,
--   and `LinearConjugateGradientMethod.nonterminalStep` is the thin derived bridge/view API.

/- Chapter04 Algorithm 4.2-extra-2 is already owned by
`LinearConjugateGradientMethod` in `Theorem_4_2_1.lean`. This file therefore stays at the
recall layer and reuses that owner directly, rather than restating its fields as a second
conjunction-style specification theorem. -/

#check LinearConjugateGradientMethod
#check LinearConjugateGradientMethod.nonterminalStep
