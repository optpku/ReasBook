/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Exercise_3_4

-- Domain sampling:
-- * primary domain: benchmark objective functions reused by Chapter 6 trust-region methods;
-- * inspected project declarations: `rosenbrockFunction`, `TrustRegionSubproblem`,
--   `TrustRegionAlgorithm.subproblem`, `OptimizationProblem`;
-- * source/core/bridge triage:
--   this exercise block is source-facing recall-only,
--   the benchmark owner is `rosenbrockFunction`,
--   the Chapter 6 method owners are `TrustRegionSubproblem` and
--   `TrustRegionAlgorithm.subproblem`,
--   and `OptimizationProblem` is a heavier packaged view that is unnecessary here.
-- Primitive-vs-derived check:
-- * the primitive benchmark data already lives upstream as `rosenbrockFunction`;
-- * the Chapter 6 trust-region model API is derived from the existing subproblem/algorithm
--   owners, so this exercise should not add a second benchmark wrapper or local Newton package.
-- The refined file therefore recalls the upstream Rosenbrock owner directly.
/-
Chapter06 Exercise 6.5: use the trust-region Newton method to minimize
`rosenbrockFunction` from Appendix Problem 1.1.
-/
#check rosenbrockFunction
