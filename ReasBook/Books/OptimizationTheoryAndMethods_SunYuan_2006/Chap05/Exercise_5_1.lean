/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Exercise_4_3

-- Domain sampling:
-- * primary domain: benchmark objective functions reused across unconstrained optimization
--   methods;
-- * inspected project declarations: `rosenbrockFunction`, `extendedRosenbrockFunction`,
--   `OptimizationProblem`;
-- * source/core/bridge triage:
--   this exercise block is source-facing recall-only,
--   the core owners are `rosenbrockFunction` and `extendedRosenbrockFunction`,
--   and `OptimizationProblem` is the heavier packaged view that is unnecessary here.
-- The Chapter 4 benchmark file therefore remains the owner surface for the Rosenbrock objectives
-- used again here with the DFP method, so this exercise reuses those declarations directly.

/-
Chapter05 Exercise 5.1: using the DFP method, minimize `rosenbrockFunction` from Appendix 1.1
and `extendedRosenbrockFunction` from Appendix 1.2.
-/
#check rosenbrockFunction
#check extendedRosenbrockFunction
