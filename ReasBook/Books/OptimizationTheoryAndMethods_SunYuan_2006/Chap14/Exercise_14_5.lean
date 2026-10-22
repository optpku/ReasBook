/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_3_3

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: convex subgradient methods and optimal-value estimates
-- * sampled upstream declarations in the minimal closure:
--   - `sunYuanOptimalSolutionSet`, `optimalValue`, and `SubgradientMethod` from `Algorithm_14_3_1`
--   - `SubgradientMethod.HasConstantStepSize` from `Theorem_14_3_3`
--   - `exists_pos_constant_subgradient_stepsize_liminf_le_optimalValue_add_of_convexOn`
--     from `Theorem_14_3_3`
-- * best owner abstraction: `SubgradientMethod E`, with the constant-stepsize predicate and
--   liminf estimate derived from that owner
-- * primitive data vs derived API: the iterate/subgradient/stepsize data are primitive in
--   `SubgradientMethod`; `HasConstantStepSize` and the liminf bound are derived theorem-level API,
--   so this exercise should recall the upstream theorem directly rather than restating local
--   copies of `sunYuanOptimalSolutionSet`, `optimalValue`, or a constant-step execution predicate.

/- Chapter14 Exercise 14.5: direct recall of the canonical Chapter 14 constant-step subgradient
method liminf estimate from Theorem 14.3.3. -/
#check exists_pos_constant_subgradient_stepsize_liminf_le_optimalValue_add_of_convexOn
