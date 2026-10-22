/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_4_2

/-!
Chapter14 Exercise 14.7

Recall the canonical Chapter 14 Theorem 14.4.2 theorem surfaces directly from their owner files.
-/

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: convergence statements for the Chapter 14 cutting-plane owner
--   `CuttingPlaneMethod`
-- * sampled project declarations in the minimal semantic closure:
--   - `CuttingPlaneMethod` and `CuttingPlaneMethod.optimalValue`
--     from `Algorithm_14_4_1`
--   - `CuttingPlaneMethod.lowerValue_tail_monotone`,
--     `CuttingPlaneMethod.lowerValue_tail_tendsto_optimalValue`, and
--     `CuttingPlaneMethod.accumulationPoint_isMinOn_feasibleSet`
--     from `Theorem_14_4_2`
-- * best owner abstraction: `CuttingPlaneMethod`
-- * primitive data vs derived API: the iterate/subgradient/lower-value data belong to
--   `CuttingPlaneMethod`, while the monotonicity, convergence, and accumulation-point results are
--   theorem-level derived API and should be recalled directly rather than restated anonymously

/- Chapter14 Exercise 14.7: direct recall of the canonical Chapter 14 Theorem 14.4.2 owner
surface. -/
#check CuttingPlaneMethod.optimalValue_eq_sInf_image
#check CuttingPlaneMethod.lowerValue_tail_monotone
#check CuttingPlaneMethod.lowerValue_tail_tendsto_optimalValue
#check CuttingPlaneMethod.accumulationPoint_isMinOn_feasibleSet
