/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_7_2

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: accumulation-point existence and stationarity for the Chapter 14.7
--   composite nonsmooth trust-region method
-- * sampled upstream declarations in the minimal semantic closure:
--   - `CompositeNonsmoothTrustRegionMethod` from `Algorithm_14_7_1`
--   - `HasSubsequenceTendstoTo` and `hasSubsequenceTendstoTo_iff` from
--     `Chapter05.Definition_5_4_extra_1`
--   - `IsClarkeStationaryPoint` from `Definition_14_1_extra_4`
--   - `compositeNonsmoothTrustRegion_exists_stationaryAccumulationPoint` and
--     `compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint` from
--     `Theorem_14_7_2`
-- * best owner abstraction: the algorithm owner is `CompositeNonsmoothTrustRegionMethod`,
--   with accumulation data expressed canonically by `HasSubsequenceTendstoTo` and
--   stationarity by `IsClarkeStationaryPoint`
-- * primitive data vs derived API: the iterate, multiplier, direction, and radius data live in
--   `CompositeNonsmoothTrustRegionMethod`; the accumulation-point existence and stationarity
--   conclusions are derived theorem-level API and should be recalled directly here rather than
--   restated through a local duplicate theorem
-- * source/core/bridge triage:
--   - source-facing: `compositeNonsmoothTrustRegion_exists_stationaryAccumulationPoint`
--   - core/canonical owners: `CompositeNonsmoothTrustRegionMethod`,
--     `HasSubsequenceTendstoTo`, `IsClarkeStationaryPoint`
--   - bridge/view:
--     `compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint`

/- Chapter14 Exercise 14.11: direct recall of the Chapter 14.7 accumulation-point theorem and
its canonical `HasSubsequenceTendstoTo` bridge. -/
#check compositeNonsmoothTrustRegion_exists_stationaryAccumulationPoint
#check compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint
