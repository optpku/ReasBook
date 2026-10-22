/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_7_2

noncomputable section

-- Domain-style sampling pass for this refine:
-- * primary domain: accumulation-point existence and Clarke stationarity for the Chapter 14
--   composite nonsmooth trust-region method;
-- * sampled declarations in the minimal semantic closure:
--   - `CompositeNonsmoothTrustRegionMethod` and
--     `CompositeNonsmoothTrustRegionMethod.hessianApproximationAt` from `Algorithm_14_7_1`;
--   - `HasSubsequenceTendstoTo` from `Chapter05.Definition_5_4_extra_1`;
--   - `IsClarkeStationaryPoint` from `Definition_14_1_extra_4`;
--   - `compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint` from
--     `Theorem_14_7_2`;
-- * best owner abstraction for this corollary's mathematical content:
--   `compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint`;
-- * primitive data vs derived API:
--   the method, its iterate sequence, and the stage Hessian approximations belong to
--   `CompositeNonsmoothTrustRegionMethod`, while convergent-subsequence existence and Clarke
--   stationarity are theorem-level derived API already owned by `Theorem_14_7_2`;
-- * layer triage:
--   this file is recall-only, not a new source-facing owner or bridge.

/- Chapter14 Corollary 14.7.3: once Theorem 14.7.2 is stated through the canonical accumulation
owner `HasSubsequenceTendstoTo`, the extra bounded-`B_k` hypothesis does not supply additional
mathematical data for the conclusion. The corollary is therefore a direct recall of the existing
Chapter 14 theorem surface rather than a second parallel theorem wrapper. -/
#check compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint
