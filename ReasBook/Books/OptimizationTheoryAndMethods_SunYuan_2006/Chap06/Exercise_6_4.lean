/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_1

-- Domain sampling:
-- * primary domain: trust-region agreement ratios and radius updates in Chapter 6;
-- * inspected project declarations:
--   `TrustRegionSubproblem.reductionRatio`,
--   `TrustRegionAlgorithm.ratio_eq`,
--   `TrustRegionAlgorithm.radius_shrink`,
--   `TrustRegionAlgorithm.radius_expand`;
-- * best owner abstraction: the Chapter 6 trust-region owners
--   `TrustRegionSubproblem` for the actual-vs-predicted comparison and
--   `TrustRegionAlgorithm` for the adaptive radius update;
-- * primitive data: the subproblem model data and the algorithm iterate/step/radius sequences;
-- * derived API: `predictedReduction`, `reductionRatio`, and the radius-update clauses.
-- Source/core/bridge triage:
-- * source-facing: this exercise is an expository summary of why the trust-region method is
--   attractive;
-- * core/canonical: `TrustRegionSubproblem.reductionRatio` and `TrustRegionAlgorithm`;
-- * bridge/view: `TrustRegionAlgorithm.ratio_eq`, which identifies the algorithm ratio with the
--   canonical actual-to-predicted reduction quotient.
-- The exercise therefore remains recall-only: it adds no new mathematical owner beyond the
-- existing Chapter 6 trust-region API.

/- Chapter06 Exercise 6.4: the attractive point of the trust-region method is that it adapts the
trust-region radius by comparing actual reduction with predicted reduction. This adaptive update
makes the method robust even when the local model is unreliable, and it underlies the strong
global convergence behavior developed later in Chapter 6. -/
#check TrustRegionSubproblem.reductionRatio
#check TrustRegionAlgorithm.ratio_eq
#check TrustRegionAlgorithm.radius_shrink
#check TrustRegionAlgorithm.radius_keep
#check TrustRegionAlgorithm.radius_expand
