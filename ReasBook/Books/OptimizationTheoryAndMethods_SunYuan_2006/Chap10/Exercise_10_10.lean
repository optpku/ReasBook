/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Lemma_10_6_2

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: Chapter 10 nonsmooth exact penalty functions.
-- * sampled upstream declarations in the minimal semantic closure:
--   - `nonsmoothExactPenalty`
--   - `nonsmoothExactPenaltyObjectiveValueMono`
--   - `nonsmoothExactPenaltyTermValueAntitone`
-- * best owner abstraction: the Chapter 10 source-facing nonsmooth exact penalty API already
--   owned by `Lemma_10_6_2`, with Exercise 10.10 itself living at the recall layer.
-- This file therefore keeps only the canonical import and recalls the existing theorem owners
-- instead of introducing duplicate local wrappers.

-- Source/core/bridge triage:
-- * source-facing theorem owners:
--   `nonsmoothExactPenaltyObjectiveValueMono`,
--   `nonsmoothExactPenaltyTermValueAntitone`
-- * core/canonical support owner: `Lemma_10_6_2`
-- * bridge/view: none; the exercise is an exact recall of the upstream Chapter 10 theorem.

/- Chapter10 Exercise 10.10: direct recall of both theorem owners for Lemma 10.6.2. -/
#check nonsmoothExactPenaltyObjectiveValueMono
#check nonsmoothExactPenaltyTermValueAntitone
