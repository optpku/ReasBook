/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.7.5 lies in the chapter's scalar convergence-rate and complexity-threshold
domain.

Primary domain:
* geometric decay bounds for real error sequences

Sampled owner-style declarations:
* `HasGeometricRateOfConvergence.complexity_bound`
* `sqrt_rate_complexity_bound`
* `le_of_complexity_bound_from_rate_estimate`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le`

Best owner abstraction:
* `HasGeometricRateOfConvergence`, with `complexity_bound` as its canonical complexity-threshold
  projection

Primitive data:
* the sequence `r`
* the constants `q` and `c`
* the owner bound `HasGeometricRateOfConvergence r q c`

Derived API:
* the logarithmic threshold consequence `r k ≤ ε`

Source/core/bridge triage:
* source-facing: the textbook logarithmic threshold consequence
* core/canonical: `HasGeometricRateOfConvergence.complexity_bound`
* bridge/view: none beyond the owner theorem's direct closed-form threshold

The former file duplicated the owner theorem under a second public name and carried an unused
nonnegativity hypothesis. This recall file now reuses the canonical owner theorem directly. -/

namespace HasGeometricRateOfConvergence

recall complexity_bound
    {r : ℕ → ℝ} {q c ε : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 < c) (hq₀ : 0 < q) (hq₁ : q ≤ 1) (hε : 0 < ε)
    {k : ℕ} (hkComplexity : Real.log (c / ε) / q ≤ (k : ℝ)) :
    r k ≤ ε

end HasGeometricRateOfConvergence
