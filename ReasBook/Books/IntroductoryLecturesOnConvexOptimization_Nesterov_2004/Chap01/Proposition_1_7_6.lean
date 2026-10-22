/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open HasEventuallySuperlinearErrorBound

variable {r : ℕ → ℝ} {c : ℝ}

/- Proposition 1.7.6 lies in the chapter's scalar superlinear-convergence domain.

Primary domain:
* quadratic tail estimates and logarithmic complexity thresholds for real error sequences

Relevant owner-style declarations sampled before refining:
* `HasEventuallySuperlinearErrorBound`
* `quadratic_tail_bound`
* `quadratic_tail_le_of_logb_bound`
* `HasSuperlinearRateOfConvergence` in `Definition_1_8_15.lean`

Best owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the base index `K`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the quadratic tail estimate from `K`
* the logarithmic threshold consequence forcing `r (K + j) ≤ ε`

Source/core/bridge triage:
* source-facing: the explicit Proposition 1.7.6 tail and threshold consequences
* core/canonical: the owner-namespace theorems `quadratic_tail_bound` and
  `quadratic_tail_le_of_logb_bound`
* bridge/view: direct recall only; this file adds no extra mathematics beyond the owner
  hypotheses or their canonical local consequences

The former file kept standalone theorem names for owner-derived consequences. Those consequences
now live with the owner abstraction, and Proposition 1.7.6 reuses them directly. -/

#check (quadratic_tail_bound :
    HasEventuallySuperlinearErrorBound r 0 c 0 →
      (∀ k : ℕ, 0 ≤ r k) →
        0 < c →
          (k0 j : ℕ) → r (k0 + j) ≤ (1 / c) * (c * r k0) ^ (2 ^ j : ℕ))

#check (quadratic_tail_le_of_logb_bound :
    HasEventuallySuperlinearErrorBound r 0 c 0 →
      (∀ k : ℕ, 0 ≤ r k) →
        0 < c →
          (k0 j : ℕ) →
            (ε : ℝ) →
              0 < c * r k0 →
                c * r k0 < 1 →
                  ε ∈ Set.Ioo (0 : ℝ) (1 / c) →
                    Real.logb 2
                        (Real.log (1 / (c * ε)) / Real.log (1 / (c * r k0))) ≤ (j : ℝ) →
                      r (k0 + j) ≤ ε)
