/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u} [PseudoMetricSpace X]

open scoped LevelMethodNotation

/- Theorem 3.57 lies in the chapter's level-method scalar-history / feasible-set-diameter domain.

Primary domain:
* stopping-time bounds for a level-method scalar history, parameterized by a bounded feasible
  set and its diameter.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`
* `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`
* `Bornology.IsBounded`
* `Metric.diam`
* `Metric.diam_eq_zero_of_unbounded`
* `exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon` in
  `Theorem_3_3_1`

Best owner abstraction:
* the scalar history is the canonical owner `LevelMethodHistory`
* the feasible-set size is organized by the canonical bounded-set predicate
  `Bornology.IsBounded Q` together with the metric owner `Metric.diam Q`

Primitive data:
* the scalar history `history`
* the feasible set `Q`
* the boundedness witness `Bornology.IsBounded Q`
* the reference value `fStar`

Derived API:
* the feasible-set diameter `Metric.diam Q`
* the canonical gap notation `δ[history](k)`
* `history.shouldStop`
* `levelMethodIterationCap`

Source/core/bridge triage:
* source-facing: the bounded-feasible-set diameter specialization of the stopping statement
* core/canonical: the scalar-history theorem from `Theorem_3_3_1`
* bridge/view: the specialization `D = Metric.diam Q` under the boundedness guard that makes
  this real-valued diameter source-faithful

Once the block-length estimate is supplied explicitly, the separate convexity and Lipschitz
assumptions are not primitive inputs to this theorem statement. This file therefore reuses the
chapter owner abstractions directly instead of rebuilding parallel raw-sequence notions of the gap,
stopping rule, and iteration cap. Because mathlib defines the real-valued diameter by
`Metric.diam Q = ENNReal.toReal (Metric.ediam Q)`, it collapses to `0` on unbounded sets. The
textbook theorem is about a genuine finite feasible-set diameter, so this source-facing
specialization records `Bornology.IsBounded Q` explicitly and only then reuses `Metric.diam Q`.
The textbook ambient model `Q ⊆ ℝⁿ` still enters only through boundedness and diameter, so the
public theorem surface stays at the intrinsic metric level, with the Euclidean case as a direct
specialization.
-/

/-- Theorem 3.57: for a bounded feasible set `Q`, a level-method scalar history `history`, and a
reference value `fStar`, if the history lower bounds stay below `fStar` and the textbook
block-length estimate holds on every positive-terminal-gap interval where the gap `δ_k` does not
shrink by more than the factor `1 - α`, then the method satisfies the
stopping criterion after at most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations; moreover any stopping index `k`
satisfies `f_k^* - fStar ≤ ε`, with the source-faithful specialization `D = Metric.diam Q`. -/
-- Proof sketch: argue by contradiction and assume `δ_k > ε` up to the claimed cap. Partition the
-- indices into maximal consecutive blocks on which the terminal gap stays at least `(1 - α)`
-- times the initial gap. The block-length hypothesis bounds each block by
-- `M_f^2 D^2 / ((1 - α)^2 δ_{p(j)}^2)`, while the block-start gaps grow geometrically by the
-- factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration cap.
theorem levelMethod_stops_and_optimalValue_sub_fStar_le_epsilon_of_diam
    {Q : Set X} (hQ_bounded : Bornology.IsBounded Q)
    {history : LevelMethodHistory} {fStar : ℝ}
    {M_f : NNReal} {ε : Set.Ioi (0 : ℝ)} {α : Set.Ioo (0 : ℝ) 1}
    (hvalidLower : ∀ k : ℕ, history.approximateOptimalValue k ≤ fStar)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * (Metric.diam Q) ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    (∃ k ≤ levelMethodIterationCap M_f (Metric.diam Q) ε α,
      history.shouldStop ε k) ∧
      ∀ k : ℕ,
        history.shouldStop ε k →
          history.optimalValue k - fStar ≤ ε := by
  have _ : Metric.ediam Q ≠ ⊤ := hQ_bounded.ediam_ne_top
  simpa using
    exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon
      history ε.2 α.2 hvalidLower hblock
