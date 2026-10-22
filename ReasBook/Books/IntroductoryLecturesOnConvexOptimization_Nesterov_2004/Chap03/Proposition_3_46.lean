/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_54

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open MeasureTheory

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E]

local notation "dim" => Module.finrank ℝ E

attribute [local instance] Classical.decPred

/- Proposition 3.46 lies in the chapter's selected-feasible best-value domain.

Mandatory domain-style sampling before refinement:
- `Nat.count`, `feasibleSubsequence`, and
  `feasibleSubsequence_count_eq_self_of_feasible` from `Definition_3_53`, the chapter owners for
  the canonical selected feasible index and subsequence;
- `bestFunctionValueUpTo` from `Definition_3_55`, the owner for sampled prefix minima;
- `selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_`
  `le_lipschitz_radius_mul_geometricDecay_volumeRatio` from `Theorem_3_54`, the owner-level
  selected-feasible best-value estimate;
- mathlib `IsMinOn` and `LipschitzOnWith`, the canonical optimization and regularity owners used
  by that estimate.

Best owner abstraction:
- source-facing: the selected-feasible best sampled objective value up to the canonical feasible
  count `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `bestFunctionValueUpTo` together with the owner theorem from `Theorem_3_54`;
- bridge/view: the specialization obtained by taking the selected sequence to be
  `feasibleSubsequence Q querySeq` and then rewriting the selected term at counted position with
  `feasibleSubsequence_count_eq_self_of_feasible`.

Primitive data:
- the objective `f`, closed-ball minimizer `xStar`, outer ball data `x0`, `R`, Lipschitz constant
  `M`, feasible set `Q`, raw query sequence `querySeq`, and the raw feasible query `querySeq k`;
- the closed-ball membership and distance estimate for that raw feasible query.

Derived API:
- the canonical selected feasible subsequence `feasibleSubsequence Q querySeq`;
- the canonical selected-feasible prefix count `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- the owner best-value bound on
  `bestFunctionValueUpTo (fun j ↦ f (feasibleSubsequence Q querySeq j))
    (Nat.count (fun j ↦ querySeq j ∈ Q) k)`.

Source/core/bridge triage:
- source-facing: the best feasible sampled-value estimate along the first `k + 1` raw queries;
- core/canonical: `bestFunctionValueUpTo` and the owner theorem from `Theorem_3_54`;
- bridge/view: passage from a raw feasible query `querySeq k` to the selected-feasible owner
  surface via `feasibleSubsequence_count_eq_self_of_feasible`.

The previous version erased this source-facing chapter statement and kept only a generic scalar
monotonicity lemma. That scalar step is not the owner of the mathematics here. This refinement
restores Proposition 3.46 as the thin bridge that the chapter actually uses: a theorem on the
canonical owners `bestFunctionValueUpTo`, `Nat.count`, and `feasibleSubsequence`, proved by direct
reuse of `Theorem_3_54`.
-/

set_option linter.style.longLine false
/-- Proposition 3.46: let `X = feasibleSubsequence Q querySeq` be the canonical selected feasible
subsequence of a raw query sequence `querySeq`, and let
`i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` be the corresponding selected-feasible prefix count.
If `querySeq k` is feasible, if `f` is `M`-Lipschitz on `B₂(xStar, R)`, if `xStar` realizes the
infimum of `f` on that ball, and if the raw feasible query `querySeq k` satisfies the standard
distance estimate to `xStar`, then the best sampled objective value among the first `i(k) + 1`
selected feasible points satisfies the same decay estimate relative to
`sInf (f '' Metric.closedBall xStar R)`. -/
theorem selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_le_lipschitz_radius_mul_geometricDecay_volumeRatio_of_feasible
    (μ : Measure E)
    {f : E → ℝ} {Q : Set E} {querySeq : ℕ → E} {xStar x0 : E} {R : ℝ} {M : NNReal}
    (k : ℕ)
    (hf_lipschitz : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar)
    (hk : querySeq k ∈ Q)
    (hquery_mem : querySeq k ∈ Metric.closedBall xStar R)
    (hquery_dist :
      ‖querySeq k - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ))) :
    bestFunctionValueUpTo
        (fun j ↦ f (feasibleSubsequence Q querySeq j))
        (Nat.count (fun j ↦ querySeq j ∈ Q) k) -
        sInf (f '' Metric.closedBall xStar R) ≤
      (M : ℝ) * R *
        Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
          Real.rpow
            (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
            (1 / (dim : ℝ)) := by
  let X : ℕ → E := feasibleSubsequence Q querySeq
  let i : ℕ → ℕ := Nat.count (fun j ↦ querySeq j ∈ Q)
  have hselected_eq :
      X (i k) = querySeq k :=
    feasibleSubsequence_count_eq_self_of_feasible Q querySeq hk
  have hselected_mem :
      X (i k) ∈ Metric.closedBall xStar R := by
    simpa [hselected_eq] using hquery_mem
  have hselected_dist :
      ‖X (i k) - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ)) := by
    simpa [hselected_eq] using hquery_dist
  simpa using
    selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_le_lipschitz_radius_mul_geometricDecay_volumeRatio
      μ
      k
      hf_lipschitz
      hxStar_opt
      hselected_mem
      hselected_dist

end
