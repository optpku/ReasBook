/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Primary domain: selected-feasible best-value decay in the Chapter 3 cutting-plane method.

Sampled owner-style declarations:
- `bestFunctionValueUpTo` and `bestFunctionValueUpTo_le` in `Definition_3_55`, the chapter owners
  for finite sampled prefix minima and their canonical comparison with a selected sample;
- mathlib `IsMinOn` and `LipschitzOnWith`, especially `LipschitzOnWith.le_add_mul`, for the
  pointwise Lipschitz gap estimate on the closed ball.

Best owner abstraction:
- source-facing: the selected feasible best-value gap at stage `i k`;
- core/canonical: `bestFunctionValueUpTo` together with the pointwise Lipschitz estimate on the
  selected sample;
- bridge/view: the Euclidean `ℝⁿ` specialization of the selected-point distance decay estimate.

Primitive data:
- the objective `f`, minimizer `xStar`, radius `R`, Lipschitz constant `M`, feasible-set data,
  and the selected feasible subsequence data `xSeq`, `i`.

Derived API:
- the best feasible sampled value `bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k)`;
- the pointwise estimate `f (xSeq (i k)) - f xStar ≤ (M : ℝ) * dist (xSeq (i k)) xStar`;
- the Euclidean specialization obtained by rewriting the norm decay hypothesis in metric form.

Source/core/bridge triage:
- source-facing: this theorem's selected feasible gap estimate;
- core/canonical: `bestFunctionValueUpTo`;
- bridge/view: the Euclidean volume-ratio specialization of the selected-point distance bound.

This refinement keeps `bestFunctionValueUpTo` as the finite-prefix owner and proves the theorem by
the direct textbook chain: compare the prefix minimum with the selected sample, control the
selected objective gap by Lipschitz continuity on the closed ball, and then substitute the
geometric decay estimate for the selected-point distance.
-/

/-- Theorem 3.2.11: if `xSeq` is the feasible subsequence selected by the cutting-plane method,
`f` is `M`-Lipschitz on `B₂(xStar, R)`, `xStar` realizes the optimal value `f^* = f(xStar)` on
that ball, and the selected feasible iterate `xSeq (i k)` satisfies the standard geometric
distance estimate, then the best feasible objective value
`bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k)` among the first `i(k) + 1` selected points
satisfies the same decay estimate relative to `f^*`. -/
-- Proof sketch: compare the finite-prefix minimum with the selected sample `xSeq (i k)` using
-- `bestFunctionValueUpTo_le`. Then apply the one-sided Lipschitz estimate to the pair
-- `(xSeq (i k), xStar)` inside the common closed ball and rewrite the assumed norm decay as a
-- metric-distance bound.
theorem selected_feasible_bestValueGap_le_lipschitz_radius_mul_geometricDecay_volumeRatio
    {f : E → ℝ} {xStar x0 : E} {R : ℝ} {M : NNReal} {Q : Set E}
    {xSeq : ℕ → E} {i : ℕ → ℕ} (k : ℕ)
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar)
    (hf_lipschitz : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hselected_mem : xSeq (i k) ∈ Metric.closedBall xStar R)
    (hselected_dist :
      ‖xSeq (i k) - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              ((volume (Metric.closedBall x0 R)).toReal / (volume Q).toReal)
              (1 / (n : ℝ))) :
    bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k) - f xStar ≤
      (M : ℝ) * R *
        Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
          Real.rpow
            ((volume (Metric.closedBall x0 R)).toReal / (volume Q).toReal)
            (1 / (n : ℝ)) := by
  -- The source statement packages optimality at `xStar`; the direct route below no longer needs
  -- to rewrite through an infimum, but we keep the hypothesis in scope as part of the theorem.
  have _ : IsMinOn f (Metric.closedBall xStar R) xStar := hxStar_opt
  -- Route correction: avoid the later `Theorem_3_54` shortcut and follow the source-faithful
  -- direct chain `best prefix ≤ selected value ≤ Lipschitz gap ≤ geometric-decay rhs`.
  have hbest_le_selected :
      bestFunctionValueUpTo (fun j ↦ f (xSeq j)) (i k) - f xStar ≤
        f (xSeq (i k)) - f xStar := by
    exact sub_le_sub_right (bestFunctionValueUpTo_le ⟨i k, Nat.lt_succ_self _⟩) _
  -- The selected iterate lies in the closed ball, so its membership also forces `R` to be
  -- nonnegative and places the center `xStar` in the same ball.
  have hdist_le_R : dist (xSeq (i k)) xStar ≤ R := by
    simpa [Metric.mem_closedBall] using hselected_mem
  have hR : 0 ≤ R := le_trans dist_nonneg hdist_le_R
  have hxStar_mem : xStar ∈ Metric.closedBall xStar R := by
    simpa [Metric.mem_closedBall] using hR
  -- Apply the one-sided Lipschitz estimate on the common closed ball and rearrange the result
  -- into an objective-gap bound relative to `f xStar`.
  have hselected_gap :
      f (xSeq (i k)) - f xStar ≤ (M : ℝ) * dist (xSeq (i k)) xStar := by
    have hLip :
        f (xSeq (i k)) ≤ f xStar + (M : ℝ) * dist (xSeq (i k)) xStar :=
      hf_lipschitz.le_add_mul hselected_mem hxStar_mem
    rw [sub_le_iff_le_add]
    simpa [add_comm, add_left_comm, add_assoc] using hLip
  -- Rewrite the given norm estimate into the metric form expected by the Lipschitz bound.
  have hselected_dist' :
      dist (xSeq (i k)) xStar ≤
        R *
          Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              ((volume (Metric.closedBall x0 R)).toReal / (volume Q).toReal)
              (1 / (n : ℝ)) := by
    simpa [dist_eq_norm] using hselected_dist
  -- Multiply the distance decay by the nonnegative Lipschitz constant.
  have hmul_dist :
      (M : ℝ) * dist (xSeq (i k)) xStar ≤
        (M : ℝ) *
          (R *
            Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
              Real.rpow
                ((volume (Metric.closedBall x0 R)).toReal / (volume Q).toReal)
                (1 / (n : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hselected_dist' M.2
  -- Chaining the three comparisons yields the claimed best-value decay estimate.
  refine le_trans hbest_le_selected ?_
  refine le_trans hselected_gap ?_
  simpa [mul_assoc] using hmul_dist

end
