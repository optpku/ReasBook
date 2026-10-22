/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_69
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_70
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]

section

variable {counterpart : ℕ → E → E} {L : ℕ → PosReal} {x0 : E} {M : ℝ} {Rα : PosReal}

local notation "x" => non_euclidean_gradient_method f counterpart L x0
local notation "xDagger" =>
  non_euclidean_gradient_method_counterpart_sequence f counterpart L x0

/- `prompt_add/` is absent in this workspace, so the owner-abstraction review is done against the
nearby Chapter 10 files.

Theorem 10.71 is `source-facing` in the non-Euclidean gradient-method analysis. Domain sampling
shows that the right existing owners are:
- `non_euclidean_gradient_method` from Algorithm 10.61 for the generated iterate sequence `x^k`;
- `ProximalGradientConstantStepsizeParameter`,
  `uses_non_euclidean_backtracking_B4_rule`, and
  `uses_non_euclidean_exact_line_search_stepsize_rule` from the nearby Chapter 10 files for the
  three admissible stepsize mechanisms;
- `uses_non_euclidean_gradient_stepsize_rule` and
  `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` from Lemma 10.66 for the
  source-facing admissible stepsize owner and its sufficient-decrease bridge.
- `non_euclidean_gradient_step_decrease_ge_sq_objective_gap` from Lemma 10.69 for the one-step
  quadratic objective-gap decrease estimate;
- `sequence_le_gamma_div_of_step_difference_ge_inv_mul_sq` from Lemma 10.70 for the
  scalar-sequence `O(1 / k)` bridge, now parameterized by the chapter owner `PosReal` for the
  positive recurrence constant and with no redundant global nonnegativity hypothesis;

The constant `C` is kept in its canonical source-facing form `R_α^2 / M`, avoiding a new wrapper
definition. -/

-- Proof sketch: apply
-- `non_euclidean_gradient_step_decrease_ge_sq_objective_gap` to the objective-gap sequence
-- `a k = f(x^k) - fOpt`, where `x^k` is the generated non-Euclidean gradient trajectory. The
-- previous lemma gives
-- `a k - a (k + 1) ≥ (M / R_α^2) * (a k)^2 = (1 / ((R_α^2) / M)) * (a k)^2`, and
-- then invoke
-- `sequence_le_gamma_div_of_step_difference_ge_inv_mul_sq` with
-- `γ = (R_α : ℝ)^2 / M`.
/-- Theorem 10.71: under the setting of Lemma 10.69, every positive iterate of the
non-Euclidean gradient method satisfies the sublinear objective-gap estimate
`f(x^k) - f_opt ≤ C / k`, where `C = R_α^2 / M`. -/
theorem non_euclidean_gradient_objective_gap_le_sublinear_rate
    (hRα : ∀ ⦃y : E⦄, f y ≤ f x0 → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (k : ℕ) (hk : 1 ≤ k) :
    f (x k) - fOpt ≤ (((Rα : ℝ) ^ (2 : ℕ)) / M) / (k : ℝ) := by
  have hM : 0 < M :=
    hstepsize.parameter_pos
  have hRα_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    exact sq_pos_of_pos (PosReal.coe_pos Rα)
  let C : PosReal := ⟨((Rα : ℝ) ^ (2 : ℕ)) / M, div_pos hRα_sq_pos hM⟩
  have hC_inv : 1 / (C : ℝ) = M / ((Rα : ℝ) ^ (2 : ℕ)) := by
    dsimp [C]
    field_simp [hM.ne', hRα_sq_pos.ne']
  have hstep :
      ∀ n : ℕ,
        (f (x n) - fOpt) - (f (x (n + 1)) - fOpt) ≥
          (1 / (C : ℝ)) * (f (x n) - fOpt) ^ (2 : ℕ) := fun n ↦ by
    have hdecrease :=
      non_euclidean_gradient_step_decrease_ge_sq_objective_gap hRα hadm hstepsize n
    calc
      (f (x n) - fOpt) - (f (x (n + 1)) - fOpt) = f (x n) - f (x (n + 1)) := by
        ring
      _ ≥ (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (x n) - fOpt) ^ (2 : ℕ) := hdecrease
      _ = (1 / C) * (f (x n) - fOpt) ^ (2 : ℕ) := by
        rw [hC_inv]
  simpa [C] using
    sequence_le_gamma_div_of_step_difference_ge_inv_mul_sq hstep hk

end

end
