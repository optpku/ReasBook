/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_71

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]

section

variable {counterpart : ℕ → E → E} {L : ℕ → PosReal} {x0 : E} {Rα : PosReal}

local notation "x" => non_euclidean_gradient_method f counterpart L x0
local notation "xDagger" =>
  non_euclidean_gradient_method_counterpart_sequence f counterpart L x0

/- `prompt_add/` is absent in this workspace, so the owner-abstraction review is done against the
nearby Chapter 10 files. Proposition 10.62 is `source-facing`, and the surrounding Chapter 10 API
already separates its primitive exact-line-search data from the derived generic stepsize owner:
- `uses_non_euclidean_exact_line_search_stepsize_rule` from Lemma 10.66 is the source-facing
  exact-line-search owner;
- `uses_non_euclidean_exact_line_search_stepsize_rule.to_gradient_stepsize_rule` is the
  `bridge/view` that upgrades that owner to the generic admissible-stepsize owner with
  coefficient `M = 1 / (2 L_f)`;
- `non_euclidean_gradient_objective_gap_le_sublinear_rate` from Theorem 10.71 is the canonical
  sublinear-rate owner.

The proposition should therefore take the primitive exact-line-search inputs directly and derive
the generic `M = 1 / (2 L_f)` branch through the upstream bridge, rather than exposing the derived
generic owner as primitive public data. -/

-- Proof sketch: upgrade the exact-line-search hypotheses to the generic admissible-stepsize owner
-- with coefficient `M = 1 / (2 * Lf)` via
-- `uses_non_euclidean_exact_line_search_stepsize_rule.to_gradient_stepsize_rule`, then apply
-- `non_euclidean_gradient_objective_gap_le_sublinear_rate`. This yields
-- `f(x^k) - fOpt ≤ (((Rα : ℝ)^2) / (1 / (2 * Lf))) / k`, and rewriting the scalar factor gives
-- the displayed bound `2 * Lf * Rα^2 / k`.
/-- Proposition 10.62: under the hypotheses of Theorem 10.71, if the stepsizes are chosen by
exact line search and `L_f > 0`, then every positive iterate satisfies
`f(x^k) - f_opt ≤ 2 L_f R_f(x^0)^2 / k`, where `R_f(x^0)` is represented here by the radius
`Rα` for the initial sublevel set `f(x) ≤ f(x^0)`. -/
theorem non_euclidean_gradient_objective_gap_le_two_Lf_mul_sublevel_radius_sq_div_k
    (hRα : ∀ ⦃y : E⦄, f y ≤ f x0 → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hLf : 0 < (Lf : ℝ))
    (hsearch : uses_non_euclidean_exact_line_search_stepsize_rule f x L xDagger)
    (k : ℕ) (hk : 1 ≤ k) :
    f (x k) - fOpt ≤ 2 * (Lf : ℝ) * (Rα : ℝ) ^ 2 / (k : ℝ) := by
  have hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger (1 / (2 * (Lf : ℝ))) :=
    hsearch.to_gradient_stepsize_rule hLf
  simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    non_euclidean_gradient_objective_gap_le_sublinear_rate hRα hadm hstepsize k hk

end

end
