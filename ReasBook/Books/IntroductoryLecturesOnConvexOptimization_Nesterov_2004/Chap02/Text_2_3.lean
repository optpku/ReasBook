/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_20_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_43

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: whole-space estimate-sequence lower bounds in smooth strongly convex
optimization on a real Hilbert space.

Owner declarations sampled for this refinement:
* `exactStep_objective_lower_bound` in `Theorem_2_43`, the chapter owner theorem for the
  whole-space exact-step lower bound;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`, the upstream set-level owner whose
  `Q = Set.univ` specialization yields `exactStep_objective_lower_bound`;
* `whole_space_phi_star_lower_bound_intermediate` in `Remark_2_20_1`, the owner whole-space
  estimate-sequence lower bound before regrouping the inner-product terms;
* `whole_space_phi_star_lower_bound_of_strong_objective_lower_bound` in `Remark_2_20_1`, the owner
  whole-space estimate-sequence lower bound after inserting the strong objective estimate.

Best owner abstraction:
* source-facing: the unconstrained estimate-sequence inequalities written with `gradientStep` and
  `∇`;
* core/canonical: `simpleSetEstimatingValue`, `simpleSetEstimatingCenter`, and
  `exactStep_objective_lower_bound`;
* bridge/view: the specialization `Q = Set.univ` connecting the set-level projected-gradient
  owner to the whole-space exact-step owner.

Primitive data:
* the objective `f`, the initial point `x0`, the parameters `(μ, L, gamma0)`, the stage data
  `(y, α)`, and the comparison point `xk`;
* the stage objects `φ_k^*`, `φ_{k+1}^*`, `γ_k`, `γ_{k+1}`, and `v_k`.

Derived API:
* the strong lower bound on `f xk` obtained from `exactStep_objective_lower_bound` at
  `xBar = y k`, `γ = L`, and `x = xk`;
* the pre-regrouped whole-space lower bound for `φ_{k+1}^*`;
* the final regrouped whole-space lower bound from Text 2.3.

This file keeps Text 2.3 at the source-facing whole-space theorem layer and reuses the existing
owner theorems instead of introducing a parallel wrapper API. -/

section

variable
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)
    (hγ : ∀ k, estimatingSequenceCurvature μ gamma0 α (k + 1) ≠ 0)
    (k : ℕ) (xk : E)

local notation "gammaK" => estimatingSequenceCurvature μ gamma0 α k
local notation "gammaKp1" => estimatingSequenceCurvature μ gamma0 α (k + 1)

local notation "phiK" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "phiKp1" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α (k + 1)

local notation "vK" =>
  simpleSetEstimatingCenter
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "yK" => y k

local notation "transportCoeff" =>
  α k * (1 - α k) * gammaK / gammaKp1

local notation "strongObjectiveLowerRhs" =>
  f (gradientStep f yK L) +
    inner ℝ (∇ f yK) (xk - yK) +
      (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f (gradientStep f yK L) +
      (α k / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
        transportCoeff * inner ℝ (∇ f yK) (vK - yK)

local notation "finalRhs" =>
  f (gradientStep f yK L) +
    (1 / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
      (1 - α k) * inner ℝ (∇ f yK)
        (((α k * gammaK) / gammaKp1) • (vK - yK) + (xk - yK))

/-- Text 2.3: assuming the whole-space estimate-sequence setting and `φ_k^* ≥ f(x_k)`, the lower
bound at `x = x_k`, `xBar = y_k` implies the regrouped lower bound for `φ_{k+1}^*`. -/
-- Proof sketch: first specialize `exactStep_objective_lower_bound` to `xBar = y k`, `γ = L`, and
-- `x = xk` to obtain the strong lower model at `xk`, then feed that estimate into
-- `whole_space_phi_star_lower_bound_of_strong_objective_lower_bound` and collect the
-- inner-product terms into the final displayed expression.
theorem whole_space_phi_star_lower_bound_of_phi_star_ge_objective
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hphi_k : f xk ≤ phiK) :
    phiKp1 ≥ finalRhs := by
  have hμ : 0 ≤ μ := (mem_S11_iff.mp hf).mu_pos.le
  have hobjective_lower :
      f xk ≥ strongObjectiveLowerRhs :=
    by
      simpa using exactStep_objective_lower_bound yK xk hf le_rfl
  simpa using
    whole_space_phi_star_lower_bound_of_strong_objective_lower_bound
      f x0 μ L gamma0 y α k xk halpha_k htransportCoeff hμ hphi_k hobjective_lower

end
