/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_35_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Whole-space estimate-sequence lower bounds are best stated as the `Q = Set.univ`
specializations of the strong-convexity owner theorems from `Text_2_1`, rewritten through the
canonical whole-space bridges `gradientMapping_univ_eq_gradient_step` and
`reducedGradient_univ_eq_gradient`.

Primary domain:
* smooth convex optimization on a real Hilbert space, specialized to the unconstrained
  estimate-sequence recursion

Owner declarations sampled for this refinement:
* `simple_set_phi_star_lower_bound_intermediate` in `Text_2_1`;
* `simple_set_phi_star_lower_bound_of_objective_lower_bound` in `Text_2_1`;
* `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient` in
  `Remark_2_35_1`.

Best owner abstraction:
* core/canonical: the strong-convexity set-level estimate-sequence lower bounds in `Text_2_1`;
* source-facing: their whole-space `Q = Set.univ` specializations written with `gradientStep`
  and `∇`;
* bridge/view: the canonical simplifications from projected-gradient data to the whole-space
  surface.

Primitive data:
* the objective `f`, initial point `x0`, the scalar parameters `(μ, L, γ₀)`, the iterate data
  `(y, α)`, and the stage data `x_k`;
* the estimating-sequence quantities `φ_k^*`, `φ_{k+1}^*`, `γ_k`, `γ_{k+1}`, and `v_k`.

Derived API:
* the textbook intermediate whole-space lower bound `(2.3.9)`;
* the final whole-space lower bound `(2.3.10)` obtained by first dropping the nonnegative strong
  objective correction from `(2.3.8)` and then specializing the μ-free owner theorem.

This file keeps only the whole-space specializations and does not introduce any parallel local
owner API. -/

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

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f (gradientStep f yK L) +
      (α k / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
        transportCoeff * inner ℝ (∇ f yK) (vK - yK)

local notation "strongObjectiveLowerRhs" =>
  f (gradientStep f yK L) +
    inner ℝ (∇ f yK) (xk - yK) +
      (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "finalRhs" =>
  f (gradientStep f yK L) +
    (1 / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
      (1 - α k) * inner ℝ (∇ f yK)
        (((α k * gammaK) / gammaKp1) • (vK - yK) + (xk - yK))

/-- The intermediate whole-space lower bound obtained from the strong-convexity owner recursion by
specializing to `Q = Set.univ` and dropping the nonnegative transport strong-convexity term. -/
-- Proof sketch: specialize `simple_set_phi_star_lower_bound_intermediate` to `Q = Set.univ` and
-- rewrite `x_Q` and `g_Q` as `gradientStep` and `∇`.
theorem whole_space_phi_star_lower_bound_intermediate
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phiK) :
    phiKp1 ≥ intermediateRhs := by
  -- Specialize the set-level owner theorem to the unconstrained domain `Set.univ`.
  have howner :=
    simple_set_phi_star_lower_bound_intermediate
      (Q := (Set.univ : Set E))
      (hQ_nonempty := Set.univ_nonempty)
      (hQ_closed := isClosed_univ)
      (hQ_convex := convex_univ)
      (f := f) (x0 := x0) (μ := μ) (L := L) (gamma0 := gamma0) (y := y) (α := α)
      (k := k) (xk := xk)
      halpha_k htransportCoeff hμ hphi_k
  -- The whole-space bridge theorems rewrite the projected-gradient quantities to `gradientStep`
  -- and `∇`, producing exactly the textbook surface form `(2.3.9)`.
  simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using howner

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Remark 2.20.1: the strong-convexity correction in `(2.3.8)` is nonnegative when
`μ ≥ 0`. -/
lemma strong_objective_correction_nonneg
    (hμ : 0 ≤ μ) :
    0 ≤ (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ) := by
  -- Both the strong-convexity coefficient and the squared norm factor are nonnegative.
  have hμ_half : 0 ≤ μ / 2 := by
    nlinarith
  have hsq : 0 ≤ ‖xk - yK‖ ^ (2 : ℕ) := by
    positivity
  exact mul_nonneg hμ_half hsq

/-- Helper for Remark 2.20.1: the strong lower model `(2.3.8)` implies the μ-free lower model
used by the owner estimate-sequence theorem. -/
lemma strong_objective_lower_implies_objective_lower
    (hμ : 0 ≤ μ)
    (hobjective_lower : f xk ≥ strongObjectiveLowerRhs) :
    f xk ≥
      f (gradientStep f yK L) +
        inner ℝ (∇ f yK) (xk - yK) +
        (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) := by
  -- Drop the nonnegative strong-convexity correction from the right-hand side.
  have hcorrection :
      0 ≤ (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ) :=
    strong_objective_correction_nonneg
      (μ := μ) (y := y) (k := k) (xk := xk) hμ
  nlinarith [hobjective_lower, hcorrection]

/-- Remark 2.20.1: if `φ_k^* ≥ f(x_k)` and the whole-space lower model `(2.3.8)` holds at `y_k`,
then the next estimate-sequence value satisfies the textbook whole-space lower bound `(2.3.10)`. -/
-- Proof sketch: first drop the nonnegative strong-convexity term from `strongObjectiveLowerRhs`
-- using `hμ`; then specialize
-- `simple_set_phi_star_lower_bound_of_objective_lower_bound` to `Q = Set.univ` and rewrite the
-- projected-gradient terms using `gradientMapping_univ_eq_gradient_step` and
-- `reducedGradient_univ_eq_gradient`.
theorem whole_space_phi_star_lower_bound_of_strong_objective_lower_bound
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phiK)
    (hobjective_lower : f xk ≥ strongObjectiveLowerRhs) :
    phiKp1 ≥ finalRhs := by
  -- First weaken `(2.3.8)` to the μ-free lower bound consumed by the owner theorem.
  have hobjective_lower' :
      f xk ≥
        f (gradientStep f yK L) +
          inner ℝ (∇ f yK) (xk - yK) +
          (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) :=
    strong_objective_lower_implies_objective_lower
      (f := f) (μ := μ) (L := L) (y := y) (k := k) (xk := xk) hμ hobjective_lower
  -- Rewrite the weakened lower model back to the owner theorem's `x_Q` / `g_Q` notation.
  have hobjective_lower_owner :
      f xk ≥
        f (x_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK)) +
          inner ℝ
            (g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK))
            (xk - yK) +
          (1 / (2 * (L : ℝ))) *
            ‖g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK)‖ ^
              (2 : ℕ) := by
    simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using
      hobjective_lower'
  -- Then specialize the set-level owner theorem to `Q = Set.univ` and rewrite to the whole-space
  -- `gradientStep` / `∇` surface form `(2.3.10)`.
  have howner :=
    simple_set_phi_star_lower_bound_of_objective_lower_bound
      (Q := (Set.univ : Set E))
      (hQ_nonempty := Set.univ_nonempty)
      (hQ_closed := isClosed_univ)
      (hQ_convex := convex_univ)
      (f := f) (x0 := x0) (μ := μ) (L := L) (gamma0 := gamma0) (y := y) (α := α)
      (k := k) (xk := xk)
      halpha_k htransportCoeff hμ hphi_k hobjective_lower_owner
  simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using howner

end
