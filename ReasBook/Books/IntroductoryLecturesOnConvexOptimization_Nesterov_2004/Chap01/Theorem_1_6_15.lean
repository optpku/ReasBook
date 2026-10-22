/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {μ L : ℝ} {M : NNRealˣ}
variable {f : E → ℝ} {xStar x0 : E}

/- Primary domain: local linear convergence of the gradient method on a real Hilbert space near a
nondegenerate critical point with Lipschitz-continuous Hessian.

Owner declarations sampled before refining:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`, written in Chapter 1 surface
  syntax as `f ∈ C22[M]`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Lemma_1_5_11.lean`
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `HasGeometricRateOfConvergence` in `Definition_1_2_6.lean`
* `localGradientRadius` and `localGradientGap_hasGeometricRate_of_optimal_step` in
  `Theorem_1_6_14.lean`, the scalar recurrence layer behind the local rate estimate

Source/core/bridge triage:
* source-facing: the local linear-rate theorem below
* core/canonical: `HasLipschitzContinuousHessian`, `gradientMethod`, and
  `HasGeometricRateOfConvergence`
* bridge/view: the intrinsic closed ball `Q = Metric.closedBall xStar radius`, where
  `radius = localGradientRadius μ M`, together with the Hessian quadratic bounds at `xStar` and
  the scalar local recurrence for the gradient-method distance sequence

Primitive data:
* `f`, `xStar`, `x0`
* the parameters `μ`, `L`, and the Hessian-Lipschitz datum `M`
* the Chapter 1 second-order owner hypothesis `f ∈ C22[(M : NNReal)]`
* the lower/upper quadratic bounds for the owner Hessian `hessian f xStar`
* the critical-point condition `∇ f xStar = 0`

Derived API:
* the intrinsic radius owner `localGradientRadius μ M`
* the constant-step trajectory `traj`
* the geometric-rate estimate for `k ↦ ‖traj k - xStar‖`
* any needed comparison between `μ` and `L`

No parallel local first-order wrapper is introduced here. The theorem is stated directly on the
Chapter 1 Hessian-Lipschitz owner `f ∈ C22[(M : NNReal)]`; the local ball is expressed through the
radius owner `localGradientRadius μ M`, and any induced strong-convex/smooth estimates are
derived consequences rather than primitive public data. -/

local notation "radius" => (2 * μ / (M : ℝ) : ℝ)
local notation "step" => 2 / (L + μ)
local notation "q" => (2 * μ) / (L + μ)
local notation "rate" => (2 * μ) / (L + 3 * μ)
local notation "traj" => gradientMethod (fun _ : ℕ ↦ step) f x0
local notation "r" => fun k : ℕ ↦ ‖traj k - xStar‖
local notation "scaled" => fun k ↦ ((M : ℝ) / (L + μ)) * r k
local notation "gap" => fun k ↦ r k / (radius - r k)

/-- Helper for Theorem 1.6.15: any nonzero displacement satisfying the Hessian quadratic bounds
forces the local curvature parameters to satisfy `μ ≤ L`. -/
lemma mu_le_L_of_nonzero_displacement
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    {x : E} (hx : x ≠ xStar) :
    μ ≤ L := by
  -- Evaluate the two quadratic-form bounds on the same nonzero displacement.
  have hnorm_pos : 0 < ‖x - xStar‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hsq_pos : 0 < ‖x - xStar‖ ^ (2 : ℕ) := by
    positivity
  nlinarith [hess_lower (x - xStar), hess_upper (x - xStar)]

/-- Helper for Theorem 1.6.15: the linearized gradient step at `xStar` contracts by the textbook
factor `(L - μ) / (L + μ)`. -/
lemma shifted_hessian_norm_le
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hμ : 0 < μ) (hμL : μ ≤ L) :
    ‖((1 : E →L[ℝ] E) - step • hessian f xStar)‖ ≤ (L - μ) / (L + μ) := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hcoeff_nonneg : 0 ≤ (L - μ) / (L + μ) := by
    exact div_nonneg (sub_nonneg.mpr hμL) hLμ.le
  let B : E →L[ℝ] E := (1 : E →L[ℝ] E) - step • hessian f xStar
  have hB_symm : B.IsSymmetric := by
    have hH_symm : (hessian f xStar).IsSymmetric := by
      exact fderiv_gradient_isSymmetric_of_contDiffAt
        (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f xStar)
    have hId_symm : (1 : E →L[ℝ] E).IsSymmetric := by
      intro z w
      simp
    have hstep_hessian_symm : (step • hessian f xStar).IsSymmetric := by
      intro z w
      simpa [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right] using
        congrArg (fun t : ℝ ↦ step * t) (hH_symm z w)
    -- The identity and the Hessian are symmetric, so their affine combination is symmetric.
    exact hId_symm.sub hstep_hessian_symm
  have hbound :
      ∀ z : E, |B.rayleighQuotient z| ≤ (L - μ) / (L + μ) := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hcoeff_nonneg
    · have hnorm_sq_pos : 0 < ‖z‖ ^ (2 : ℕ) := by
        positivity
      have hupper :
          inner ℝ (B z) z ≤ ((L - μ) / (L + μ)) * ‖z‖ ^ (2 : ℕ) := by
        have hquad := hess_lower z
        have hstep_nonneg : 0 ≤ step := by
          positivity
        -- The strong-convexity lower bound controls the upper side of the shifted map.
        have hrewrite :
            inner ℝ (B z) z =
              ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z := by
          simp [B, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
        rw [hrewrite]
        have hscaled_quad :
            step * (μ * ‖z‖ ^ (2 : ℕ))
              ≤ step * inner ℝ (hessian f xStar z) z :=
          mul_le_mul_of_nonneg_left hquad hstep_nonneg
        have hlin :
            ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z
              ≤ ‖z‖ ^ (2 : ℕ) - step * (μ * ‖z‖ ^ (2 : ℕ)) := by
          linarith
        calc
          ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z
              ≤ ‖z‖ ^ (2 : ℕ) - step * (μ * ‖z‖ ^ (2 : ℕ)) := hlin
          _ = ((L - μ) / (L + μ)) * ‖z‖ ^ (2 : ℕ) := by
              field_simp [hLμ.ne']
              ring
      have hlower :
          -(((L - μ) / (L + μ)) * ‖z‖ ^ (2 : ℕ)) ≤ inner ℝ (B z) z := by
        have hquad := hess_upper z
        have hstep_nonneg : 0 ≤ step := by
          positivity
        -- The smoothness upper bound controls the lower side of the shifted map.
        have hrewrite :
            inner ℝ (B z) z =
              ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z := by
          simp [B, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
        rw [hrewrite]
        have hscaled_quad :
            step * inner ℝ (hessian f xStar z) z
              ≤ step * (L * ‖z‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hquad hstep_nonneg
        have hlin :
            ‖z‖ ^ (2 : ℕ) - step * (L * ‖z‖ ^ (2 : ℕ))
              ≤ ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z := by
          linarith
        calc
          -(((L - μ) / (L + μ)) * ‖z‖ ^ (2 : ℕ))
              = ‖z‖ ^ (2 : ℕ) - step * (L * ‖z‖ ^ (2 : ℕ)) := by
                field_simp [hLμ.ne']
                ring
          _ ≤ ‖z‖ ^ (2 : ℕ) - step * inner ℝ (hessian f xStar z) z := hlin
      have habs :
          |inner ℝ (B z) z| ≤ ((L - μ) / (L + μ)) * ‖z‖ ^ (2 : ℕ) := by
        exact abs_le.mpr ⟨hlower, hupper⟩
      rw [ContinuousLinearMap.rayleighQuotient]
      have hgoal :
          |inner ℝ (B z) z| / ‖z‖ ^ (2 : ℕ) ≤ (L - μ) / (L + μ) := by
        exact (div_le_iff₀ hnorm_sq_pos).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using habs
      simpa [abs_div, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hgoal
  -- The Rayleigh-quotient description of the norm closes the operator estimate.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient B hB_symm]
  exact ciSup_le hbound

/-- Helper for Theorem 1.6.15: one gradient step satisfies the exact scalar distance recurrence
from the Chapter 1 local model. -/
lemma gradient_step_distance_bound
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (x : E) :
    ‖(x - step • ∇ f x) - xStar‖
      ≤ (((L - μ) + (M : ℝ) * ‖x - xStar‖) / (L + μ)) * ‖x - xStar‖ := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hstep_nonneg : 0 ≤ step := by
    positivity
  let d : E := x - xStar
  have hdev :=
    HasLipschitzContinuousHessian.gradient_deviation_le
      (hf := hf) xStar x
  have hrewrite :
      (x - step • ∇ f x) - xStar =
        (((1 : E →L[ℝ] E) - step • hessian f xStar) d) -
          step • (∇ f x - ∇ f xStar - hessian f xStar d) := by
    -- Expand the one-step map around `xStar` into the linearized part plus the Hessian remainder.
    dsimp [d]
    rw [hgradStar]
    simp [ContinuousLinearMap.sub_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      smul_add]
  calc
    ‖(x - step • ∇ f x) - xStar‖
        = ‖(((1 : E →L[ℝ] E) - step • hessian f xStar) d) -
            step • (∇ f x - ∇ f xStar - hessian f xStar d)‖ := by
            rw [hrewrite]
    _ ≤ ‖(((1 : E →L[ℝ] E) - step • hessian f xStar) d)‖ +
          ‖step • (∇ f x - ∇ f xStar - hessian f xStar d)‖ := norm_sub_le _ _
    _ ≤ ‖((1 : E →L[ℝ] E) - step • hessian f xStar)‖ * ‖d‖ +
          ‖step • (∇ f x - ∇ f xStar - hessian f xStar d)‖ := by
            exact add_le_add (ContinuousLinearMap.le_opNorm _ _) le_rfl
    _ ≤ ((L - μ) / (L + μ)) * ‖d‖ +
          step * ‖∇ f x - ∇ f xStar - hessian f xStar d‖ := by
            rw [norm_smul, Real.norm_of_nonneg hstep_nonneg]
            gcongr
            exact shifted_hessian_norm_le
              (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
              hμ hμL
    _ ≤ ((L - μ) / (L + μ)) * ‖d‖ +
          step * (((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) := by
            have hmul :
                step * ‖∇ f x - ∇ f xStar - hessian f xStar d‖
                  ≤ step * (((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left (by simpa [d] using hdev) hstep_nonneg
            linarith
    _ = (((L - μ) + (M : ℝ) * ‖x - xStar‖) / (L + μ)) * ‖x - xStar‖ := by
          dsimp [d]
          field_simp [hLμ.ne']

/-- Helper for Theorem 1.6.15: the trajectory distances satisfy the textbook scalar recurrence
with coefficient `((L - μ) + M r_k) / (L + μ)`. -/
lemma gradient_traj_distance_recurrence
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (k : ℕ) :
    r (k + 1) ≤ (((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k := by
  -- Specialize the one-step bound at the current gradient-method iterate.
  simpa [gradientMethod_succ] using
    gradient_step_distance_bound
      (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
      (hgradStar := hgradStar) hμ hμL (traj k)

/-- Helper for Theorem 1.6.15: starting inside the local radius `2 * μ / M` keeps every
subsequent gradient iterate strictly inside the same radius. -/
lemma gradient_traj_strict_radius_invariant
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : r 0 < radius)
    (hμ : 0 < μ) (hμL : μ ≤ L) :
    ∀ k : ℕ, r k < radius := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  intro k
  induction k with
  | zero =>
      simpa [gradientMethod_zero] using h0
  | succ k ih =>
      have hMr_lt : (M : ℝ) * r k < 2 * μ := by
        -- The inductive radius bound keeps the source recurrence coefficient below one.
        have hmul : r k * (M : ℝ) < 2 * μ := by
          exact (lt_div_iff₀ hM).mp ih
        simpa [mul_comm] using hmul
      have hcoeff_lt_one : (((L - μ) + (M : ℝ) * r k) / (L + μ)) < 1 := by
        have hnumer_lt : (L - μ) + (M : ℝ) * r k < L + μ := by
          nlinarith
        have hdiv :
            (((L - μ) + (M : ℝ) * r k) / (L + μ)) < (L + μ) / (L + μ) := by
          exact (div_lt_div_iff_of_pos_right hLμ).2 hnumer_lt
        simpa [hLμ.ne'] using hdiv
      calc
        r (k + 1) ≤ (((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k := by
          exact gradient_traj_distance_recurrence
            (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
            (hgradStar := hgradStar) hμ hμL k
        _ ≤ r k := by
          have hrk_nonneg : 0 ≤ r k := norm_nonneg _
          nlinarith
        _ < radius := ih

/-- Helper for Theorem 1.6.15: inside the invariant region `r_k < 2 * μ / M`, the scaled
distance variable stays below `q = 2 * μ / (L + μ)`. -/
lemma gradient_traj_scaled_lt_q_of_radius_lt
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} (hrk_lt : r k < radius) :
    scaled k < q := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hMr_lt : (M : ℝ) * r k < 2 * μ := by
    -- Clearing the positive denominator `M` converts the radius bound into the scaled bound.
    have hmul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    simpa [mul_comm] using hmul
  -- Divide the same numerator inequality by the positive factor `L + μ`.
  have hscaled :
      scaled k = ((M : ℝ) * r k) / (L + μ) := by
    ring
  rw [hscaled]
  exact (div_lt_div_iff_of_pos_right hLμ).2 hMr_lt

/-- Helper for Theorem 1.6.15: the source gap ratio can be rewritten in terms of the scaled
distance variable. -/
lemma gradient_traj_gap_eq_scaled_div_q_sub_scaled
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} (hrk_lt : r k < radius) :
    gap k = scaled k / (q - scaled k) := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM_ne : (M : ℝ) ≠ 0 := by
    exact_mod_cast (show (M : NNReal) ≠ 0 from by
      exact Units.ne_zero M)
  have hscaled_lt_q :=
    gradient_traj_scaled_lt_q_of_radius_lt (hμ := hμ) (hμL := hμL) hrk_lt
  have hgap_den : radius - r k ≠ 0 := sub_ne_zero.mpr hrk_lt.ne.symm
  have hscaled_den : q - scaled k ≠ 0 := sub_ne_zero.mpr hscaled_lt_q.ne.symm
  -- Both sides reduce to the same rational expression in `r_k`.
  change r k / (radius - r k) =
      (((M : ℝ) / (L + μ)) * r k) / ((2 * μ / (L + μ)) - ((M : ℝ) / (L + μ)) * r k)
  field_simp [hLμ.ne', hM_ne, hgap_den, hscaled_den]

/-- Helper for Theorem 1.6.15: the scaled radius recurrence is exactly
`a_{k+1} ≤ (1 - q + a_k) a_k`. -/
lemma gradient_traj_scaled_recurrence
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (k : ℕ) :
    scaled (k + 1) ≤ (1 - q + scaled k) * scaled k := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hscale_nonneg : 0 ≤ (M : ℝ) / (L + μ) := by
    positivity
  have hraw :
      ((M : ℝ) / (L + μ)) * r (k + 1) ≤
        ((M : ℝ) / (L + μ)) *
          ((((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k) :=
    mul_le_mul_of_nonneg_left
      (gradient_traj_distance_recurrence
        (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
        (hgradStar := hgradStar) hμ hμL k)
      hscale_nonneg
  -- Multiply the distance recurrence by `M / (L + μ)` and rewrite into the scaled variable.
  calc
    scaled (k + 1) = ((M : ℝ) / (L + μ)) * r (k + 1) := by
      rfl
    _ ≤ ((M : ℝ) / (L + μ)) *
        ((((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k) := hraw
    _ = (1 - q + scaled k) * scaled k := by
      field_simp [hLμ.ne', hM.ne']
      ring_nf

/-- Helper for Theorem 1.6.15: a scaled recurrence `b ≤ (1 - q + a) a` with `0 ≤ a < q ≤ 1`
contracts the Möbius gap transform `t ↦ t / (q - t)` by the factor `1 / (1 + q)`. -/
lemma local_gap_step_bound_of_scaled_recurrence
    {a b qq : ℝ}
    (hq_nonneg : 0 ≤ qq)
    (ha_nonneg : 0 ≤ a) (ha_lt : a < qq)
    (hb_nonneg : 0 ≤ b)
    (hrec : b ≤ (1 - qq + a) * a) :
    b / (qq - b) ≤ (a / (qq - a)) / (1 + qq) := by
  have hq_pos : 0 < qq := lt_of_le_of_lt ha_nonneg ha_lt
  have hone_add_q_pos : 0 < 1 + qq := by
    nlinarith
  have hshift_nonneg : 0 ≤ 1 + qq - a := by
    nlinarith
  have hshift_ge_one : 1 ≤ 1 + qq - a := by
    nlinarith
  have hshift_rec : (1 + qq - a) * b ≤ a := by
    -- Multiply the scaled recurrence by the positive complementary factor `1 + qq - a`.
    have hmul := mul_le_mul_of_nonneg_left hrec hshift_nonneg
    have hprod_le_one : (1 + qq - a) * (1 - qq + a) ≤ 1 := by
      have hsq : 0 ≤ (qq - a) ^ (2 : ℕ) := sq_nonneg (qq - a)
      nlinarith
    nlinarith
  have hb_le_a : b ≤ a := by
    -- Because `1 + qq - a ≥ 1`, the shifted bound already dominates `b`.
    have hb_le_shift : b ≤ (1 + qq - a) * b := by
      nlinarith
    nlinarith
  have hb_lt : b < qq := lt_of_le_of_lt hb_le_a ha_lt
  have hqb_pos : 0 < qq - b := sub_pos.mpr hb_lt
  have hqa_pos : 0 < qq - a := sub_pos.mpr ha_lt
  have hcross : ((1 + qq) * b) * (qq - a) ≤ a * (qq - b) := by
    -- Clearing denominators reduces the gap contraction to the shifted recurrence above.
    nlinarith [hshift_rec, hq_pos]
  have hdiv : ((1 + qq) * b) / (qq - b) ≤ a / (qq - a) := by
    exact (div_le_div_iff₀ hqb_pos hqa_pos).2 hcross
  -- Divide by the positive factor `1 + qq` to recover the desired one-step contraction.
  exact (le_div_iff₀ hone_add_q_pos).2 <| by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Theorem 1.6.15: the scalar gap-rate parameter `q / (1 + q)` is exactly the
displayed rate `2 * μ / (L + 3 * μ)`. -/
lemma local_gap_rate_eq_rate
    (hμ : 0 < μ) (hμL : μ ≤ L) :
    q / (1 + q) = rate := by
  have hLμ : L + μ ≠ 0 := by
    nlinarith
  have hL3μ : L + 3 * μ ≠ 0 := by
    nlinarith
  -- Expand `q` and `rate`, then clear the common positive denominators.
  change (2 * μ / (L + μ)) / (1 + 2 * μ / (L + μ)) = 2 * μ / (L + 3 * μ)
  field_simp [hLμ, hL3μ]
  ring

/-- Helper for Theorem 1.6.15: the gap ratio contracts by the factor `1 / (1 + q)` at each
gradient step. -/
lemma gradient_traj_gap_step_bound
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : r 0 < radius)
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (k : ℕ) :
    gap (k + 1) ≤ gap k / (1 + q) := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hq_nonneg : 0 ≤ q := by
    positivity
  have hq_le_one : q ≤ 1 := by
    have hnumer_le : 2 * μ ≤ 1 * (L + μ) := by
      nlinarith
    exact (div_le_iff₀ hLμ).2 hnumer_le
  have hradius_lt := gradient_traj_strict_radius_invariant
    (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
    (hgradStar := hgradStar) h0 hμ hμL
  have hscaled_k_lt_q :=
    gradient_traj_scaled_lt_q_of_radius_lt (hμ := hμ) (hμL := hμL) (hradius_lt k)
  have hscaled_succ_nonneg : 0 ≤ scaled (k + 1) := by
    have hscale_nonneg : 0 ≤ (M : ℝ) / (L + μ) := by
      positivity
    exact mul_nonneg hscale_nonneg (norm_nonneg _)
  -- Route correction: clear the scalar denominators in a standalone helper, then rewrite the two
  -- gap terms through the stable scaled-variable identity.
  calc
    gap (k + 1) = scaled (k + 1) / (q - scaled (k + 1)) := by
      exact gradient_traj_gap_eq_scaled_div_q_sub_scaled
        (hμ := hμ) (hμL := hμL) (hradius_lt (k + 1))
    _ ≤ (scaled k / (q - scaled k)) / (1 + q) := by
      exact local_gap_step_bound_of_scaled_recurrence
        hq_nonneg
        (by positivity)
        hscaled_k_lt_q
        hscaled_succ_nonneg
        (gradient_traj_scaled_recurrence
          (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
          (hgradStar := hgradStar) hμ hμL k)
    _ = gap k / (1 + q) := by
      rw [gradient_traj_gap_eq_scaled_div_q_sub_scaled
        (hμ := hμ) (hμL := hμL) (hradius_lt k)]

/-- Helper for Theorem 1.6.15: the source gap ratio has geometric rate
`q / (1 + q)` with initial constant `gap 0`. -/
lemma gradient_traj_gap_geometric_rate
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : r 0 < radius)
    (hμ : 0 < μ) (hμL : μ ≤ L) :
    HasGeometricRateOfConvergence gap (q / (1 + q)) (gap 0) := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hone_add_q_pos : 0 < 1 + q := by
    positivity
  have hq_le_one : q / (1 + q) ≤ 1 := by
    exact (div_le_iff₀ hone_add_q_pos).2 <| by
      nlinarith
  have hcontract : 1 - q / (1 + q) = 1 / (1 + q) := by
    field_simp [hone_add_q_pos.ne']
    ring
  -- Package the pointwise gap contraction through the generic one-step geometric-rate API.
  refine HasGeometricRateOfConvergence.of_step_bound hq_le_one ?_ ?_
  · rfl
  · intro k
    calc
      gap (k + 1) ≤ gap k / (1 + q) := by
        exact gradient_traj_gap_step_bound
          (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
          (hgradStar := hgradStar) h0 hμ hμL k
      _ = (1 - q / (1 + q)) * gap k := by
        rw [hcontract]
        ring

/-- Theorem 1.6.15: if `f` has `M`-Lipschitz Hessian, the Hessian at the stationary point `xStar`
has quadratic form bounded between `μ` and `L`, and the initial point lies in the intrinsic ball
of radius `localGradientRadius μ M` around `xStar`, then the fixed-step gradient method with
step size `2 / (L + μ)` satisfies the stated geometric error bound with rate parameter
`2 * μ / (L + 3 * μ)`. -/
-- Proof sketch: apply the Chapter 1 owner estimate `hf.gradient_deviation_le` on the ball
-- centered at `xStar` to compare `∇ f x` with the linearized model
-- `hessian f xStar (x - xStar)`.
-- The Hessian bounds at `xStar` supply the source local coefficients `μ - (M / 2) r_k` and
-- `L + (M / 2) r_k` for the distance sequence `r_k = ‖x_k - xStar‖`, while `hf` keeps `M`
-- tied to the genuine Hessian-Lipschitz datum. Any comparison between `μ` and `L` needed by the
-- scalar recurrence is derived internally from these Hessian bounds rather than stored as extra
-- public data, and the initial-radius hypothesis `h0` yields `0 < μ` because `M : NNRealˣ`
-- already forces `0 < (M : ℝ)`. The scalar recurrence layer from
-- `Theorem_1_6_14` uses the optimal constant step `2 / (L + μ)` and then yields the announced
-- geometric estimate with rate parameter `2 * μ / (L + 3 * μ)`.
theorem gradient_descent_local_linear_rate
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : ‖x0 - xStar‖ < radius) :
    HasGeometricRateOfConvergence
      (fun k : ℕ ↦ ‖traj k - xStar‖)
      rate
      (radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)) := by
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  by_cases hx0 : x0 = xStar
  · have htraj_fixed : ∀ k : ℕ, traj k = xStar := by
      intro k
      induction k with
      | zero =>
          simpa [gradientMethod_zero, hx0]
      | succ k ih =>
          calc
            traj (k + 1) = traj k - step • ∇ f (traj k) := by
              simp [gradientMethod_succ]
            _ = xStar - step • ∇ f xStar := by
              rw [ih]
            _ = xStar := by
              rw [hgradStar]
              simp
    intro k
    change ‖traj k - xStar‖ ≤
        (radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)) * (1 - rate) ^ k
    rw [htraj_fixed k]
    simp [hx0]
  · have hμL : μ ≤ L :=
      mu_le_L_of_nonzero_displacement
        (hess_lower := hess_lower) (hess_upper := hess_upper) hx0
    have hradius_pos : 0 < radius := by
      exact lt_of_le_of_lt (norm_nonneg _) h0
    have hμ : 0 < μ := by
      have htwo_mu_pos : 0 < 2 * μ := by
        have hM_inv_pos : 0 < (M : ℝ)⁻¹ := inv_pos.mpr hM
        have hmul_pos : 0 < (2 * μ) * (M : ℝ)⁻¹ := by
          change 0 < (2 * μ) * (M : ℝ)⁻¹
          simpa [div_eq_mul_inv] using hradius_pos
        exact (mul_pos_iff_of_pos_right hM_inv_pos).1 hmul_pos
      nlinarith
    have hradius_lt := gradient_traj_strict_radius_invariant
      (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
      (hgradStar := hgradStar) h0 hμ hμL
    have hgap_rate :=
      gradient_traj_gap_geometric_rate
        (hf := hf) (hess_lower := hess_lower) (hess_upper := hess_upper)
        (hgradStar := hgradStar) h0 hμ hμL
    have hrate : q / (1 + q) = rate :=
      local_gap_rate_eq_rate (hμ := hμ) (hμL := hμL)
    intro k
    -- Bound the distance by `radius * gap k`, then insert the geometric decay of `gap`.
    calc
      ‖traj k - xStar‖ = r k := rfl
      _ ≤ radius * gap k := by
        have hrk_nonneg : 0 ≤ r k := norm_nonneg _
        have hden_pos : 0 < radius - r k := sub_pos.mpr (hradius_lt k)
        have hbound : r k ≤ (radius * r k) / (radius - r k) := by
          exact (le_div_iff₀ hden_pos).2 <| by
            nlinarith [hrk_nonneg]
        have hradius_gap :
            radius * gap k = (radius * r k) / (radius - r k) := by
          change radius * (r k / (radius - r k)) = (radius * r k) / (radius - r k)
          simpa [div_eq_mul_inv, mul_assoc]
        rw [hradius_gap]
        exact hbound
      _ ≤ radius * (gap 0 * (1 - q / (1 + q)) ^ k) := by
        gcongr
        exact hgap_rate k
      _ = (radius * gap 0) * (1 - rate) ^ k := by
        rw [hrate]
        ring
      _ = (radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)) * (1 - rate) ^ k := by
        have hgap0 :
            radius * gap 0 = radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖) := by
          change radius * (r 0 / (radius - r 0)) =
              radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)
          simp [gradientMethod_zero, div_eq_mul_inv, mul_assoc]
        rw [hgap0]

end

end
