/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The upper endpoint `2 (3 + q_f) / (3 + √(21 + 4 q_f))` of the admissible interval for the
initial acceleration parameter `α₀` in constant-step scheme II. -/
def constantStepSchemeIIAlphaUpper (qf : ℝ) : ℝ :=
  2 * (3 + qf) / (3 + Real.sqrt (21 + 4 * qf))

/-- The initial curvature parameter `γ₀ = α₀ (α₀ L - μ) / (1 - α₀)` attached to the initial
acceleration parameter `α₀` in the optimal method. -/
def optimal_method_alpha0_initial_curvature
    (μ L alpha0 : ℝ) : ℝ :=
  alpha0 * (alpha0 * L - μ) / (1 - alpha0)

/-
Primary domain: constant-step type-II accelerated recurrences on real Hilbert spaces.

Owner declarations sampled in this domain:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, which owns the heavier
  `(x_k, y_k, v_k, α_k, γ_k)` estimating-sequence recurrence;
* `ConstantStepSchemeI` in `Algorithm_2_3`, the source-facing exact-step specialization of that
  heavier owner;
* `constantStepSchemeIII` in `Algorithm_2_5`, the chapter's recursive source-facing trajectory
  pattern for a fixed-step accelerated method;
* `ConstantStepSchemeIIIMomentumRecurrence` in `Proposition_2_12`, which shows the chapter style
  for keeping a lighter momentum recurrence as the owner and adding the exact gradient step only
  in the labeled source-facing algorithm.

Layer triage for this file:
* `source-facing`: the recursive trajectory `constantStepSchemeII` specialized to
  `q_f = q[μ, L]` and the admissible source interval for `α₀`;
* `core/canonical`: `ConstantStepSchemeIIMomentumRecurrence`, `ConstantStepSchemeIIRecurrence`,
  and the broader helper trajectory `constantStepSchemeIICore`;
* `bridge/view`: `optimal_method_alpha0_initial_curvature_mem_Ioc`,
  `OptimalMethodRecurrence.alpha_zero_eq_of_initial_curvature`,
  `constantStepSchemeIIToMomentumRecurrence`, `constantStepSchemeIIToRecurrence`, and any later
  recovery of auxiliary optimal-method data such as `γ_k` or `v_k`.

Primitive source-facing data here are exactly the objective `f`, the strong-convexity/smoothness
parameters `μ, L`, the initial point `x0`, and the admissible source scalar
`α₀ ∈ (√q[μ, L], constantStepSchemeIIAlphaUpper q[μ, L]]`. The broader free-`q_f` recursion is
retained only as a core helper, while the auxiliary optimal-method sequences `γ_k` and `v_k`
remain derived bridge data rather than primitive public fields of the main scheme-II object.
-/

section Alpha0InitialCurvature

variable {μ L alpha0 : ℝ}

/-- Helper for Algorithm 2.4: when `q_f ≥ 0`, the admissible upper endpoint rewrites to the
rationalized root form `(√(21 + 4 q_f) - 3) / 2`. -/
private theorem admissible_alpha_upper_eq
    {qf : ℝ} (hqf : 0 ≤ qf) :
    constantStepSchemeIIAlphaUpper qf =
      (Real.sqrt (21 + 4 * qf) - 3) / 2 := by
  -- Rationalize the displayed fraction to expose the positive quadratic root.
  have hrad : 0 ≤ 21 + 4 * qf := by
    nlinarith
  have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
    positivity
  unfold constantStepSchemeIIAlphaUpper
  refine (div_eq_iff hden.ne').2 ?_
  nlinarith [Real.sq_sqrt hrad]

/-- Helper for Algorithm 2.4: if `q_f < 1`, then the admissible upper endpoint lies below `1`. -/
private theorem admissible_alpha_upper_lt_one
    {qf : ℝ} (hqf : qf < 1) :
    constantStepSchemeIIAlphaUpper qf < 1 := by
  -- Split off the easy region where the numerator is already nonpositive.
  unfold constantStepSchemeIIAlphaUpper
  by_cases hqf_small : qf ≤ -3
  · have hnum_nonpos : 2 * (3 + qf) ≤ 0 := by
      nlinarith
    have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (21 + 4 * qf) := Real.sqrt_nonneg _
      linarith
    have hupper_nonpos :
        2 * (3 + qf) / (3 + Real.sqrt (21 + 4 * qf)) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden.le
    linarith
  · have hqf_gt : -3 < qf := by
      linarith
    have hsqrt : 3 + 2 * qf < Real.sqrt (21 + 4 * qf) := by
      have hsq : (3 + 2 * qf) ^ (2 : ℕ) < 21 + 4 * qf := by
        nlinarith
      exact Real.lt_sqrt_of_sq_lt hsq
    have hnum : 2 * (3 + qf) < 3 + Real.sqrt (21 + 4 * qf) := by
      nlinarith
    have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (21 + 4 * qf) := Real.sqrt_nonneg _
      linarith
    exact (div_lt_one hden).2 hnum

/-- Helper for Algorithm 2.4: if `1 ≤ q_f`, then the admissible upper endpoint is at most
`√q_f`. -/
private theorem admissible_alpha_upper_le_sqrt_of_one_le
    {qf : ℝ} (hqf : 1 ≤ qf) :
    constantStepSchemeIIAlphaUpper qf ≤ Real.sqrt qf := by
  -- Compare the explicit root form with `√q_f` after squaring both sides.
  have hqf_nonneg : 0 ≤ qf := by
    linarith
  have hsqrt_le : Real.sqrt (21 + 4 * qf) ≤ 2 * Real.sqrt qf + 3 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · have hsq_q : Real.sqrt qf ^ (2 : ℕ) = qf := Real.sq_sqrt hqf_nonneg
      have hsqrtq_ge_one : 1 ≤ Real.sqrt qf := by
        simpa using (Real.sqrt_le_sqrt hqf)
      have hsq :
          21 + 4 * qf ≤ (2 * Real.sqrt qf + 3) ^ (2 : ℕ) := by
        calc
          21 + 4 * qf ≤ 9 + 4 * qf + 12 * Real.sqrt qf := by
            nlinarith
          _ = (2 * Real.sqrt qf + 3) ^ (2 : ℕ) := by
            nlinarith
      exact hsq
  rw [admissible_alpha_upper_eq hqf_nonneg]
  nlinarith

/-- Helper for Algorithm 2.4: the admissible interval `(√q_f, ᾱ(q_f)]` forces `q_f < 1`. -/
private theorem admissible_qf_lt_one_of_mem_Ioc
    {qf alpha0 : ℝ}
    (hα0 : alpha0 ∈ Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)) :
    qf < 1 := by
  -- Otherwise the interval would be empty because its right endpoint drops below `√q_f`.
  by_contra hqf
  have hqf' : 1 ≤ qf := by
    linarith
  have hupper_le :
      constantStepSchemeIIAlphaUpper qf ≤ Real.sqrt qf :=
    admissible_alpha_upper_le_sqrt_of_one_le hqf'
  linarith [hα0.1, hα0.2, hupper_le]

/-- Helper for Algorithm 2.4: the admissible interval `(√q_f, ᾱ(q_f)]` is contained in
`(0, 1)`. -/
private theorem admissible_alpha_mem_Ioo_of_mem_Ioc
    {qf alpha0 : ℝ}
    (hα0 : alpha0 ∈ Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)) :
    alpha0 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · -- The lower endpoint `√q_f` is nonnegative, so the strict left inequality gives positivity.
    have hsqrt_nonneg : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
    linarith [hα0.1, hsqrt_nonneg]
  · -- The right endpoint lies below `1` once `q_f < 1`.
    have hupper_lt : constantStepSchemeIIAlphaUpper qf < 1 :=
      admissible_alpha_upper_lt_one
        (admissible_qf_lt_one_of_mem_Ioc hα0)
    linarith [hα0.2, hupper_lt]

/-- Helper for Algorithm 2.4: the admissible upper endpoint is the positive root of
`a^2 + 3 a = 3 + q_f`. -/
private theorem admissible_alpha_upper_quadratic
    {qf : ℝ} (hqf : 0 ≤ qf) :
    constantStepSchemeIIAlphaUpper qf ^ (2 : ℕ) +
        3 * constantStepSchemeIIAlphaUpper qf =
      3 + qf := by
  -- Rewrite the endpoint in root form and square once.
  rw [admissible_alpha_upper_eq hqf]
  have hrad : 0 ≤ 21 + 4 * qf := by
    nlinarith
  nlinarith [Real.sq_sqrt hrad]

/-- Helper for Algorithm 2.4: the induced initial curvature makes `α₀` satisfy the owner
quadratic `L α₀² = (1 - α₀) γ₀ + α₀ μ`. -/
private theorem optimal_method_alpha0_satisfies_owner_quadratic
    {μ L alpha0 : ℝ}
    (hα0 : alpha0 ∈ Set.Ioo (0 : ℝ) 1) :
    L * alpha0 ^ (2 : Nat) =
      (1 - alpha0) * optimal_method_alpha0_initial_curvature μ L alpha0 +
        alpha0 * μ := by
  -- Expand `γ₀` and clear the denominator `1 - α₀`.
  have hden_ne : 1 - alpha0 ≠ 0 := by
    linarith [hα0.2]
  unfold optimal_method_alpha0_initial_curvature
  field_simp [hden_ne]
  ring

/-- If `L > 0`, `μ > 0`, and the type-II initial parameter `α₀` lies in the admissible source
interval, then the induced optimal-method initial curvature belongs to the owner interval
`(μ, 3L + μ]`. -/
-- Proof sketch: use the admissible interval to prove `α₀ ∈ (sqrt q[μ, L], 1)`, substitute the
-- defining formula `γ₀ = α₀ (α₀ L - μ) / (1 - α₀)`, and simplify the lower and upper bounds
-- separately.
theorem optimal_method_alpha0_initial_curvature_mem_Ioc
    (hμ : 0 < μ)
    (hL : 0 < L)
    (hα0 :
      alpha0 ∈ Set.Ioc (Real.sqrt (q[μ, L])) (constantStepSchemeIIAlphaUpper (q[μ, L]))) :
    optimal_method_alpha0_initial_curvature μ L alpha0 ∈ Set.Ioc μ (3 * L + μ) := by
  have hq_nonneg : 0 ≤ q[μ, L] := by
    exact div_nonneg hμ.le hL.le
  have hα0_Ioo : alpha0 ∈ Set.Ioo (0 : ℝ) 1 :=
    admissible_alpha_mem_Ioo_of_mem_Ioc hα0
  have hα0_pos : 0 < alpha0 := hα0_Ioo.1
  have hden_pos : 0 < 1 - alpha0 := by
    linarith [hα0_Ioo.2]
  have hsq_lt : q[μ, L] < alpha0 ^ (2 : ℕ) := by
    -- Square the strict lower bound `√q[μ,L] < α₀`.
    have hsqrt_sq :
        Real.sqrt (q[μ, L]) ^ (2 : ℕ) = q[μ, L] :=
      Real.sq_sqrt hq_nonneg
    nlinarith [hα0.1, Real.sqrt_nonneg (q[μ, L]), hsqrt_sq]
  have hμ_lt : μ < L * alpha0 ^ (2 : ℕ) := by
    -- Rescale by `L > 0` to recover the curvature inequality in owner variables.
    have hmul := (div_lt_iff₀ hL).mp hsq_lt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hlower : μ < optimal_method_alpha0_initial_curvature μ L alpha0 := by
    -- The lower owner bound is exactly `μ < L α₀²`.
    unfold optimal_method_alpha0_initial_curvature
    refine (lt_div_iff₀ hden_pos).2 ?_
    nlinarith [hμ_lt]
  have hpoly : alpha0 ^ (2 : ℕ) + 3 * alpha0 ≤ 3 + q[μ, L] := by
    -- Control `α₀² + 3 α₀` by the explicit admissible upper endpoint.
    have hmono :
        alpha0 ^ (2 : ℕ) + 3 * alpha0 ≤
          constantStepSchemeIIAlphaUpper (q[μ, L]) ^ (2 : ℕ) +
            3 * constantStepSchemeIIAlphaUpper (q[μ, L]) := by
      nlinarith [hα0.2, hα0_pos]
    linarith [admissible_alpha_upper_quadratic hq_nonneg, hmono]
  have hpoly_scaled :
      L * alpha0 ^ (2 : ℕ) + 3 * L * alpha0 ≤ 3 * L + μ := by
    -- Multiply the quadratic control by `L` and rewrite `L * q[μ, L] = μ`.
    have hmul := mul_le_mul_of_nonneg_left hpoly hL.le
    nlinarith
      [(show L * (3 + μ / L) = 3 * L + μ by field_simp [hL.ne'])]
  have hupper :
      optimal_method_alpha0_initial_curvature μ L alpha0 ≤ 3 * L + μ := by
    -- After clearing the same denominator, the upper owner bound becomes `α₀² + 3 α₀ ≤ 3 + q`.
    unfold optimal_method_alpha0_initial_curvature
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith [hpoly_scaled]
  exact ⟨hlower, hupper⟩

namespace OptimalMethodRecurrence

variable {f : E → ℝ} {x0 : E}

/-- If an optimal-method recurrence is started from the curvature induced by an admissible type-II
parameter `α₀`, then the zeroth owner coefficient is exactly that parameter. -/
-- Proof sketch: evaluate the owner quadratic relation at `k = 0`, substitute the defining
-- formula for `γ₀`, factor the resulting quadratic in `method.alpha 0`, and discard the second
-- root using `0 < method.alpha 0` together with the admissible interval for `α₀`.
theorem alpha_zero_eq_of_initial_curvature
    (hμ : 0 < μ)
    (method : OptimalMethodRecurrence f L μ x0
      (optimal_method_alpha0_initial_curvature μ L alpha0))
    (hα0 :
      alpha0 ∈ Set.Ioc (Real.sqrt (q[μ, L])) (constantStepSchemeIIAlphaUpper (q[μ, L]))) :
    method.alpha 0 = alpha0 := by
  have hγ_mem :
      optimal_method_alpha0_initial_curvature μ L alpha0 ∈ Set.Ioc μ (3 * L + μ) :=
    optimal_method_alpha0_initial_curvature_mem_Ioc hμ method.L_pos hα0
  have hα0_Ioo : alpha0 ∈ Set.Ioo (0 : ℝ) 1 :=
    admissible_alpha_mem_Ioo_of_mem_Ioc hα0
  have hroot_method :
      L * method.alpha 0 ^ (2 : ℕ) =
        (1 - method.alpha 0) *
            optimal_method_alpha0_initial_curvature μ L alpha0 +
          method.alpha 0 * μ := by
    -- Evaluate the owner quadratic at `k = 0` and rewrite `γ₀`.
    simpa [method.gamma_zero] using method.alpha_equation 0
  have hroot_alpha0 :
      L * alpha0 ^ (2 : ℕ) =
        (1 - alpha0) * optimal_method_alpha0_initial_curvature μ L alpha0 +
          alpha0 * μ := by
    -- The source parameter `α₀` satisfies the same quadratic with the induced `γ₀`.
    exact optimal_method_alpha0_satisfies_owner_quadratic hα0_Ioo
  have hfactor_zero :
      (method.alpha 0 - alpha0) *
          (L * (method.alpha 0 + alpha0) +
            (optimal_method_alpha0_initial_curvature μ L alpha0 - μ)) =
        0 := by
    -- Subtract the two quadratic identities and factor the difference of roots.
    nlinarith [hroot_method, hroot_alpha0]
  have hfactor_pos :
      0 < L * (method.alpha 0 + alpha0) +
        (optimal_method_alpha0_initial_curvature μ L alpha0 - μ) := by
    -- The second factor is strictly positive because both roots are positive and `γ₀ > μ`.
    have hmethod_pos : 0 < method.alpha 0 := (method.alpha_mem_Ioo 0).1
    have halpha0_pos : 0 < alpha0 := hα0_Ioo.1
    have hγ_gt : μ < optimal_method_alpha0_initial_curvature μ L alpha0 := hγ_mem.1
    nlinarith [method.L_pos, hmethod_pos, halpha0_pos, hγ_gt]
  nlinarith [hfactor_zero, hfactor_pos]

end OptimalMethodRecurrence

end Alpha0InitialCurvature

/-- The core type-II momentum recurrence shared by the chapter's constant-step variants. This
owner is purely algebraic: it records only the iterate, extrapolation, and scalar recurrences.
The iterate carrier `X` may be the ambient space or a constrained subtype coercing into it. -/
structure ConstantStepSchemeIIMomentumRecurrence
    (E : Type u) [AddCommGroup E] [Module ℝ E]
    (X : Type*) [CoeTC X E] (qf : ℝ) (x0 : X) (alpha0 : ℝ) where
  /-- The main iterate sequence. -/
  x : ℕ → X
  /-- The extrapolated sequence. -/
  y : ℕ → E
  /-- The scalar parameters `α_k`. -/
  alpha : ℕ → ℝ
  /-- The zeroth iterate is the prescribed initial point. -/
  x_zero : x 0 = x0
  /-- The auxiliary sequence starts from `y₀ = x₀`. -/
  y_zero : y 0 = (x0 : E)
  /-- The scalar sequence starts from the prescribed initial value `α₀`. -/
  alpha_zero : alpha 0 = alpha0
  /-- Each `α_{k+1}` satisfies the scheme-II quadratic recurrence. -/
  alpha_succ_equation (k : ℕ) :
    alpha (k + 1) ^ (2 : ℕ) =
      (1 - alpha (k + 1)) * alpha k ^ (2 : ℕ) + qf * alpha (k + 1)
  /-- The extrapolated point `y_{k+1}` is defined using the momentum coefficient `β_k`. -/
  y_succ (k : ℕ) :
    y (k + 1) =
      (x (k + 1) : E) +
        ((alpha k * (1 - alpha k)) / (alpha k ^ (2 : ℕ) + alpha (k + 1))) •
          ((x (k + 1) : E) - (x k : E))

/-- The exact-step type-II recurrence augments the core momentum data with the defining gradient
step and the scalar side conditions needed by the chapter's smooth variants. -/
structure ConstantStepSchemeIIRecurrence
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Type*) [CoeTC X E] (f : E → ℝ) (L qf : ℝ) (x0 : X) (alpha0 : ℝ)
    extends ConstantStepSchemeIIMomentumRecurrence E X qf x0 alpha0 where
  /-- The constant step parameter is positive. -/
  L_pos : 0 < L
  /-- The iterates are produced by the textbook type-II gradient step from `y_k`. -/
  x_succ (k : ℕ) :
    x (k + 1) = y k - (1 / L) • ∇ f (y k)
  /-- Each newly chosen scalar parameter lies in the open unit interval. -/
  alpha_succ_mem_Ioo (k : ℕ) : alpha (k + 1) ∈ Set.Ioo (0 : ℝ) 1

section

/-- The positive root of the scheme-II quadratic scalar equation
`α₊² = (1 - α₊) α² + q_f α₊`. -/
def constantStepSchemeIIAlphaNext
    (qf alpha : ℝ) : ℝ :=
  ((qf - alpha ^ (2 : ℕ)) +
      Real.sqrt ((alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) + 4 * alpha ^ (2 : ℕ))) / 2

/-- The one-step state update of Algorithm 2.4 on triples `(x_k, y_k, α_k)`. -/
noncomputable def constantStepSchemeIIStep
    (f : E → ℝ) (L qf : ℝ) :
    E × E × ℝ → E × E × ℝ :=
  fun state ↦
    let xk := state.1
    let yk := state.2.1
    let alphak := state.2.2
    let alphaNext := constantStepSchemeIIAlphaNext qf alphak
    let xNext := yk - (1 / L) • ∇ f yk
    let yNext :=
      xNext +
        ((alphak * (1 - alphak)) / (alphak ^ (2 : ℕ) + alphaNext)) •
          (xNext - xk)
    (xNext, yNext, alphaNext)

/-- Core recursive type-II trajectory for a fixed scalar parameter `q_f` and initial
`α₀ ∈ (0, 1)`. This broader free-`q_f` recursion is kept only as the internal core layer behind
the textbook source-facing specialization `constantStepSchemeII`. -/
noncomputable def constantStepSchemeIICore
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    ℕ → E × E × ℝ
  | 0 => (x0, x0, (alpha0 : ℝ))
  | k + 1 => constantStepSchemeIIStep f L qf (constantStepSchemeIICore f L qf x0 alpha0 k)

/-- The main iterate sequence `x_k` of the core recursive type-II trajectory. -/
noncomputable def constantStepSchemeIICoreX
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeIICore f L qf x0 alpha0 k).1

/-- The extrapolated sequence `y_k` of the core recursive type-II trajectory. -/
noncomputable def constantStepSchemeIICoreY
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeIICore f L qf x0 alpha0 k).2.1

/-- The scalar sequence `α_k` of the core recursive type-II trajectory. -/
noncomputable def constantStepSchemeIICoreAlpha
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    ℕ → ℝ :=
  fun k ↦ (constantStepSchemeIICore f L qf x0 alpha0 k).2.2

@[simp] theorem constantStepSchemeIICore_zero
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIICore f L qf x0 alpha0 0 = (x0, x0, (alpha0 : ℝ)) :=
  rfl

/-- The core recursive state satisfies the one-step state update law. -/
@[simp] theorem constantStepSchemeIICore_succ
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIICore f L qf x0 alpha0 (k + 1) =
      constantStepSchemeIIStep f L qf (constantStepSchemeIICore f L qf x0 alpha0 k) :=
  rfl

@[simp] theorem constantStepSchemeIICoreX_zero
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIICoreX f L qf x0 alpha0 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIICoreY_zero
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIICoreY f L qf x0 alpha0 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIICoreAlpha_zero
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIICoreAlpha f L qf x0 alpha0 0 = (alpha0 : ℝ) :=
  rfl

/-- The core recursive type-II trajectory starts from the prescribed scalar `α₀ ∈ (0, 1)`. -/
theorem constantStepSchemeIICoreAlpha_zero_mem_Ioo
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIICoreAlpha f L qf x0 alpha0 0 ∈ Set.Ioo (0 : ℝ) 1 :=
  alpha0.2

/-- The recursively chosen scalar `α_{k+1}` is the positive quadratic root determined by
`α_k`. -/
@[simp] theorem constantStepSchemeIICoreAlpha_succ
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIICoreAlpha f L qf x0 alpha0 (k + 1) =
      constantStepSchemeIIAlphaNext qf (constantStepSchemeIICoreAlpha f L qf x0 alpha0 k) :=
  rfl

/-- If `q_f < 1`, then the admissible upper endpoint for the source parameter `α₀` lies below
`1`. -/
theorem constantStepSchemeIIAlphaUpper_lt_one
    {qf : ℝ} (hqf : qf < 1) :
    constantStepSchemeIIAlphaUpper qf < 1 := by
  unfold constantStepSchemeIIAlphaUpper
  by_cases hqf_small : qf ≤ -3
  · have hnum_nonpos : 2 * (3 + qf) ≤ 0 := by
      nlinarith
    have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (21 + 4 * qf) := Real.sqrt_nonneg _
      linarith
    have hupper_nonpos : 2 * (3 + qf) / (3 + Real.sqrt (21 + 4 * qf)) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden.le
    linarith
  · have hqf_gt : -3 < qf := by
      linarith
    have hsqrt : 3 + 2 * qf < Real.sqrt (21 + 4 * qf) := by
      have hsq : (3 + 2 * qf) ^ (2 : ℕ) < 21 + 4 * qf := by
        nlinarith
      exact Real.lt_sqrt_of_sq_lt hsq
    have hnum : 2 * (3 + qf) < 3 + Real.sqrt (21 + 4 * qf) := by
      nlinarith
    have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (21 + 4 * qf) := Real.sqrt_nonneg _
      linarith
    exact (div_lt_one hden).2 hnum

private theorem constantStepSchemeIIAlphaUpper_le_sqrt_of_one_le
    {qf : ℝ} (hqf : 1 ≤ qf) :
    constantStepSchemeIIAlphaUpper qf ≤ Real.sqrt qf := by
  have hqf_nonneg : 0 ≤ qf := by
    linarith
  have hrad : 0 ≤ 21 + 4 * qf := by
    linarith
  have hsqrt_le :
      Real.sqrt (21 + 4 * qf) ≤ 2 * Real.sqrt qf + 3 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · have hsq_q : Real.sqrt qf ^ (2 : ℕ) = qf := Real.sq_sqrt hqf_nonneg
      have hsqrtq_ge_one : 1 ≤ Real.sqrt qf := by
        simpa using (Real.sqrt_le_sqrt hqf)
      have hsq : 21 + 4 * qf ≤ (2 * Real.sqrt qf + 3) ^ (2 : ℕ) := by
        calc
          21 + 4 * qf ≤ 9 + 4 * qf + 12 * Real.sqrt qf := by
            nlinarith
          _ = (2 * Real.sqrt qf + 3) ^ (2 : ℕ) := by
            nlinarith [hsq_q]
      exact hsq
  have hden : 0 < 3 + Real.sqrt (21 + 4 * qf) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (21 + 4 * qf) := Real.sqrt_nonneg _
    linarith
  have hupper_eq :
      constantStepSchemeIIAlphaUpper qf =
        (Real.sqrt (21 + 4 * qf) - 3) / 2 := by
    unfold constantStepSchemeIIAlphaUpper
    refine (div_eq_iff hden.ne').2 ?_
    nlinarith [Real.sq_sqrt hrad]
  rw [hupper_eq]
  nlinarith

/-- The admissible scheme-II scalar interval `(√q_f, constantStepSchemeIIAlphaUpper q_f]`
forces `q_f < 1`. -/
theorem constantStepSchemeII_qf_lt_one_of_mem_Ioc
    {qf alpha0 : ℝ}
    (hα0 : alpha0 ∈ Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)) :
    qf < 1 := by
  by_contra hqf
  have hqf' : 1 ≤ qf := by
    linarith
  have hupper_le :
      constantStepSchemeIIAlphaUpper qf ≤ Real.sqrt qf :=
    constantStepSchemeIIAlphaUpper_le_sqrt_of_one_le hqf'
  linarith [hα0.1, hα0.2, hupper_le]

/-- The admissible scheme-II scalar interval `(√q_f, constantStepSchemeIIAlphaUpper q_f]`
is contained in `(0, 1)`. -/
theorem constantStepSchemeII_alpha_mem_Ioo_of_mem_Ioc
    {qf alpha0 : ℝ}
    (hα0 : alpha0 ∈ Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)) :
    alpha0 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · have hsqrt_nonneg : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
    linarith [hα0.1, hsqrt_nonneg]
  · have hupper_lt : constantStepSchemeIIAlphaUpper qf < 1 :=
      constantStepSchemeIIAlphaUpper_lt_one
        (constantStepSchemeII_qf_lt_one_of_mem_Ioc hα0)
    linarith [hα0.2, hupper_lt]

/-- The admissible source interval for Algorithm 2.4 forces `q[μ, L] < 1`. -/
theorem constantStepSchemeII_qf_lt_one
    {μ L alpha0 : ℝ}
    (hα0 :
      alpha0 ∈ Set.Ioc (Real.sqrt (q[μ, L])) (constantStepSchemeIIAlphaUpper (q[μ, L]))) :
    q[μ, L] < 1 := by
  simpa using constantStepSchemeII_qf_lt_one_of_mem_Ioc hα0

/-- The admissible source interval for Algorithm 2.4 is contained in the open unit interval. -/
theorem constantStepSchemeII_alpha0_mem_Ioo
    {μ L alpha0 : ℝ}
    (hα0 :
      alpha0 ∈ Set.Ioc (Real.sqrt (q[μ, L])) (constantStepSchemeIIAlphaUpper (q[μ, L]))) :
    alpha0 ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa using constantStepSchemeII_alpha_mem_Ioo_of_mem_Ioc hα0

section SourceFacing

variable (μ L : ℝ)

local notation "qf" => q[μ, L]
local notation "αRange" => Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)

/-- Under the source-facing type-II hypotheses `μ > 0`, `L > 0`, and
`α₀ ∈ (√q[μ, L], constantStepSchemeIIAlphaUpper q[μ, L]]`, the reciprocal condition number lies
in `(0, 1)`. -/
theorem constantStepSchemeII_qf_mem_Ioo
    (hμ : 0 < μ) (hL : 0 < L)
    {alpha0 : ℝ} (hα0 : alpha0 ∈ αRange) :
    qf ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos hμ hL
  · exact constantStepSchemeII_qf_lt_one hα0

/-- Algorithm 2.4: for `f : E → ℝ`, parameters `μ, L`, initial point `x0`, and admissible source
parameter
`α₀ ∈ (√q[μ, L], constantStepSchemeIIAlphaUpper q[μ, L]]`, the recursive type-II trajectory
`(x_k, y_k, α_k)` starts from `(x₀, y₀, α₀) = (x0, x0, α₀)` and applies the exact gradient step
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)`, the quadratic scalar update for `α_{k+1}`, and the textbook
momentum formula for `y_{k+1}`. -/
noncomputable def constantStepSchemeII
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    ℕ → E × E × ℝ :=
  constantStepSchemeIICore f L qf x0
    ⟨(alpha0 : ℝ), constantStepSchemeII_alpha0_mem_Ioo alpha0.2⟩

/-- The main iterate sequence `x_k` of the recursive scheme-II trajectory. -/
noncomputable def constantStepSchemeIIX
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeII μ L f x0 alpha0 k).1

/-- The extrapolated sequence `y_k` of the recursive scheme-II trajectory. -/
noncomputable def constantStepSchemeIIY
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeII μ L f x0 alpha0 k).2.1

/-- The scalar sequence `α_k` of the recursive scheme-II trajectory. -/
noncomputable def constantStepSchemeIIAlpha
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    ℕ → ℝ :=
  fun k ↦ (constantStepSchemeII μ L f x0 alpha0 k).2.2

@[simp] theorem constantStepSchemeII_zero
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    constantStepSchemeII μ L f x0 alpha0 0 = (x0, x0, (alpha0 : ℝ)) :=
  rfl

/-- The recursive scheme-II state satisfies the one-step state update law. -/
@[simp] theorem constantStepSchemeII_succ
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeII μ L f x0 alpha0 (k + 1) =
      constantStepSchemeIIStep f L qf (constantStepSchemeII μ L f x0 alpha0 k) :=
  rfl

@[simp] theorem constantStepSchemeIIX_zero
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    constantStepSchemeIIX μ L f x0 alpha0 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIIY_zero
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    constantStepSchemeIIY μ L f x0 alpha0 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIIAlpha_zero
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    constantStepSchemeIIAlpha μ L f x0 alpha0 0 = (alpha0 : ℝ) :=
  rfl

/-- The recursive scheme-II trajectory starts from the prescribed scalar `α₀ ∈ (0, 1)`. -/
theorem constantStepSchemeIIAlpha_zero_mem_Ioo
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    constantStepSchemeIIAlpha μ L f x0 alpha0 0 ∈ Set.Ioo (0 : ℝ) 1 := by
  change (alpha0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
  exact constantStepSchemeII_alpha0_mem_Ioo alpha0.2

/-- The recursively chosen scalar `α_{k+1}` is the positive quadratic root determined by
`α_k`. -/
@[simp] theorem constantStepSchemeIIAlpha_succ
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIAlpha μ L f x0 alpha0 (k + 1) =
      constantStepSchemeIIAlphaNext qf (constantStepSchemeIIAlpha μ L f x0 alpha0 k) :=
  rfl

end SourceFacing

/-- The positive quadratic root satisfies the defining scheme-II scalar equation. -/
theorem constantStepSchemeIIAlphaNext_satisfies_equation
    (qf alpha : ℝ) :
    constantStepSchemeIIAlphaNext qf alpha ^ (2 : ℕ) =
      (1 - constantStepSchemeIIAlphaNext qf alpha) * alpha ^ (2 : ℕ) +
        qf * constantStepSchemeIIAlphaNext qf alpha := by
  unfold constantStepSchemeIIAlphaNext
  set d : ℝ := (alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) + 4 * alpha ^ (2 : ℕ)
  have hd : 0 ≤ d := by
    dsimp [d]
    positivity
  have hs : Real.sqrt d ^ (2 : ℕ) = d := by
    nlinarith [Real.sq_sqrt hd]
  nlinarith [hs]

/-- If `q_f ∈ [0, 1)` and `α ∈ (0, 1)`, then the recursive positive root again lies in
`(0, 1)`. -/
theorem constantStepSchemeIIAlphaNext_mem_Ioo
    {qf alpha : ℝ}
    (hqf : qf ∈ Set.Ico (0 : ℝ) 1)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    constantStepSchemeIIAlphaNext qf alpha ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold constantStepSchemeIIAlphaNext
  constructor
  · have hlt : (alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) <
        (alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) + 4 * alpha ^ (2 : ℕ) := by
      have hα : 0 < alpha := halpha.1
      have hsq : 0 < 4 * alpha ^ (2 : ℕ) := by
        positivity
      nlinarith
    have hsqrt : alpha ^ (2 : ℕ) - qf <
        Real.sqrt ((alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) + 4 * alpha ^ (2 : ℕ)) := by
      exact Real.lt_sqrt_of_sq_lt hlt
    nlinarith
  · have hpos : 0 < 2 - qf + alpha ^ (2 : ℕ) := by
      nlinarith [hqf.2]
    have hsqrt_lt :
        Real.sqrt ((alpha ^ (2 : ℕ) - qf) ^ (2 : ℕ) + 4 * alpha ^ (2 : ℕ)) <
          2 - qf + alpha ^ (2 : ℕ) := by
      rw [Real.sqrt_lt' hpos]
      nlinarith [hqf.2]
    nlinarith

/-- The core recursive type-II scalar sequence satisfies the textbook quadratic recurrence. -/
theorem constantStepSchemeIICoreAlpha_succ_equation
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIICoreAlpha f L qf x0 alpha0 (k + 1) ^ (2 : ℕ) =
      (1 - constantStepSchemeIICoreAlpha f L qf x0 alpha0 (k + 1)) *
          constantStepSchemeIICoreAlpha f L qf x0 alpha0 k ^ (2 : ℕ) +
        qf * constantStepSchemeIICoreAlpha f L qf x0 alpha0 (k + 1) := by
  simpa [constantStepSchemeIICoreAlpha_succ] using
    constantStepSchemeIIAlphaNext_satisfies_equation
      qf (constantStepSchemeIICoreAlpha f L qf x0 alpha0 k)

/-- If `q_f ∈ [0, 1)`, every scalar in the core recursive type-II trajectory lies in `(0, 1)`. -/
theorem constantStepSchemeIICoreAlpha_mem_Ioo
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1)
    (hqf : qf ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k : ℕ, constantStepSchemeIICoreAlpha f L qf x0 alpha0 k ∈ Set.Ioo (0 : ℝ) 1
  | 0 => constantStepSchemeIICoreAlpha_zero_mem_Ioo f L qf x0 alpha0
  | k + 1 => by
      simpa [constantStepSchemeIICoreAlpha_succ] using
        constantStepSchemeIIAlphaNext_mem_Ioo hqf
          (constantStepSchemeIICoreAlpha_mem_Ioo f L qf x0 alpha0 hqf k)

/-- The core recursive type-II iterates satisfy the textbook exact gradient-step update. -/
@[simp] theorem constantStepSchemeIICoreX_succ
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIICoreX f L qf x0 alpha0 (k + 1) =
      constantStepSchemeIICoreY f L qf x0 alpha0 k -
        (1 / L) • ∇ f (constantStepSchemeIICoreY f L qf x0 alpha0 k) :=
  rfl

/-- The core recursive type-II extrapolated points satisfy the textbook momentum update. -/
@[simp] theorem constantStepSchemeIICoreY_succ
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIICoreY f L qf x0 alpha0 (k + 1) =
      constantStepSchemeIICoreX f L qf x0 alpha0 (k + 1) +
        ((constantStepSchemeIICoreAlpha f L qf x0 alpha0 k *
              (1 - constantStepSchemeIICoreAlpha f L qf x0 alpha0 k)) /
            (constantStepSchemeIICoreAlpha f L qf x0 alpha0 k ^ (2 : ℕ) +
              constantStepSchemeIICoreAlpha f L qf x0 alpha0 (k + 1))) •
          (constantStepSchemeIICoreX f L qf x0 alpha0 (k + 1) -
            constantStepSchemeIICoreX f L qf x0 alpha0 k) :=
  rfl

/-- The core free-`q_f` recursive trajectory, viewed through the owner type-II momentum
recurrence API. -/
def constantStepSchemeIICoreToMomentumRecurrence
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1) :
    ConstantStepSchemeIIMomentumRecurrence E E qf x0 (alpha0 : ℝ) where
  x := constantStepSchemeIICoreX f L qf x0 alpha0
  y := constantStepSchemeIICoreY f L qf x0 alpha0
  alpha := constantStepSchemeIICoreAlpha f L qf x0 alpha0
  x_zero := constantStepSchemeIICoreX_zero f L qf x0 alpha0
  y_zero := constantStepSchemeIICoreY_zero f L qf x0 alpha0
  alpha_zero := constantStepSchemeIICoreAlpha_zero f L qf x0 alpha0
  alpha_succ_equation := constantStepSchemeIICoreAlpha_succ_equation f L qf x0 alpha0
  y_succ := constantStepSchemeIICoreY_succ f L qf x0 alpha0

/-- The core free-`q_f` recursive trajectory, viewed through the owner exact-step type-II
recurrence API under the standard analytic side conditions. -/
def constantStepSchemeIICoreToRecurrence
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (alpha0 : Set.Ioo (0 : ℝ) 1)
    (hL : 0 < L) (hqf : qf ∈ Set.Ico (0 : ℝ) 1) :
    ConstantStepSchemeIIRecurrence E E f L qf x0 (alpha0 : ℝ) where
  toConstantStepSchemeIIMomentumRecurrence :=
    constantStepSchemeIICoreToMomentumRecurrence f L qf x0 alpha0
  L_pos := hL
  x_succ := constantStepSchemeIICoreX_succ f L qf x0 alpha0
  alpha_succ_mem_Ioo := fun k ↦
    constantStepSchemeIICoreAlpha_mem_Ioo f L qf x0 alpha0 hqf (k + 1)

section SourceFacing

variable (μ L : ℝ)

local notation "qf" => q[μ, L]
local notation "αRange" => Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)

/-- The recursive source-facing Algorithm 2.4 scalar sequence satisfies the textbook quadratic
recurrence. -/
theorem constantStepSchemeIIAlpha_succ_equation
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIAlpha μ L f x0 alpha0 (k + 1) ^ (2 : ℕ) =
      (1 - constantStepSchemeIIAlpha μ L f x0 alpha0 (k + 1)) *
          constantStepSchemeIIAlpha μ L f x0 alpha0 k ^ (2 : ℕ) +
        qf * constantStepSchemeIIAlpha μ L f x0 alpha0 (k + 1) := by
  simpa [constantStepSchemeIIAlpha, constantStepSchemeII] using
    constantStepSchemeIICoreAlpha_succ_equation f L qf x0
      ⟨(alpha0 : ℝ), constantStepSchemeII_alpha0_mem_Ioo alpha0.2⟩ k

/-- Under the source-facing type-II hypotheses, every scalar in the source-facing Algorithm 2.4
trajectory lies in `(0, 1)`. -/
theorem constantStepSchemeIIAlpha_mem_Ioo
    (f : E → ℝ) (hμ : 0 < μ) (hL : 0 < L) (x0 : E) (alpha0 : αRange) :
    ∀ k : ℕ, constantStepSchemeIIAlpha μ L f x0 alpha0 k ∈ Set.Ioo (0 : ℝ) 1 := by
  have hqf : qf ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨(constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).1.le,
      (constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).2⟩
  simpa [constantStepSchemeIIAlpha, constantStepSchemeII] using
    constantStepSchemeIICoreAlpha_mem_Ioo f L qf x0
      ⟨(alpha0 : ℝ), constantStepSchemeII_alpha0_mem_Ioo alpha0.2⟩ hqf

/-- The recursive source-facing Algorithm 2.4 iterates satisfy the textbook exact gradient-step
update. -/
@[simp] theorem constantStepSchemeIIX_succ
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIX μ L f x0 alpha0 (k + 1) =
      constantStepSchemeIIY μ L f x0 alpha0 k -
        (1 / L) • ∇ f (constantStepSchemeIIY μ L f x0 alpha0 k) :=
  rfl

/-- The recursive source-facing Algorithm 2.4 extrapolated points satisfy the textbook momentum
update. -/
@[simp] theorem constantStepSchemeIIY_succ
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIY μ L f x0 alpha0 (k + 1) =
      constantStepSchemeIIX μ L f x0 alpha0 (k + 1) +
        ((constantStepSchemeIIAlpha μ L f x0 alpha0 k *
              (1 - constantStepSchemeIIAlpha μ L f x0 alpha0 k)) /
            (constantStepSchemeIIAlpha μ L f x0 alpha0 k ^ (2 : ℕ) +
              constantStepSchemeIIAlpha μ L f x0 alpha0 (k + 1))) •
          (constantStepSchemeIIX μ L f x0 alpha0 (k + 1) -
            constantStepSchemeIIX μ L f x0 alpha0 k) :=
  rfl

/-- The recursive source-facing Algorithm 2.4 trajectory, viewed through the owner type-II
momentum recurrence API. -/
def constantStepSchemeIIToMomentumRecurrence
    (f : E → ℝ) (x0 : E) (alpha0 : αRange) :
    ConstantStepSchemeIIMomentumRecurrence E E qf x0 (alpha0 : ℝ) :=
  constantStepSchemeIICoreToMomentumRecurrence f L qf x0
    ⟨(alpha0 : ℝ), constantStepSchemeII_alpha0_mem_Ioo alpha0.2⟩

/-- The recursive source-facing Algorithm 2.4 trajectory, viewed through the owner exact-step
type-II recurrence API. -/
def constantStepSchemeIIToRecurrence
    (f : E → ℝ) (hμ : 0 < μ) (hL : 0 < L) (x0 : E) (alpha0 : αRange)
    :
    ConstantStepSchemeIIRecurrence E E f L qf x0 (alpha0 : ℝ) :=
  constantStepSchemeIICoreToRecurrence f L qf x0
    ⟨(alpha0 : ℝ), constantStepSchemeII_alpha0_mem_Ioo alpha0.2⟩
    hL
    ⟨(constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).1.le,
      (constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).2⟩

end SourceFacing

end

namespace ConstantStepSchemeIIMomentumRecurrence

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {X : Type*} [CoeTC X E]
variable {qf : ℝ} {x0 : X} {alpha0 : ℝ}

/-- A type-II recurrence can be used as its underlying iterate sequence `x_k`. -/
instance :
    CoeFun (ConstantStepSchemeIIMomentumRecurrence E X qf x0 alpha0)
      (fun _ ↦ ℕ → X) where
  coe scheme := scheme.x

end ConstantStepSchemeIIMomentumRecurrence

namespace ConstantStepSchemeIIRecurrence

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [CoeTC X E]
variable {f : E → ℝ} {L qf : ℝ} {x0 : X} {alpha0 : ℝ}

/-- A type-II exact-step recurrence can be used as its underlying iterate sequence `x_k`. -/
instance :
    CoeFun (ConstantStepSchemeIIRecurrence E X f L qf x0 alpha0)
      (fun _ ↦ ℕ → X) where
  coe scheme := scheme.toConstantStepSchemeIIMomentumRecurrence

end ConstantStepSchemeIIRecurrence

end
