/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.6 lies in the Chapter 4 cubic-regularization / gradient-domination rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate
  sequence, regularization schedule, and accepted-step relation;
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owner and witness predicate for the minimizer and gradient-domination constant;
* `RegularizedNewton.acceptedParameters` in `Definition_4_1_16`, the fixed-iterate owner behind
  method `(4.1.16)` already reused by `CubicRegularizationMethod`;
* `cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap` in `Text_4_2_10`, the
  nearby chapter pattern where a source-facing rate theorem is driven by a one-step
  `‖∇ f‖^(3/2)` decrease hypothesis rather than lower-level step internals.

Best owner abstraction:
* source-facing: the two phase estimates from Theorem 4.1.6 for a cubic-regularization method
  applied to a degree-one gradient-dominated objective;
* core/canonical: `CubicRegularizationMethod`, `GradientDominatedOn 1 Set.univ f`, and the
  witness package `GradientDominatedOn.UsesConstant (p := 1) (𝓕 := Set.univ) (f := f) xStar τf`;
* bridge/view: the scalar textbook threshold `hatω`, together with the source-level one-step
  gradient-`3/2` descent inequality for the method.

Primitive data:
* the objective `f`;
* the cubic-regularization method `method`;
* the minimizer witness `xStar` and domination constant `τf`;
* the source-facing one-step descent inequality
  `f(x_k) - f(x_{k+1}) ≥ c ‖∇ f(x_{k+1})‖^(3/2)`.

Derived API:
* the scalar threshold `hatω`;
* the large-gap logarithmic contraction estimate;
* the small-gap inverse-square estimate.

This refinement keeps the source-facing rate statements, reuses the existing chapter owners for the
algorithm and domination data, and removes the lower-level residual inequality from the public API
in favor of the textbook one-step gradient-`3/2` decrease hypothesis already matching the source
statement layer.
-/

/-- The threshold `hatω = (18 / L0^2) τf^3 (L + L0)^3` appearing in the two-phase convergence
estimate for cubic regularization of a degree-one gradient-dominated function. -/
abbrev gradientDominatedCubicHatOmega
    (L L0 τf : ℝ) : ℝ :=
  (18 / L0 ^ (2 : ℕ)) * τf ^ (3 : ℕ) * (L + L0) ^ (3 : ℕ)

/-- Expanding `gradientDominatedCubicHatOmega L L0 τf` recovers the textbook
formula for `hatω`. -/
@[simp]
theorem gradientDominatedCubicHatOmega_def
    (L L0 τf : ℝ) :
    gradientDominatedCubicHatOmega L L0 τf =
      (18 / L0 ^ (2 : ℕ)) * τf ^ (3 : ℕ) * (L + L0) ^ (3 : ℕ) :=
  rfl

section GradientDominatedCubicRegularization

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L τf : ℝ} {x0 : E}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

variable (xStar : E)
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar
local notation "κ" =>
  (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ)
local notation "ω̂" => gradientDominatedCubicHatOmega L L0 τf
variable
  (hgradientDominated :
    GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
  (hdescent :
    ∀ k : ℕ,
      f (method k) - f (method (k + 1)) ≥
        κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))

/-- Helper for Theorem 4.1.6: the scalar threshold `hatω` matches the squared cubic-descent
coefficient exactly. -/
lemma gradient_dominated_cubic_hatOmega_coefficient
    (hL0 : 0 < L0) (hLsum_pos : 0 < L + L0) :
    κ ^ (2 : ℕ) * ω̂ = τf ^ (3 : ℕ) := by
  -- Clear the textbook constants once so the main recurrence can use a clean normalized form.
  have hsqrt2 : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
    simp [pow_two]
  have hrpow :
      Real.rpow (L + L0) (3 / 2 : ℝ) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
    calc
      Real.rpow (L + L0) (3 / 2 : ℝ) ^ (2 : ℕ)
          = Real.rpow (L + L0) ((3 / 2 : ℝ) + (3 / 2 : ℝ)) := by
              rw [pow_two]
              symm
              exact Real.rpow_add hLsum_pos (3 / 2 : ℝ) (3 / 2 : ℝ)
      _ = (L + L0) ^ (3 : ℕ) := by
            norm_num
  have hrpow' :
      Real.rpow (L0 + L) (3 / 2 : ℝ) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
    simpa [add_comm] using hrpow
  field_simp [gradientDominatedCubicHatOmega, hL0.ne', hLsum_pos.ne']
  ring_nf
  rw [hsqrt2, hrpow]
  ring_nf

/-- Helper for Theorem 4.1.6: squaring a nonnegative `3/2`-power recovers the cubic power. -/
lemma gradient_dominated_cubic_rpow_three_halves_sq {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (3 / 2 : ℝ)) ^ (2 : ℕ) = x ^ (3 : ℕ) := by
  -- Rewrite `x^(3/2)` as `x * sqrt x`, then square that expression.
  rw [pow_two]
  by_cases hzero : x = 0
  · simp [hzero]
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hrpow : Real.rpow x (3 / 2 : ℝ) = x * Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      calc
        x ^ (3 / 2 : ℝ) = x ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
            norm_num
        _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_add hx_pos]
        _ = x * x ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_one]
    rw [hrpow]
    nlinarith [Real.sq_sqrt hx]

/-- Helper for Theorem 4.1.6: the minimizer witness makes every objective gap along the method
nonnegative. -/
lemma gradient_dominated_cubic_gap_nonneg
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (k : ℕ) :
    0 ≤ Δ k := by
  -- Expand `xStar ∈ argmin[univ] f` to the minimizing inequality at the current iterate.
  rcases mem_constrainedArgmin_iff.mp
      (GradientDominatedOn.UsesConstant.mem_argmin hgradientDominated) with
    ⟨_, hxStar_min⟩
  exact sub_nonneg.mpr ((isMinOn_iff.mp hxStar_min) (method k) (by simp))

/-- Helper for Theorem 4.1.6: the normalized `hatω` term is dominated by the cubic descent term
coming from the gradient lower bound. -/
lemma gradient_dominated_cubic_normalized_term_le_descent_term
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (k : ℕ) :
    ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤
      κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
  -- Compare squares: the gap bound gives `Δ^3 ≤ τf^3 ‖∇f‖^3`, and the coefficient identity turns
  -- `τf^3` into `κ^2 hatω`.
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  have hΔ_nonneg : 0 ≤ Δ (k + 1) := gradient_dominated_cubic_gap_nonneg
      (method := method) (xStar := xStar) hgradientDominated (k + 1)
  have hg_nonneg : 0 ≤ ‖∇ f (method (k + 1))‖ := by
    positivity
  have hκ_nonneg : 0 ≤ κ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hden_pos :
        0 < 3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ) := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := by
        positivity
      have hrpow_pos : 0 < Real.rpow (L + L0) (3 / 2 : ℝ) :=
        Real.rpow_pos_of_pos hLsum_pos (3 / 2 : ℝ)
      positivity
    exact div_nonneg (CubicRegularizationMethod.L0_pos method).le hden_pos.le
  have hbound : Δ (k + 1) ≤ τf * ‖∇ f (method (k + 1))‖ := by
    -- On `Set.univ`, the within-gradient is the ambient gradient.
    simpa [gradientWithin, gradient, fderivWithin_univ, Real.rpow_natCast] using
      (GradientDominatedOn.UsesConstant.bound
        (p := 1) (𝓕 := Set.univ) (f := f) (xStar := xStar) (τf := τf)
        hgradientDominated (x := method (k + 1)) (by simp))
  have hleft_nonneg :
      0 ≤ ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) := by
    exact mul_nonneg hω_pos.le (Real.rpow_nonneg (by positivity) _)
  have hright_nonneg :
      0 ≤ κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
    exact mul_nonneg hκ_nonneg (Real.rpow_nonneg hg_nonneg _)
  have hleft_sq :
      (ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        Δ (k + 1) ^ (3 : ℕ) / ω̂ := by
    have hdiv_nonneg : 0 ≤ Δ (k + 1) / ω̂ := by
      positivity
    rw [mul_pow, gradient_dominated_cubic_rpow_three_halves_sq hdiv_nonneg]
    field_simp [hω_pos.ne']
  have hright_sq :
      (κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) ^ (2 : ℕ) =
        κ ^ (2 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
    rw [mul_pow, gradient_dominated_cubic_rpow_three_halves_sq hg_nonneg]
  have hcube :
      Δ (k + 1) ^ (3 : ℕ) ≤ τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
    have hcube' :
        Δ (k + 1) ^ (3 : ℕ) ≤
          (τf * ‖∇ f (method (k + 1))‖) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hΔ_nonneg hbound 3
    simpa [mul_pow] using hcube'
  have hsq :
      (ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ)) ^ (2 : ℕ) ≤
        (κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) ^ (2 : ℕ) := by
    rw [hleft_sq, hright_sq]
    have h1 :
        Δ (k + 1) ^ (3 : ℕ) / ω̂ ≤
          (τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ)) / ω̂ :=
      div_le_div_of_nonneg_right hcube hω_pos.le
    have h2 :
        (τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ)) / ω̂ =
          κ ^ (2 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
      have hLsum_pos : 0 < L + L0 := by
        linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
      rw [← gradient_dominated_cubic_hatOmega_coefficient
        (L0 := L0) (L := L) (τf := τf)
        (hL0 := CubicRegularizationMethod.L0_pos method) (hLsum_pos := hLsum_pos)]
      field_simp [hω_pos.ne', (GradientDominatedOn.UsesConstant.pos hgradientDominated).ne']
    exact h1.trans_eq h2
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq

/-- Helper for Theorem 4.1.6: the normalized gaps satisfy the scalar source recurrence
`δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}`. -/
lemma gradient_dominated_cubic_normalized_gap_step
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (hdescent :
      ∀ k : ℕ,
        f (method k) - f (method (k + 1)) ≥
          κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))
    (k : ℕ) :
    let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
    δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) := by
  -- Route correction: use the next-gap recurrence from the source proof, not a same-index
  -- recurrence. This is the scalar invariant that drives both phases.
  let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  have hmain :
      ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤ Δ k - Δ (k + 1) := by
    have hleft :=
      gradient_dominated_cubic_normalized_term_le_descent_term
        (method := method) (xStar := xStar) hgradientDominated k
    have hright :
        κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) ≤ Δ k - Δ (k + 1) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdescent k
    exact le_trans hleft hright
  have hrewrite :
      Δ k / ω̂ - Δ (k + 1) / ω̂ = (Δ k - Δ (k + 1)) / ω̂ := by
    field_simp [hω_pos.ne']
  -- Divide the unnormalized inequality by the positive threshold `hatω`.
  have hdiv0 :
      Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) * ω̂ ≤ Δ k - Δ (k + 1) := by
    simpa [mul_comm] using hmain
  have hdiv :
      Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤ (Δ k - Δ (k + 1)) / ω̂ := by
    exact (le_div_iff₀ hω_pos).2 hdiv0
  simpa [δ, hrewrite] using hdiv

/-- Helper for Theorem 4.1.6: once the next normalized gap is at least `1`, one recurrence step
contracts its logarithm by the factor `2/3`. -/
lemma log_step_le_two_thirds_of_previous {a b : ℝ}
    (hb : 1 ≤ b)
    (hstep : a - b ≥ Real.rpow b (3 / 2 : ℝ)) :
    Real.log b ≤ (2 / 3 : ℝ) * Real.log a := by
  -- The recurrence implies `a ≥ b^(3/2)`, so taking logs gives the desired factor.
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hrpow_le : Real.rpow b (3 / 2 : ℝ) ≤ a := by
    have hsum : b + Real.rpow b (3 / 2 : ℝ) ≤ a := by
      linarith
    linarith [Real.rpow_nonneg hb_pos.le (3 / 2 : ℝ)]
  have hlog : (3 / 2 : ℝ) * Real.log b ≤ Real.log a := by
    rw [← Real.log_rpow hb_pos (3 / 2 : ℝ)]
    exact Real.log_le_log (Real.rpow_pos_of_pos hb_pos (3 / 2 : ℝ)) hrpow_le
  nlinarith

/-- Helper for Theorem 4.1.6: a nonnegative sequence satisfying the source recurrence inherits the
geometric logarithmic contraction of part (1). -/
lemma gradient_dominated_cubic_log_gap_le_geometric_of_step
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ))
    (h0 : 1 ≤ δ 0) :
    ∀ k : ℕ, Real.log (δ k) ≤ (2 / 3 : ℝ) ^ k * Real.log (δ 0) := by
  -- Split into the small-gap branch, where the logarithm is already nonpositive, and the
  -- large-gap branch, where the scalar log-step lemma applies.
  have hlog0_nonneg : 0 ≤ Real.log (δ 0) := by
    simpa [Real.log_one] using (Real.log_le_log zero_lt_one h0)
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      by_cases hnext_pos : 0 < δ (k + 1)
      · by_cases hsmall : δ (k + 1) ≤ 1
        · have hlog_nonpos : Real.log (δ (k + 1)) ≤ 0 := by
            simpa [Real.log_one] using (Real.log_le_log hnext_pos hsmall)
          have hrhs_nonneg : 0 ≤ (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
            positivity
          linarith
        · have hbig : 1 < δ (k + 1) := lt_of_not_ge hsmall
          have hstep_log :
              Real.log (δ (k + 1)) ≤ (2 / 3 : ℝ) * Real.log (δ k) := by
            exact log_step_le_two_thirds_of_previous hbig.le (hstep k)
          calc
            Real.log (δ (k + 1)) ≤ (2 / 3 : ℝ) * Real.log (δ k) := hstep_log
            _ ≤ (2 / 3 : ℝ) * ((2 / 3 : ℝ) ^ k * Real.log (δ 0)) := by
                  nlinarith [hk]
            _ = (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
                  rw [pow_succ]
                  ring
      · have hnext_eq : δ (k + 1) = 0 := by
          linarith [hδ_nonneg (k + 1)]
        have hrhs_nonneg : 0 ≤ (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
          positivity
        simp [hnext_eq, hrhs_nonneg]

/-- Helper for Theorem 4.1.6: one recurrence step in the small-gap regime increases the reciprocal
square root by at least the source constant `1 / (2 + 3B/2)`. -/
lemma reciprocal_sqrt_increment_ge_small_gap_constant
    {a b B : ℝ} (hb_pos : 0 < b)
    (hstep : a - b ≥ Real.rpow b (3 / 2 : ℝ))
    (hbB : b ≤ B ^ (2 : ℕ)) (hB : 0 ≤ B) :
    1 / Real.sqrt b - 1 / Real.sqrt a ≥ 1 / (2 + (3 / 2 : ℝ) * B) := by
  -- Rationalize the exact reciprocal difference, then bound `sqrt (1 + s)` by `1 + s / 2`.
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hrpow : Real.rpow b (3 / 2 : ℝ) = b * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
    calc
      b ^ (3 / 2 : ℝ) = b ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
          norm_num
      _ = b ^ (1 : ℝ) * b ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_add hb_pos]
      _ = b * b ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_one]
  have hstep' : b + Real.rpow b (3 / 2 : ℝ) ≤ a := by
    linarith
  have ha_lower : b * (1 + Real.sqrt b) ≤ a := by
    calc
      b * (1 + Real.sqrt b) = b + b * Real.sqrt b := by
          ring
      _ = b + Real.rpow b (3 / 2 : ℝ) := by
            rw [hrpow]
      _ ≤ a := hstep'
  have ha_pos : 0 < a := by
    have : 0 < b * (1 + Real.sqrt b) := by
      positivity
    linarith
  have hroot : Real.sqrt (b * (1 + Real.sqrt b)) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt ha_lower
  have hsqrt_mul :
      Real.sqrt (b * (1 + Real.sqrt b)) = Real.sqrt b * Real.sqrt (1 + Real.sqrt b) := by
    rw [Real.sqrt_mul hb_nonneg]
  have hsqrt_mul_le : Real.sqrt b * Real.sqrt (1 + Real.sqrt b) ≤ Real.sqrt a := by
    simpa [hsqrt_mul] using hroot
  have hrecip_le :
      1 / Real.sqrt a ≤ 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) := by
    exact (one_div_le_one_div (Real.sqrt_pos.mpr ha_pos) (by positivity)).2 hsqrt_mul_le
  have hmain :
      1 / Real.sqrt b - 1 / Real.sqrt a ≥
        1 / Real.sqrt b - 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) := by
    linarith
  have hid :
      1 / Real.sqrt b - 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) =
        1 / (Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b))) := by
    have hsq : Real.sqrt (1 + Real.sqrt b) ^ (2 : ℕ) = 1 + Real.sqrt b := by
      exact Real.sq_sqrt (by positivity)
    field_simp [hb_pos.ne']
    nlinarith [hsq]
  have hsqrtB : Real.sqrt b ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨hB, by simpa using hbB⟩
  have hsqrt_one : Real.sqrt (1 + Real.sqrt b) ≤ 1 + Real.sqrt b / 2 := by
    have : -(1 : ℝ) ≤ Real.sqrt b := by
      nlinarith [Real.sqrt_nonneg b]
    exact Real.sqrt_one_add_le this
  have hrewrite :
      Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) =
        1 + Real.sqrt b + Real.sqrt (1 + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + Real.sqrt b)]
  have hden :
      Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) ≤
        2 + (3 / 2 : ℝ) * B := by
    rw [hrewrite]
    nlinarith
  have hden_pos :
      0 < Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) := by
    positivity
  have hpos_rhs : 0 < 2 + (3 / 2 : ℝ) * B := by
    positivity
  have htarget :
      1 / (2 + (3 / 2 : ℝ) * B) ≤
        1 / (Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b))) := by
    exact (one_div_le_one_div hpos_rhs hden_pos).2 hden
  rw [hid] at hmain
  linarith

/-- Helper for Theorem 4.1.6: the source recurrence makes the normalized sequence monotone. -/
lemma gradient_dominated_cubic_step_nonincreasing
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ)) :
    ∀ k, δ (k + 1) ≤ δ k := by
  -- The recurrence lower-bounds the drop by a nonnegative quantity.
  intro k
  have hnonneg : 0 ≤ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (hδ_nonneg (k + 1)) _
  linarith [hstep k]

/-- Helper for Theorem 4.1.6: every normalized gap stays below the initial one. -/
lemma gradient_dominated_cubic_step_le_initial
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ)) :
    ∀ k, δ k ≤ δ 0 := by
  -- Iterate monotonicity to compare every later index with `δ 0`.
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      exact le_trans (gradient_dominated_cubic_step_nonincreasing hδ_nonneg hstep k) hk

/-- Helper for Theorem 4.1.6: under the small-gap initial condition, each normalized gap is either
already zero or has the reciprocal lower bound used in part (2). -/
lemma gradient_dominated_cubic_reciprocal_or_zero
    {δ : ℕ → ℝ} {γ : ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ))
    (hγ : 1 < γ) (h0 : δ 0 ≤ γ ^ (2 : ℕ)) :
    ∀ k : ℕ,
      δ k = 0 ∨
        1 / Real.sqrt (δ k) ≥ 1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ) := by
  -- Sum the one-step reciprocal increment, while keeping a separate zero-gap branch to avoid
  -- dividing by `sqrt 0`.
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hγ_nonneg : 0 ≤ γ := hγ_pos.le
  intro k
  induction k with
  | zero =>
      by_cases hzero : δ 0 = 0
      · exact Or.inl hzero
      · have hpos : 0 < δ 0 := lt_of_le_of_ne (hδ_nonneg 0) (Ne.symm hzero)
        have hsqrt_le : Real.sqrt (δ 0) ≤ γ := by
          rw [Real.sqrt_le_iff]
          exact ⟨hγ_nonneg, by simpa using h0⟩
        have hrecip : 1 / γ ≤ 1 / Real.sqrt (δ 0) := by
          exact (one_div_le_one_div hγ_pos (Real.sqrt_pos.mpr hpos)).2 hsqrt_le
        right
        simpa using hrecip
  | succ k hk =>
      rcases hk with hzero | hrecip
      · have hnext_nonneg : 0 ≤ δ (k + 1) := hδ_nonneg (k + 1)
        have hstepk := hstep k
        have hnext_eq : δ (k + 1) = 0 := by
          rw [hzero] at hstepk
          have : 0 ≤ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) :=
            Real.rpow_nonneg hnext_nonneg _
          linarith
        exact Or.inl hnext_eq
      · by_cases hnext_zero : δ (k + 1) = 0
        · exact Or.inl hnext_zero
        · have hnext_pos : 0 < δ (k + 1) := lt_of_le_of_ne (hδ_nonneg (k + 1)) (Ne.symm hnext_zero)
          have hnext_le_gamma_sq : δ (k + 1) ≤ γ ^ (2 : ℕ) := by
            exact le_trans (gradient_dominated_cubic_step_le_initial hδ_nonneg hstep (k + 1)) h0
          have hincr :=
            reciprocal_sqrt_increment_ge_small_gap_constant
              hnext_pos (hstep k) hnext_le_gamma_sq hγ_nonneg
          right
          have hsucc :
              1 / γ + ((k + 1 : ℕ) : ℝ) / (2 + (3 / 2 : ℝ) * γ) =
                (1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ)) +
                  1 / (2 + (3 / 2 : ℝ) * γ) := by
            norm_num [Nat.cast_add]
            ring
          rw [hsucc]
          linarith

/-- Helper for Theorem 4.1.6: a reciprocal-square-root lower bound converts into the exact
inverse-square upper bound from part (2). -/
lemma inverse_square_of_reciprocal_nat
    {δ γ : ℝ} (k : ℕ) (hδ_pos : 0 < δ) (hγ : 0 < γ)
    (hrecip :
      1 / Real.sqrt δ ≥ 1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ)) :
    δ ≤
      γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
        (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ) := by
  -- Rewrite the reciprocal lower bound as a bound on `sqrt δ`, square it, and clear the
  -- denominator algebraically.
  let C : ℝ := 2 + (3 / 2 : ℝ) * γ
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hmul : (1 / γ + (k : ℝ) / C) * Real.sqrt δ ≤ 1 := by
    have htmp := mul_le_mul_of_nonneg_right hrecip (Real.sqrt_nonneg δ)
    have hsqrt : Real.sqrt δ * (1 / Real.sqrt δ) = 1 := by
      field_simp [Real.sqrt_pos.mpr hδ_pos]
    nlinarith [hsqrt]
  have hsq' : ((1 / γ + (k : ℝ) / C) * Real.sqrt δ) ^ (2 : ℕ) ≤ 1 := by
    have hnonneg : 0 ≤ (1 / γ + (k : ℝ) / C) * Real.sqrt δ := by
      positivity
    simpa using pow_le_pow_left₀ hnonneg hmul 2
  have hsqmul : (1 / γ + (k : ℝ) / C) ^ (2 : ℕ) * δ ≤ 1 := by
    have hsqrt_sq : Real.sqrt δ ^ (2 : ℕ) = δ := Real.sq_sqrt hδ_pos.le
    nlinarith [hsq', hsqrt_sq]
  have hAeq : 1 / γ + (k : ℝ) / C = (C + (k : ℝ) * γ) / (γ * C) := by
    dsimp [C]
    field_simp [hγ.ne']
  rw [hAeq] at hsqmul
  have hmul_pos : 0 < γ * C := by
    positivity
  have hcore : (C + (k : ℝ) * γ) ^ (2 : ℕ) * δ ≤ γ ^ (2 : ℕ) * C ^ (2 : ℕ) := by
    field_simp [hmul_pos.ne'] at hsqmul
    nlinarith
  have hden_eq : C + (k : ℝ) * γ = 2 + ((k : ℝ) + 3 / 2) * γ := by
    dsimp [C]
    ring
  have htarget : δ ≤ γ ^ (2 : ℕ) * C ^ (2 : ℕ) / (C + (k : ℝ) * γ) ^ (2 : ℕ) := by
    refine (le_div_iff₀ (by positivity)).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcore
  simpa [C, hden_eq] using htarget

/-- Helper for Theorem 4.1.6: once the gradient-domination witness and the source one-step
descent estimate are available, the large-gap logarithmic phase is exactly the scalar recurrence
argument proved above. -/
lemma gradient_dominated_cubic_log_gap_le_geometric_of_data
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (hdescent :
      ∀ k : ℕ,
        f (method k) - f (method (k + 1)) ≥
          κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))
    (hgap0 : ω̂ ≤ Δ 0) :
    ∀ k : ℕ,
      Real.log (Δ k / ω̂) ≤ (2 / 3 : ℝ) ^ k * Real.log (Δ 0 / ω̂) := by
  let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
  -- The source threshold is positive, so dividing by it preserves the scalar inequalities.
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  -- Normalize the method gaps into the scalar recurrence from the source proof.
  have hδ_nonneg : ∀ k, 0 ≤ δ k := by
    intro k
    exact div_nonneg
      (gradient_dominated_cubic_gap_nonneg
        (method := method) (xStar := xStar) hgradientDominated k)
      hω_pos.le
  have hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) := by
    intro k
    simpa [δ] using
      gradient_dominated_cubic_normalized_gap_step
        (method := method) (xStar := xStar) hgradientDominated hdescent k
  -- The large-gap hypothesis becomes the scalar initial condition `1 ≤ δ 0`.
  have h0 : 1 ≤ δ 0 := by
    refine (le_div_iff₀ hω_pos).2 ?_
    simpa [δ] using hgap0
  -- Apply the scalar logarithmic contraction and rewrite back to `Δ`.
  intro k
  simpa [δ] using
    gradient_dominated_cubic_log_gap_le_geometric_of_step hδ_nonneg hstep h0 k

/-- Helper for Theorem 4.1.6: once the gradient-domination witness and the source one-step
descent estimate are available, the small-gap phase is exactly the reciprocal and inverse-square
scalar argument proved above. -/
lemma gradient_dominated_cubic_gap_le_inverse_square_of_data
    {γ : ℝ}
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (hdescent :
      ∀ k : ℕ,
        f (method k) - f (method (k + 1)) ≥
          κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))
    (hγ : 1 < γ)
    (hgap0 : Δ 0 ≤ γ ^ (2 : ℕ) * ω̂) :
    ∀ k : ℕ,
      Δ k ≤
        ω̂ *
          (γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
            (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ)) := by
  let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
  -- The source threshold is positive, so we can divide through by it and use scalar bounds.
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  -- Normalize the method gaps into the scalar recurrence from the source proof.
  have hδ_nonneg : ∀ k, 0 ≤ δ k := by
    intro k
    exact div_nonneg
      (gradient_dominated_cubic_gap_nonneg
        (method := method) (xStar := xStar) hgradientDominated k)
      hω_pos.le
  have hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) := by
    intro k
    simpa [δ] using
      gradient_dominated_cubic_normalized_gap_step
        (method := method) (xStar := xStar) hgradientDominated hdescent k
  -- The small-gap hypothesis becomes the scalar initial bound `δ 0 ≤ γ^2`.
  have h0 : δ 0 ≤ γ ^ (2 : ℕ) := by
    refine (div_le_iff₀ hω_pos).2 ?_
    simpa [δ] using hgap0
  intro k
  rcases gradient_dominated_cubic_reciprocal_or_zero hδ_nonneg hstep hγ h0 k with hzero | hrecip
  · -- A zero normalized gap means the objective gap itself vanishes.
    have hδk_eq : Δ k / ω̂ = 0 := by
      simpa [δ] using hzero
    have hΔk_eq : Δ k = 0 := by
      have hdiv_zero : Δ k = 0 ∨ ω̂ = 0 := by
        rw [div_eq_zero_iff] at hδk_eq
        exact hδk_eq
      exact hdiv_zero.resolve_right hω_pos.ne'
    rw [hΔk_eq]
    positivity
  · -- In the positive branch, convert the reciprocal bound into the displayed inverse-square law.
    by_cases hδk_zero : δ k = 0
    · have hδk_eq : Δ k / ω̂ = 0 := by
        simpa [δ] using hδk_zero
      have hΔk_eq : Δ k = 0 := by
        have hdiv_zero : Δ k = 0 ∨ ω̂ = 0 := by
          rw [div_eq_zero_iff] at hδk_eq
          exact hδk_eq
        exact hdiv_zero.resolve_right hω_pos.ne'
      rw [hΔk_eq]
      positivity
    · have hδk_pos : 0 < δ k := lt_of_le_of_ne (hδ_nonneg k) (Ne.symm hδk_zero)
      have hδ_bound :
          δ k ≤
            γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
              (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ) := by
        exact inverse_square_of_reciprocal_nat
          k hδk_pos (lt_trans zero_lt_one hγ) hrecip
      have hΔ_eq : ω̂ * δ k = Δ k := by
        change ω̂ * (Δ k / ω̂) = Δ k
        rw [mul_comm, div_mul_cancel₀ _ hω_pos.ne']
      calc
        Δ k = ω̂ * δ k := by simpa using hΔ_eq.symm
        _ ≤ ω̂ *
              (γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
                (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hδ_bound hω_pos.le

-- Proof sketch: combine the assumed one-step estimate
-- `f(x_k) - f(x_{k+1}) ≥ κ ‖∇ f(x_{k+1})‖^(3/2)` with the degree-one
-- gradient-domination inequality to obtain the scalar
-- recurrence `δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}` for the normalized gaps `δ_k = Δ k / hatω`. Then
-- use
-- `log δ_k ≥ (3 / 2) log δ_{k+1}` and iterate to get the geometric decay of the logarithm.
include hgradientDominated hdescent

/-- Theorem 4.1.6 (1): if the initial objective gap is at least `hatω`, then the normalized
suboptimality logarithm along the cubic-regularized Newton iterates contracts by the factor
`(2 / 3)^k`. -/
theorem gradientDominated_cubicRegularization_log_gap_le_geometric
    (hgap0 : ω̂ ≤ Δ 0) :
    ∀ k : ℕ,
      Real.log (Δ k / ω̂) ≤ (2 / 3 : ℝ) ^ k * Real.log (Δ 0 / ω̂) := by
  -- Reuse the source-faithful scalar recurrence proof already assembled in the data lemma.
  intro k
  simpa using
    gradient_dominated_cubic_log_gap_le_geometric_of_data
      (method := method) (xStar := xStar) hgradientDominated hdescent hgap0 k

-- Proof sketch: derive the same scalar recurrence
-- `δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}`, then derive the reciprocal estimate
-- `1 / sqrt δ_{k+1} - 1 / sqrt δ_k ≥ 1 / (2 + (3 / 2) * sqrt δ_0)` under the small-gap
-- hypothesis `δ_0 ≤ γ^2`. Summing this inequality yields
-- `1 / sqrt δ_k ≥ 1 / γ + k / (2 + (3 / 2) * γ)`, which rearranges to the displayed
-- inverse-square bound for `Δ k`.
/-- Theorem 4.1.6 (2): if the initial objective gap is at most `γ^2 hatω` for some `γ > 1`,
then every cubic-regularized Newton iterate satisfies the inverse-square upper bound from
equation `(4.1.36)`. -/
theorem gradientDominated_cubicRegularization_gap_le_inverse_square
    {γ : ℝ} (hγ : 1 < γ)
    (hgap0 : Δ 0 ≤ γ ^ (2 : ℕ) * ω̂) :
    ∀ k : ℕ,
      Δ k ≤
        ω̂ *
          (γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
            (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ)) := by
  -- Reuse the source-faithful scalar reciprocal argument already assembled in the data lemma.
  intro k
  simpa using
    gradient_dominated_cubic_gap_le_inverse_square_of_data
      (method := method) (xStar := xStar) hgradientDominated hdescent hγ hgap0 k

omit hgradientDominated hdescent

end GradientDominatedCubicRegularization

end
