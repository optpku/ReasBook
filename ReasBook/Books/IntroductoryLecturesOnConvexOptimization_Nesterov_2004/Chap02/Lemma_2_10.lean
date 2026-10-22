/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace OptimalMethodRecurrence

variable {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}

open Real
open scoped StrongConvexSmooth

local notation "qf" => q[μ, L]

/-
Primary domain: scalar weight recurrences attached to the chapter's optimal-method estimating
sequences.

Owner declarations sampled before refining this file:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, which owns the trajectory data and the scalar
  recurrences `αₖ`, `γₖ`;
* `OptimalMethodRecurrence.weight`, `OptimalMethodRecurrence.weight_pos`, and
  `OptimalMethodRecurrence.gamma_sub_mu_eq_weight_mul_initial_gap` in `Algorithm_2_2`, which own
  the canonical estimating-sequence weight `λₖ` and its basic scalar recurrence API;
* `OptimalMethodRecurrence.gamma_succ_eq_L_mul_sq` in `Algorithm_2_2`, which converts the owner
  curvature update into the scalar quadratic identity used in this lemma;
* `optimal_method_alpha0_initial_curvature` in `Algorithm_2_4`, which is only a downstream
  bridge `α₀ ↦ γ₀`, not a second owner for the same weight sequence.

Layer triage:
* `source-facing`: the textbook upper bounds on the owner weight sequence and the `γ₀ = μ`
  closed form;
* `core/canonical`: `OptimalMethodRecurrence` together with `weight`;
* `bridge/view`: later reparametrizations of `γ₀` in terms of `α₀`.

Primitive data:
* the owner recurrence `method`;
* the positivity / interval hypotheses on `μ` and `γ₀` when they change the mathematics.

Derived API:
* the hyperbolic and quadratic upper bounds for `method.weight k`;
* the geometric closed form when `γ₀ = μ`.

The redundant public inequality `μ ≤ L` is not kept below: in the interval case it follows from
the owner recurrence together with `γ₀ ∈ (μ, 3L + μ]`, and in the `γ₀ = μ` case the owner
recurrence already forces the required range conditions.
-/

/-- Helper for Lemma 2.10: when `γ₀ ∈ (μ, 3L + μ]`, the owner recurrence forces `μ < L`. -/
lemma mu_lt_L_of_interval_init
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    μ < L := by
  have halpha0 : method.alpha 0 ∈ Set.Ioo (0 : ℝ) 1 := method.alpha_mem_Ioo 0
  have hgamma1_gt : μ < method.gamma 1 := by
    -- The owner curvature-gap identity stays positive at `k = 1`.
    have hgap1 := gamma_sub_mu_eq_weight_mul_initial_gap method 1
    have hpos : 0 < method.weight 1 * (gamma0 - μ) := by
      exact mul_pos (weight_pos method 1) (sub_pos.mpr hgamma0.1)
    linarith
  have hgamma1_lt : method.gamma 1 < L := by
    -- The quadratic identity rewrites `γ₁` as `L α₀²`, and `α₀ ∈ (0, 1)` makes this `< L`.
    rw [method.gamma_succ_eq_L_mul_sq 0]
    have hsq_lt : method.alpha 0 ^ (2 : ℕ) < 1 := by
      nlinarith [halpha0.1, halpha0.2]
    nlinarith [method.L_pos, hsq_lt]
  linarith

/-- Helper for Lemma 2.10: the interval hypothesis implies `q[μ, L] ∈ (0, 1)`. -/
lemma qf_mem_Ioo_of_interval_init
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    q[μ, L] ∈ Set.Ioo (0 : ℝ) 1 := by
  have hμL : μ < L := mu_lt_L_of_interval_init method hgamma0
  exact ⟨div_pos hμ method.L_pos, (div_lt_one method.L_pos).2 hμL⟩

/-- Helper for Lemma 2.10: `1 - sqrt (1 - a)` always dominates `a / 2` on `[0, 1]`. -/
lemma half_le_one_sub_sqrt_sub
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.sqrt (1 - a) := by
  -- Squaring the auxiliary square root reduces the claim to a quadratic identity.
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - a) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (1 - a)) ^ (2 : ℕ) = 1 - a := by
    rw [Real.sq_sqrt]
    linarith
  nlinarith

/-- Helper for Lemma 2.10: the rescaled inverse-square-root weight satisfies the one-step
lower bound coming from the owner scalar recurrence. -/
lemma weight_xi_step_lower_bound
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (j : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
    ξ (j + 1) - ξ j ≥
      (1 / 2 : ℝ) * Real.sqrt (1 + q[μ, L] * ξ (j + 1) ^ (2 : ℕ)) := by
  dsimp
  have hgap : 0 < gamma0 - μ := by
    linarith [hγ0.1]
  have hα0 : 0 ≤ method.alpha j := (method.alpha_mem_Ioo j).1.le
  have hα1 : method.alpha j < 1 := (method.alpha_mem_Ioo j).2
  have hwj : 0 < method.weight j := weight_pos method j
  have hwj1 : 0 < method.weight (j + 1) := weight_pos method (j + 1)
  have hξj :
      Real.sqrt (L / ((gamma0 - μ) * method.weight j)) =
        Real.sqrt (1 - method.alpha j) *
          Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
    -- Rewrite `ξ_j` using the exact weight recurrence `λ_{j+1} = (1 - α_j) λ_j`.
    have hrew :
        L / ((gamma0 - μ) * method.weight j) =
          (1 - method.alpha j) * (L / ((gamma0 - μ) * method.weight (j + 1))) := by
      rw [method.weight_succ]
      field_simp [hgap.ne', hwj.ne', sub_ne_zero.mpr hα1.ne']
    rw [hrew, Real.sqrt_mul (sub_nonneg.mpr hα1.le)]
  have hroot :
      Real.sqrt
          (1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ)) =
        method.alpha j *
          Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
    -- The quadratic owner identity rewrites the square root exactly as `α_j ξ_{j+1}`.
    have hξsq :
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) =
          L / ((gamma0 - μ) * method.weight (j + 1)) := by
      rw [Real.sq_sqrt]
      apply div_nonneg
      · exact method.L_pos.le
      · positivity
    have hgapw :
        (gamma0 - μ) * method.weight (j + 1) = method.gamma (j + 1) - μ := by
      simpa [mul_comm] using
        (gamma_sub_mu_eq_weight_mul_initial_gap method (j + 1)).symm
    have hsq :
        1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) =
          method.alpha j ^ (2 : ℕ) *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) := by
      rw [hξsq]
      rw [method.gamma_succ_eq_L_mul_sq j] at hgapw
      field_simp [method.L_pos.ne', hgap.ne', hwj1.ne'] at hgapw ⊢
      nlinarith
    have hnonneg :
        0 ≤
          method.alpha j *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
      positivity
    rw [hsq, ← mul_pow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  calc
    Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) -
        Real.sqrt (L / ((gamma0 - μ) * method.weight j))
        =
      (1 - Real.sqrt (1 - method.alpha j)) *
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
          rw [hξj]
          ring
    _ ≥ (method.alpha j / 2) *
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
          -- The scalar inequality `1 - sqrt (1 - α_j) ≥ α_j / 2` finishes the discrete step.
          gcongr
          exact half_le_one_sub_sqrt_sub hα0 hα1.le
    _ = (1 / 2 : ℝ) *
        Real.sqrt
          (1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ)) := by
          rw [hroot]
          ring

/-- Helper for Lemma 2.10: a one-step lower bound of the form
`b - a ≥ δ * sqrt (1 + b^2)` implies an additive `arsinh` increment. -/
lemma arsinh_sub_ge_of_sub_ge_mul_sqrt
    {a b δ : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hδ : 0 ≤ δ)
    (hstep : b - a ≥ δ * Real.sqrt (1 + b ^ (2 : ℕ))) :
    δ ≤ Real.arsinh b - Real.arsinh a := by
  by_cases hab_eq : a = b
  · -- In the degenerate case, the step inequality already forces `δ = 0`.
    subst hab_eq
    have hδ_zero : δ = 0 := by
      have hsqrt_pos : 0 < Real.sqrt (1 + a ^ (2 : ℕ)) := by positivity
      nlinarith
    simp [hδ_zero]
  · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    rcases exists_deriv_eq_slope Real.arsinh hab_lt Real.continuous_arsinh.continuousOn
        (fun x hx ↦ (Real.hasDerivAt_arsinh x).differentiableAt.differentiableWithinAt) with
      ⟨c, hc, hcderiv⟩
    have hc_nonneg : 0 ≤ c := le_trans ha hc.1.le
    have hsqrt_le :
        Real.sqrt (1 + c ^ (2 : ℕ)) ≤ Real.sqrt (1 + b ^ (2 : ℕ)) := by
      gcongr
      nlinarith [hc_nonneg, hc.2.le]
    have hderiv_lb :
        (Real.sqrt (1 + b ^ (2 : ℕ)))⁻¹ ≤ deriv Real.arsinh c := by
      -- The derivative of `arsinh` decreases on `[0, ∞)`, so the slope is bounded below by
      -- its right-endpoint value.
      have h_inv :
          (Real.sqrt (1 + b ^ (2 : ℕ)))⁻¹ ≤
            (Real.sqrt (1 + c ^ (2 : ℕ)))⁻¹ := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by positivity) hsqrt_le)
      simpa using h_inv.trans_eq (by simpa using (Real.hasDerivAt_arsinh c).deriv.symm)
    have hsqrt_pos : 0 < Real.sqrt (1 + b ^ (2 : ℕ)) := by positivity
    have hδ_le_div : δ ≤ (b - a) / Real.sqrt (1 + b ^ (2 : ℕ)) := by
      rw [le_div_iff₀ hsqrt_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
    have hmul_le :
        (b - a) / Real.sqrt (1 + b ^ (2 : ℕ)) ≤
          (b - a) * deriv Real.arsinh c := by
      have hba_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hderiv_lb hba_nonneg
    have hslope_eq :
        Real.arsinh b - Real.arsinh a = (b - a) * deriv Real.arsinh c := by
      -- Lagrange's theorem turns the difference of `arsinh` values into an exact slope.
      have hmul := congrArg (fun t ↦ t * (b - a)) hcderiv
      have hne : b - a ≠ 0 := sub_ne_zero.mpr hab_lt.ne'
      field_simp [hne] at hmul
      linarith
    exact (hδ_le_div.trans hmul_le).trans_eq hslope_eq.symm

/-- Helper for Lemma 2.10: the interval constraint on `γ₀` gives the base lower bound for the
rescaled inverse-square-root weight `ξ₀`. -/
lemma initial_weight_xi_lower_bound
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    1 / Real.sqrt 3 ≤ Real.sqrt (L / (gamma0 - μ)) := by
  -- Rewriting `γ₀ - μ ≤ 3L` as a reciprocal estimate gives the textbook base bound on `ξ₀`.
  have hgap_pos : 0 < gamma0 - μ := by
    linarith [hγ0.1]
  have hdiv_le : (1 : ℝ) / 3 ≤ L / (gamma0 - μ) := by
    have hgap_le : gamma0 - μ ≤ 3 * L := by
      linarith [hγ0.2]
    field_simp [hgap_pos.ne', (show (3 : ℝ) ≠ 0 by norm_num)]
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hdiv_le
  have hleft : Real.sqrt ((1 : ℝ) / 3) = 1 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (3 : ℝ), Real.sqrt_one]
  simpa [hleft] using hsqrt

/-- Helper for Lemma 2.10: on `[0, 1]`, the scalar map `s ↦ arsinh (s / √3)` dominates `s / 2`.
-/
lemma half_le_arsinh_div_sqrt_three
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s / 2 ≤ Real.arsinh (s / Real.sqrt 3) := by
  let h : ℝ → ℝ := fun t ↦ Real.arsinh (t / Real.sqrt 3) - t / 2
  have hcont : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have harsinh :
        ContinuousAt (fun t : ℝ ↦ Real.arsinh (t / Real.sqrt 3)) x :=
      continuous_arsinh.continuousAt.comp
        (continuousAt_id.div_const (Real.sqrt 3))
    exact (harsinh.sub (continuousAt_id.div_const 2)).continuousWithinAt
  have hderiv :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivWithinAt h
          ((((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) - 1 / 2)
          (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    have harsinh :
        HasDerivAt (fun t : ℝ ↦ Real.arsinh (t / Real.sqrt 3))
          (((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) x := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_arsinh (x / Real.sqrt 3)).comp x
          ((hasDerivAt_id x).div_const (Real.sqrt 3))
    simpa [h] using
      harsinh.hasDerivWithinAt.sub ((hasDerivAt_id x).div_const 2).hasDerivWithinAt
  have hderiv_nonneg :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
        0 ≤ (((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) - 1 / 2 := by
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt3_ne : Real.sqrt 3 ≠ 0 := hsqrt3_pos.ne'
    have hx_sq_le : x ^ (2 : ℕ) ≤ 1 := by
      nlinarith [hx.1.le, hx.2.le]
    have hsq_eq : (x / Real.sqrt 3) ^ (2 : ℕ) = x ^ (2 : ℕ) / 3 := by
      field_simp [pow_two, hsqrt3_ne]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hinside_le : 1 + (x / Real.sqrt 3) ^ (2 : ℕ) ≤ 4 / 3 := by
      rw [hsq_eq]
      nlinarith
    have hsqrt_le : Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)) ≤ 2 / Real.sqrt 3 := by
      refine (Real.sqrt_le_sqrt hinside_le).trans_eq ?_
      have hfour : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
      have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
      calc
        Real.sqrt (4 / 3 : ℝ) = Real.sqrt 4 / Real.sqrt 3 := by
          rw [Real.sqrt_div h4_nonneg (3 : ℝ)]
        _ = 2 / Real.sqrt 3 := by simp [hfour]
    have hInv :
        (1 / (2 / Real.sqrt 3 : ℝ)) ≤
          1 / Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)) :=
      one_div_le_one_div_of_le (by positivity) hsqrt_le
    have hmul := mul_le_mul_of_nonneg_right hInv
      (by positivity : 0 ≤ (1 / Real.sqrt 3 : ℝ))
    have hhalf : (1 / 2 : ℝ) = (1 / (2 / Real.sqrt 3 : ℝ)) * (1 / Real.sqrt 3) := by
      have hrewrite : (1 / 2 : ℝ) = (Real.sqrt 3 / 2) * (1 / Real.sqrt 3) := by
        field_simp [hsqrt3_ne]
      simpa [one_div_div] using hrewrite
    have hderiv_ge_half :
        (1 / 2 : ℝ) ≤ ((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3 := by
      calc
        (1 / 2 : ℝ) = (1 / (2 / Real.sqrt 3 : ℝ)) * (1 / Real.sqrt 3) := hhalf
        _ ≤ (1 / Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ))) * (1 / Real.sqrt 3) := hmul
        _ = ((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3 := by
            ring_nf
    linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    hcont hderiv hderiv_nonneg
  have hzero : h 0 = 0 := by
    simp [h]
  have hstep : h 0 ≤ h s := hmono (by simp) ⟨hs0, hs1⟩ hs0
  -- Evaluating the monotone auxiliary function at `0` and `s` gives the desired bound.
  simpa [h, hzero] using hstep

/-- Helper for Lemma 2.10: the interval initialization already satisfies the base `arsinh`
barrier used in the discrete induction. -/
lemma initial_arsinh_barrier
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    Real.sqrt q[μ, L] / 2 ≤
      Real.arsinh (Real.sqrt q[μ, L] * Real.sqrt (L / (gamma0 - μ))) := by
  -- Combine the scalar interval estimate `ξ₀ ≥ 1 / √3` with the monotone `arsinh` bridge.
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hγ0
  have hs0 : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
  have hs1 : Real.sqrt qf ≤ 1 := by
    simpa using (Real.sqrt_le_one.2 hqf.2.le)
  have hbase :
      Real.sqrt qf / 2 ≤ Real.arsinh (Real.sqrt qf / Real.sqrt 3) :=
    half_le_arsinh_div_sqrt_three hs0 hs1
  have hxi0 :
      Real.sqrt qf / Real.sqrt 3 ≤
        Real.sqrt qf * Real.sqrt (L / (gamma0 - μ)) := by
    have hξ := initial_weight_xi_lower_bound hγ0
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hξ hs0
  exact hbase.trans ((Real.arsinh_le_arsinh).2 hxi0)

/-- Helper for Lemma 2.10: the discrete `arsinh` barrier accumulated along the `ξ` recurrence. -/
lemma weight_xi_arsinh_lower_bound
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
    (((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2) ≤
      Real.arsinh (Real.sqrt q[μ, L] * ξ k) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hγ0
  induction k with
  | zero =>
      -- The new standalone base barrier matches the `k = 0` case after `weight_zero`.
      simpa [ξ] using initial_arsinh_barrier method hμ hγ0
  | succ k ih =>
      -- The step recurrence for `ξ` yields an additive `arsinh` increment after rescaling by `√qf`.
      have ih' :
          (((k + 1 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ k) := by
        simpa [ξ] using ih
      have hstep :
          ξ (k + 1) - ξ k ≥
            (1 / 2 : ℝ) * Real.sqrt (1 + qf * ξ (k + 1) ^ (2 : ℕ)) := by
        simpa [ξ] using weight_xi_step_lower_bound method hγ0 k
      have hξ_nonneg : 0 ≤ ξ k := by
        dsimp [ξ]
        positivity
      have hscaled_step :
          Real.sqrt qf * ξ (k + 1) - Real.sqrt qf * ξ k ≥
            (Real.sqrt qf / 2) *
              Real.sqrt (1 + qf * ξ (k + 1) ^ (2 : ℕ)) := by
        have hmul := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg qf)
        nlinarith
      have hscaled_step' :
          Real.sqrt qf * ξ (k + 1) - Real.sqrt qf * ξ k ≥
            (Real.sqrt qf / 2) *
              Real.sqrt (1 + (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ)) := by
        have hsq_rewrite :
            qf * ξ (k + 1) ^ (2 : ℕ) = (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ) := by
          nlinarith [Real.sq_sqrt hqf.1.le]
        simpa [hsq_rewrite] using hscaled_step
      have hξ_mono :
          Real.sqrt qf * ξ k ≤ Real.sqrt qf * ξ (k + 1) := by
        have hstep_nonneg :
            0 ≤
              (Real.sqrt qf / 2) *
                Real.sqrt (1 + (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ)) := by
          positivity
        nlinarith [hscaled_step', hstep_nonneg]
      have hscaled_nonneg : 0 ≤ Real.sqrt qf * ξ k := by
        positivity
      have harsinh_step :
          Real.sqrt qf / 2 ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) -
              Real.arsinh (Real.sqrt qf * ξ k) := by
        exact arsinh_sub_ge_of_sub_ge_mul_sqrt hscaled_nonneg hξ_mono
          (by positivity) hscaled_step'
      have hacc :
          (((k + 1 : ℝ) * Real.sqrt qf) / 2) + Real.sqrt qf / 2 ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        linarith
      have hacc' :
          (((k + 2 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        have hrewrite :
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) + Real.sqrt qf / 2 =
              (((k + 2 : ℝ) * Real.sqrt qf) / 2) := by
          ring
        rw [← hrewrite]
        exact hacc
      have hacc'' :
          (((k + 1 + 1 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        have hrewrite' :
            (((k + 1 + 1 : ℝ) * Real.sqrt qf) / 2) =
              (((k + 2 : ℝ) * Real.sqrt qf) / 2) := by
          ring
        rw [hrewrite']
        exact hacc'
      simpa [ξ] using hacc''

/-- Helper for Lemma 2.10: the hyperbolic denominator dominates the quadratic one because
`t ≤ sinh t` on `[0, ∞)`. -/
lemma hyperbolic_bound_le_quadratic_bound
    (hμ : 0 < μ)
    (hL : 0 < L)
    (hgap : 0 < gamma0 - μ)
    (hqf : q[μ, L] ∈ Set.Ioo (0 : ℝ) 1)
    (k : ℕ) :
    let t := ((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2
    4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ)) ≤
      4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  dsimp
  have ht_nonneg : 0 ≤ ((k + 1 : ℝ) * Real.sqrt qf) / 2 := by positivity
  have ht_pos : 0 < ((k + 1 : ℝ) * Real.sqrt qf) / 2 := by positivity
  have hsinh_eq :
      Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
          Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2)) =
        2 * Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
    rw [Real.sinh_eq]
    ring
  have hhyper_eq :
      4 * μ /
          ((gamma0 - μ) *
            (Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
                Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2))) ^ (2 : ℕ)) =
        μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
    calc
      4 * μ /
          ((gamma0 - μ) *
            (Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
                Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2))) ^ (2 : ℕ))
          =
        4 * μ /
          ((gamma0 - μ) *
            (2 * Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2)) ^ (2 : ℕ)) := by
              rw [hsinh_eq]
      _ =
        μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
              by_cases hs :
                  Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) = 0
              · simp [hs]
              · field_simp [hs]
                ring
  have hsinh_ge :
      ((k + 1 : ℝ) * Real.sqrt qf) / 2 ≤
        Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
    exact (Real.self_le_sinh_iff).2 ht_nonneg
  have hsinh_sq_ge :
      (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) ≤
        Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) := by
    have hsinh_nonneg :
        0 ≤ Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
      exact (Real.sinh_nonneg_iff).2 ht_nonneg
    nlinarith [hsinh_ge, hsinh_nonneg]
  have hmono :
      μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) ≤
        μ /
          ((gamma0 - μ) *
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
    have hdenom_le :
        (gamma0 - μ) * (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) ≤
          (gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) := by
      gcongr
    have hInv :
        1 /
            ((gamma0 - μ) *
              Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) ≤
          1 /
            ((gamma0 - μ) *
              (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
      exact one_div_le_one_div_of_le (by positivity) hdenom_le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hInv hμ.le
  have hquad_eq :
      μ /
          ((gamma0 - μ) *
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) =
        4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    field_simp [hL.ne', hgap.ne']
    rw [Real.sq_sqrt hqf.1.le, div_eq_mul_inv]
    ring_nf
    field_simp [hL.ne']
  exact hhyper_eq.trans_le (hmono.trans_eq hquad_eq)

/-- Lemma 2.10: if an optimal-method recurrence has `μ > 0` and initial curvature
`γ₀ ∈ (μ, 3L + μ]`, then its canonical estimating-sequence weight `λₖ = method.weight k` is
bounded above by the stated hyperbolic expression, and that hyperbolic bound is itself bounded
above by `4L / ((γ₀ - μ) (k + 1)^2)`. -/
-- Proof sketch: first use the step-`(a)` recurrences for `γ_k` and `λ_k` to show
-- `γ_{k+1} - μ = λ_{k+1} (γ₀ - μ)`. Substitute this identity into the quadratic equation from
-- step `(a)` to obtain a scalar recurrence for `λ_k`, introduce
-- `ξ_k = sqrt (L / ((γ₀ - μ) λ_k))`, prove the claimed hyperbolic lower bound on `ξ_k` by
-- induction, and then translate that estimate back into the two displayed upper bounds for `λ_k`.
theorem weight_bounds
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    let t := ((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2
    let hyperbolicBound :=
      4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ))
    method.weight k ≤ hyperbolicBound ∧
      hyperbolicBound ≤ 4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
  let t := ((k + 1 : ℝ) * Real.sqrt qf) / 2
  let hyperbolicBound :=
    4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ))
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hgamma0
  have hgap : 0 < gamma0 - μ := by
    linarith [hgamma0.1]
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_pos : 0 < t := by
    dsimp [t]
    have hsqrt_qf_pos : 0 < Real.sqrt qf := Real.sqrt_pos.2 hqf.1
    have hk_pos : 0 < (k + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos k
    positivity
  have hxi_nonneg : 0 ≤ ξ k := by
    dsimp [ξ]
    positivity
  have hsinh_le : Real.sinh t ≤ Real.sqrt qf * ξ k := by
    -- Applying `sinh` to the discrete `arsinh` barrier exposes the exact lower bound on `ξ_k`.
    simpa [t, ξ] using
      (Real.sinh_le_sinh).2 (weight_xi_arsinh_lower_bound method hμ hgamma0 k)
  have hsinh_sq_le :
      Real.sinh t ^ (2 : ℕ) ≤ qf * ξ k ^ (2 : ℕ) := by
    have hsinh_nonneg : 0 ≤ Real.sinh t := (Real.sinh_nonneg_iff).2 ht_nonneg
    have hscaled_nonneg : 0 ≤ Real.sqrt qf * ξ k := by positivity
    have hsinh_sq_le_scaled :
        Real.sinh t ^ (2 : ℕ) ≤ (Real.sqrt qf * ξ k) ^ (2 : ℕ) := by
      nlinarith
    have hscaled_sq : (Real.sqrt qf * ξ k) ^ (2 : ℕ) = qf * ξ k ^ (2 : ℕ) := by
      nlinarith [Real.sq_sqrt hqf.1.le]
    exact hsinh_sq_le_scaled.trans_eq hscaled_sq
  have hξ_sq : ξ k ^ (2 : ℕ) = L / ((gamma0 - μ) * method.weight k) := by
    dsimp [ξ]
    rw [Real.sq_sqrt]
    apply div_nonneg
    · exact method.L_pos.le
    · exact mul_nonneg hgap.le (weight_pos method k).le
  have hqf_xi_sq :
      qf * ξ k ^ (2 : ℕ) = μ / ((gamma0 - μ) * method.weight k) := by
    let A := (gamma0 - μ) * method.weight k
    have hcancelL : (μ / L) * L = μ := by
      calc
        (μ / L) * L = μ * (L / L) := by
          field_simp [method.L_pos.ne']
        _ = μ := by
          have hLL : L / L = (1 : ℝ) := div_self method.L_pos.ne'
          calc
            μ * (L / L) = μ * 1 := by rw [hLL]
            _ = μ := by ring
    calc
      qf * ξ k ^ (2 : ℕ) =
          (μ / L) * (L / A) := by
            rw [hξ_sq]
      _ = ((μ / L) * L) * A⁻¹ := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ = μ * A⁻¹ := by
            rw [hcancelL]
      _ = μ / ((gamma0 - μ) * method.weight k) := by
            dsimp [A]
            rw [div_eq_mul_inv]
  have hsinh_sq_le' :
      Real.sinh t ^ (2 : ℕ) ≤ μ / ((gamma0 - μ) * method.weight k) := by
    simpa [hqf_xi_sq] using hsinh_sq_le
  have hfirst_aux :
      method.weight k ≤ μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ)) := by
    have hden_pos : 0 < (gamma0 - μ) * Real.sinh t ^ (2 : ℕ) := by
      positivity
    refine (le_div_iff₀ hden_pos).2 ?_
    have hweight_factor_nonneg : 0 ≤ (gamma0 - μ) * method.weight k := by
      exact mul_nonneg hgap.le (weight_pos method k).le
    have hmul := mul_le_mul_of_nonneg_left hsinh_sq_le' hweight_factor_nonneg
    have hcancel :
        ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k)) = μ := by
      have hAne : ((gamma0 - μ) * method.weight k) ≠ 0 :=
        mul_ne_zero hgap.ne' (weight_pos method k).ne'
      calc
        ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k))
            = μ * (((gamma0 - μ) * method.weight k) / ((gamma0 - μ) * method.weight k)) := by
                ring
        _ = μ * 1 := by rw [div_self hAne]
        _ = μ := by ring
    calc
      method.weight k * ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ))
          = ((gamma0 - μ) * method.weight k) * Real.sinh t ^ (2 : ℕ) := by ring
      _ ≤ ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = μ := hcancel
  have hsinh_eq :
      Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    rw [Real.sinh_eq]
    ring
  have hhyper_eq :
      μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ)) = hyperbolicBound := by
    dsimp [hyperbolicBound]
    calc
      μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ))
          =
        4 * μ / ((gamma0 - μ) * (2 * Real.sinh t) ^ (2 : ℕ)) := by
            by_cases hs : Real.sinh t = 0
            · exfalso
              exact (Real.sinh_pos_iff.2 ht_pos).ne' hs
            · field_simp [hs]
              ring
      _ = 4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ)) := by
            rw [hsinh_eq]
  have hfirst : method.weight k ≤ hyperbolicBound := by
    exact hfirst_aux.trans_eq hhyper_eq
  have hsecond : hyperbolicBound ≤ 4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    simpa [t, hyperbolicBound] using
      hyperbolic_bound_le_quadratic_bound hμ method.L_pos hgap hqf k
  exact ⟨hfirst, hsecond⟩

/-- Helper for Lemma 2.10: if the initial curvature equals `μ`, then every later curvature also
equals `μ`. -/
lemma gamma_eq_mu_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ) (k : ℕ) :
    method.gamma k = μ := by
  -- The shared curvature-gap identity collapses because the initial gap is zero.
  have hgap : method.gamma k - μ = 0 := by
    simpa using gamma_sub_mu_eq_weight_mul_initial_gap method k
  linarith

/-- Helper for Lemma 2.10: in the `γ₀ = μ` regime, each owner scalar `α_k` is exactly
`sqrt q[μ, L]`. -/
lemma alpha_eq_sqrt_qf_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ) (k : ℕ) :
    method.alpha k = Real.sqrt q[μ, L] := by
  have hL : 0 < L := method.L_pos
  have hgamma : μ = L * method.alpha k ^ (2 : ℕ) := by
    simpa [gamma_eq_mu_of_gamma0_eq_mu method (k + 1)] using method.gamma_succ_eq_L_mul_sq k
  have hsq : method.alpha k ^ (2 : ℕ) = qf := by
    -- The curvature identity `γ_{k+1} = L α_k²` becomes `μ = L α_k²`.
    apply (eq_div_iff hL.ne').2
    simpa [mul_comm] using hgamma.symm
  have hsqrt_sq : (Real.sqrt qf) ^ (2 : ℕ) = qf := by
    apply Real.sq_sqrt
    exact div_nonneg method.mu_nonneg method.L_pos.le
  have hsq_eq : method.alpha k ^ (2 : ℕ) = (Real.sqrt qf) ^ (2 : ℕ) := by
    rw [hsq, hsqrt_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with halpha | halpha
  · exact halpha
  · have halpha_pos : 0 < method.alpha k := method.alpha_pos k
    have hsqrt_nonneg : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
    linarith

/-- If an optimal-method recurrence is initialized with `γ₀ = μ`, expressed by specializing the
owner to `OptimalMethodRecurrence f L μ x0 μ`, then its canonical estimating-sequence weight is
the geometric progression `(1 - sqrt q[μ, L])^k`. -/
-- Proof sketch: from `γ₀ = μ` and the curvature recurrence, prove by induction that every
-- `γ_k = μ`. The quadratic equation from step `(a)` then forces `α_k = sqrt q[μ, L]` for all
-- `k`, and the recurrence `λ_{k+1} = (1 - α_k) λ_k` yields the displayed closed form.
theorem weight_eq_geometric_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ)
    (k : ℕ) :
    method.weight k = (1 - Real.sqrt q[μ, L]) ^ k := by
  induction k with
  | zero =>
      -- The zeroth weight is `1`, matching the zeroth geometric term.
      simp
  | succ k ih =>
      -- Once `α_k = sqrt q[μ, L]`, the owner weight recurrence becomes a constant-coefficient
      -- geometric recurrence.
      rw [method.weight_succ, ih, alpha_eq_sqrt_qf_of_gamma0_eq_mu method]
      simp [pow_succ, mul_comm]

-- The remaining `μ = 0`, `γ₀ = 3L` endpoint is handled by a direct specialization of the
-- previously built `ξ` machinery.
/-- Helper for Lemma 2.10: in the smooth-convex endpoint case `μ = 0`, `γ₀ = 3L`, the
rescaled inverse-square-root weight gains at least `1 / 2` at each step. -/
lemma weightXiStepHalfOfGamma0EqThreeMul
    (method : OptimalMethodRecurrence f L 0 x0 (3 * L))
    (j : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((3 * L) * method.weight m))
    ξ (j + 1) - ξ j ≥ (1 / 2 : ℝ) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((3 * L) * method.weight m))
  have hγ0 : (3 * L : ℝ) ∈ Set.Ioc (0 : ℝ) (3 * L + 0) := by
    constructor
    · nlinarith [method.L_pos]
    · simp
  -- Specializing the general `ξ` step bound to `q[0, L] = 0` removes the square-root factor.
  have hstep :
      ξ (j + 1) - ξ j ≥
        (1 / 2 : ℝ) * Real.sqrt (1 + q[(0 : ℝ), L] * ξ (j + 1) ^ (2 : ℕ)) := by
    simpa [ξ] using weight_xi_step_lower_bound method hγ0 j
  have hq_zero : q[(0 : ℝ), L] = 0 := by
    simp
  calc
    ξ (j + 1) - ξ j
        ≥ (1 / 2 : ℝ) * Real.sqrt (1 + q[(0 : ℝ), L] * ξ (j + 1) ^ (2 : ℕ)) := hstep
    _ = (1 / 2 : ℝ) := by simp [hq_zero]

/-- Helper for Lemma 2.10: in the smooth-convex endpoint case `μ = 0`, `γ₀ = 3L`, the
rescaled inverse-square-root weight dominates the affine barrier `1 / √3 + k / 2`. -/
lemma weightXiAffineLowerBoundOfGamma0EqThreeMul
    (method : OptimalMethodRecurrence f L 0 x0 (3 * L))
    (k : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((3 * L) * method.weight m))
    1 / Real.sqrt 3 + k / 2 ≤ ξ k := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((3 * L) * method.weight m))
  have hγ0 : (3 * L : ℝ) ∈ Set.Ioc (0 : ℝ) (3 * L + 0) := by
    constructor
    · nlinarith [method.L_pos]
    · simp
  induction k with
  | zero =>
      -- The initial barrier is exactly the interval base case specialized to `γ₀ = 3L`.
      simpa [ξ] using
        (initial_weight_xi_lower_bound (μ := (0 : ℝ)) (L := L) (gamma0 := 3 * L) hγ0)
  | succ k ih =>
      -- Adding the constant one-step increment turns the base barrier into an affine lower bound.
      have hih : 1 / Real.sqrt 3 + (k : ℝ) / 2 ≤ ξ k := by
        simpa using ih
      have hstep : ξ (k + 1) - ξ k ≥ (1 / 2 : ℝ) := by
        simpa [ξ] using weightXiStepHalfOfGamma0EqThreeMul method k
      calc
        1 / Real.sqrt 3 + ((k + 1 : ℕ) : ℝ) / 2
            = (1 / Real.sqrt 3 + (k : ℝ) / 2) + 1 / 2 := by
                rw [Nat.cast_add, Nat.cast_one]
                ring
        _ ≤ ξ k + (ξ (k + 1) - ξ k) := by gcongr
        _ = ξ (k + 1) := by ring

/-- Helper for Lemma 2.10: in the smooth-convex endpoint case `μ = 0`, `γ₀ = 3L`, the owner
weight satisfies the quadratic estimate `λₖ ≤ 4 / (3 (k + 1)^2)`. -/
lemma weightLeQuadraticBoundOfGamma0EqThreeMul
    (method : OptimalMethodRecurrence f L 0 x0 (3 * L))
    (k : ℕ) :
    method.weight k ≤ 4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((3 * L) * method.weight m))
  have hhalf_le_base : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 3 := by
    have hsqrt3_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
    have hsqrt3_le_two : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hsqrt3_nonneg]
    have hsqrt3_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    exact one_div_le_one_div_of_le hsqrt3_pos hsqrt3_le_two
  have hξ_affine : 1 / Real.sqrt 3 + k / 2 ≤ ξ k := by
    simpa [ξ] using weightXiAffineLowerBoundOfGamma0EqThreeMul method k
  have hξ_half : ((k + 1 : ℝ) / 2) ≤ ξ k := by
    -- The base term `1 / √3` already contributes at least the missing `1 / 2`.
    nlinarith
  have hξ_nonneg : 0 ≤ ξ k := by
    dsimp [ξ]
    positivity
  have hξ_sq_lower : (((k + 1 : ℝ) / 2) ^ (2 : ℕ)) ≤ ξ k ^ (2 : ℕ) := by
    -- Squaring preserves the order because both sides are nonnegative.
    have hdiff_nonneg : 0 ≤ ξ k - (k + 1 : ℝ) / 2 := by
      linarith
    have hsum_nonneg : 0 ≤ ξ k + (k + 1 : ℝ) / 2 := by
      positivity
    have hmul_nonneg :
        0 ≤ (ξ k - (k + 1 : ℝ) / 2) * (ξ k + (k + 1 : ℝ) / 2) := by
      exact mul_nonneg hdiff_nonneg hsum_nonneg
    nlinarith
  have hξ_sq :
      ξ k ^ (2 : ℕ) = 1 / (3 * method.weight k) := by
    -- Squaring `ξₖ` and canceling the common factor `L` isolates the reciprocal weight.
    calc
      ξ k ^ (2 : ℕ) = L / ((3 * L) * method.weight k) := by
        dsimp [ξ]
        rw [Real.sq_sqrt]
        apply div_nonneg
        · exact method.L_pos.le
        · have hthreeL_nonneg : 0 ≤ 3 * L := by
            nlinarith [method.L_pos]
          exact mul_nonneg hthreeL_nonneg (weight_pos method k).le
      _ = 1 / (3 * method.weight k) := by
        field_simp [method.L_pos.ne', (weight_pos method k).ne']
  have hrecip :
      (((k + 1 : ℝ) / 2) ^ (2 : ℕ)) ≤ 1 / (3 * method.weight k) := by
    exact hξ_sq_lower.trans_eq hξ_sq
  have hpoly := hrecip
  field_simp [(weight_pos method k).ne'] at hpoly
  have hscaled :
      (3 * (k + 1 : ℝ) ^ (2 : ℕ)) * method.weight k ≤ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hpoly (weight_pos method k).le
    have hright : ((2 : ℝ) ^ (2 : ℕ)) / method.weight k * method.weight k = 4 := by
      field_simp [(weight_pos method k).ne']
      norm_num
    nlinarith [hmul, hright]
  have hden_pos : 0 < 3 * (k + 1 : ℝ) ^ (2 : ℕ) := by
    positivity
  refine (le_div_iff₀ hden_pos).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

-- Proof sketch: specialize the smooth-convex `γ₀ = 3L` scalar recurrence for `λₖ`, prove the
-- quadratic upper bound `λₖ ≤ 4 / (3 (k + 1)^2)`, and then rewrite `λₖ / (1 - λₖ)` using that
-- estimate.
/-- Helper for Lemma 2.10: in the smooth-convex specialization `μ = 0`, `γ₀ = 3L`, the owner
weight factor `λₖ / (1 - λₖ)` is bounded by the rational expression used later in
Theorem 2.22. -/
lemma weight_ratio_le_of_gamma0_eq_three_mul
    (method : OptimalMethodRecurrence f L 0 x0 (3 * L))
    {k : ℕ} (hk : 1 ≤ k) :
    method.weight k / (1 - method.weight k) ≤
      4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
  let a : ℝ := 4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ))
  have hw_le_a : method.weight k ≤ a := by
    simpa [a] using weightLeQuadraticBoundOfGamma0EqThreeMul method k
  have hw_pos : 0 < method.weight k := weight_pos method k
  have hk_two : (2 : ℝ) ≤ k + 1 := by
    exact_mod_cast Nat.succ_le_succ hk
  have hden_gt_four : 4 < 3 * (k + 1 : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_lt_one : a < 1 := by
    -- The lower bound `k + 1 ≥ 2` makes the quadratic denominator strictly larger than `4`.
    dsimp [a]
    have hden_pos : 0 < 3 * (k + 1 : ℝ) ^ (2 : ℕ) := by
      positivity
    exact (div_lt_one hden_pos).2 hden_gt_four
  have hw_lt_one : method.weight k < 1 := lt_of_le_of_lt hw_le_a ha_lt_one
  have h_inv : 1 / a ≤ 1 / method.weight k := by
    -- Inverting the quadratic estimate rewrites the comparison into an affine reciprocal form.
    exact one_div_le_one_div_of_le hw_pos hw_le_a
  have hratio_inv :
      (1 - a) / a ≤ (1 - method.weight k) / method.weight k := by
    have hleft :
        (1 - a) / a = 1 / a - 1 := by
      field_simp [ha_pos.ne']
    have hright :
        (1 - method.weight k) / method.weight k = 1 / method.weight k - 1 := by
      field_simp [hw_pos.ne']
    rw [hleft, hright]
    linarith
  have hratio :
      method.weight k / (1 - method.weight k) ≤ a / (1 - a) := by
    -- A second reciprocal comparison turns the affine form into the desired weight ratio.
    have hone_sub_a_pos : 0 < 1 - a := by
      linarith
    have hleft_pos : 0 < (1 - a) / a := by
      positivity
    have hinv := one_div_le_one_div_of_le hleft_pos hratio_inv
    simpa [one_div_div] using hinv
  have ha_eq :
      a / (1 - a) = 4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
    -- Clearing denominators gives the closed-form rational expression from the statement.
    dsimp [a]
    field_simp [show 3 * (k + 1 : ℝ) ^ (2 : ℕ) ≠ 0 by positivity,
      show 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4 ≠ 0 by linarith]
  simpa [ha_eq] using hratio

end OptimalMethodRecurrence

end
