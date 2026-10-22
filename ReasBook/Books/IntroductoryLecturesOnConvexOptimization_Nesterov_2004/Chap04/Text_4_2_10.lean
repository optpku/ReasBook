/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.10 lies in the cubic-Newton linear-rate domain on a real Hilbert space.

Sampled owner-style declarations:
* `conditionNumberOfDegree` in `Definition_4_2_11`
* `uniformConvexityParameterOfDegree` in `Definition_4_2_11`
* `iteratedFDerivLipschitzConstantOfDegree` in `Definition_4_2_11`
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, where the source threshold is rewritten
  in multiplication form to avoid division-by-zero artifacts
* `acceleratedCubicNewtonQuadraticConvergenceRegion` in `Text_4_2_22`, which uses the same
  multiplication-form threshold discipline for the local cubic region
* the positive-parameter owner style in `Lemma_4_4_8`, where `NNRealˣ` carries positivity in the
  public API instead of separate proof binders

Best owner abstraction:
* source-facing: the cubic-Newton rate bounds driven by arbitrary positive parameters `σ₃` and
  `L₃` satisfying the textbook gap and descent inequalities
* core/canonical: the chapter owner `γ[3](f)` for the degree-`3` condition number of a function
* bridge/view: the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)`, equivalent to
  `(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹`

Primitive data:
* a function `f`, a reference point `xStar`, and an iterate sequence `x`
* positive scalars `σ₃`, `L₃`, now owned canonically as `NNRealˣ`
* the two source hypotheses bounding the gap by `‖∇ f‖^(3/2)` and the one-step decrease by
  `‖∇ f‖^(3/2)`, stated in multiplication form rather than through `1 / sqrt σ₃` and
  `1 / sqrt L₃`

Derived API:
* the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)` and its exponential companion
  `√σ₃ / (2 √L₃ + √σ₃)`

Semantic-priority note:
* the file remains source-facing over arbitrary `σ₃` and `L₃`; replacing them by the canonical
  owner `γ[3](f)` would change the theorem interface from textbook assumptions to a stronger
  function-level conditioning API.
* the refined statements keep those source parameters, but encode their positivity by `NNRealˣ`
  and rewrite the public inequalities in multiplication form, following the nearby chapter style
  that avoids division-by-zero and `Real.sqrt` artifacts in theorem surfaces.
-/

section CubicNewtonConditionNumberRate

variable {f : E → ℝ} {x : ℕ → E} {xStar : E} {σ₃ L₃ : NNRealˣ}

local notation "Δ" => fun k : ℕ ↦ f (x k) - f xStar
local notation "ρ" =>
  ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) / ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))

-- Proof sketch: apply the global gap estimate at `x_{k+1}` to bound
-- `Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2)` from below, then substitute that lower bound into the
-- assumed one-step descent inequality. Writing the source bounds in multiplication form yields
-- `√σ₃ * Δ_{k+1} ≤ 2 √L₃ * (f(x_k) - f(x_{k+1}))`, which is equivalent to the textbook factor
-- `(1 / 2) * sqrt (σ₃ / L₃)` because `σ₃, L₃ > 0` are owned by `NNRealˣ`.
/-- Text 4.2.10 (1): if
`3 √σ₃ (f x - f xStar) ≤ 2 ‖∇ f x‖^(3/2)` for every `x`, and if the sequence `x`
satisfies
`‖∇ f(x_{k+1})‖^(3/2) ≤ 3 √L₃ (f(x_k) - f(x_{k+1}))`,
then each one-step decrease controls the next gap by
`√σ₃ (f(x_{k+1}) - f(xStar)) ≤ 2 √L₃ (f(x_k) - f(x_{k+1}))`, equivalently by the textbook
factor `(1 / 2) * sqrt (σ₃ / L₃)`. -/
theorem cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (k : ℕ) :
    Real.sqrt (σ₃ : ℝ) * Δ (k + 1) ≤
      (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := by
  -- Compare the next-gap lower bound with the one-step descent estimate at the same iterate.
  have hcombined :
      (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * Δ (k + 1) ≤
        (2 : ℝ) * ((3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1)))) := by
    refine (hgap (x (k + 1))).trans ?_
    gcongr
    exact hdescent k
  -- Divide the combined inequality by `3` to recover the advertised coefficient.
  calc
    Real.sqrt (σ₃ : ℝ) * Δ (k + 1)
        = ((1 : ℝ) / 3 : ℝ) * ((3 : ℝ) * Real.sqrt (σ₃ : ℝ) * Δ (k + 1)) := by ring
    _ ≤ ((1 : ℝ) / 3 : ℝ) *
          ((2 : ℝ) * ((3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))) := by
      gcongr
    _ = (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := by ring

/-- Helper for Text 4 2 10: the one-step gap estimate rewrites as the scalar recurrence
`Δ (k + 1) ≤ ρ * Δ k`. -/
lemma cubic_newton_gap_step_le_contraction_factor
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (k : ℕ) :
    Δ (k + 1) ≤ ρ * Δ k := by
  have hdrop :=
    cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap hgap hdescent k
  have hscaled :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) * Δ (k + 1)) ≤
        (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ k := by
    -- Move the `Δ (k + 1)` term to the left so the contraction denominator becomes explicit.
    have hsum :
        (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ (k + 1) +
            Real.sqrt (σ₃ : ℝ) * Δ (k + 1) ≤
          (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ (k + 1) +
            (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hdrop ((2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ (k + 1))
    calc
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) * Δ (k + 1))
          = (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ (k + 1) +
              Real.sqrt (σ₃ : ℝ) * Δ (k + 1) := by ring
      _ ≤ (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ (k + 1) +
            (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := hsum
      _ = (2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ k := by
        ring
  have hL₃_nonzero : (L₃ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero L₃
  have hL₃_pos : 0 < (L₃ : ℝ) := by
    exact lt_of_le_of_ne (by positivity) hL₃_nonzero.symm
  have hsqrtL_pos : 0 < Real.sqrt (L₃ : ℝ) := Real.sqrt_pos.2 hL₃_pos
  have hdenom_pos :
      0 < (2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ) := by
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hsqrtL_pos) (by positivity)
  have hdiv :
      Δ (k + 1) ≤
        ((2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ k) /
          ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) := by
    exact (le_div_iff₀ hdenom_pos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  -- Rewrite the normalized quotient exactly as the textbook contraction factor `ρ`.
  calc
    Δ (k + 1) ≤
        ((2 : ℝ) * Real.sqrt (L₃ : ℝ) * Δ k) /
          ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) := hdiv
    _ = (((2 : ℝ) * Real.sqrt (L₃ : ℝ)) /
          ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) * Δ k := by
      ring

-- Proof sketch: apply the one-step estimate from
-- `cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap` to the gaps
-- `Δ_k = f (x k) - f xStar`, rewrite it as
-- `Δ_{k+1} ≤ ρ * Δ_k` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃)`, and iterate this scalar recurrence from
-- `1` to `k - 1`.
/-- Text 4.2.10 (2): under the same assumptions, the objective gaps along `x` decay at the linear
rate
`ρ^(k-1)` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃) =
(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹` for every `k ≥ 1`. -/
theorem cubic_newton_gap_le_linear_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤ ρ ^ (k - 1) * Δ 1 := by
  have hρ_nonneg : 0 ≤ ρ := by
    show 0 ≤
      ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) /
        ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))
    positivity
  -- Iterate the scalar recurrence from the first iterate onward.
  have hiter : ∀ n : ℕ, Δ (n + 1) ≤ ρ ^ n * Δ 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          Δ ((n + 1) + 1) ≤ ρ * Δ (n + 1) :=
            cubic_newton_gap_step_le_contraction_factor hgap hdescent (n + 1)
          _ ≤ ρ * (ρ ^ n * Δ 1) := by
            exact mul_le_mul_of_nonneg_left ih hρ_nonneg
          _ = ρ ^ (n + 1) * Δ 1 := by
            rw [pow_succ]
            ring
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [Nat.add_comm] using hiter n

/-- Helper for Text 4 2 10: powers of the contraction factor are dominated by the displayed
exponential rate. -/
lemma cubic_newton_contraction_factor_pow_le_exp (n : ℕ) :
    ρ ^ n ≤
      Real.exp
        (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) /
          ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) := by
  let d : ℝ := (2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)
  let t : ℝ := Real.sqrt (σ₃ : ℝ) / d
  have hL₃_nonzero : (L₃ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero L₃
  have hL₃_pos : 0 < (L₃ : ℝ) := by
    exact lt_of_le_of_ne (by positivity) hL₃_nonzero.symm
  have hsqrtL_pos : 0 < Real.sqrt (L₃ : ℝ) := Real.sqrt_pos.2 hL₃_pos
  have hd_pos : 0 < d := by
    dsimp [d]
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hsqrtL_pos) (by positivity)
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hρ_nonneg : 0 ≤ ρ := by
    show 0 ≤
      ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) /
        ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))
    positivity
  have hrho_eq : ρ = 1 - t := by
    show
      ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) /
        ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) = 1 - t
    dsimp [d, t]
    field_simp [hd_ne]
    ring
  have hbase : ρ ≤ Real.exp (-t) := by
    rw [hrho_eq]
    exact Real.one_sub_le_exp_neg t
  -- Raise the one-step scalar bound to the `n`th power and rewrite the exponent.
  calc
    ρ ^ n ≤ (Real.exp (-t)) ^ n := by
      exact pow_le_pow_left₀ hρ_nonneg hbase n
    _ = Real.exp ((n : ℝ) * (-t)) := by
      rw [← Real.exp_nat_mul (-t) n]
    _ = Real.exp (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) / d) := by
      congr 1
      dsimp [t]
      ring
    _ = Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) := by
      rfl

-- Proof sketch: combine `cubic_newton_gap_le_linear_rate` with the initial cubic upper bound on
-- `f (x 1) - f xStar`, then use
-- `ρ ≤ exp (-√σ₃ / (2 √L₃ + √σ₃))` to bound the geometric factor by the displayed exponential
-- term.
/-- Text 4.2.10 (3): if in addition the first gap satisfies
`3 (f(x₁) - f(xStar)) ≤ L₃ ‖x₀ - xStar‖³`, then for every `k ≥ 1` the gap is bounded by the
displayed exponential expression, written with the equivalent rate coefficient
`√σ₃ / (2 √L₃ + √σ₃)`. -/
theorem cubic_newton_gap_le_exponential_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤
      Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
        (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
  have hinit' :
      Δ 1 ≤ (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
    -- Normalize the initial estimate by dividing through by `3`.
    calc
      Δ 1 = ((1 : ℝ) / 3 : ℝ) * ((3 : ℝ) * Δ 1) := by ring
      _ ≤ ((1 : ℝ) / 3 : ℝ) * ((L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
        gcongr
      _ = (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by ring
  have hprefactor_nonneg :
      0 ≤ (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
    positivity
  have hpow_exp :
      ρ ^ (k - 1) ≤
        Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) := by
    simpa [Nat.cast_sub hk] using
      (cubic_newton_contraction_factor_pow_le_exp (σ₃ := σ₃) (L₃ := L₃) (k - 1))
  -- Combine the geometric recurrence with the exponential majorant for `ρ ^ (k - 1)`.
  calc
    Δ k ≤ ρ ^ (k - 1) * Δ 1 :=
      cubic_newton_gap_le_linear_rate hgap hdescent hk
    _ ≤ ρ ^ (k - 1) * (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hinit' (by positivity)
    _ ≤ Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
          (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right hpow_exp hprefactor_nonneg

/-- Helper for Text 4 2 10: the logarithmic lower bound on the iteration count implies the
required exponential prefactor is at most `ε`. -/
lemma cubic_newton_exp_prefactor_le_epsilon_of_log_bound
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) {n : ℕ}
    (hlog :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) * Real.log (A / ε) ≤
        (n : ℝ) * Real.sqrt (σ₃ : ℝ))) :
    Real.exp
        (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) /
          ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
      A ≤ ε := by
  let d : ℝ := (2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)
  have hL₃_nonzero : (L₃ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero L₃
  have hL₃_pos : 0 < (L₃ : ℝ) := by
    exact lt_of_le_of_ne (by positivity) hL₃_nonzero.symm
  have hsqrtL_pos : 0 < Real.sqrt (L₃ : ℝ) := Real.sqrt_pos.2 hL₃_pos
  have hd_pos : 0 < d := by
    dsimp [d]
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hsqrtL_pos) (by positivity)
  by_cases hA_zero : A = 0
  · -- The degenerate prefactor vanishes immediately.
    simp [hA_zero, hε.le]
  have hA_ne : 0 ≠ A := by
    simpa [eq_comm] using hA_zero
  have hA_pos : 0 < A := lt_of_le_of_ne hA hA_ne
  have hlog_div :
      Real.log (A / ε) ≤ ((n : ℝ) * Real.sqrt (σ₃ : ℝ)) / d := by
    exact (le_div_iff₀ hd_pos).2 (by
      simpa [d, mul_comm, mul_left_comm, mul_assoc] using hlog)
  have hneg :
      -(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) / d ≤ -Real.log (A / ε) := by
    have hneg' := neg_le_neg hlog_div
    simpa [d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hneg'
  have hratio_pos : 0 < A / ε := div_pos hA_pos hε
  have hexp :
      Real.exp (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) / d) ≤ ε / A := by
    calc
      Real.exp (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) / d) ≤ Real.exp (-Real.log (A / ε)) := by
        exact Real.exp_le_exp_of_le hneg
      _ = ε / A := by
        rw [Real.exp_neg, Real.exp_log hratio_pos]
        field_simp [hA_pos.ne', hε.ne']
  -- Multiply the scalar exponential bound by `A` to recover the target inequality.
  calc
    Real.exp (-(Real.sqrt (σ₃ : ℝ) * (n : ℝ)) / d) * A ≤ (ε / A) * A := by
      exact mul_le_mul_of_nonneg_right hexp hA
    _ = ε := by
      field_simp [hA_pos.ne']

-- Proof sketch: start from `cubic_newton_gap_le_exponential_rate`, replace `‖x 0 - xStar‖` by
-- the bound `D`, and solve the resulting exponential inequality for `k` in terms of `ε` by
-- taking logarithms. The lower bound on `k` is written in multiplication form to avoid the
-- surface factor `(2 √L₃ + √σ₃) / √σ₃`.
/-- Text 4 2 10: if `‖x₀ - xStar‖ ≤ D`, then the target accuracy `f(x_k) - f(xStar) ≤ ε` is
guaranteed once `k` satisfies the explicit logarithmic lower bound corresponding to the textbook
`O((√L₃ / √σ₃) * log (L₃ D^3 / ε))` estimate, stated in multiplication form. This is the final
iteration-complexity form of Text 4.2.10 (4). -/
theorem cubic_newton_gap_le_of_iteration_count_bound
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {D ε : ℝ}
    (hD : ‖x 0 - xStar‖ ≤ D)
    (hε : 0 < ε)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hk_bound :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) *
          Real.log ((((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) / ε) ≤
        (k - 1 : ℝ) * Real.sqrt (σ₃ : ℝ))) :
    Δ k ≤ ε := by
  have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg (x 0 - xStar)) hD
  have hpow_le : ‖x 0 - xStar‖ ^ (3 : ℕ) ≤ D ^ (3 : ℕ) := by
    exact pow_le_pow_left₀ (norm_nonneg (x 0 - xStar)) hD 3
  have hprefactor_le :
      (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) ≤
        (((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  have hA_nonneg : 0 ≤ (((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) := by
    positivity
  have hk_bound' :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) *
          Real.log ((((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) / ε) ≤
        ((k - 1 : ℕ) : ℝ) * Real.sqrt (σ₃ : ℝ)) := by
    simpa [Nat.cast_sub hk, mul_comm, mul_left_comm, mul_assoc] using hk_bound
  have hclose :
      Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (((k - 1 : ℕ) : ℝ))) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
        (((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) ≤ ε :=
    cubic_newton_exp_prefactor_le_epsilon_of_log_bound
      (σ₃ := σ₃) (L₃ := L₃) (n := k - 1) hA_nonneg hε hk_bound'
  have hexp_nonneg :
      0 ≤
        Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) := by
    positivity
  -- Replace the initial norm factor by `D` and then invoke the scalar log-to-exp estimate.
  calc
    Δ k ≤
        Real.exp
            (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
              ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
          (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) :=
      cubic_newton_gap_le_exponential_rate hgap hdescent hinit hk
    _ ≤
        Real.exp
            (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
              ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
          (((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hprefactor_le hexp_nonneg
    _ ≤ ε :=
      by
        simpa [Nat.cast_sub hk] using hclose

end CubicNewtonConditionNumberRate
