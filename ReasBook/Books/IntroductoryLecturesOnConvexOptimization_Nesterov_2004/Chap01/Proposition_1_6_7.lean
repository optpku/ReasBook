/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain:
* sufficient-decrease estimates for real-Hilbert-space gradient-method trajectories

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` in `Lemma_1_6_6.lean`
* `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`, the generic line-search owner
  used directly at theorem level once `ContDiff ℝ 1 f` already supplies the gradient witness
* `SatisfiesArmijoRule` in `Definition_1_6_4.lean`, whose lower Armijo bound and parameter
  inequalities are the primitive components consumed here after removing its redundant
  `HasGradientAt` field at theorem level

Source/core/bridge triage:
* source-facing: Proposition 1.6.7's explicit sufficient-decrease inequalities for the
  constant step `h`, its specialization `h = 2 α / L`, exact line search, and Armijo
  backtracking
* core/canonical owner: the trajectory `gradientMethod stepSize f x0` together with the
  one-step estimate
  `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`
* bridge/view: the `∃ ω > 0` corollaries in the exact descent-hypothesis shape used by
  `Theorem_1_6_8`

Primitive data:
* the objective `f`, the initial point `x0`, and the step-size data of the chosen rule
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`
* the rule parameters `α`, `β` only when the step rule requires them
* the backtracking exponents `m_k` in the Armijo case

Derived API:
* the explicit `h = 2 α / L` normalization of the constant-step bound
* the exact-line-search and Armijo-backtracking decrease bounds
* the companion `∃ ω > 0` corollaries with the exact downstream orientation

The arbitrary-point constant-step estimate is already owned upstream by
`gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`. This file keeps only the
source-facing iterate form that Proposition 1.6.7 states, together with the `∃ ω > 0` bridge
corollaries used later in the chapter. The `h = 2 α / L` formula is kept as a direct
specialization of the owner constant-step estimate, not as an equality-based wrapper around an
arbitrary schedule. The exact-line-search proposition uses the generic owner
`SatisfiesExactLineSearchAlong` directly, since `ContDiff ℝ 1 f` already implies the gradient
existence field bundled in `SatisfiesExactLineSearch`. Likewise, the Armijo propositions consume
only the primitive lower-bound and parameter data extracted from `SatisfiesArmijoRule`; the only
extra source-facing data kept here is the minimality of the accepted exponent `m_k`, expressed by
rejection of every smaller trial. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `ℝⁿ` formulation. -/

section GradientMethod

variable {L : NNReal} {f : E → ℝ} {x0 : E}

/- The companion corollaries below are stated directly in the sufficient-decrease shape consumed
by `Theorem_1_6_8`, rather than through a parallel local wrapper predicate. -/

section ConstantStepSize

variable (h : ℝ)

local notation "traj" => gradientMethod (fun _ ↦ h) f x0

-- Proof sketch: apply the owner one-step estimate
-- `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` at `x = traj k`, rewrite
-- `traj (k + 1)` using `gradientMethod_succ`, and use that `traj` is already the constant-step
-- trajectory.
/-- Proposition 1.6.7 (1): if a gradient method for a `C_L^{1,1}(ℝⁿ)` objective uses the constant
step size `h`, then
`f(x_k) - f(x_(k+1)) ≥ h (1 - L h / 2) ‖∇ f(x_k)‖²` for every `k`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Rewrite the textbook iterate update into the pointwise owner descent lemma.
  have hstep :
      f (traj (k + 1)) ≤
        f (traj k) - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    simpa [gradientMethod_succ] using
      gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient hf hgrad (traj k) h
  -- Rearranging the one-step estimate gives the displayed sufficient decrease bound.
  linarith

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` and choose
-- `ω = (L : ℝ) * h * (1 - ((L : ℝ) * h) / 2)`. The step-size range `0 < h < 2 / L` makes this
-- choice positive.
/-- Companion corollary: any constant-step gradient method with `0 < h < 2 / L` satisfies the
chapter's `∃ ω > 0` sufficient-decrease form. -/
theorem gradientMethod_exists_sufficientDecrease_of_constant_stepsize
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hh0 : 0 < h)
    (hh1 : h < 2 / (L : ℝ)) :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- The admissible step-size range forces `L > 0`, so the standard coefficient is positive.
  refine ⟨(L : ℝ) * h * (1 - ((L : ℝ) * h) / 2), ?_, ?_⟩
  · have hLne : (L : ℝ) ≠ 0 := by
      intro hL
      simp [hL] at hh1
      linarith
    have hLpos : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hLne)
    have hhL : h * (L : ℝ) < 2 := by
      exact (lt_div_iff₀ hLpos).mp hh1
    have hcoeff : 0 < 1 - ((L : ℝ) * h) / 2 := by
      nlinarith
    exact mul_pos (mul_pos hLpos hh0) hcoeff
  · intro k
    -- Match the bridge coefficient `(ω / L)` with the owner constant-step estimate.
    have hLne : (L : ℝ) ≠ 0 := by
      intro hL
      simp [hL] at hh1
      linarith
    have hω :
        (((L : ℝ) * h * (1 - ((L : ℝ) * h) / 2)) / (L : ℝ)) =
          h * (1 - ((L : ℝ) * h) / 2) := by
      field_simp [hLne]
    simpa [hω] using
      gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
        (h := h) hf hgrad k

end ConstantStepSize

section ConstantStepSizeSpecialization

variable {α : ℝ}

local notation "traj" => gradientMethod (fun _ ↦ (2 * α) / (L : ℝ)) f x0

-- Proof sketch: specialize
-- `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` at `h = (2 * α) / L` and simplify
-- the coefficient.
/-- Proposition 1.6.7 (1), specialized: if the constant step size is `h = 2 α / L`, then
`f(x_k) - f(x_(k+1)) ≥ ((2 / L) * α * (1 - α)) ‖∇ f(x_k)‖²` for every `k`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize_eq_two_mul_div
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (((2 : ℝ) / (L : ℝ)) * α * (1 - α)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Specialize the constant-step estimate to `h = 2 α / L`.
  have hconst :=
    gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize
      (x0 := x0) (h := (2 * α) / (L : ℝ)) hf hgrad k
  -- Normalize the coefficient exactly into the source-facing textbook form.
  by_cases hL : (L : ℝ) = 0
  · simp [hL] at hconst ⊢
  · have hcoeff :
        ((2 * α) / (L : ℝ)) * (1 - ((L : ℝ) * ((2 * α) / (L : ℝ))) / 2) =
          (((2 : ℝ) / (L : ℝ)) * α * (1 - α)) := by
      field_simp [hL]
    simpa [hcoeff] using hconst

end ConstantStepSizeSpecialization

section ExactLineSearch

variable {stepSize : ℕ → ℝ}

local notation "traj" => gradientMethod stepSize f x0
local notation "grad" => (∇ f) ∘ traj

-- Proof sketch: use that `stepSize k` minimizes the line-search objective over `h ≥ 0`, compare
-- the accepted value with the trial step `h = 1 / L`, and then specialize
-- `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` at the point `traj k`.
/-- Proposition 1.6.7 (2): if the step sizes satisfy the exact line-search minimization condition
along `-∇ f(x_k)`, then each gradient-method step decreases the objective by at least
`(2L)⁻¹ ‖∇ f(x_k)‖²`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hexact : SatisfiesExactLineSearchAlong f traj grad stepSize)
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (1 / (2 * (L : ℝ))) * ‖grad k‖ ^ (2 : ℕ) := by
  -- Compare the accepted step with the trial step `1 / L` using the exact line-search owner.
  have hLnonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast L.2
  have htrial_mem : (1 / (L : ℝ)) ∈ Set.Ici (0 : ℝ) := by
    rw [Set.mem_Ici]
    exact one_div_nonneg.mpr hLnonneg
  have hmin := hexact.isMinOn k
  rw [isMinOn_iff] at hmin
  have hcmp :
      f (traj (k + 1)) ≤ f (traj k - (1 / (L : ℝ)) • grad k) := by
    simpa [gradientMethod_succ] using hmin (1 / (L : ℝ)) htrial_mem
  by_cases hL : (L : ℝ) = 0
  · -- When `L = 0`, the target coefficient is zero, so monotonicity from the trial step `0` is enough.
    have hzero_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp
    have hcmp0 : f (traj (k + 1)) ≤ f (traj k) := by
      simpa [gradientMethod_succ] using hmin 0 hzero_mem
    have hdrop_nonneg : 0 ≤ f (traj k) - f (traj (k + 1)) := by
      linarith
    simpa [hL] using hdrop_nonneg
  · -- For `L ≠ 0`, import the descent-lemma estimate at the trial step `1 / L`.
    have hcoeff :
        (1 / (2 * (L : ℝ))) * ‖grad k‖ ^ (2 : ℕ) =
          (1 / (L : ℝ)) * (‖grad k‖ ^ (2 : ℕ) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) := by
      field_simp [hL]
      ring
    have hstep :
        f (traj k - (1 / (L : ℝ)) • grad k) ≤
          f (traj k) - (1 / (L : ℝ)) *
            (‖grad k‖ ^ (2 : ℕ) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hf hgrad (traj k) (1 / (L : ℝ))
    linarith

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch` and choose
-- `ω = 1 / 2`.
/-- Companion corollary to Proposition 1.6.7 (2): exact line search also yields the source-style
`∃ ω > 0` sufficient-decrease formulation. -/
theorem gradientMethod_exists_sufficientDecrease_of_exactLineSearch
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hexact : SatisfiesExactLineSearchAlong f traj grad stepSize)
    :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖grad k‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- The exact-line-search coefficient is obtained by the fixed choice `ω = 1 / 2`.
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro k
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    gradientMethod_value_drop_ge_sqnorm_of_exactLineSearch
      (hf := hf) (hgrad := hgrad) hexact k

end ExactLineSearch

section ArmijoBacktracking

variable {α β : ℝ} (armijoIndex : ℕ → ℕ)

local notation "stepSize" => fun k ↦ β ^ armijoIndex k
local notation "traj" => gradientMethod stepSize f x0
local notation "grad" => (∇ f) ∘ traj

/-
Primitive source-facing data beyond the owner `SatisfiesArmijoRule`:
* the theorem-local rejection of every smaller geometric trial exponent

Derived from the owner:
* genuine gradient existence along `traj`
* positivity and ordering of the Armijo parameters
* the accepted lower Armijo inequality at the chosen exponent

At theorem level, `ContDiff ℝ 1 f` already supplies the gradient witness along `traj`, so the
propositions below use the canonical owner `SatisfiesArmijoRule` for the accepted-step data. The
source-facing minimality condition from Proposition 1.6.7 (3) remains theorem-local, rather than
being exported as a second public raw-gradient owner.
-/

/-- Helper for Proposition 1.6.7: if the gradient at iterate `k` is nonzero, then the accepted
Armijo step is bounded below by `((2 / L) * (1 - β))`. -/
lemma armijo_stepsize_lower_bound_of_nonzero_gradient
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (k : ℕ)
    (hgradk : grad k ≠ 0) :
    (((2 : ℝ) / (L : ℝ)) * (1 - β)) ≤ stepSize k := by
  by_cases hL : (L : ℝ) = 0
  · -- In the degenerate `L = 0` branch the lower bound is simply `0 ≤ stepSize k`.
    simp [hL, le_of_lt (hArmijo.stepSize_pos k)]
  · -- Route correction: use the owner upper Armijo bound plus Lemma 1.6.6 at the accepted step.
    have hstep :
        f (traj (k + 1)) ≤
          f (traj k) - (stepSize k * (1 - ((L : ℝ) * stepSize k) / 2)) * ‖grad k‖ ^ (2 : ℕ) := by
      simpa [gradientMethod_succ] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hf hgrad (traj k) (stepSize k)
    have hdrop :
        (stepSize k * (1 - ((L : ℝ) * stepSize k) / 2)) * ‖grad k‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)) := by
      linarith
    have hupp :
        f (traj k) - f (traj (k + 1)) ≤ β * (stepSize k * ‖grad k‖ ^ (2 : ℕ)) := by
      simpa [gradientMethod_succ, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two,
        mul_assoc, mul_left_comm, mul_comm] using hArmijo.upperBound k
    have hnormsq_pos : 0 < ‖grad k‖ ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hgradk)
    have hcoeff : stepSize k * (1 - ((L : ℝ) * stepSize k) / 2) ≤ β * stepSize k := by
      nlinarith
    have hLpos : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL)
    have hmul : (2 : ℝ) * (1 - β) ≤ (L : ℝ) * stepSize k := by
      have hstep_pos : 0 < stepSize k := hArmijo.stepSize_pos k
      nlinarith
    have hdiv : ((2 : ℝ) * (1 - β)) / (L : ℝ) ≤ stepSize k := by
      exact (div_le_iff₀ hLpos).mpr (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

-- Proof sketch: the descent lemma shows that every trial step
-- `h ≤ 2 * (1 - α) / L` satisfies the Armijo acceptance inequality. If the accepted exponent
-- `armijoIndex k` were too large, the previous geometric trial would still be acceptable,
-- contradicting the theorem-local rejection hypothesis `hminimal`. Hence
-- `β * (2 * (1 - α) / L) ≤ stepSize k`. Combine this lower bound with the accepted Armijo
-- inequality, then use `β * (1 - α) ≥ 1 - β`, which follows from `α < β`.
/-- Proposition 1.6.7 (3): fix `0 < α < β < 1`. Suppose
`h_k = β^(armijoIndex k)` and `armijoIndex k` is the smallest nonnegative exponent whose trial
point satisfies the Armijo acceptance inequality along `-∇ f(x_k)`. Equivalently, the trajectory
is `gradientMethod (fun k ↦ β ^ armijoIndex k) f x0`, the accepted-step data is the owner
`SatisfiesArmijoRule f (fun k ↦ β ^ armijoIndex k) x0 α β`, and `hminimal` records rejection of
smaller exponents.
Then every gradient-method step decreases the objective by at least
`((2 / L) * α * (1 - β)) ‖∇ f(x_k)‖²`. -/
theorem gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (hminimal :
      ∀ ⦃k j : ℕ⦄, j < armijoIndex k →
        f (traj k - β ^ j • grad k) >
          f (traj k) - α * β ^ j * ‖grad k‖ ^ (2 : ℕ))
    (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≥
      (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) * ‖grad k‖ ^ (2 : ℕ) := by
  -- The owner-based proof route does not need the explicit rejection hypothesis, but we keep it
  -- present because it is part of the textbook Armijo statement recorded in this theorem.
  let _ := hminimal
  by_cases hgradk : grad k = 0
  · -- If the gradient vanishes, the next iterate is unchanged and the desired lower bound is `0`.
    have hgradk' : ∇ f (traj k) = 0 := hgradk
    simp [gradientMethod_succ, hgradk']
  · -- The lower Armijo inequality becomes quantitative once the step-size lower bound is inserted.
    have hstep_lower :=
      armijo_stepsize_lower_bound_of_nonzero_gradient
        (armijoIndex := armijoIndex) (hf := hf) (hgrad := hgrad) hArmijo k hgradk
    have hlow :
        (α * stepSize k) * ‖grad k‖ ^ (2 : ℕ) ≤ f (traj k) - f (traj (k + 1)) := by
      simpa [gradientMethod_succ, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two,
        mul_assoc, mul_left_comm, mul_comm] using hArmijo.lowerBound k
    have hαnonneg : 0 ≤ α := le_of_lt hArmijo.alpha_pos
    have hnormsq_nonneg : 0 ≤ ‖grad k‖ ^ (2 : ℕ) := by
      positivity
    have htarget :
        (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) * ‖grad k‖ ^ (2 : ℕ) ≤
          (α * stepSize k) * ‖grad k‖ ^ (2 : ℕ) := by
      have hcoeff : α * (((2 : ℝ) / (L : ℝ)) * (1 - β)) ≤ α * stepSize k := by
        exact mul_le_mul_of_nonneg_left hstep_lower hαnonneg
      have hmul := mul_le_mul_of_nonneg_right hcoeff hnormsq_nonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans htarget hlow

-- Proof sketch: apply `gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking` and choose
-- `ω = 2 * α * (1 - β)`.
/-- Companion corollary to Proposition 1.6.7 (3): the Armijo backtracking rule also yields the
source-style `∃ ω > 0` sufficient-decrease formulation. -/
theorem gradientMethod_exists_sufficientDecrease_of_armijo_backtracking
    (hf : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β)
    (hminimal :
      ∀ ⦃k j : ℕ⦄, j < armijoIndex k →
        f (traj k - β ^ j • grad k) >
          f (traj k) - α * β ^ j * ‖grad k‖ ^ (2 : ℕ))
    :
    ∃ ω > 0, ∀ k : ℕ,
      (ω / (L : ℝ)) * ‖grad k‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)) := by
  -- Choose the textbook Armijo coefficient `ω = 2 α (1 - β)`.
  refine ⟨2 * α * (1 - β), ?_, ?_⟩
  · have hαpos : 0 < α := hArmijo.alpha_pos
    have hβlt : β < 1 := hArmijo.beta_lt_one
    nlinarith
  · intro k
    have hcoeff :
        ((2 * α * (1 - β)) / (L : ℝ)) =
          (((2 : ℝ) / (L : ℝ)) * α * (1 - β)) := by
      by_cases hL : (L : ℝ) = 0
      · simp [hL]
      · field_simp [hL]
    simpa [hcoeff] using
      gradientMethod_value_drop_ge_sqnorm_of_armijo_backtracking
        (armijoIndex := armijoIndex) (hf := hf) (hgrad := hgrad) hArmijo hminimal k

end ArmijoBacktracking

end GradientMethod

end
