/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

section CubicRegularizationResidual

variable {E : Type u} [NormedAddCommGroup E]

/-- The cubic-regularization residual attached to a trial point `y` is the function
`x ↦ ‖x - y‖`; when `y = T_M(x)` this is the textbook residual `r_M(x)`. -/
def cubicRegularizationResidual
    (trialPoint : E) : E → ℝ :=
  fun x ↦ ‖x - trialPoint‖

namespace CubicRegularizationResidual

scoped notation:max "r[" trialPoint "]" => cubicRegularizationResidual trialPoint

end CubicRegularizationResidual

open scoped CubicRegularizationResidual

/-- Expanding `r[trialPoint] x` recovers the norm `‖x - trialPoint‖`. -/
@[simp] theorem cubicRegularizationResidual_eq_norm_sub
    (trialPoint x : E) :
    r[trialPoint] x = ‖x - trialPoint‖ :=
  rfl

end CubicRegularizationResidual

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open SetConstrainedMinimizationProblem

/- Definition 4.1.3 lies in the cubic-regularization / global minimization domain.

Sampled owner-style declarations:
* `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the upstream quadratic Taylor-model
  owner reused here;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_3` and
  `Chap01/Definition_1_3_7`, the canonical whole-space owner and its optimal value;
* `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, the attained-minimum bridge
  from a global minimizer to the canonical owner optimal value;
* `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet`, the owner-level upper
  bound by each trial value;
* `constrainedArgmin` and `mem_constrainedArgmin_iff`, the chapter's canonical argmin owner on a
  feasible set, specialized here to `Set.univ`.

Source/core/bridge triage:
* source-facing: the cubic model `m_x^M(y)`, its global minimizers
  `argmin[Set.univ] (cubicRegularizationQuadraticApproximation f M x)`, and the displayed minimum
  value realized by the whole-space minimization problem attached to that model;
* core/canonical: the owner function `cubicRegularizationQuadraticApproximation f M x`, the
  source-facing bridge `cubicRegularizationProblem f M x`, and
  `(cubicRegularizationProblem f M x).optimalValue`;
* bridge/view: the attained-minimum / `toReal` lemmas recovering the textbook real value from an
  explicit minimizer or, under positive regularization, from bounded-below coercivity.

Primitive data:
* the objective `f`;
* the regularization parameter `M`;
* the base point `x`.

Derived API:
* pointwise evaluation of the cubic model;
* the canonical whole-space minimization problem for that model;
* global minimality of a trial point via `argmin[Set.univ] ...` or `IsMinOn`;
* the owner-valued optimality equality and upper-bound theorems;
* the real-valued bridges recovering the textbook minimum at an explicit minimizer or, for
  `M > 0`, the real lower bound against every trial point.

This refinement keeps the source-facing cubic model and minimum semantics, uses the canonical
Chapter 1 owner `SetConstrainedMinimizationProblem.optimalValue` for the minimum-value layer,
keeps `argmin[Set.univ] ...` for the minimizer layer, and exposes only thin `toReal` bridges
instead of a parallel local real-valued `sInf` owner. -/

/-- The cubic-regularized second-order Taylor model of `f` centered at `x`, obtained by adding
the cubic penalty to `secondOrderTaylorModelAt f x`. -/
def cubicRegularizationQuadraticApproximation
    (f : E → ℝ) (M : ℝ) (x : E) : E → ℝ :=
  fun y ↦ secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ)

/-- Evaluating `cubicRegularizationQuadraticApproximation f M x` at `y` recovers the textbook
cubic model formula. -/
@[simp] theorem cubicRegularizationQuadraticApproximation_apply
    (f : E → ℝ) (M : ℝ) (x y : E) :
    cubicRegularizationQuadraticApproximation f M x y =
      secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) :=
  rfl

/-- The unconstrained minimization problem whose objective is the cubic-regularized second-order
Taylor model centered at `x`. -/
abbrev cubicRegularizationProblem
    (f : E → ℝ) (M : ℝ) (x : E) : SetConstrainedMinimizationProblem E :=
  unconstrained (cubicRegularizationQuadraticApproximation f M x)

/- Source-facing Lean notation for the textbook cubic model `m_x^M(y)` and its minimum-value
layers `Φ_M(x)` and `\bar f_M(x)`. -/
namespace CubicRegularizationModelNotation

scoped notation:max "m[" f:arg "; " M:arg "](" x:arg ")" =>
  cubicRegularizationQuadraticApproximation f M x

scoped notation:max "m[" f:arg "; " M:arg "](" x:arg "; " y:arg ")" =>
  cubicRegularizationQuadraticApproximation f M x y

scoped notation:max "Φ[" f:arg "; " M:arg "](" x:arg ")" =>
  SetConstrainedMinimizationProblem.optimalValue (cubicRegularizationProblem f M x)

scoped notation:max "f̄[" f:arg "; " M:arg "](" x:arg ")" =>
  EReal.toReal (SetConstrainedMinimizationProblem.optimalValue (cubicRegularizationProblem f M x))

end CubicRegularizationModelNotation

open scoped CubicRegularizationModelNotation

/-- A global minimizer of the cubic model realizes the canonical owner optimal value. -/
theorem cubicRegularizationProblem_optimalValue_eq_of_isMinOn
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    Φ[f; M](x) = (m[f; M](x; y) : EReal) := by
  simpa [cubicRegularizationProblem] using
    (cubicRegularizationProblem f M x).optimalValue_eq_of_isMinOn (by simp) hy

/-- Definition 4.1.3: any point of
`argmin[Set.univ] (m[f; M](x))` realizes the displayed minimum value `\bar f_M(x)` through the
canonical owner optimal value. -/
theorem cubicRegularizationProblem_optimalValue_eq_of_mem_argmin
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    Φ[f; M](x) = (m[f; M](x; y) : EReal) := by
  exact cubicRegularizationProblem_optimalValue_eq_of_isMinOn
    (mem_constrainedArgmin_iff.mp hy).2

/-- A global minimizer of the cubic model realizes the textbook real value `\bar f_M(x)`. -/
theorem cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    f̄[f; M](x) = m[f; M](x; y) := by
  rw [cubicRegularizationProblem_optimalValue_eq_of_isMinOn hy]
  exact EReal.toReal_coe _

/-- Any point of the global minimizer set of the cubic model realizes the textbook real value
`\bar f_M(x)`. -/
theorem cubicRegularizationProblem_optimalValue_toReal_eq_of_mem_argmin
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    f̄[f; M](x) = m[f; M](x; y) := by
  exact cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn
    (mem_constrainedArgmin_iff.mp hy).2

/-- The canonical owner optimal value is bounded above by the cubic model at every trial point,
with no extra coercivity hypothesis. -/
theorem cubicRegularizationProblem_optimalValue_le_quadraticApproximation
    {f : E → ℝ} {M : ℝ} {x z : E} :
    Φ[f; M](x) ≤ (m[f; M](x; z) : EReal) := by
  simpa [cubicRegularizationProblem] using
    (cubicRegularizationProblem f M x).optimalValue_le_of_mem_feasibleSet (by simp)

/-- Helper for Definition 4.1.3: the cubic model dominates a scalar cubic polynomial in the
radius `‖y - x‖`. -/
lemma cubic_regularization_model_ge_radius_polynomial
    {f : E → ℝ} {M : ℝ} {x y : E} :
    f x - ‖∇ f x‖ * ‖y - x‖ - (‖hessian f x‖ / 2) * ‖y - x‖ ^ (2 : ℕ) +
      (M / 6) * ‖y - x‖ ^ (3 : ℕ) ≤
        m[f; M](x; y) := by
  -- Bound the linear Taylor term from below by the gradient norm times the radius.
  have hgrad_abs :
      |inner ℝ (∇ f x) (y - x)| ≤ ‖∇ f x‖ * ‖y - x‖ := by
    simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f x) (y - x)
  have hgrad_lower :
      -(‖∇ f x‖ * ‖y - x‖) ≤ inner ℝ (∇ f x) (y - x) := by
    exact (abs_le.mp hgrad_abs).1
  -- Bound the quadratic Taylor term from below by the Hessian operator norm times the squared
  -- radius.
  have hhess_abs :
      |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ) := by
    have hinner :
        |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x (y - x)‖ * ‖y - x‖ := by
      simpa [real_inner_comm] using abs_real_inner_le_norm (hessian f x (y - x)) (y - x)
    calc
      |inner ℝ (hessian f x (y - x)) (y - x)| ≤ ‖hessian f x (y - x)‖ * ‖y - x‖ := hinner
      _ ≤ (‖hessian f x‖ * ‖y - x‖) * ‖y - x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ) := by
        ring
  have hhess_lower :
      -(‖hessian f x‖ * ‖y - x‖ ^ (2 : ℕ)) ≤
        inner ℝ (hessian f x (y - x)) (y - x) := by
    exact (abs_le.mp hhess_abs).1
  -- Rewriting the model exposes a scalar cubic polynomial whose coefficients are controlled by
  -- the two norm bounds above.
  rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
  nlinarith

/-- Helper for Definition 4.1.3: a nonnegative linear term is controlled by a positive cubic term
up to an explicit constant. -/
lemma linear_term_le_cubic_term_add_constant
    {a ε r : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hr : 0 ≤ r) :
    a * r ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
  by_cases hsmall : r ≤ a / ε + 1
  · -- On the bounded region, the constant term already dominates the linear growth.
    calc
      a * r ≤ a * (a / ε + 1) := by
        gcongr
      _ ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
        have hnonneg : 0 ≤ ε * r ^ (3 : ℕ) := by
          positivity
        linarith
  · -- Outside that region, the cubic term dominates the linear term directly.
    have hlarge : a / ε + 1 < r := lt_of_not_ge hsmall
    have hratio2 : a / ε ≤ r ^ (2 : ℕ) := by
      nlinarith
    have hmul : a ≤ ε * r ^ (2 : ℕ) := by
      have htmp : ε * (a / ε) ≤ ε * r ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hratio2 (le_of_lt hε)
      calc
        a = ε * (a / ε) := by
          rw [mul_div_assoc', mul_comm ε a, mul_div_cancel_right₀ a hε.ne']
        _ ≤ ε * r ^ (2 : ℕ) := htmp
    have hmulr : a * r ≤ (ε * r ^ (2 : ℕ)) * r := by
      gcongr
    calc
      a * r ≤ (ε * r ^ (2 : ℕ)) * r := hmulr
      _ = ε * r ^ (3 : ℕ) := by
        ring
      _ ≤ ε * r ^ (3 : ℕ) + a * (a / ε + 1) := by
        have hnonneg : 0 ≤ a * (a / ε + 1) := by
          positivity
        linarith

/-- Helper for Definition 4.1.3: a nonnegative quadratic term is controlled by a positive cubic
term up to an explicit constant. -/
lemma quadratic_term_le_cubic_term_add_constant
    {b ε r : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hr : 0 ≤ r) :
    b * r ^ (2 : ℕ) ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
  by_cases hsmall : r ≤ b / ε + 1
  · -- On the bounded region, the quadratic term is absorbed into the explicit constant.
    have hr2 : r ^ (2 : ℕ) ≤ (b / ε + 1) ^ (2 : ℕ) := by
      nlinarith
    calc
      b * r ^ (2 : ℕ) ≤ b * (b / ε + 1) ^ (2 : ℕ) := by
        gcongr
      _ ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
        have hnonneg : 0 ≤ ε * r ^ (3 : ℕ) := by
          positivity
        linarith
  · -- Outside that region, one power of `r` is enough for the cubic term to dominate.
    have hlarge : b / ε + 1 < r := lt_of_not_ge hsmall
    have hratio : b / ε ≤ r := by
      linarith
    have hmul : b ≤ ε * r := by
      have htmp : ε * (b / ε) ≤ ε * r := by
        exact mul_le_mul_of_nonneg_left hratio (le_of_lt hε)
      calc
        b = ε * (b / ε) := by
          rw [mul_div_assoc', mul_comm ε b, mul_div_cancel_right₀ b hε.ne']
        _ ≤ ε * r := htmp
    have hmulr2 : b * r ^ (2 : ℕ) ≤ (ε * r) * r ^ (2 : ℕ) := by
      gcongr
    calc
      b * r ^ (2 : ℕ) ≤ (ε * r) * r ^ (2 : ℕ) := hmulr2
      _ = ε * r ^ (3 : ℕ) := by
        ring
      _ ≤ ε * r ^ (3 : ℕ) + b * (b / ε + 1) ^ (2 : ℕ) := by
        have hnonneg : 0 ≤ b * (b / ε + 1) ^ (2 : ℕ) := by
          positivity
        linarith

/-- For positive regularization, the cubic model is bounded below on the ambient space. -/
theorem cubicRegularizationQuadraticApproximation_bddBelow
    {f : E → ℝ} {M : ℝ} {x : E} (hM : 0 < M) :
    BddBelow (Set.range (m[f; M](x))) := by
  let ε : ℝ := M / 12
  let C₁ : ℝ := ‖∇ f x‖ * (‖∇ f x‖ / ε + 1)
  let C₂ : ℝ := (‖hessian f x‖ / 2) * ((‖hessian f x‖ / 2) / ε + 1) ^ (2 : ℕ)
  refine ⟨f x - C₁ - C₂, ?_⟩
  rintro z ⟨y, rfl⟩
  -- First reduce the model to the scalar radius polynomial from the source proof skeleton.
  have hpoly :=
    cubic_regularization_model_ge_radius_polynomial (f := f) (M := M) (x := x) (y := y)
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hgrad_nonneg : 0 ≤ ‖∇ f x‖ := norm_nonneg _
  have hhess_nonneg : 0 ≤ ‖hessian f x‖ / 2 := by
    positivity
  have hr_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
  -- Then absorb the linear and quadratic radius terms into two copies of the positive cubic term.
  have hlin :
      ‖∇ f x‖ * ‖y - x‖ ≤ ε * ‖y - x‖ ^ (3 : ℕ) + C₁ := by
    simpa [C₁] using
      linear_term_le_cubic_term_add_constant
        (a := ‖∇ f x‖) (ε := ε) (r := ‖y - x‖) hgrad_nonneg hε hr_nonneg
  have hquad :
      (‖hessian f x‖ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ ε * ‖y - x‖ ^ (3 : ℕ) + C₂ := by
    simpa [C₂] using
      quadratic_term_le_cubic_term_add_constant
        (b := ‖hessian f x‖ / 2) (ε := ε) (r := ‖y - x‖) hhess_nonneg hε hr_nonneg
  have hεeq : (M / 6 : ℝ) = ε + ε := by
    dsimp [ε]
    ring
  rw [hεeq] at hpoly
  -- The remaining scalar inequality gives the global lower bound on the whole range.
  nlinarith [hpoly, hlin, hquad]

/-- Positive regularization makes the canonical owner optimal value finite from below. -/
theorem cubicRegularizationProblem_optimalValue_ne_bot
    {f : E → ℝ} {M : ℝ} {x : E} (hM : 0 < M) :
    Φ[f; M](x) ≠ ⊥ := by
  have hbdd : BddBelow (Set.range (m[f; M](x))) :=
    cubicRegularizationQuadraticApproximation_bddBelow hM
  rcases hbdd with ⟨m, hm⟩
  have hlower : (m : EReal) ≤ Φ[f; M](x) := by
    change (m : EReal) ≤
      sInf ((fun y : E ↦ (m[f; M](x; y) : EReal)) '' Set.univ)
    refine le_csInf ?_ ?_
    · exact ⟨_, ⟨x, by simp, rfl⟩⟩
    · rintro _ ⟨y, -, rfl⟩
      change ((m : ℝ) : EReal) ≤ (m[f; M](x; y) : EReal)
      exact EReal.coe_le_coe_iff.mpr (hm (Set.mem_range_self y))
  intro hbot
  rw [hbot] at hlower
  simp at hlower

/-- For positive regularization, the real part of the canonical owner optimal value is bounded
above by the cubic model at every trial point `y` without supplying a minimizer. -/
theorem cubicRegularizationProblem_optimalValue_toReal_le_quadraticApproximation
    {f : E → ℝ} {M : ℝ} {x y : E} (hM : 0 < M) :
    f̄[f; M](x) ≤ m[f; M](x; y) := by
  have hle : Φ[f; M](x) ≤ (m[f; M](x; y) : EReal) :=
    cubicRegularizationProblem_optimalValue_le_quadraticApproximation
  have hopt_ne_top : Φ[f; M](x) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (EReal.coe_ne_top (m[f; M](x; y))) hle
  simpa using
    EReal.toReal_le_toReal hle
      (cubicRegularizationProblem_optimalValue_ne_bot hM)
      (EReal.coe_ne_top (m[f; M](x; y)))
