/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Primary domain: parameter comparison for exact values of quadratically regularized local models
on a feasible set in a real inner-product space.

Owner declarations sampled before refining:
* `quadraticallyRegularizedObjective` in `FirstOrderTaylorModel.lean`, which owns the regularized
  local model `x ↦ f(xBar; x) + (γ / 2) ‖x - xBar‖²`;
* `quadraticallyRegularizedObjective_apply`, the owner pointwise evaluation formula;
* `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the Chapter 1 owner for
  exact constrained values;
* `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, the attained-value bridge for
  that owner.

Best owner abstraction:
* the constrained problem
  `SetConstrainedMinimizationProblem.mk Q
    (quadraticallyRegularizedObjective (f xBar) γ xBar)`;
* source-facing exact values as the real view `modelValue γ` of that owner optimal value.

Source/core/bridge triage:
* source-facing: the lower quadratic model inequality for the triple `(x_f, g_f, f^*)`;
* core/canonical: the owner exact values above, built from the Chapter 1 constrained-minimization
  owner applied to `quadraticallyRegularizedObjective`;
* bridge/view: the theorem below, which converts the source lower-model inequality at `γ₁`
  into the canonical exact-value comparison between `γ₁` and `γ₂`.

Primitive data:
* the feasible set `Q`;
* the local model family `f : E → E → ℝ`;
* the base point `xBar`;
* the parameters `γ₁`, `γ₂`;
* the source-facing reduced-gradient vector `g₁`.

Derived API:
* the exact local values at `γ₁` and `γ₂` through the local source-facing notation `modelValue`,
  defined as the real view of the owner constrained optimal values.

The previous file-level theorem was keyed to a chosen minimizer at `γ₂`. That moved the public
API away from Lemma 2.19's source-facing lower-model hypothesis. This refinement restores the
source mathematics while keeping the exact-value terms as a bridge from the Chapter 1 constrained
minimization owner, and it removes the unnecessary coordinate model `EuclideanSpace ℝ (Fin n)`
from the public API because the statement uses only the real inner-product-space structure. -/

section

variable (Q : Set E) (f : E → E → ℝ) (xBar : E)

local notation "modelOptimalValue" => fun γ : ℝ ↦
  SetConstrainedMinimizationProblem.optimalValue
    ((SetConstrainedMinimizationProblem.mk Q
      (quadraticallyRegularizedObjective (f xBar) γ xBar)) :
        SetConstrainedMinimizationProblem E)
local notation "modelValue" => fun γ : ℝ ↦ EReal.toReal (modelOptimalValue γ)

/-- Any exact minimizer of the quadratically regularized local model realizes the real view of the
Chapter 1 owner exact value `modelValue γ` for that regularized local problem. -/
theorem regularizedModelOptimalValue_toReal_eq_of_isMinOn
    (x : E) (γ : ℝ)
    (hx : x ∈ Q)
    (hmin : IsMinOn (quadraticallyRegularizedObjective (f xBar) γ xBar) Q x) :
    modelValue γ = quadraticallyRegularizedObjective (f xBar) γ xBar x := by
  let problem : SetConstrainedMinimizationProblem E :=
    .mk Q (quadraticallyRegularizedObjective (f xBar) γ xBar)
  have hopt :
      problem.optimalValue =
        (quadraticallyRegularizedObjective (f xBar) γ xBar x : EReal) :=
    problem.optimalValue_eq_of_isMinOn hx hmin
  change EReal.toReal problem.optimalValue =
    quadraticallyRegularizedObjective (f xBar) γ xBar x
  simpa using congrArg EReal.toReal hopt

variable [InnerProductSpace ℝ E]

/-- Helper for Lemma 2.19: completing the square isolates the `γ₂`-quadratic term and the
comparison constant contributed by `g₁`. -/
lemma lower_affine_quadratic_eq_completed_square
    (value₁ γ₁ γ₂ : ℝ) (g₁ xBar x : E)
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) :
    value₁ +
        inner ℝ g₁ (x - xBar) +
        (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
        (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ) =
      value₁ +
        (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
  -- Complete the square around the shifted center `xBar - γ₂⁻¹ • g₁`.
  have hsub :
      x - (xBar - γ₂⁻¹ • g₁) = (x - xBar) + γ₂⁻¹ • g₁ := by
    abel_nf
  have hsq :
      (γ₂ / 2 : ℝ) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) =
        (γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
          inner ℝ g₁ (x - xBar) +
          (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
    calc
      (γ₂ / 2 : ℝ) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ)
          = (γ₂ / 2 : ℝ) *
              inner ℝ (x - (xBar - γ₂⁻¹ • g₁)) (x - (xBar - γ₂⁻¹ • g₁)) := by
                rw [real_inner_self_eq_norm_sq]
      _ = (γ₂ / 2 : ℝ) *
            inner ℝ ((x - xBar) + γ₂⁻¹ • g₁) ((x - xBar) + γ₂⁻¹ • g₁) := by
              rw [hsub]
      _ = (γ₂ / 2 : ℝ) *
            (inner ℝ (x - xBar) (x - xBar) +
              inner ℝ (x - xBar) (γ₂⁻¹ • g₁) +
              inner ℝ (γ₂⁻¹ • g₁) (x - xBar) +
              inner ℝ (γ₂⁻¹ • g₁) (γ₂⁻¹ • g₁)) := by
                rw [inner_add_add_self]
      _ = (γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g₁ (x - xBar) +
            (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq, inner_smul_right, real_inner_smul_left,
                real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
              have hcomm : inner ℝ (x - xBar) g₁ = inner ℝ g₁ (x - xBar) := by
                simpa using (real_inner_comm (x - xBar) g₁).symm
              rw [hcomm]
              field_simp [hγ₂]
              ring
  have hcoeff :
      (1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂) = (γ₂ - γ₁) / (2 * γ₁ * γ₂) := by
    field_simp [hγ₁, hγ₂]
  calc
    value₁ +
        inner ℝ g₁ (x - xBar) +
        (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
        (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ)
      =
        value₁ +
          ((γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g₁ (x - xBar) +
            (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) +
          (((1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) := by
            ring
    _ = value₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          (((1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) := by
            rw [← hsq]
    _ = value₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
            rw [hcoeff]

/-- Helper for Lemma 2.19: the source lower model at `γ₁` yields a pointwise lower bound for the
`γ₂`-regularized objective by a constant independent of `x`. -/
lemma regularized_objective_ge_comparison_constant
    (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    ∀ x ∈ Q,
      modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) ≤
      quadraticallyRegularizedObjective (f xBar) γ₂ xBar x := by
  intro x hx
  -- Add the `γ₂`-penalty to the source lower bound.
  have hregularized :
      modelValue γ₁ +
          inner ℝ g₁ (x - xBar) +
          (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
          (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ) ≤
        quadraticallyRegularizedObjective (f xBar) γ₂ xBar x := by
    simpa [quadraticallyRegularizedObjective_apply, add_assoc, add_left_comm, add_comm] using
      add_le_add_right (hlower x hx) ((γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ))
  -- Complete the square so the only extra term is nonnegative.
  rw [lower_affine_quadratic_eq_completed_square (value₁ := modelValue γ₁)
      (γ₁ := γ₁) (γ₂ := γ₂) (g₁ := g₁) (xBar := xBar) (x := x) hγ₁.ne' hγ₂.ne'] at hregularized
  have hnonneg :
      0 ≤ (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) := by
    positivity
  have hconst_le :
      modelValue γ₁ +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) ≤
        modelValue γ₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
    linarith
  exact hconst_le.trans hregularized

/-- Helper for Lemma 2.19: the comparison constant is bounded above by the owner optimal value of
the `γ₂`-regularized problem. -/
lemma comparison_constant_le_modelOptimalValue
    (hQ : Q.Nonempty) (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    (((modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
      modelOptimalValue γ₂ := by
  let comparisonValue : ℝ :=
    modelValue γ₁ + ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)
  let comparisonProblem : SetConstrainedMinimizationProblem E :=
    .mk Q (fun _ : E ↦ comparisonValue)
  let regularizedProblem : SetConstrainedMinimizationProblem E :=
    .mk Q (quadraticallyRegularizedObjective (f xBar) γ₂ xBar)
  -- Compare the constant problem with the actual regularized problem on the shared feasible set.
  have hpointwise :
      ∀ x ∈ comparisonProblem.feasibleSet, comparisonProblem x ≤ regularizedProblem x := by
    intro x hx
    simpa [comparisonProblem, regularizedProblem, comparisonValue] using
      regularized_objective_ge_comparison_constant
        (Q := Q) (f := f) (xBar := xBar) γ₁ γ₂ g₁ hγ₁ hγ₂ hlower x hx
  have hopt_le :
      comparisonProblem.optimalValue ≤ regularizedProblem.optimalValue := by
    exact SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      comparisonProblem regularizedProblem rfl hpointwise
  rcases hQ with ⟨xQ, hxQ⟩
  -- The constant problem attains its optimal value at any feasible point.
  have hcomparison_eq : comparisonProblem.optimalValue = (comparisonValue : EReal) := by
    simpa [comparisonProblem] using
      comparisonProblem.optimalValue_eq_of_isMinOn hxQ (isMinOn_const : IsMinOn _ Q xQ)
  rw [hcomparison_eq] at hopt_le
  change (comparisonValue : EReal) ≤ modelOptimalValue γ₂ at hopt_le
  simpa [regularizedProblem, comparisonValue] using hopt_le

/-- Lemma 2.19: if the source-facing lower quadratic model inequality holds at `xBar` with
parameter `γ₁ > 0` and reduced-gradient vector `g₁`, then the exact regularized model values
satisfy
`f^*(xBar; γ₂) ≥ f^*(xBar; γ₁) + ((γ₂ - γ₁) / (2 γ₁ γ₂)) ‖g₁‖²`
for every `γ₂ > 0`. Here the textbook value `f^*(xBar; γ)` is recorded by the local notation
`modelValue γ`, i.e. the real view of the Chapter 1 owner exact value of the constrained problem
with feasible set `Q` and objective
`quadraticallyRegularizedObjective (f xBar) γ xBar`. -/
-- Proof sketch: add the `γ₂`-regularization term to the assumed lower model inequality at `γ₁`.
-- The right-hand side becomes the owner exact value `modelValue γ₁` plus an
-- affine-quadratic
-- function of `x - xBar`
-- with linear part `g₁` and curvature `γ₂ / 2`; complete the square to identify its minimum as
-- `((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖²` above that owner exact value. Taking the infimum over
-- the nonempty feasible set `Q` of the left-hand side gives the corresponding owner exact value
-- `modelValue γ₂`.
theorem exactValue_ge_of_lowerQuadraticModel
    (hQ : Q.Nonempty) (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    modelValue γ₂ ≥
      modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
  let comparisonValue : ℝ :=
    modelValue γ₁ + ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)
  -- Compare the owner optimal value with the constant lower bound produced by the source model.
  have hcomparison :
      ((comparisonValue : ℝ) : EReal) ≤
        modelOptimalValue γ₂ := by
    simpa [comparisonValue] using comparison_constant_le_modelOptimalValue
      (Q := Q) (f := f) (xBar := xBar) hQ γ₁ γ₂ g₁ hγ₁ hγ₂ hlower
  rcases hQ with ⟨xQ, hxQ⟩
  -- Any feasible point shows that the owner optimal value is not `⊤`.
  have hmodel_ne_top : modelOptimalValue γ₂ ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (EReal.coe_ne_top (quadraticallyRegularizedObjective (f xBar) γ₂ xBar xQ))
      (((SetConstrainedMinimizationProblem.mk Q
          (quadraticallyRegularizedObjective (f xBar) γ₂ xBar)) :
            SetConstrainedMinimizationProblem E).optimalValue_le_of_mem_feasibleSet hxQ)
  -- Convert the owner `EReal` inequality back to the source-facing real exact values.
  have htoReal :
      comparisonValue ≤
        modelValue γ₂ := by
    have htoReal' :=
      EReal.toReal_le_toReal hcomparison (EReal.coe_ne_bot _) hmodel_ne_top
    change comparisonValue ≤ EReal.toReal (modelOptimalValue γ₂) at htoReal'
    simpa using htoReal'
  simpa [comparisonValue] using htoReal

end
