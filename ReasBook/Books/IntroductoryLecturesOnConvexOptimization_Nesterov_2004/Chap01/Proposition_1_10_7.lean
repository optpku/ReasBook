/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ} (problem : LagrangianProblem Q m)

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "ψ" => problem.dualFunction
local notation "X⋆" => problem.lagrangianMinimizers

/-
Primary domain: Lagrangian duality for inequality-constrained problems.

Owner declarations sampled before refining this file:
* `LagrangianProblem.dualFunction`, `dualDomain`, `lagrangianMinimizers`, and
  `dualFunction_eq_lagrangian` in
  `Definition_1_10_2`;
* mathlib's owner predicate `ConcaveOn` in `Mathlib/Analysis/Convex/Function`, the canonical
  Jensen-style abstraction when the codomain is an `ℝ`-module;
* the Chapter 3 finite-part API `extendedRealEffectiveDomain`, `extendedRealRealPart`, and the
  resulting `ConcaveOn`-based owner style for `EReal`-valued functions once such a bridge is
  available;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualFunction_eq_lagrangian` in
  `Definition_2_31`, a downstream bridge that should delegate to the owner-level single-minimizer
  identity rather than reprove it.

Best owner abstraction: `problem : LagrangianProblem Q m`. The primitive data remain only the
owner fields `objective` and `constraints`; `constraintVector`, `dualFunction`, `dualDomain`, and
`lagrangianMinimizers` are derived API.

Source/core/bridge triage in this file:
* source-facing: Proposition 1.10.7's affine upper-support inequality for `dualFunction`;
* core/canonical: the owner identity `ψ(λ) = 𝓛(x, λ)` at a point `x ∈ X*(λ)`, now attached
  directly to `LagrangianProblem`;
* bridge/view: the Jensen-style concavity inequality on `dualDomain`.

Because `dualFunction` is `EReal`-valued, the direct mathlib owner `ConcaveOn ℝ _ ψ` is not
available here: `EReal` does not carry the required `SMul ℝ EReal` instance. The Chapter 3
finite-part bridge `ConcaveOn ℝ (dom ψ) (extendedRealRealPart ψ)` is therefore a later
bridge/view layer, not the Chapter 1 owner. This file correspondingly keeps the source-facing
Jensen inequality rather than forcing an ad hoc real-valued wrapper.
-/

-- The source proof first identifies the affine dependence of `𝓛(x, ·)` on the multiplier and
-- then transfers that pointwise structure to the infimum defining `ψ`.
/-- Helper for Proposition 1.10.7: changing the multiplier changes the Lagrangian by the
corresponding constraint inner product. -/
lemma lagrangian_eq_add_inner_sub
    {x : Q} {lam₁ lam₂ : Λ} :
    (problem.lagrangian x lam₂ : EReal) =
      (problem.lagrangian x lam₁ : EReal) +
        inner ℝ (problem.constraintVector x) (lam₂ - lam₁) := by
  -- Normalize the affine change in the multiplier on the real side before casting to `EReal`.
  have hreal :
      problem.lagrangian x lam₂ =
        problem.lagrangian x lam₁ + inner ℝ (problem.constraintVector x) (lam₂ - lam₁) := by
    rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
    have hcomm :
        inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
          inner ℝ (lam₂ - lam₁) (problem.constraintVector x) := by
      simpa using (real_inner_comm (problem.constraintVector x) (lam₂ - lam₁)).symm
    rw [hcomm, inner_sub_left]
    ring_nf
  exact_mod_cast hreal

/-- Helper for Proposition 1.10.7: for each fixed `x`, the Lagrangian is affine in the
multiplier. -/
lemma lagrangian_convexCombination_eq
    {x : Q} {lam₁ lam₂ : Λ} {a b : ℝ} (hab : a + b = 1) :
    problem.lagrangian x (a • lam₁ + b • lam₂) =
      a * problem.lagrangian x lam₁ + b * problem.lagrangian x lam₂ := by
  -- Expand the Lagrangian and collect the objective and inner-product terms by the weights.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    problem x + (a * inner ℝ lam₁ (problem.constraintVector x) +
        b * inner ℝ lam₂ (problem.constraintVector x)) =
      (a + b) * problem x +
        (a * inner ℝ lam₁ (problem.constraintVector x) +
          b * inner ℝ lam₂ (problem.constraintVector x)) := by
        rw [hab, one_mul]
    _ = a * (problem x + inner ℝ lam₁ (problem.constraintVector x)) +
        b * (problem x + inner ℝ lam₂ (problem.constraintVector x)) := by
      ring

/-- Helper for Proposition 1.10.7: every weighted average of two dual values is bounded above by
the corresponding weighted Lagrangian evaluation at any fixed point `x`. -/
lemma weighted_dualFunction_le_lagrangian_convexCombination
    {x : Q} {lam₁ lam₂ : Λ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤
      (problem.lagrangian x (a • lam₁ + b • lam₂) : EReal) := by
  -- Bound each dual value by evaluating the defining infimum at the chosen point `x`.
  have h₁ : ψ lam₁ ≤ (problem.lagrangian x lam₁ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₁))
        (x := x)
        (by simp))
  have h₂ : ψ lam₂ ≤ (problem.lagrangian x lam₂ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₂))
        (x := x)
        (by simp))
  -- Preserve those bounds under the nonnegative weights and collapse the right-hand side.
  have hmul₁ :
      (a : EReal) * ψ lam₁ ≤ (a : EReal) * (problem.lagrangian x lam₁ : EReal) := by
    exact mul_le_mul_of_nonneg_left h₁ (by exact_mod_cast ha)
  have hmul₂ :
      (b : EReal) * ψ lam₂ ≤ (b : EReal) * (problem.lagrangian x lam₂ : EReal) := by
    exact mul_le_mul_of_nonneg_left h₂ (by exact_mod_cast hb)
  calc
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤
        (a : EReal) * (problem.lagrangian x lam₁ : EReal) +
          (b : EReal) * (problem.lagrangian x lam₂ : EReal) := by
      exact add_le_add hmul₁ hmul₂
    _ = (problem.lagrangian x (a • lam₁ + b • lam₂) : EReal) := by
      exact_mod_cast (problem.lagrangian_convexCombination_eq (x := x) (hab := hab)).symm

/-- Proposition 1.10.7: if `x₁ ∈ X*(λ₁)`, then the dual function is bounded above by the affine
support determined by `x₁` at `λ₁`. -/
-- Proof sketch: bound `ψ(λ₂)` by evaluating the infimum defining `ψ(λ₂)` at `x₁`, use
-- `problem.dualFunction_eq_lagrangian hx₁` to replace `𝓛(x₁, λ₁)` with `ψ(λ₁)`, and simplify the
-- difference of the two
-- Lagrangian values into the inner product with `λ₂ - λ₁`.
theorem dualFunction_le_affine_support_of_mem_lagrangianMinimizers
    {lam₁ lam₂ : Λ} {x₁ : Q}
    (hx₁ : x₁ ∈ X⋆ lam₁) :
    ψ lam₂ ≤ ψ lam₁ + (inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) : EReal) := by
  -- Evaluate the infimum defining `ψ(λ₂)` at the chosen minimizer `x₁`.
  have hdualLe : ψ lam₂ ≤ (problem.lagrangian x₁ lam₂ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₂))
        (x := x₁)
        (by simp))
  -- Replace the value at `λ₁` by `ψ(λ₁)` and rewrite the multiplier shift affinely.
  calc
    ψ lam₂ ≤ (problem.lagrangian x₁ lam₂ : EReal) := hdualLe
    _ = (problem.lagrangian x₁ lam₁ : EReal) +
          inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) :=
      problem.lagrangian_eq_add_inner_sub
    _ = ψ lam₁ + (inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) : EReal) := by
      rw [problem.dualFunction_eq_lagrangian hx₁]

/-- On `dom ψ = {λ | ψ(λ) > -∞}`, the dual function satisfies the Jensen inequality for
concavity. -/
-- Proof sketch: write `ψ` as the pointwise infimum of the affine maps
-- `λ ↦ 𝓛(x, λ)` indexed by `x ∈ Q`, evaluate those affine maps at the convex combination
-- `a • λ₁ + b • λ₂`, and then pass to the infimum over `x`.
theorem dualFunction_concave_on_dualDomain
    {lam₁ lam₂ : Λ}
    (h_lam₁ : lam₁ ∈ problem.dualDomain) (h_lam₂ : lam₂ ∈ problem.dualDomain)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤ ψ (a • lam₁ + b • lam₂) := by
  -- The domain hypotheses record the stated domain restriction; the Jensen argument is pointwise.
  let _ := h_lam₁
  let _ := h_lam₂
  -- Rewrite the dual value at the convex combination as an infimum over all Lagrangian values.
  rw [LagrangianProblem.dualFunction,
    SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, -, rfl⟩
  -- Each pointwise affine upper bound survives to the infimum over all `x`.
  exact problem.weighted_dualFunction_le_lagrangian_convexCombination
    (x := x) ha hb hab

end LagrangianProblem
