/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_39
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_40
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_2_1_Implementability_Assumptions_for_Primal_Dual_Structure

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u v

/- Theorem 6.2.3 lies in the Chapter 6 excessive-gap / adjoint-gradient update domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_38`, the `μ₁ = 0`
  excessive-gap owner already built on the chapter certificate owner;
- `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`, and
  `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_30` and `Chap06/Definition_6_32`, the
  Chapter 6 owners for the smoothed primal value, the dual oracle argmax set, and the
  zero-smoothing primal minimizer subproblem;
- `IsAdjointGradientMappingOn` in `Chap06/Definition_6_40`, the source-facing owner for the
  feasible adjoint gradient update map;
- `tau_mem_Icc` in `Chap06/Theorem_6_4`, the chapter helper turning `0 < τ < 1` into the
  canonical convex-combination parameter `τ ∈ Set.Icc (0 : ℝ) 1`;
- `predicted_primal_point`, `updated_dual_point`, and `updated_primal_point` in
  `Chap06/Theorem_6_4`, whose source-facing update-owner shape matches the odd-step updates here.

Best owner abstraction:
- source-facing: the odd-step update points `\hat u`, `\bar x_+`, and `\bar u_+` together with
  preservation of `satisfiesExcessiveGapConditionWithMu1Zero`;
- core/canonical: `satisfiesExcessiveGapConditionWithMu1Zero`, `smoothedPrimalObjective`,
  `smoothedDualObjective`, `smoothedPrimalObjectiveArgmax`,
  `smoothedDualObjectiveMinimand`, `IsAdjointGradientMappingOn`, and the convex-combination owner
  `τ ∈ Set.Icc (0 : ℝ) 1`;
- bridge/view: the subtype-valued update maps below, which keep the updated points feasible
  without introducing a second certificate owner.

Primitive data:
- the convex feasible sets `Q₁`, `Q₂`;
- the Chapter 6 zero-smoothing primal minimizer and positive-smoothing dual argmax data selecting
  `x₀`, the fixed oracle `u_{μ₂}`, and the adjoint gradient map `V`;
- the current feasible pair `(xBar, uBar)` and the step size `τ`.

Derived API:
- the reduced smoothing parameter `μ₂⁺ = (1 - τ) μ₂` from the positive source parameter
  `μ₂ : {μ : ℝ // 0 < μ}`;
- the feasible update points `predictedDualPoint`, `updatedPrimalPoint`, and `updatedDualPoint`;
- the preserved `μ₁ = 0` excessive-gap certificate.

The previous file exposed separate public membership lemmas whose only role was to build the
subtype-valued update points, and it parameterized the odd-step updates by an artificial family
`Q₁ → ℝ → Q₂` instead of the fixed source oracle `u_{μ₂}`. The refinement keeps the source-facing
update owners, reuses the chapter's `τ ∈ Set.Icc` owner shape from `Theorem_6_4`, and states the
main theorem on the actual Chapter 6 primal and dual value owners rather than on arbitrary raw
functions.
-/

namespace StronglyConvexDualUpdate

section Updates

section DualUpdates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The reduced dual smoothing parameter `μ₂⁺ = (1 - τ) μ₂`. -/
def reducedDualSmoothing (μ₂ τ : ℝ) : ℝ :=
  (1 - τ) * μ₂

/-- Expanding `reducedDualSmoothing` recovers the formula `μ₂⁺ = (1 - τ) μ₂`. -/
theorem reducedDualSmoothing_def (μ₂ τ : ℝ) :
    reducedDualSmoothing μ₂ τ = (1 - τ) * μ₂ :=
  rfl

/-- The intermediate dual point `\hat u = (1 - τ) \bar u + τ u_{μ₂}(\bar x)`. -/
def predictedDualPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₂ :=
  ⟨(1 - τ) • (uBar : E₂) + τ • (uμ₂ xBar : E₂),
    by
      have hu :
          (uBar : E₂) + τ • ((uμ₂ xBar : Q₂) - (uBar : E₂)) ∈ Q₂ :=
        hQ₂.add_smul_sub_mem uBar.property (uμ₂ xBar).property hτ
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using hu⟩

/-- Expanding `predictedDualPoint` recovers
`\hat u = (1 - τ) \bar u + τ u_{μ₂}(\bar x)`. -/
@[simp] theorem predictedDualPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ : E₂) =
      (1 - τ) • (uBar : E₂) + τ • (uμ₂ xBar : E₂) :=
  rfl

/-- The updated dual point `\bar u_+ = V(\hat u)`. -/
def updatedDualPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₂ :=
  V (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ)

/-- Expanding `updatedDualPoint` recovers `\bar u_+ = V(\hat u)`. -/
@[simp] theorem updatedDualPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updatedDualPoint hQ₂ uμ₂ V xBar uBar τ hτ : E₂) =
      V (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) :=
  rfl

end DualUpdates

section PrimalUpdate

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The updated primal point `\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`. -/
def updatedPrimalPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (x₀ : Q₂ → Q₁) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₁ :=
  ⟨(1 - τ) • (xBar : E₁) +
      τ •
        (x₀ (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) : E₁),
    by
      let uHat := predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ
      have hx :
          (xBar : E₁) + τ • ((x₀ uHat : Q₁) - (xBar : E₁)) ∈ Q₁ :=
        hQ₁.add_smul_sub_mem xBar.property (x₀ uHat).property hτ
      simpa [uHat, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul]
        using hx⟩

/-- Expanding `updatedPrimalPoint` recovers
`\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`. -/
@[simp] theorem updatedPrimalPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (x₀ : Q₂ → Q₁) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updatedPrimalPoint hQ₁ hQ₂ x₀ uμ₂ xBar uBar τ hτ : E₁) =
      (1 - τ) • (xBar : E₁) +
        τ • (x₀ (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) : E₁) :=
  rfl

end PrimalUpdate

end Updates

section Theorem

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Helper for Theorem 6.2.3: the updated dual point `V(\hat u)` maximizes the adjoint-gradient
quadratic model based at the predicted dual point `\hat u`. -/
theorem updatedDualPoint_isMaxOn
    {Q₁ : Set E₁} {Q₂ : Set E₂} {φ : E₂ → ℝ} {Lphi : ℝ}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hV : IsAdjointGradientMappingOn Q₂ φ Lphi V) :
    IsMaxOn
      (adjointGradientMaximand φ Lphi
        (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ : E₂))
      Q₂
      (updatedDualPoint hQ₂ uμ₂ V xBar uBar τ hτ : E₂) := by
  -- `updatedDualPoint` is exactly the adjoint-gradient map `V` applied at the predicted point.
  simpa [updatedDualPoint_val] using
    isAdjointGradientMappingOn_isMaxOn hV
      (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ)

/-- Helper for Theorem 6.2.3: evaluating the zero-smoothed dual objective at a selected primal
argmin replaces the infimum by the attained slice value. -/
theorem zeroSmoothedDualObjective_value_at_selector
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (u : problem.dualSet) :
    extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u =
      -problem.dualPenalty u +
        problem.linearMap (x₀ u) (u : E₂) +
        problem.smoothPart (x₀ u) := by
  -- The selected primal point `x₀ u` attains the zero-smoothed dual slice at `u`.
  have hvalue :
      extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u =
        -problem.dualPenalty u +
          problem.linearMap (x₀ u) (u : E₂) +
          problem.smoothPart (x₀ u) := by
    simpa using
      (smoothedDualObjective_value_at_selected_argmin problem.linearMap (hx₀ u))
  exact hvalue

/-- Helper for Theorem 6.2.3: a within-set gradient field with Lipschitz constant `L` yields the
standard lower quadratic model on a convex feasible set. -/
theorem lowerQuadraticModel_of_hasGradientWithinAt_lipschitzOn
    {Q : Set E₂} {φ : E₂ → ℝ} {g : E₂ → E₂} {L : NNReal}
    (hgrad : ∀ ⦃u : E₂⦄, u ∈ Q → HasGradientWithinAt φ (g u) Q u)
    (hg_lipschitz : LipschitzOnWith L g Q)
    (hQ_convex : Convex ℝ Q)
    {u₀ u : E₂} (hu₀ : u₀ ∈ Q) (hu : u ∈ Q) :
    φ u₀ +
        inner ℝ (g u₀) (u - u₀) -
        ((L : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) ≤
      φ u := by
  have hgrad_neg :
      ∀ ⦃v : E₂⦄, v ∈ Q →
        HasGradientWithinAt (fun w : E₂ ↦ -φ w) (-g v) Q v := by
    intro v hv
    -- Negating the objective negates its within-set gradient witness.
    simpa using ((hgrad hv).hasFDerivWithinAt.neg).hasGradientWithinAt
  have hg_neg_lipschitz : LipschitzOnWith L (fun v : E₂ ↦ -g v) Q := by
    intro v hv w hw
    -- The negated vector field has the same Lipschitz constant.
    simpa using hg_lipschitz hv hw
  have hupper_neg :
      -φ u ≤
        -φ u₀ +
          inner ℝ (-g u₀) (u - u₀) +
            ((L : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) := by
    -- Apply the standard upper model to the negated objective.
    simpa using
      (upper_model_of_hasGradientWithinAt_lipschitzOn
        hgrad_neg hg_neg_lipschitz hQ_convex hu₀ hu)
  -- Rearranging the upper model for `-φ` gives the lower model for `φ`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_neg_left] using
    (neg_le_neg hupper_neg)

/-- Helper for Theorem 6.2.3: the chapter dual oracle attains the old smoothed primal value at
`xBar`. -/
theorem dualOracleValue_eq_oldSmoothedPrimalObjective
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}} :
    smoothedPrimalObjective problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar =
      problem.smoothPart xBar +
        problem.linearMap xBar (problem.dualOracleSolver xBar μ₂) -
        problem.dualPenalty (problem.dualOracleSolver xBar μ₂) -
        (μ₂ : ℝ) * problem.dualProxFunction (problem.dualOracleSolver xBar μ₂) := by
  -- Rewrite the supremum term by the oracle value supplied by the Chapter 6 argmax owner.
  have horacle :
      smoothedPrimalObjective problem.linearMap problem.dualSet
          (fun _ : E₁ ↦ 0) problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar =
        smoothedPrimalObjectiveMaximand problem.linearMap
          problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar
          (problem.dualOracleSolver xBar μ₂) := by
    exact smoothedPrimalObjectiveArgmax.value_eq (problem.dualOracleSolver_spec xBar μ₂)
  have hsSup :
      sSup
          (smoothedPrimalObjectiveMaximand problem.linearMap
            problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) (xBar : E₁) ''
            problem.dualSet) =
        smoothedPrimalObjectiveMaximand problem.linearMap
          problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar
          (problem.dualOracleSolver xBar μ₂) := by
    simpa [smoothedPrimalObjective_apply] using horacle
  -- Expand the old smoothed primal objective after replacing the attained supremum.
  rw [smoothedPrimalObjective_apply, hsSup]
  simp [smoothedPrimalObjectiveMaximand, sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Theorem 6.2.3: if `0 < μ₂` and `τ < 1`, then the updated smoothing
`μ₂⁺ = (1 - τ) μ₂` is still positive. -/
theorem reducedDualSmoothing_pos
    {μ₂ τ : ℝ} (hμ₂ : 0 < μ₂) (hτ_lt : τ < 1) :
    0 < reducedDualSmoothing μ₂ τ := by
  -- Positivity is preserved because both factors in `(1 - τ) μ₂` are positive.
  have hfactor : 0 < 1 - τ := sub_pos.mpr hτ_lt
  rw [reducedDualSmoothing_def]
  nlinarith

/-- Helper for Theorem 6.2.3: the new smoothed primal value at `\bar x_+` is bounded by the
weighted old certificate term together with the selector slice at the actual new oracle. -/
theorem updatedPrimalObjective_le_weightedGapAndSelectorSliceAtNewOracle
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    smoothedPrimalObjective problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction
        (reducedDualSmoothing μ₂ τ) xBarPlus ≤
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
        τ *
          (problem.smoothPart (x₀ uHat) +
            problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  have hone_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_lt.le
  have hsmooth_conv :
      problem.smoothPart xBarPlus ≤
        (1 - τ) * problem.smoothPart xBar + τ * problem.smoothPart (x₀ uHat) := by
    -- Convexity of `\hat f` controls the updated primal point by its two defining endpoints.
    simpa [xBarPlus, uHat, hτIcc, updatedPrimalPoint_val] using
      (problem.smoothPart_convex.2 xBar.property (x₀ uHat).property hone_sub_nonneg hτ.le
        (by ring))
  have hold_support :
      problem.smoothPart xBar +
          problem.linearMap xBar (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle ≤
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar := by
    have hmax :
        smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar
            (uPlusOracle : E₂) ≤
          smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar
            (problem.dualOracleSolver xBar μ₂ : E₂) :=
      (problem.dualOracleSolver_isMaxOn xBar μ₂) uPlusOracle.property
    have hmax_support :
        problem.linearMap xBar (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle -
            (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle ≤
          problem.linearMap xBar (problem.dualOracleSolver xBar μ₂ : E₂) -
            problem.dualPenalty (problem.dualOracleSolver xBar μ₂) -
            (μ₂ : ℝ) * problem.dualProxFunction (problem.dualOracleSolver xBar μ₂) := by
      simpa [smoothedPrimalObjectiveMaximand] using hmax
    have horacle_value :
        smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar =
          problem.smoothPart xBar +
            problem.linearMap xBar (problem.dualOracleSolver xBar μ₂ : E₂) -
            problem.dualPenalty (problem.dualOracleSolver xBar μ₂) -
            (μ₂ : ℝ) * problem.dualProxFunction (problem.dualOracleSolver xBar μ₂) :=
      dualOracleValue_eq_oldSmoothedPrimalObjective problem
    -- Compare the selected new oracle with the old maximizing dual oracle at `xBar`.
    rw [horacle_value]
    nlinarith [hmax_support]
  have hxBarPlus_val :
      (xBarPlus : E₁) = (1 - τ) • (xBar : E₁) + τ • (x₀ uHat : E₁) := by
    simp [xBarPlus, uHat, updatedPrimalPoint_val]
  have hnew_value :
      smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction
          (reducedDualSmoothing μ₂ τ) xBarPlus =
        problem.smoothPart xBarPlus +
          problem.linearMap xBarPlus (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (reducedDualSmoothing μ₂ τ) * problem.dualProxFunction uPlusOracle := by
    have horacle_new :
        smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂Plus : ℝ) xBarPlus =
          problem.smoothPart xBarPlus +
            problem.linearMap xBarPlus (problem.dualOracleSolver xBarPlus μ₂Plus : E₂) -
            problem.dualPenalty (problem.dualOracleSolver xBarPlus μ₂Plus) -
            (μ₂Plus : ℝ) * problem.dualProxFunction (problem.dualOracleSolver xBarPlus μ₂Plus) := by
      exact dualOracleValue_eq_oldSmoothedPrimalObjective problem
    -- Evaluate the new smoothed primal objective at the actual new oracle.
    simpa [μ₂Plus, uPlusOracle] using horacle_new
  have hlinear_split :
      problem.linearMap xBarPlus (uPlusOracle : E₂) =
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) := by
    -- The linear map in the primal variable splits exactly across the update formula.
    rw [hxBarPlus_val]
    simp
  have hsplit :
      problem.smoothPart xBarPlus +
          problem.linearMap xBarPlus (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (reducedDualSmoothing μ₂ τ) * problem.dualProxFunction uPlusOracle =
        problem.smoothPart xBarPlus +
          ((1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
            τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂)) -
          problem.dualPenalty uPlusOracle -
          ((1 - τ) * (μ₂ : ℝ)) * problem.dualProxFunction uPlusOracle := by
    rw [hlinear_split, reducedDualSmoothing_def]
  -- Evaluate the new smoothed primal value at its actual oracle and split the update formula.
  calc
    smoothedPrimalObjective problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction
        (reducedDualSmoothing μ₂ τ) xBarPlus =
      problem.smoothPart xBarPlus +
        problem.linearMap xBarPlus (uPlusOracle : E₂) -
        problem.dualPenalty uPlusOracle -
        (reducedDualSmoothing μ₂ τ) * problem.dualProxFunction uPlusOracle := hnew_value
    _ =
        problem.smoothPart xBarPlus +
          ((1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
            τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂)) -
          problem.dualPenalty uPlusOracle -
          ((1 - τ) * (μ₂ : ℝ)) * problem.dualProxFunction uPlusOracle := hsplit
    _ ≤
        (1 - τ) *
            (problem.smoothPart xBar +
              problem.linearMap xBar (uPlusOracle : E₂) -
              problem.dualPenalty uPlusOracle -
              (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle) +
          τ *
            (problem.smoothPart (x₀ uHat) +
              problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.dualPenalty uPlusOracle) := by
          -- After the exact linear splitting, only the smooth part needs an inequality.
          nlinarith [hsmooth_conv]
    _ ≤
        (1 - τ) *
            smoothedPrimalObjective problem.linearMap problem.dualSet
              problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
          τ *
            (problem.smoothPart (x₀ uHat) +
              problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.dualPenalty uPlusOracle) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hold_support hone_sub_nonneg)
            le_rfl

/-- Helper for Theorem 6.2.3: the predicted dual update rewrites the old displacement into the
`τ^2 / (1 - τ)` coefficient shape used by the step-size bound. -/
theorem predictedDualPoint_oldDual_displacement
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    (uBar : E₂) - (uHat : E₂) =
      -(τ / (1 - τ)) • ((uMuBar : E₂) - (uHat : E₂)) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  have huHat_val :
      (uHat : E₂) = (1 - τ) • (uBar : E₂) + τ • (uMuBar : E₂) := by
    simp [uHat, uMuBar, predictedDualPoint_val]
  have huMuBar_sub :
      (uMuBar : E₂) - (uHat : E₂) = (1 - τ) • ((uMuBar : E₂) - (uBar : E₂)) := by
    -- Expand the predicted point and collect the shared old dual iterate.
    rw [huHat_val]
    calc
      (uMuBar : E₂) - ((1 - τ) • (uBar : E₂) + τ • (uMuBar : E₂)) =
          (1 : ℝ) • (uMuBar : E₂) - (1 - τ) • (uBar : E₂) - τ • (uMuBar : E₂) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 : ℝ) • (uMuBar : E₂) - τ • (uMuBar : E₂)) - (1 - τ) • (uBar : E₂) := by
            abel_nf
      _ = (1 - τ) • (uMuBar : E₂) - (1 - τ) • (uBar : E₂) := by
            rw [← sub_smul]
      _ = (1 - τ) • ((uMuBar : E₂) - (uBar : E₂)) := by
            rw [smul_sub]
  have hone_sub_ne : 1 - τ ≠ 0 := sub_ne_zero.mpr (ne_of_lt hτ_lt).symm
  have hneg_rev :
      -(τ : ℝ) • ((uMuBar : E₂) - (uBar : E₂)) = τ • ((uBar : E₂) - (uMuBar : E₂)) := by
    rw [smul_sub, smul_sub]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  calc
    (uBar : E₂) - (uHat : E₂) = τ • ((uBar : E₂) - (uMuBar : E₂)) := by
      -- The predicted point displacement is the expected `τ`-scaled oracle difference.
      rw [huHat_val]
      calc
        (uBar : E₂) - ((1 - τ) • (uBar : E₂) + τ • (uMuBar : E₂)) =
            (1 : ℝ) • (uBar : E₂) - (1 - τ) • (uBar : E₂) - τ • (uMuBar : E₂) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = ((1 : ℝ) • (uBar : E₂) - (1 - τ) • (uBar : E₂)) - τ • (uMuBar : E₂) := by
              abel_nf
        _ = τ • (uBar : E₂) - τ • (uMuBar : E₂) := by
              rw [← sub_smul]
              simp
        _ = τ • ((uBar : E₂) - (uMuBar : E₂)) := by
              rw [smul_sub]
    _ = -(τ / (1 - τ)) • ((uMuBar : E₂) - (uHat : E₂)) := by
      rw [huMuBar_sub, smul_smul]
      have hcoeff : -(τ / (1 - τ)) * (1 - τ) = -τ := by
        field_simp [hone_sub_ne]
      rw [hcoeff]
      exact hneg_rev.symm

/-- Helper for Theorem 6.2.3: the step-size condition absorbs the old predicted-dual quadratic
remainder into the old dual-oracle displacement term. -/
theorem stepSizeAbsorbsPredictedDualQuadraticError
    {uBar uMuBar uHat : E₂} {μ₂ τ Lphi : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hdisp : uBar - uHat = -(τ / (1 - τ)) • (uMuBar - uHat))
    (hstep : τ ^ (2 : ℕ) / (1 - τ) ≤ μ₂ / Lphi)
    (hμ₂ : 0 < μ₂) :
    (1 - τ) * (Lphi / 2) * ‖uBar - uHat‖ ^ (2 : ℕ) ≤
      (μ₂ / 2) * ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
  have hone_sub : 0 < 1 - τ := sub_pos.mpr hτ_lt
  have hone_sub_ne : 1 - τ ≠ 0 := ne_of_gt hone_sub
  by_cases hLphi_nonneg : 0 ≤ Lphi
  · by_cases hLphi_zero : Lphi = 0
    · -- When `Lphi = 0`, the quadratic remainder vanishes identically.
      subst hLphi_zero
      have hright_nonneg : 0 ≤ (μ₂ / 2) * ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
        positivity
      simpa using hright_nonneg
    · have hLphi_pos : 0 < Lphi := lt_of_le_of_ne hLphi_nonneg (Ne.symm hLphi_zero)
      have hLphi_ne : Lphi ≠ 0 := ne_of_gt hLphi_pos
      have hcoeff :
          Lphi * τ ^ (2 : ℕ) ≤ μ₂ * (1 - τ) := by
        have hstep' : τ ^ (2 : ℕ) ≤ (μ₂ / Lphi) * (1 - τ) := by
          exact (div_le_iff₀ hone_sub).mp hstep
        have hscaled :
            Lphi * τ ^ (2 : ℕ) ≤ Lphi * ((μ₂ / Lphi) * (1 - τ)) :=
          mul_le_mul_of_nonneg_left hstep' hLphi_pos.le
        calc
          Lphi * τ ^ (2 : ℕ) ≤ Lphi * ((μ₂ / Lphi) * (1 - τ)) := hscaled
          _ = μ₂ * (1 - τ) := by
              field_simp [hLphi_ne]
      have hratio_nonneg : 0 ≤ τ / (1 - τ) := div_nonneg hτ.le hone_sub.le
      have hnorm :
          ‖uBar - uHat‖ ^ (2 : ℕ) =
            (τ / (1 - τ)) ^ (2 : ℕ) * ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
        -- Rewrite the old displacement as a scalar multiple of the oracle displacement.
        rw [hdisp, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hratio_nonneg]
        ring
      have hcoef_le :
          ((1 - τ) * (Lphi / 2)) * (τ / (1 - τ)) ^ (2 : ℕ) ≤ μ₂ / 2 := by
        have htarget : Lphi * τ ^ (2 : ℕ) ≤ μ₂ * (1 - τ) := hcoeff
        field_simp [hone_sub_ne]
        nlinarith
      have hsq_nonneg : 0 ≤ ‖uMuBar - uHat‖ ^ (2 : ℕ) := by positivity
      -- Compare the coefficients after rewriting the displacement norm through `hdisp`.
      calc
        (1 - τ) * (Lphi / 2) * ‖uBar - uHat‖ ^ (2 : ℕ) =
            (((1 - τ) * (Lphi / 2)) * (τ / (1 - τ)) ^ (2 : ℕ)) *
              ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
              rw [hnorm]
              ring
        _ ≤ (μ₂ / 2) * ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef_le hsq_nonneg
  · -- If `Lphi < 0`, the left side is nonpositive while the right side is nonnegative.
    have hleft_nonpos :
        (1 - τ) * (Lphi / 2) * ‖uBar - uHat‖ ^ (2 : ℕ) ≤ 0 := by
      have hcoeff_nonpos : (1 - τ) * (Lphi / 2) ≤ 0 := by
        have hhalf_nonpos : Lphi / 2 ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos hone_sub.le hhalf_nonpos
      have hsq_nonneg : 0 ≤ ‖uBar - uHat‖ ^ (2 : ℕ) := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hsq_nonneg
    have hright_nonneg :
        0 ≤ (μ₂ / 2) * ‖uMuBar - uHat‖ ^ (2 : ℕ) := by
      have hsq_nonneg : 0 ≤ ‖uMuBar - uHat‖ ^ (2 : ℕ) := by positivity
      nlinarith
    exact hleft_nonpos.trans hright_nonneg

/-- Helper for Theorem 6.2.3: after rewriting the old displacement
`uBar - uHat = -(τ / (1 - τ)) • (uMuBar - uHat)`, the weighted first-order terms collapse to the
normalized oracle-gap core. -/
theorem weightedGradientTerms_eq_normalizedOracleGapCore
    {g uBar uMuBar uHat uPlus : E₂} {τ : ℝ}
    (hτ_lt : τ < 1)
    (hdisp : uBar - uHat = -(τ / (1 - τ)) • (uMuBar - uHat)) :
    (1 - τ) * inner ℝ g (uBar - uHat) + τ * inner ℝ g (uPlus - uHat) =
      τ * inner ℝ g (uPlus - uHat) - τ * inner ℝ g (uMuBar - uHat) := by
  have hone_sub_ne : 1 - τ ≠ 0 := sub_ne_zero.mpr (ne_of_lt hτ_lt).symm
  have hcoeff : (1 - τ) * (-(τ / (1 - τ))) = -τ := by
    field_simp [hone_sub_ne]
  -- Rewrite the transported old gradient term through the scalar displacement identity.
  calc
    (1 - τ) * inner ℝ g (uBar - uHat) + τ * inner ℝ g (uPlus - uHat) =
        (1 - τ) * (-(τ / (1 - τ)) * inner ℝ g (uMuBar - uHat)) +
          τ * inner ℝ g (uPlus - uHat) := by
            rw [hdisp, inner_smul_right]
    _ = ((1 - τ) * (-(τ / (1 - τ)))) * inner ℝ g (uMuBar - uHat) +
          τ * inner ℝ g (uPlus - uHat) := by
            ring
    _ = (-τ) * inner ℝ g (uMuBar - uHat) +
          τ * inner ℝ g (uPlus - uHat) := by
            rw [hcoeff]
    _ = τ * inner ℝ g (uPlus - uHat) - τ * inner ℝ g (uMuBar - uHat) := by
            ring

/-- Helper for Theorem 6.2.3: specializing the weighted gradient collapse at `uPlus = uHat`
isolates the exact balance between the old iterate gradient term and the old-oracle gradient term.
-/
theorem predictedDualGradientBalance
    {g uBar uMuBar uHat : E₂} {τ : ℝ}
    (hτ_lt : τ < 1)
    (hdisp : uBar - uHat = -(τ / (1 - τ)) • (uMuBar - uHat)) :
    τ * inner ℝ g (uMuBar - uHat) = -(1 - τ) * inner ℝ g (uBar - uHat) := by
  have hcore :
      (1 - τ) * inner ℝ g (uBar - uHat) =
        -τ * inner ℝ g (uMuBar - uHat) := by
    -- Set `uPlus = uHat` so the normalized oracle-gap identity keeps only the old-oracle term.
    simpa using
      (weightedGradientTerms_eq_normalizedOracleGapCore
        (g := g)
        (uBar := uBar)
        (uMuBar := uMuBar)
        (uHat := uHat)
        (uPlus := uHat)
        hτ_lt
        hdisp)
  nlinarith [hcore]

/-- Helper for Theorem 6.2.3: the actual new oracle dominates the old oracle when both are
tested in the selector slice based at the predicted dual point `\hat u`. -/
theorem scaledOldOracleSelectorSlice_le_scaledNewOracleSelectorSlice
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    τ *
        (problem.smoothPart (x₀ uHat) +
          problem.linearMap (x₀ uHat) (uMuBar : E₂) -
          problem.dualPenalty uMuBar) ≤
      τ *
        (problem.smoothPart (x₀ uHat) +
          problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  have holdMax :
      problem.linearMap xBar (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle ≤
        problem.linearMap xBar (uMuBar : E₂) -
          problem.dualPenalty uMuBar -
          (μ₂ : ℝ) * problem.dualProxFunction uMuBar := by
    -- The old oracle still maximizes the old smoothed primal slice at `xBar`.
    simpa [uMuBar, uPlusOracle, smoothedPrimalObjectiveMaximand] using
      (problem.dualOracleSolver_isMaxOn xBar μ₂) uPlusOracle.property
  have hnewMax :
      problem.linearMap xBarPlus (uMuBar : E₂) -
          problem.dualPenalty uMuBar -
          (μ₂Plus : ℝ) * problem.dualProxFunction uMuBar ≤
        problem.linearMap xBarPlus (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (μ₂Plus : ℝ) * problem.dualProxFunction uPlusOracle := by
    -- The new oracle maximizes the updated smoothed primal slice at `xBarPlus`.
    simpa [uMuBar, uPlusOracle, smoothedPrimalObjectiveMaximand] using
      (problem.dualOracleSolver_isMaxOn xBarPlus μ₂Plus) uMuBar.property
  have hxBarPlus_val :
      (xBarPlus : E₁) = (1 - τ) • (xBar : E₁) + τ • (x₀ uHat : E₁) := by
    simp [xBarPlus, uHat, hτIcc, updatedPrimalPoint_val]
  have hlin_uMu :
      problem.linearMap xBarPlus (uMuBar : E₂) =
        (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
          τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) := by
    rw [hxBarPlus_val]
    simp
  have hlin_uPlus :
      problem.linearMap xBarPlus (uPlusOracle : E₂) =
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) := by
    rw [hxBarPlus_val]
    simp
  have hsplit :
      (1 - τ) *
          (problem.linearMap xBar (uMuBar : E₂) -
            problem.dualPenalty uMuBar -
            (μ₂ : ℝ) * problem.dualProxFunction uMuBar) +
        τ * (problem.linearMap (x₀ uHat) (uMuBar : E₂) - problem.dualPenalty uMuBar) ≤
      (1 - τ) *
          (problem.linearMap xBar (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle -
            (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle) +
        τ * (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) - problem.dualPenalty uPlusOracle) := by
    -- Expand the new maximizer comparison using `xBarPlus = (1 - τ) xBar + τ x₀(uHat)`.
    have hnewExpanded :
        (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
            τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) -
            problem.dualPenalty uMuBar -
            (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uMuBar ≤
          (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
            τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle -
            (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle := by
      simpa [μ₂Plus, reducedDualSmoothing_def, hlin_uMu, hlin_uPlus] using hnewMax
    nlinarith
  have hslices :
      τ * (problem.linearMap (x₀ uHat) (uMuBar : E₂) - problem.dualPenalty uMuBar) ≤
        τ * (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) - problem.dualPenalty uPlusOracle) := by
    -- Cancel the shared `(1 - τ)`-weighted old-slice terms using the old oracle maximality.
    nlinarith [hsplit, holdMax]
  -- Add the common smooth-part constant to both sides of the scaled comparison.
  nlinarith

/-- Helper for Theorem 6.2.3: before canceling the old positive-smoothed support term, the new
oracle optimality comparison has the explicit `(1 - τ)`/`τ` split form coupling the old slice at
`xBar` with the selector slice based at `\hat u`. -/
theorem newOracleSplitSupportComparison
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
        τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) -
        problem.dualPenalty uMuBar -
        (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uMuBar ≤
      (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
        τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
        problem.dualPenalty uPlusOracle -
        (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  have hnewMax :
      problem.linearMap xBarPlus (uMuBar : E₂) -
          problem.dualPenalty uMuBar -
          (μ₂Plus : ℝ) * problem.dualProxFunction uMuBar ≤
        problem.linearMap xBarPlus (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (μ₂Plus : ℝ) * problem.dualProxFunction uPlusOracle := by
    -- The actual new oracle maximizes the updated positive-smoothed slice at `xBarPlus`.
    simpa [uMuBar, uPlusOracle, smoothedPrimalObjectiveMaximand] using
      (problem.dualOracleSolver_isMaxOn xBarPlus μ₂Plus) uMuBar.property
  have hxBarPlus_val :
      (xBarPlus : E₁) = (1 - τ) • (xBar : E₁) + τ • (x₀ uHat : E₁) := by
    -- Expand the updated primal point into its defining convex combination.
    simp [xBarPlus, uHat, updatedPrimalPoint_val]
  have hlin_uMu :
      problem.linearMap xBarPlus (uMuBar : E₂) =
        (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
          τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) := by
    -- Split the linear term at the old oracle through the updated primal point.
    rw [hxBarPlus_val]
    simp
  have hlin_uPlus :
      problem.linearMap xBarPlus (uPlusOracle : E₂) =
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) := by
    -- The same splitting holds for the actual new oracle.
    rw [hxBarPlus_val]
    simp
  -- Rewriting the new-oracle maximizer comparison exposes the explicit split support inequality.
  simpa [μ₂Plus, reducedDualSmoothing_def, hlin_uMu, hlin_uPlus] using hnewMax

/-- Helper for Theorem 6.2.3: rewriting the new-oracle split support comparison in the
`oldSupport`/`selectorSlice` owners keeps the uncanceled old-support term available for the later
quadratic-gap step. -/
theorem selectorSlice_oldSupport_rearranged
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun v ↦
      problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
    let selectorSlice : E₂ → ℝ := fun v ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
    τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
      (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun v ↦
    problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
  let selectorSlice : E₂ → ℝ := fun v ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
  have hraw :
      (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
          τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) -
          problem.dualPenalty uMuBar -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uMuBar ≤
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle := by
    exact newOracleSplitSupportComparison problem x₀ hτ hτ_lt
  -- Rearranging the split-support inequality isolates the selector difference against the
  -- uncanceled old-support difference.
  nlinarith [hraw]

/-- Helper for Theorem 6.2.3: the selected zero-smoothed slice at the predicted point `\hat u`
is controlled by the affine linearization of the dual objective at `\hat u`. -/
theorem selectedAffineModel_le_explicitDualLinearization
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {u v : problem.dualSet}
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u)) :
    problem.smoothPart (x₀ u) +
        problem.linearMap (x₀ u) (v : E₂) -
        problem.dualPenalty v ≤
      extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u +
        inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
          ((v : E₂) - (u : E₂)) := by
  have hpenalty :
      problem.dualPenalty (u : E₂) +
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
            ((v : E₂) - (u : E₂)) ≤
        problem.dualPenalty v := by
    -- Convexity of the dual penalty gives the supporting nesterovHyperplane inequality at the base point.
    exact
      problem.dualPenalty_convex.lower_tangent_plane_of_hasGradientWithinAt
        (u : E₂)
        u.property
        (gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
        (problem.dualPenalty_hasGradientWithinAt u.property)
        (v : E₂)
        v.property
  have hlinear :
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)))
          ((v : E₂) - (u : E₂)) =
        problem.linearMap (x₀ u) (v : E₂) - problem.linearMap (x₀ u) (u : E₂) := by
    -- The Riesz-vector form of `A (x₀ u)` evaluates to the expected affine increment.
    rw [InnerProductSpace.toDual_symm_apply]
    simp [map_sub]
  -- Expand the selected zero-smoothed dual value at `u`, then reduce the claim to the dual
  -- penalty tangent inequality.
  rw [zeroSmoothedDualObjective_value_at_selector problem x₀ hx₀ u]
  rw [inner_sub_left, hlinear]
  nlinarith

/-- Helper for Theorem 6.2.3: transporting the old excessive-gap certificate from `\bar u` to
the predicted base point `\hat u` costs one smooth quadratic remainder. -/
theorem weightedOldCertificate_le_predictedBaseWithQuadraticRemainder
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet)
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    (1 - τ) *
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
      (1 - τ) * φ uHat +
        (1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
        (1 - τ) * ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  have hgap_old :
      smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
        φ uBar := by
    -- Unfold the old excessive-gap certificate before transporting it to `\hat u`.
    exact
      (satisfiesExcessiveGapConditionWithMu1Zero_iff
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦ φ u)
        xBar
        uBar).mp hgap
  have hupper :
      φ uBar ≤
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- The zero-smoothed dual objective satisfies the standard smooth upper model on `Q₂`.
    exact
      upper_model_of_hasGradientWithinAt_lipschitzOn
        hphi_hasGradientWithinAt
        hphi_lipschitz
        problem.dualSet_convex
        uHat.property
        uBar.property
  have htransport :
      smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- First use the old certificate at `\bar u`, then transport from `\bar u` to `\hat u`.
    exact hgap_old.trans hupper
  have hscaled :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
        (1 - τ) *
          (φ uHat +
            inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
            ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left htransport (sub_nonneg.mpr hτ_lt.le)
  -- Weight the transported certificate by `1 - τ`, which is nonnegative because `τ < 1`.
  calc
    (1 - τ) *
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
      (1 - τ) *
        (φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := hscaled
    _ =
        (1 - τ) * φ uHat +
          (1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          (1 - τ) * ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
        ring

/-- Helper for Theorem 6.2.3: the selected zero-smoothed slice at the predicted point `\hat u`
uses the Chapter 6 identification of the zero-smoothed dual gradient with the selected
slope attached to `x₀`. -/
theorem zeroSmoothedDualGradientPairing_eq_selectedSlope
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {u v : problem.dualSet}
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂)) :
    inner ℝ
        ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
          gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
        ((v : E₂) - (u : E₂)) =
      inner ℝ
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (u : E₂))
        ((v : E₂) - (u : E₂)) := by
  -- Rewrite the selected-slope vector to the actual dual gradient at the base point `u`.
  rw [← hgradient_eq_selectedSlope u]

/-- Helper for Theorem 6.2.3: the old dual oracle minimizes the old positive slice strongly
enough to give a quadratic gap at the predicted point `\hat u`. -/
theorem oldDualOracleSlice_quadraticGapAtPredictedPoint
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let oldSlice : E₂ → ℝ := fun u : E₂ ↦
      problem.dualPenalty u + (μ₂ : ℝ) * problem.dualProxFunction u - problem.linearMap xBar u
    oldSlice (uHat : E₂) ≥
      oldSlice (uMuBar : E₂) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let oldSlice : E₂ → ℝ := fun u : E₂ ↦
    problem.dualPenalty u + (μ₂ : ℝ) * problem.dualProxFunction u - problem.linearMap xBar u
  have huMu_mem : (uMuBar : E₂) ∈ problem.dualSet := uMuBar.property
  have huMu_min : IsMinOn oldSlice problem.dualSet (uMuBar : E₂) := by
    refine isMinOn_iff.mpr ?_
    intro v hv
    have hmax :
        smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar v ≤
          smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar (uMuBar : E₂) := by
      exact (isMaxOn_iff.mp (problem.dualOracleSolver_isMaxOn xBar μ₂)) v hv
    have hu_neg :
        oldSlice (uMuBar : E₂) =
          -smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar (uMuBar : E₂) := by
      simp [oldSlice, smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
      ring
    have hv_neg :
        oldSlice v =
          -smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar v := by
      simp [oldSlice, smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
      ring
    rw [hu_neg, hv_neg]
    exact neg_le_neg hmax
  have hold_strong :
      StrongConvexOn problem.dualSet (μ₂ : ℝ) oldSlice := by
    -- Rewrite the Chapter 6 slice strong-convexity owner to the old slice used in the update.
    simpa [oldSlice] using
      (smoothedObjective_slice_strongConvexOn
        problem.linearMap
        problem.dualSet
        problem.dualPenalty
        problem.dualProxFunction
        problem.dualPenalty_convex
        hdualProx
        μ₂.property
        (xBar : E₁))
  -- Apply quadratic growth at the predicted point while keeping the old oracle as the slice
  -- minimizer.
  have hquad :
      oldSlice (uHat : E₂) ≥
        oldSlice (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uHat : E₂) - (uMuBar : E₂)‖ ^ (2 : ℕ) := by
    exact hold_strong.quadratic_growth_of_isMinOn_of_mem
      huMu_mem
      huMu_min
      (uHat : E₂)
      uHat.property
  have huHat_val :
      (uHat : E₂) = (1 - τ) • (uBar : E₂) + τ • (uMuBar : E₂) := by
    simp [uHat, uMuBar, hτIcc, predictedDualPoint_val]
  simpa [huHat_val, oldSlice, map_add, map_smul, norm_sub_rev] using hquad

/-- Helper for Theorem 6.2.3: rewriting the old quadratic-gap lemma in the `oldSupport` owner
puts the strong-convexity gain on the same side as the split-support comparison. -/
theorem oldSupportAtPredictedPoint_le_oldOracleSupport_sub_quadratic
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let oldSupport : E₂ → ℝ := fun v ↦
      problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
    oldSupport (uHat : E₂) ≤
      oldSupport (uMuBar : E₂) -
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let oldSupport : E₂ → ℝ := fun v ↦
    problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
  have hraw :
      (fun u : E₂ ↦
          problem.dualPenalty u + (μ₂ : ℝ) * problem.dualProxFunction u - problem.linearMap xBar u)
          (uHat : E₂) ≥
        (fun u : E₂ ↦
            problem.dualPenalty u + (μ₂ : ℝ) * problem.dualProxFunction u - problem.linearMap xBar u)
            (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    exact oldDualOracleSlice_quadraticGapAtPredictedPoint problem hdualProx hτ hτ_lt
  -- Negating the old slice converts the quadratic growth statement into the `oldSupport`
  -- inequality used by the final owner-level comparison.
  nlinarith [hraw]

/-- Helper for Theorem 6.2.3: the old dual oracle dominates every feasible competitor in the
`oldSupport` owner, with the strong-convexity gain written directly at that competitor. -/
theorem oldSupportAtCompetitor_le_oldOracleSupport
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}}
    (v : problem.dualSet) :
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    oldSupport (v : E₂) ≤ oldSupport (uMuBar : E₂) := by
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  have hmax :
      smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
          problem.dualProxFunction (μ₂ : ℝ) xBar (v : E₂) ≤
        smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
          problem.dualProxFunction (μ₂ : ℝ) xBar (uMuBar : E₂) := by
    -- The Chapter 6 old dual oracle maximizes the old smoothed primal slice at `xBar`.
    exact (isMaxOn_iff.mp (problem.dualOracleSolver_isMaxOn xBar μ₂)) (v : E₂) v.property
  -- Rewriting the maximizer comparison in the `oldSupport` owner gives the desired inequality.
  simpa [oldSupport, smoothedPrimalObjectiveMaximand, sub_eq_add_neg] using hmax

/-- Helper for Theorem 6.2.3: the old dual oracle dominates every feasible competitor in the
`oldSupport` owner, with the strong-convexity gain written directly at that competitor. -/
theorem oldSupportAtCompetitor_le_oldOracleSupport_sub_quadratic
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}}
    (v : problem.dualSet) :
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    oldSupport (v : E₂) ≤
      oldSupport (uMuBar : E₂) -
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ) := by
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let oldSlice : E₂ → ℝ := fun w ↦
    problem.dualPenalty w + (μ₂ : ℝ) * problem.dualProxFunction w - problem.linearMap xBar w
  have huMu_mem : (uMuBar : E₂) ∈ problem.dualSet := uMuBar.property
  have huMu_min : IsMinOn oldSlice problem.dualSet (uMuBar : E₂) := by
    refine isMinOn_iff.mpr ?_
    intro w hw
    have hmax :
        smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar w ≤
          smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar (uMuBar : E₂) := by
      exact (isMaxOn_iff.mp (problem.dualOracleSolver_isMaxOn xBar μ₂)) w hw
    have hu_neg :
        oldSlice (uMuBar : E₂) =
          -smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar (uMuBar : E₂) := by
      simp [oldSlice, smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
      ring
    have hw_neg :
        oldSlice w =
          -smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
            problem.dualProxFunction (μ₂ : ℝ) xBar w := by
      simp [oldSlice, smoothedPrimalObjectiveMaximand, sub_eq_add_neg]
      ring
    rw [hu_neg, hw_neg]
    exact neg_le_neg hmax
  have hold_strong :
      StrongConvexOn problem.dualSet (μ₂ : ℝ) oldSlice := by
    -- Rewrite the Chapter 6 slice strong-convexity owner to the old slice used by the update.
    simpa [oldSlice] using
      (smoothedObjective_slice_strongConvexOn
        problem.linearMap
        problem.dualSet
        problem.dualPenalty
        problem.dualProxFunction
        problem.dualPenalty_convex
        hdualProx
        μ₂.property
        (xBar : E₁))
  have hquad :
      oldSlice (v : E₂) ≥
        oldSlice (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(v : E₂) - (uMuBar : E₂)‖ ^ (2 : ℕ) := by
    -- Compare the old oracle with the arbitrary feasible competitor `v`.
    exact hold_strong.quadratic_growth_of_isMinOn_of_mem
      huMu_mem
      huMu_min
      (v : E₂)
      v.property
  have hquad' :
      -(oldSupport (v : E₂)) ≥
        -(oldSupport (uMuBar : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(v : E₂) - (uMuBar : E₂)‖ ^ (2 : ℕ) := by
    -- Rewrite the old-slice inequality into the negated `oldSupport` normal form first.
    simpa [oldSlice, oldSupport, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hquad
  have hquad'' :
      -(oldSupport (v : E₂)) ≥
        -(oldSupport (uMuBar : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ) := by
    -- Normalize the distance so the support statement uses the oracle-minus-competitor order.
    simpa [norm_sub_rev] using hquad'
  -- Negating the old slice again converts the quadratic growth statement into the support owner.
  nlinarith [hquad'']

/-- Helper for Theorem 6.2.3: the old-support quadratic residual is nonpositive for every feasible
competitor. -/
theorem oldSupportResidual_nonpos
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}}
    (v : problem.dualSet) :
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    oldSupport (v : E₂) - oldSupport (uMuBar : E₂) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ) ≤
      0 := by
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  have hcompetitor :
      oldSupport (v : E₂) ≤
        oldSupport (uMuBar : E₂) -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ) := by
    -- Package the old-oracle gap in the residual sign used by the closing bridge.
    exact oldSupportAtCompetitor_le_oldOracleSupport_sub_quadratic problem hdualProx v
  nlinarith [hcompetitor]

/-- Helper for Theorem 6.2.3: multiplying the old-support residual by `1 - τ` preserves its
nonpositive sign. This isolates the weighted old-support owner used by the repaired middle
bridge. -/
theorem scaledOldSupportResidual_nonpos
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ_lt : τ < 1)
    (v : problem.dualSet) :
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    (1 - τ) *
        (oldSupport (v : E₂) - oldSupport (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ)) ≤
      0 := by
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  have holdResidual :
      oldSupport (v : E₂) - oldSupport (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (v : E₂)‖ ^ (2 : ℕ) ≤
        0 := by
    -- Reuse the unweighted old-support residual before scaling it by `1 - τ`.
    simpa [uMuBar, oldSupport] using
      (oldSupportResidual_nonpos problem hdualProx (xBar := xBar) (μ₂ := μ₂) v)
  -- The weighted old-support residual keeps the same sign because `1 - τ ≥ 0`.
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτ_lt.le) holdResidual

/-- Helper for Theorem 6.2.3: the selected zero-smoothed slice at the predicted point `\hat u`
is controlled by the affine linearization of the dual objective at `\hat u`. -/
theorem selectorSliceAtPredictedPoint_le_selectedAffineModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {u v : problem.dualSet}
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂)) :
    problem.smoothPart (x₀ u) +
        problem.linearMap (x₀ u) (v : E₂) -
        problem.dualPenalty v ≤
      extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u +
        inner ℝ
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂))
          ((v : E₂) - (u : E₂)) := by
  have hexplicit :
      problem.smoothPart (x₀ u) +
          problem.linearMap (x₀ u) (v : E₂) -
          problem.dualPenalty v ≤
        extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u +
          inner ℝ
            ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
              gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
            ((v : E₂) - (u : E₂)) := by
    exact selectedAffineModel_le_explicitDualLinearization problem x₀ hx₀
  -- Once the chord pairing is identified, the explicit selected-slope model rewrites to the
  -- target affine model using `gradient φ u`.
  exact hexplicit.trans_eq (by
    rw [zeroSmoothedDualGradientPairing_eq_selectedSlope
      problem
      x₀
      hx₀
      hgradient_eq_selectedSlope])

/-- Helper for Theorem 6.2.3: evaluating the selector slice at the predicted point `\hat u`
recovers the zero-smoothed dual value `φ(\hat u)`. -/
theorem selectorSliceAtPredictedPoint_eq_zeroSmoothedDualValue
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let selectorSlice : E₂ → ℝ := fun v ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
    selectorSlice (uHat : E₂) = φ uHat := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let selectorSlice : E₂ → ℝ := fun v ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
  -- Evaluate the zero-smoothed dual owner at the selected primal point attached to `\hat u`.
  dsimp [selectorSlice]
  change
    problem.smoothPart (x₀ uHat) +
        problem.linearMap (x₀ uHat) (uHat : E₂) - problem.dualPenalty uHat =
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) uHat
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (zeroSmoothedDualObjective_value_at_selector problem x₀ hx₀ uHat).symm

/-- Helper for Theorem 6.2.3: the selector slice equals the zero-smoothed dual value plus the
gradient pairing, minus the dual-penalty tangent residual. -/
theorem selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {u v : problem.dualSet}
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂)) :
    let φ : E₂ → ℝ := fun w : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ u) + problem.linearMap (x₀ u) w - problem.dualPenalty w
    selectorSlice (v : E₂) =
      φ u +
        inner ℝ (gradient φ (u : E₂)) ((v : E₂) - (u : E₂)) -
        (problem.dualPenalty v - problem.dualPenalty u -
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
            ((v : E₂) - (u : E₂))) := by
  let φ : E₂ → ℝ := fun w : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ u) + problem.linearMap (x₀ u) w - problem.dualPenalty w
  have hvalue :
      φ u =
        problem.smoothPart (x₀ u) +
          problem.linearMap (x₀ u) (u : E₂) -
          problem.dualPenalty u := by
    -- Evaluate the zero-smoothed dual owner exactly at the selected minimizer attached to `u`.
    have hvalue' :
        problem.smoothPart (x₀ u) +
            problem.linearMap (x₀ u) (u : E₂) -
            problem.dualPenalty u =
          φ u := by
      simpa [φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (zeroSmoothedDualObjective_value_at_selector problem x₀ hx₀ u).symm
    exact hvalue'.symm
  have hpair :
      inner ℝ (gradient φ (u : E₂)) ((v : E₂) - (u : E₂)) =
        problem.linearMap (x₀ u) (v : E₂) -
          problem.linearMap (x₀ u) (u : E₂) -
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
            ((v : E₂) - (u : E₂)) := by
    -- Rewrite the Chapter 6 selected slope into the actual dual gradient pairing.
    rw [hgradient_eq_selectedSlope u, inner_sub_left, InnerProductSpace.toDual_symm_apply]
    simp [map_sub]
  -- Expanding the selected value and the gradient pairing isolates the tangent residual.
  calc
    selectorSlice (v : E₂) =
        problem.smoothPart (x₀ u) +
          problem.linearMap (x₀ u) (v : E₂) -
          problem.dualPenalty v := by
            rfl
    _ =
        φ u +
          inner ℝ (gradient φ (u : E₂)) ((v : E₂) - (u : E₂)) -
          (problem.dualPenalty v - problem.dualPenalty u -
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
              ((v : E₂) - (u : E₂))) := by
            rw [hvalue, hpair]
            ring

/-- Helper for Theorem 6.2.3: comparing the actual new oracle against the predicted base point
`\hat u` keeps the new-oracle optimality statement in the same `uHat`-centered support language
used by the selector interface. -/
theorem newOracleSupportComparisonAtPredictedPoint
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun v ↦
      problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
    let selectorSlice : E₂ → ℝ := fun v ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
    (1 - τ) * oldSupport (uHat : E₂) + τ * selectorSlice (uHat : E₂) ≤
      (1 - τ) * oldSupport (uPlusOracle : E₂) + τ * selectorSlice (uPlusOracle : E₂) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun v ↦
    problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
  let selectorSlice : E₂ → ℝ := fun v ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
  have hnewMax :
      problem.linearMap xBarPlus (uHat : E₂) -
          problem.dualPenalty uHat -
          (μ₂Plus : ℝ) * problem.dualProxFunction uHat ≤
        problem.linearMap xBarPlus (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (μ₂Plus : ℝ) * problem.dualProxFunction uPlusOracle := by
    -- The actual new oracle maximizes the updated positive-smoothed slice at `xBarPlus`.
    simpa [uPlusOracle, smoothedPrimalObjectiveMaximand] using
      (problem.dualOracleSolver_isMaxOn xBarPlus μ₂Plus) uHat.property
  have hxBarPlus_val :
      (xBarPlus : E₁) = (1 - τ) • (xBar : E₁) + τ • (x₀ uHat : E₁) := by
    -- Expand the updated primal point into its defining convex combination.
    simp [xBarPlus, uHat, updatedPrimalPoint_val]
  have hlin_uHat :
      problem.linearMap xBarPlus (uHat : E₂) =
        (1 - τ) * problem.linearMap xBar (uHat : E₂) +
          τ * problem.linearMap (x₀ uHat) (uHat : E₂) := by
    -- Split the new-slice linear term at the predicted point `\hat u`.
    rw [hxBarPlus_val]
    simp
  have hlin_uPlus :
      problem.linearMap xBarPlus (uPlusOracle : E₂) =
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) := by
    -- The same linear splitting holds for the actual new oracle.
    rw [hxBarPlus_val]
    simp
  have hraw :
      (1 - τ) * problem.linearMap xBar (uHat : E₂) +
          τ * problem.linearMap (x₀ uHat) (uHat : E₂) -
          problem.dualPenalty uHat -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uHat ≤
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle := by
    -- Rewriting the maximizer inequality exposes the desired split-support normal form.
    simpa [μ₂Plus, reducedDualSmoothing_def, hlin_uHat, hlin_uPlus] using hnewMax
  -- Add the common `τ * smoothPart (x₀ uHat)` term so the split-support comparison matches the
  -- `selectorSlice` owner exactly.
  nlinarith [hraw]

/-- Helper for Theorem 6.2.3: rewriting the mixed `uHat`/`uPlusOracle` support comparison at the
predicted point replaces the predicted selector slice by the zero-smoothed dual value `φ uHat`. -/
theorem newOracleSupportComparisonAtPredictedPoint_explicit
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun v ↦
      problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
    let selectorSlice : E₂ → ℝ := fun v ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
    (1 - τ) * oldSupport (uHat : E₂) + τ * φ uHat ≤
      (1 - τ) * oldSupport (uPlusOracle : E₂) + τ * selectorSlice (uPlusOracle : E₂) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun v ↦
    problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
  let selectorSlice : E₂ → ℝ := fun v ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
  have hselectorAtPredicted :
      selectorSlice (uHat : E₂) = φ uHat := by
    -- Rewrite the predicted-point selector slice to the actual zero-smoothed dual value.
    simpa [φ, hτIcc, uHat, selectorSlice] using
      (selectorSliceAtPredictedPoint_eq_zeroSmoothedDualValue
        problem
        x₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hx₀
        hτ
        hτ_lt)
  have hraw :
      (1 - τ) * oldSupport (uHat : E₂) + τ * selectorSlice (uHat : E₂) ≤
        (1 - τ) * oldSupport (uPlusOracle : E₂) + τ * selectorSlice (uPlusOracle : E₂) := by
    -- Keep the support comparison in the stable `oldSupport`/`selectorSlice` owner first.
    simpa [hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle, oldSupport, selectorSlice] using
      (newOracleSupportComparisonAtPredictedPoint
        problem
        x₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hτ
        hτ_lt)
  -- Replace the predicted selector slice by `φ uHat` and keep the actual new-oracle slice fixed.
  have hraw' := hraw
  rw [hselectorAtPredicted] at hraw'
  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle, oldSupport, selectorSlice] using hraw'

/-- Helper for Theorem 6.2.3: the split-support comparison keeps the old-oracle curvature when the
old-support term is specialized at the actual new oracle. -/
theorem selectorSlice_oldOracleResidual_le_curvedNewOracleResidual
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun v ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
    τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
      -(1 - τ) * ((μ₂ : ℝ) / 2) * ‖(uPlusOracle : E₂) - (uMuBar : E₂)‖ ^ (2 : ℕ) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun v ↦
    problem.linearMap xBar v - problem.dualPenalty v - (μ₂ : ℝ) * problem.dualProxFunction v
  let selectorSlice : E₂ → ℝ := fun v ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) v - problem.dualPenalty v
  have hsplit :
      τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
        (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) := by
    -- Keep the old-support term uncanceled so the competitor quadratic gap can still be inserted.
    exact selectorSlice_oldSupport_rearranged problem x₀ hτ hτ_lt
  have holdQuadPlus :
      oldSupport (uPlusOracle : E₂) ≤
        oldSupport (uMuBar : E₂) -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ) := by
    -- Specialize the old-slice quadratic gap at the actual new oracle.
    exact
      oldSupportAtCompetitor_le_oldOracleSupport_sub_quadratic
        problem
        hdualProx
        (xBar := xBar)
        (μ₂ := μ₂)
        uPlusOracle
  have holdQuadPlus' :
      oldSupport (uPlusOracle : E₂) ≤
        oldSupport (uMuBar : E₂) -
          ((μ₂ : ℝ) / 2) * ‖(uPlusOracle : E₂) - (uMuBar : E₂)‖ ^ (2 : ℕ) := by
    -- Normalize the norm term so the final inequality matches the theorem statement verbatim.
    simpa [norm_sub_rev] using holdQuadPlus
  -- Multiply the old-slice competitor gap by `1 - τ` and combine it with the split-support
  -- comparison.
  nlinarith [hsplit, holdQuadPlus']

/-- Helper for Theorem 6.2.3: the weighted old certificate and a selector slice at an arbitrary
competitor reduce to the predicted dual model, up to the explicit old-support residual. -/
theorem weightedGapAndSelectorSlice_le_explicitResidualCore
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet)
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ))
    (v : problem.dualSet) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) *
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
      τ * selectorSlice (v : E₂) ≤
      φ uHat +
        τ * (problem.linearMap (x₀ uHat) (v : E₂) - problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
        τ *
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂)) +
        τ * (problem.dualPenalty uHat - problem.dualPenalty v) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hweightedOld :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
        (1 - τ) * φ uHat +
          (1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          (1 - τ) * ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Transport the old certificate from `\bar u` to the predicted point `\hat u`.
    exact
      weightedOldCertificate_le_predictedBaseWithQuadraticRemainder
        problem
        Lphi
        hgap
        hphi_hasGradientWithinAt
        hphi_lipschitz
        hτ
        hτ_lt
  have hdisp :
      (uBar : E₂) - (uHat : E₂) =
        -(τ / (1 - τ)) • ((uMuBar : E₂) - (uHat : E₂)) := by
    -- Rewrite the old displacement through the old oracle at `xBar`.
    exact predictedDualPoint_oldDual_displacement problem hτ hτ_lt
  have hquadAbsorb :
      (1 - τ) * ((Lphi : ℝ) / 2) * ‖(uBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- The step-size bound absorbs the old quadratic remainder.
    exact
      stepSizeAbsorbsPredictedDualQuadraticError
        hτ
        hτ_lt
        hdisp
        hstep
        μ₂.property
  have hgradCore :
      (1 - τ) *
            inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          τ * inner ℝ (gradient φ (uHat : E₂)) ((v : E₂) - (uHat : E₂)) =
        τ * inner ℝ (gradient φ (uHat : E₂)) ((v : E₂) - (uHat : E₂)) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) := by
    -- Collapse the weighted first-order terms to the normalized oracle-gap core.
    exact weightedGradientTerms_eq_normalizedOracleGapCore hτ_lt hdisp
  have hselectorEq :
      selectorSlice (v : E₂) =
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((v : E₂) - (uHat : E₂)) -
          (problem.dualPenalty v - problem.dualPenalty uHat -
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((v : E₂) - (uHat : E₂))) := by
    -- Rewrite the selector slice exactly as the zero-smoothed value plus the tangent residual.
    exact
      selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
  have hweightedOldAbsorbed :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar ≤
        (1 - τ) * φ uHat +
          (1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Absorb the transported smooth quadratic remainder into the old-oracle distance term.
    nlinarith [hweightedOld, hquadAbsorb]
  have hbase :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
        τ * selectorSlice (v : E₂) ≤
      φ uHat +
        ((1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
          τ * inner ℝ (gradient φ (uHat : E₂)) ((v : E₂) - (uHat : E₂))) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) -
        τ *
          (problem.dualPenalty v - problem.dualPenalty uHat -
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((v : E₂) - (uHat : E₂))) := by
    -- Add the exact selector formula to the absorbed old certificate before any owner changes.
    calc
      (1 - τ) *
            smoothedPrimalObjective problem.linearMap problem.dualSet
              problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
          τ * selectorSlice (v : E₂) ≤
          (1 - τ) * φ uHat +
            (1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) +
              τ * selectorSlice (v : E₂) := by
            nlinarith [hweightedOldAbsorbed]
      _ =
          φ uHat +
            ((1 - τ) * inner ℝ (gradient φ (uHat : E₂)) ((uBar : E₂) - (uHat : E₂)) +
              τ * inner ℝ (gradient φ (uHat : E₂)) ((v : E₂) - (uHat : E₂))) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) -
            τ *
              (problem.dualPenalty v - problem.dualPenalty uHat -
                inner ℝ
                  (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
                  ((v : E₂) - (uHat : E₂))) := by
            rw [hselectorEq]
            ring
  have hlin_v :
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ uHat)))
          ((v : E₂) - (uHat : E₂)) =
        problem.linearMap (x₀ uHat) (v : E₂) -
          problem.linearMap (x₀ uHat) (uHat : E₂) := by
    -- Convert the Riesz-represented linear form into the concrete affine increment at `v`.
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ uHat)))
          ((v : E₂) - (uHat : E₂)) =
        problem.linearMap (x₀ uHat) ((v : E₂) - (uHat : E₂)) := by
          rw [InnerProductSpace.toDual_symm_apply]
      _ =
        problem.linearMap (x₀ uHat) (v : E₂) -
          problem.linearMap (x₀ uHat) (uHat : E₂) := by
          rw [map_sub]
  have hlin_uMuBar :
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ uHat)))
          ((uMuBar : E₂) - (uHat : E₂)) =
        problem.linearMap (x₀ uHat) (uMuBar : E₂) -
          problem.linearMap (x₀ uHat) (uHat : E₂) := by
    -- The same linearization rewrite holds at the old oracle point.
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ uHat)))
          ((uMuBar : E₂) - (uHat : E₂)) =
        problem.linearMap (x₀ uHat) ((uMuBar : E₂) - (uHat : E₂)) := by
          rw [InnerProductSpace.toDual_symm_apply]
      _ =
        problem.linearMap (x₀ uHat) (uMuBar : E₂) -
          problem.linearMap (x₀ uHat) (uHat : E₂) := by
          rw [map_sub]
  have hbase' := hbase
  -- Rewrite the normalized scalar core entirely in the concrete Chapter 6 owners.
  rw [hgradCore, hgradient_eq_selectedSlope uHat] at hbase'
  rw [inner_sub_left, inner_sub_left] at hbase'
  rw [hlin_v, hlin_uMuBar] at hbase'
  nlinarith [hbase']

/-- Helper for Theorem 6.2.3: the predicted dual model plus the explicit old-support residual
expands to a concrete scalar expression in the `adjointGradientMaximand` and `oldSupport`
owners. -/
theorem predictedDualModelWithResidual_eq_explicit
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (uHat uMuBar v : E₂) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) uHat v +
        (1 - τ) *
          (oldSupport v - oldSupport uMuBar +
            ((μ₂ : ℝ) / 2) * ‖uMuBar - v‖ ^ (2 : ℕ)) =
      φ uHat +
        (inner ℝ (gradient φ uHat) (v - uHat) - ((Lphi : ℝ) / 2) * ‖v - uHat‖ ^ (2 : ℕ)) +
        (1 - τ) *
          (problem.linearMap xBar v - problem.dualPenalty v -
            (μ₂ : ℝ) * problem.dualProxFunction v -
            (problem.linearMap xBar uMuBar - problem.dualPenalty uMuBar -
              (μ₂ : ℝ) * problem.dualProxFunction uMuBar) +
            ((μ₂ : ℝ) / 2) * ‖uMuBar - v‖ ^ (2 : ℕ)) := by
  -- Unfold the two owners once so later proofs can work in one stable scalar normal form.
  simp [adjointGradientMaximand]

/-- Helper for Theorem 6.2.3: at the actual new oracle, the explicit scalar core from the
weighted-gap estimate rewrites exactly into the selector-based normal form centered at `\hat u`. -/
theorem newOracleExplicitCore_eq_selectorBridgeForm
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    φ uHat +
        τ *
          (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
        τ *
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂)) +
        τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
      (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hselectorEq :
      selectorSlice (uPlusOracle : E₂) =
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
          (problem.dualPenalty uPlusOracle - problem.dualPenalty uHat -
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uPlusOracle : E₂) - (uHat : E₂))) := by
    -- Rewrite the selector slice once so the new-oracle core is compared in a single owner.
    exact
      selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
  have hmain :
      φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
        (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Route correction: normalize the explicit core directly to the selector owner before any
    -- residual-model comparison.
    rw [hselectorEq, hgradient_eq_selectedSlope uHat]
    rw [inner_sub_left, inner_sub_left]
    rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
    simp [selectorSlice, map_sub]
    ring
  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, selectorSlice] using hmain

/-- Helper for Theorem 6.2.3: the dual-penalty tangent residual at the old oracle is nonnegative
when based at the predicted point `\hat u`. -/
theorem predictedPointPenaltyResidual_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (v : problem.dualSet) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    0 ≤
      problem.dualPenalty v - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((v : E₂) - (uHat : E₂)) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  have hpenalty :
      problem.dualPenalty uHat +
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((v : E₂) - (uHat : E₂)) ≤
        problem.dualPenalty v := by
    -- Convexity of the dual penalty gives the tangent underestimator at the predicted point for
    -- every feasible competitor.
    exact
      problem.dualPenalty_convex.lower_tangent_plane_of_hasGradientWithinAt
        (uHat : E₂)
        uHat.property
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        (problem.dualPenalty_hasGradientWithinAt uHat.property)
        (v : E₂)
        v.property
  -- Rearranging the tangent inequality isolates the nonnegative residual.
  nlinarith [hpenalty]

/-- Helper for Theorem 6.2.3: the dual-penalty tangent residual at the old oracle is nonnegative
when based at the predicted point `\hat u`. -/
theorem predictedPointOldOraclePenaltyResidual_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let uMuBar := problem.dualOracleSolver xBar μ₂
    0 ≤
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂)) := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let uMuBar := problem.dualOracleSolver xBar μ₂
  -- Specialize the generic feasible-competitor residual bound to the old oracle.
  simpa [uMuBar] using
    (predictedPointPenaltyResidual_nonneg
      problem
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hτ
      hτ_lt
      uMuBar)

/-- Helper for Theorem 6.2.3: rewriting the new-oracle split-support comparison through the
old-oracle selector identity exposes the residualized support inequality that remains before the
quadratic-model closure. -/
theorem newOracleResidualizedSupportComparison_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let φAtUHt := φ uHat
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    0 ≤
      (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * φAtUHt -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        τ * penaltyResidual := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let φAtUHt := φ uHat
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hsplit :
      (1 - τ) * problem.linearMap xBar (uMuBar : E₂) +
          τ * problem.linearMap (x₀ uHat) (uMuBar : E₂) -
          problem.dualPenalty uMuBar -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uMuBar ≤
        (1 - τ) * problem.linearMap xBar (uPlusOracle : E₂) +
          τ * problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle -
          (1 - τ) * (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle := by
    -- Keep the new-oracle maximizer comparison in its explicit split-support owner.
    exact
      newOracleSplitSupportComparison
        problem
        x₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hτ
        hτ_lt
  have hselectorEq :
      selectorSlice (uMuBar : E₂) =
        φAtUHt +
          inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
          penaltyResidual := by
    -- Rewrite the old-oracle selector slice once so the split-support comparison exposes the
    -- residualized support term directly.
    exact
      selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
  have hsplit' :
      0 ≤
        (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uPlusOracle : E₂) - selectorSlice (uMuBar : E₂)) := by
    -- Rearranging the split-support comparison isolates the new-minus-old support increment.
    nlinarith [hsplit]
  -- Substitute the old-oracle selector identity to expose the residualized support inequality.
  rw [hselectorEq] at hsplit'
  nlinarith [hsplit']

/-- Helper for Theorem 6.2.3: subtracting the selector-bridge form from the residualized target
exposes the actual support residual sign and a purely scalar remainder. -/
theorem newOracleTargetDifference_eq_supportResidual_addScalarRemainder
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    (φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
        ((1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hselectorEq :
      selectorSlice (uMuBar : E₂) =
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
          penaltyResidual := by
    -- Rewrite the old-oracle selector slice once so the target difference stays in one owner.
    exact
      selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
  have htarget :
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ *
              (φ uHat +
                  inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
                  penaltyResidual -
                selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    simp [adjointGradientMaximand, oldSupport, selectorSlice, penaltyResidual]
    ring
  -- Route correction: the exact target-difference audit shows the support residual appears with
  -- a `+ τ * (selectorSlice uMuBar - selectorSlice uPlusOracle)` sign.
  calc
    (φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
        ((1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ *
            (φ uHat +
                inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
                penaltyResidual -
              selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := htarget
    _ =
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
      rw [hselectorEq]

/-- Helper for Theorem 6.2.3: transport nonnegativity from the audited split owner back to the
original target difference. This isolates the remaining blocker to a single scalar inequality in
the split owner. -/
theorem newOracleTargetDifference_nonneg_of_splitNonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hsplitNonneg :
      let φ : E₂ → ℝ := fun u : E₂ ↦
        extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
      let hτIcc := tau_mem_Icc hτ hτ_lt
      let uHat :=
        predictedDualPoint problem.dualSet_convex
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let xBarPlus :=
        updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let μ₂Plus : {μ : ℝ // 0 < μ} :=
        ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
      let uMuBar := problem.dualOracleSolver xBar μ₂
      let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
      let oldSupport : E₂ → ℝ := fun w ↦
        problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
      let selectorSlice : E₂ → ℝ := fun w ↦
        problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
      let penaltyResidual :=
        problem.dualPenalty uMuBar - problem.dualPenalty uHat -
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂))
      0 ≤
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ))) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    0 ≤
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              ((problem.linearMap xBar (uPlusOracle : E₂) - problem.dualPenalty uPlusOracle -
                    (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle) -
                  (problem.linearMap xBar (uMuBar : E₂) - problem.dualPenalty uMuBar -
                    (μ₂ : ℝ) * problem.dualProxFunction uMuBar) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ *
              (problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
                problem.dualPenalty uPlusOracle) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hsplit :
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Reuse the audited split equality before transporting the inequality back to the target.
    simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
      penaltyResidual] using
      (newOracleTargetDifference_eq_supportResidual_addScalarRemainder
        problem
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt)
  -- Move the already-proved sign from the split owner back across the audited equality.
  linarith [hsplit, hsplitNonneg]

/-- Helper for Theorem 6.2.3: route correction at the actual new oracle. The explicit scalar
core from the weighted-gap estimate should land directly in the plain predicted dual model owner. -/
theorem selectorBridgeForm_le_affineGapCore
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        τ *
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hselectorUpper :
      selectorSlice (uPlusOracle : E₂) ≤
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) := by
    -- Bound the selector slice by the affine linearization at `uHat` before comparing models.
    simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle, selectorSlice] using
      (selectorSliceAtPredictedPoint_le_selectedAffineModel
        problem
        x₀
        (u := uHat)
        (v := uPlusOracle)
        hx₀
        hgradient_eq_selectedSlope)
  have hscaledSelectorUpper :
      τ * selectorSlice (uPlusOracle : E₂) ≤
        τ *
          (φ uHat +
            inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂))) := by
    -- Scale the selector upper bound by the positive step size before rearranging the bridge.
    exact mul_le_mul_of_nonneg_left hselectorUpper (le_of_lt hτ)
  -- Replace the selector slice by its affine upper bound and keep the remaining oracle-gap core
  -- unchanged.
  linarith

/-- Helper for Theorem 6.2.3: the former `iff` bridge is no longer part of the active proof
route. It is retained only as a theorem-local placeholder while the direct audited-difference
route is being stabilized. -/
theorem newOracleSplitOwner_nonneg_iff_selectorBridge_le_residualizedModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    True := by
  trivial

/-- Helper for Theorem 6.2.3: at the actual new oracle, the weighted old-support residual plus the
selector residual is nonpositive. This packages the pure support-side comparison independently of
the remaining model-term bookkeeping. -/
theorem weightedSupportResidual_nonposAtNewOracle
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
        τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
      0 := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have holdResidual :
      oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) ≤ 0 := by
    -- The old oracle still dominates the actual new oracle in the old-support owner.
    have hcompetitor :
        oldSupport (uPlusOracle : E₂) ≤ oldSupport (uMuBar : E₂) := by
      exact oldSupportAtCompetitor_le_oldOracleSupport problem (xBar := xBar) (μ₂ := μ₂) uPlusOracle
    linarith
  have hscaledResidual :
      (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) ≤ 0 := by
    -- The weighted old-support residual inherits the same nonpositive sign.
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτ_lt.le) holdResidual
  have hselectorResidual :
      τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
        (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) := by
    -- Reuse the split-support comparison before any cancellation of the old-support term.
    simpa [hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, selectorSlice] using
      (selectorSlice_oldSupport_rearranged
        problem
        x₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hτ
        hτ_lt)
  -- Both support-side residual pieces are bounded above by the same nonpositive old-support term.
  linarith [hscaledResidual, hselectorResidual]

/-- Helper for Theorem 6.2.3: the former affine-gap core differs from the selector-bridge form by
exactly the new-oracle penalty residual, so the old target was strictly stronger than the repaired
selector-bridge route. -/
theorem affineGapCore_eq_selectorBridgeForm_add_newPenaltyResidual
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidualAtNew :=
      problem.dualPenalty uPlusOracle - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uPlusOracle : E₂) - (uHat : E₂))
    φ uHat +
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
      (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) +
        τ * penaltyResidualAtNew := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidualAtNew :=
    problem.dualPenalty uPlusOracle - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uPlusOracle : E₂) - (uHat : E₂))
  have hselectorAtNew :
      selectorSlice (uPlusOracle : E₂) =
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
          penaltyResidualAtNew := by
    -- Rewrite the actual new-oracle selector slice once so the mismatch is a single residual term.
    exact
      selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
  -- Route correction: the old affine-gap target is exactly the selector-bridge form plus the
  -- new-oracle penalty residual, so any proof must account for that extra nonnegative term.
  calc
    φ uHat +
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
        (1 - τ) * φ uHat +
          τ *
            (φ uHat +
              inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
              penaltyResidualAtNew) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) +
          τ * penaltyResidualAtNew := by
            ring
    _ =
        (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) +
          τ * penaltyResidualAtNew := by
            rw [← hselectorAtNew]

/-- Helper for Theorem 6.2.3: once the audited residualized-model difference is nonnegative, the
split-owner scalar follows immediately by rewriting across the target-difference identity. -/
theorem newOracleSplitOwnerNonneg_of_targetDifferenceNonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hdifferenceNonneg :
      let φ : E₂ → ℝ := fun u : E₂ ↦
        extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
      let hτIcc := tau_mem_Icc hτ hτ_lt
      let uHat :=
        predictedDualPoint problem.dualSet_convex
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let xBarPlus :=
        updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let μ₂Plus : {μ : ℝ // 0 < μ} :=
        ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
      let uMuBar := problem.dualOracleSolver xBar μ₂
      let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
      let oldSupport : E₂ → ℝ := fun w ↦
        problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
      let selectorSlice : E₂ → ℝ := fun w ↦
        problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
      0 ≤
        (φ uHat +
              adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) *
                (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                  ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
            ((1 - τ) * φ uHat +
              τ * selectorSlice (uPlusOracle : E₂) -
              τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ))) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    0 ≤
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have htargetDifference :
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Reuse the audited equality once so the split-owner statement is purely a transport step.
    simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
      penaltyResidual] using
      (newOracleTargetDifference_eq_supportResidual_addScalarRemainder
        problem
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt)
  -- The split-owner scalar is just the audited residualized-model difference in a different owner.
  linarith [htargetDifference, hdifferenceNonneg]

/-- Helper for Theorem 6.2.3: the audited target difference rewrites exactly into the split-owner
scalar used by the remaining closure step. -/
theorem newOracleAuditedDifference_eq_splitOwner
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    (φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
        ((1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  -- Reuse the audited equality once so the remaining blocker is a single split-owner inequality.
  simpa using
    (newOracleTargetDifference_eq_supportResidual_addScalarRemainder
      problem
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt)

/-- Helper for Theorem 6.2.3: rewrite the predicted-point support comparison directly as a
nonnegative difference in the `oldSupport`/`selectorSlice` owner. -/
theorem newOracleSupportComparisonAtPredictedPointDifference_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    0 ≤
      (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uHat : E₂)) +
        τ * (selectorSlice (uPlusOracle : E₂) - φ uHat) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hsupport :
      (1 - τ) * oldSupport (uHat : E₂) + τ * φ uHat ≤
        (1 - τ) * oldSupport (uPlusOracle : E₂) + τ * selectorSlice (uPlusOracle : E₂) := by
    -- Keep the actual new-oracle support comparison in the `uHat`-centered owner first.
    exact
      newOracleSupportComparisonAtPredictedPoint_explicit
        problem
        x₀
        hx₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hτ
        hτ_lt
  -- Rearranging the support comparison isolates the nonnegative predicted-point difference.
  nlinarith [hsupport]

/-- Helper for Theorem 6.2.3: weighting the old-support quadratic gap at `uHat` by `1 - τ`
keeps the strong-convexity defect nonpositive in the exact owner used by the repaired bridge. -/
theorem scaledOldSupportPredictedResidual_nonpos
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    (1 - τ) *
        (oldSupport (uHat : E₂) - oldSupport (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) ≤
      0 := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  have holdResidual :
      oldSupport (uHat : E₂) - oldSupport (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        0 := by
    -- Rewrite the predicted-point old-support gap into the residual sign used by the bridge.
    have hgap :
        oldSupport (uHat : E₂) ≤
          oldSupport (uMuBar : E₂) -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
      exact
        oldSupportAtPredictedPoint_le_oldOracleSupport_sub_quadratic
          problem
          hdualProx
          (xBar := xBar)
          (uBar := uBar)
          (μ₂ := μ₂)
          (τ := τ)
          hτ
          hτ_lt
    nlinarith [hgap]
  -- The weighted residual keeps the same sign because `1 - τ ≥ 0`.
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτ_lt.le) holdResidual

/-- Helper for Theorem 6.2.3: rewriting `selectorSlice (uMuBar)` once cancels the explicit
`τ * penaltyResidual` term in the split-owner scalar, so the remaining blocker lives in one
normalized owner. -/
theorem newOracleSplitOwner_eq_penaltyCanceledNormalForm
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ *
              (φ uHat +
                inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
                selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) -
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hselectorAtOldOracle :
      selectorSlice (uMuBar : E₂) =
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
          penaltyResidual := by
    -- Rewrite the old-oracle selector slice once so the explicit `τ * penaltyResidual` term can
    -- cancel in the normalized split owner.
    simpa [φ, selectorSlice, penaltyResidual] using
      (selectorSlice_eq_phiAddGradientPairing_subPenaltyResidual
        problem
        x₀
        (u := uHat)
        (v := uMuBar)
        hx₀
        hgradient_eq_selectedSlope)
  have hnormalizedRaw :
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
              τ *
                (φ uHat +
                  inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
                  selectorSlice (uPlusOracle : E₂))) +
            (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) -
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Substitute the normalized old-oracle selector slice and cancel the matching residual term
    -- before reintroducing the theorem-level `let` bindings.
    rw [hselectorAtOldOracle]
    ring
  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
    penaltyResidual] using hnormalizedRaw

/-- Helper for Theorem 6.2.3: the remaining direct bridge is the selector-bridge inequality at the
actual new oracle, before reattaching the explicit new-oracle penalty residual. -/
theorem selectorBridgeForm_le_residualizedModelDirect
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
        (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
  -- Route correction: keep the main theorem as a transport step from the audited target
  -- difference. The only remaining frontier is the exact split-owner nonnegativity premise.
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hsplitNonneg :
      0 ≤
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    have hnormalized :
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
              τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
            (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
              τ * penaltyResidual -
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
          ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
                τ *
                  (φ uHat +
                    inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) -
                    selectorSlice (uPlusOracle : E₂))) +
              (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
                (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) -
                  ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
      -- Normalize the split-owner scalar once so the explicit `τ * penaltyResidual` term
      -- cancels before the final sign comparison.
      simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
        penaltyResidual] using
        (newOracleSplitOwner_eq_penaltyCanceledNormalForm
          problem
          x₀
          hx₀
          Lphi
          (xBar := xBar)
          (uBar := uBar)
          (μ₂ := μ₂)
          (τ := τ)
          hgradient_eq_selectedSlope
          hτ
          hτ_lt)
    rw [hnormalized]
    have hbridgeToAffine :
        (1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
          φ uHat +
            τ *
              inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
      -- First replace the selector slice at the new oracle by the affine upper model at `uHat`.
      simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, selectorSlice] using
        (selectorBridgeForm_le_affineGapCore
          problem
          x₀
          hx₀
          (xBar := xBar)
          (uBar := uBar)
          (μ₂ := μ₂)
          (τ := τ)
          hgradient_eq_selectedSlope
          hτ
          hτ_lt)
    have hpredictedSupport :
        0 ≤
          (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uHat : E₂)) +
            τ * (selectorSlice (uPlusOracle : E₂) - φ uHat) := by
      -- The source proof compares the actual new oracle against the predicted point in the mixed
      -- old-support/selector owner.
      simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice]
        using
          (newOracleSupportComparisonAtPredictedPointDifference_nonneg
            problem
            x₀
            hx₀
            (xBar := xBar)
            (uBar := uBar)
            (μ₂ := μ₂)
            (τ := τ)
            hτ
            hτ_lt)
    have holdPredictedResidual :
        (1 - τ) *
            (oldSupport (uHat : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) ≤
          0 := by
      -- The old oracle still dominates the predicted point after inserting its quadratic defect.
      simpa [hτIcc, uHat, uMuBar, oldSupport] using
        (scaledOldSupportPredictedResidual_nonpos
          problem
          hdualProx
          (xBar := xBar)
          (uBar := uBar)
          (μ₂ := μ₂)
          (τ := τ)
          hτ
          hτ_lt)
    have holdNewResidual :
        oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ) ≤
          0 := by
      -- Strong convexity of the old-support owner controls the actual new oracle as a competitor.
      simpa [uMuBar, oldSupport] using
        (oldSupportResidual_nonpos
          problem
          hdualProx
          (xBar := xBar)
          (μ₂ := μ₂)
          uPlusOracle)
    have hpenaltyResidualNonneg :
        0 ≤
          problem.dualPenalty uPlusOracle - problem.dualPenalty uHat -
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uPlusOracle : E₂) - (uHat : E₂)) := by
      -- The dual penalty is convex, so its tangent residual at `uHat` is nonnegative.
      simpa [hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle] using
        (predictedPointPenaltyResidual_nonneg
          problem
          (xBar := xBar)
          (uBar := uBar)
          (μ₂ := μ₂)
          (τ := τ)
          hτ
          hτ_lt
          uPlusOracle)
    have haffineToResidualized :
        φ uHat +
            τ *
              inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
          φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
      -- Unfold the quadratic model and combine the predicted-point support comparison with the
      -- old/new residual controls already established above.
      simp [adjointGradientMaximand] at *
      nlinarith [hbridgeToAffine, hpredictedSupport, holdPredictedResidual, holdNewResidual]
    have hbridge :
        (1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
          φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
      -- Chain the selector-to-affine bridge with the residualized-model closure.
      exact hbridgeToAffine.trans haffineToResidualized
    -- After the normalization rewrite, the goal is the expanded nonnegative difference attached to
    -- the selector-bridge inequality.
    linarith [hbridge]
  have hdifferenceNonneg :
      0 ≤
        (φ uHat +
              adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) *
                (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                  ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
            ((1 - τ) * φ uHat +
              τ * selectorSlice (uPlusOracle : E₂) -
              τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Transport the split-owner sign back to the audited target difference before converting it
    -- into the requested inequality.
    exact
      newOracleTargetDifference_nonneg_of_splitNonneg
        problem
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hsplitNonneg
  -- Convert the audited target-difference sign back to the selector-bridge inequality.
  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice] using
    (sub_nonneg.mp hdifferenceNonneg)

/-- Helper for Theorem 6.2.3: route correction for the legacy affine-gap helper name. The active
frontier is the selector-bridge inequality at the actual new oracle, so this legacy wrapper now
exposes that exact statement directly. -/
theorem affineGapCore_le_residualizedModelDirect
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
        (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
  -- Keep the legacy theorem name as a direct alias of the repaired selector-bridge inequality.
  exact
    selectorBridgeForm_le_residualizedModelDirect
      problem
      hdualProx
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep

/-- Helper for Theorem 6.2.3: once the repaired legacy bridge is phrased in the selector owner,
this compatibility wrapper is the identity transport back to the active residualized-model
statement. -/
theorem selectorBridgeForm_le_residualizedModel_of_affineGapBridge
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (haffineBridge :
      let φ : E₂ → ℝ := fun u : E₂ ↦
        extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
      let hτIcc := tau_mem_Icc hτ hτ_lt
      let uHat :=
        predictedDualPoint problem.dualSet_convex
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let xBarPlus :=
        updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
          (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
      let μ₂Plus : {μ : ℝ // 0 < μ} :=
        ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
      let uMuBar := problem.dualOracleSolver xBar μ₂
      let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
      let oldSupport : E₂ → ℝ := fun w ↦
        problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
      let selectorSlice : E₂ → ℝ := fun w ↦
        problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
      (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
        (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
  -- The repaired legacy bridge is already stated in the selector owner, so no further transport
  -- is required.
  exact haffineBridge

theorem newOracleSelectorBridgeDifference_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    0 ≤
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              ((problem.linearMap xBar (uPlusOracle : E₂) - problem.dualPenalty uPlusOracle -
                    (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle) -
                  (problem.linearMap xBar (uMuBar : E₂) - problem.dualPenalty uMuBar -
                    (μ₂ : ℝ) * problem.dualProxFunction uMuBar) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ *
              (problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
                problem.dualPenalty uPlusOracle) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  -- Keep the audited difference as the direct `sub_nonneg` wrapper over the primitive bridge.
  exact
    sub_nonneg.mpr
      (selectorBridgeForm_le_residualizedModelDirect
        problem
        hdualProx
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep)

/-- Helper for Theorem 6.2.3: route correction for the legacy helper name. The proof pipeline now
targets the selector-bridge inequality at the actual new oracle, because the former affine-gap
statement differs from it by the extra nonnegative term `τ * penaltyResidualAtNew`. -/
theorem newOracleSplitOwnerNonnegDirect
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    0 ≤
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  -- Route correction: the split-owner theorem is now only the audited transport step. The
  -- remaining frontier is the direct nonnegativity of the residualized-model minus selector-bridge
  -- difference at `uPlusOracle`.
  let _ := hdualProx
  let _ := hstep
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  exact
    newOracleSplitOwnerNonneg_of_targetDifferenceNonneg
      problem
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      (by
        -- Reuse the canonical audited difference so this legacy theorem is only a transport step.
        simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport,
          selectorSlice] using
          (newOracleSelectorBridgeDifference_nonneg
            problem
            hdualProx
            x₀
            hx₀
            Lphi
            (xBar := xBar)
            (uBar := uBar)
            (μ₂ := μ₂)
            (τ := τ)
            hgradient_eq_selectedSlope
            hτ
            hτ_lt
            hstep))

/-- Helper for Theorem 6.2.3: route correction for the legacy helper name. The proof pipeline now
targets the selector-bridge inequality at the actual new oracle, because the former affine-gap
statement differs from it by the extra nonnegative term `τ * penaltyResidualAtNew`. -/
theorem affineGapCore_le_residualizedModelAtNewOracle
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
        (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
  -- Route correction: keep the legacy public name as a direct alias of the selector-bridge
  -- frontier, without reintroducing the stronger affine-gap owner.
  exact
    selectorBridgeForm_le_residualizedModelDirect
      problem
      hdualProx
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep

/-- Helper for Theorem 6.2.3: once the selector slice is replaced by its affine upper model, the
remaining comparison is exactly the residualized-model bridge at the actual new oracle. -/
theorem selectorBridgeForm_le_residualizedModelAtNewOracle
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
        (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
  -- Route correction: this companion name is judgmentally the same audited inequality, so keep it
  -- as a one-line alias of the legacy wrapper.
  exact
    affineGapCore_le_residualizedModelAtNewOracle
      problem
      hdualProx
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep

/-- Helper for Theorem 6.2.3: route correction for the legacy helper name. The real remaining
frontier is the exact split-owner domination inequality consumed by
`newOracleTargetDifference_nonneg_of_splitNonneg`, and it now factors through the direct
selector-bridge comparison. -/
theorem newOracleAffineGapCore_le_residualizedModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    0 ≤
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  have hsplit :
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ * selectorSlice (uPlusOracle : E₂) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) =
        ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
            τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
          (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
            τ * penaltyResidual -
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Reuse the audited equality before transporting the bridge inequality back to the split owner.
    simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
      penaltyResidual] using
      (newOracleTargetDifference_eq_supportResidual_addScalarRemainder
        problem
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt)
  have hbridge :
      (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
    -- The split-owner target now factors through the direct selector-to-residualized-model bridge.
    simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice] using
      (selectorBridgeForm_le_residualizedModelAtNewOracle
        problem
        hdualProx
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep)
  have hdifferenceNonneg :
      0 ≤
        (φ uHat +
              adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) *
                (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                  ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
            ((1 - τ) * φ uHat +
              τ * selectorSlice (uPlusOracle : E₂) -
              τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Convert the bridge inequality back into the audited scalar difference.
    exact sub_nonneg.mpr hbridge
  -- Transport the direct bridge back through the audited split-owner equality.
  linarith [hsplit, hdifferenceNonneg]

/-- Helper for Theorem 6.2.3: the repaired middle bridge is the audited residualized difference
between the predicted dual model and the selector-bridge form at the actual new oracle. -/
theorem newOracleSplitOwner_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    let penaltyResidual :=
      problem.dualPenalty uMuBar - problem.dualPenalty uHat -
        inner ℝ
          (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
          ((uMuBar : E₂) - (uHat : E₂))
    0 ≤
      ((1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
          τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂))) +
        (adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) * (((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) +
          τ * penaltyResidual -
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  let penaltyResidual :=
    problem.dualPenalty uMuBar - problem.dualPenalty uHat -
      inner ℝ
        (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
        ((uMuBar : E₂) - (uHat : E₂))
  -- Route correction: after retargeting the legacy helper name, the split-owner theorem is just a
  -- transparent wrapper over that exact frontier.
  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uMuBar, uPlusOracle, oldSupport, selectorSlice,
    penaltyResidual] using
    (newOracleAffineGapCore_le_residualizedModel
      problem
      hdualProx
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep)

/-- Helper for Theorem 6.2.3: the repaired middle bridge is the audited residualized difference
between the predicted dual model and the selector-bridge form at the actual new oracle. -/
theorem newOracleResidualizedModelDifference_nonneg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    0 ≤
      (φ uHat +
            adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
            (1 - τ) *
              ((problem.linearMap xBar (uPlusOracle : E₂) - problem.dualPenalty uPlusOracle -
                    (μ₂ : ℝ) * problem.dualProxFunction uPlusOracle) -
                  (problem.linearMap xBar (uMuBar : E₂) - problem.dualPenalty uMuBar -
                    (μ₂ : ℝ) * problem.dualProxFunction uMuBar) +
                ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
          ((1 - τ) * φ uHat +
            τ *
              (problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
                problem.dualPenalty uPlusOracle) -
            τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  -- Reuse the canonical audited-difference theorem so later wrappers no longer recreate the
  -- same scalar frontier.
  simpa using
    (newOracleSelectorBridgeDifference_nonneg
      problem
      hdualProx
      x₀
      hx₀
      Lphi
      (xBar := xBar)
      (uBar := uBar)
      (μ₂ := μ₂)
      (τ := τ)
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep)

/-- Helper for Theorem 6.2.3: the remaining scalar bookkeeping for the selector-bridge comparison
reduces to checking that the audited residualized-model difference is nonnegative. -/
theorem selectorBridgeScalarCore_le_residualizedModel
    {τ φu gradOld oldOracle oldNew selectorNew quadPredicted quadNew modelNew : ℝ}
    (hdifference_nonneg :
      0 ≤
        (φu + modelNew + (1 - τ) * (oldNew - oldOracle + quadNew)) -
          ((1 - τ) * φu + τ * selectorNew - τ * gradOld + quadPredicted)) :
    ((1 - τ) * φu + τ * selectorNew - τ * gradOld + quadPredicted) ≤
      φu + modelNew + (1 - τ) * (oldNew - oldOracle + quadNew) := by
  -- Once the audited scalar difference has the correct sign, the target inequality is immediate.
  linarith

/-- Helper for Theorem 6.2.3: the mixed old-support and selector residual exposed by the
target-difference audit is already nonpositive at the actual new oracle. -/
theorem newOracleSupportResidual_nonpos
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let oldSupport : E₂ → ℝ := fun w ↦
      problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) +
        τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
      0 := by
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have holdResidual :
      oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) ≤ 0 := by
    -- The old oracle still dominates the actual new oracle in the old-support owner.
    have hcompetitor :
        oldSupport (uPlusOracle : E₂) ≤ oldSupport (uMuBar : E₂) := by
      exact oldSupportAtCompetitor_le_oldOracleSupport problem (xBar := xBar) (μ₂ := μ₂) uPlusOracle
    nlinarith [hcompetitor]
  have hscaledResidual :
      (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) ≤ 0 := by
    -- The weighted old-support residual inherits the same nonpositive sign.
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτ_lt.le) holdResidual
  have hselectorResidual :
      τ * (selectorSlice (uMuBar : E₂) - selectorSlice (uPlusOracle : E₂)) ≤
        (1 - τ) * (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂)) := by
    -- Reuse the split-support comparison before any cancellation of the old-support term.
    exact
      selectorSlice_oldSupport_rearranged
        problem
        x₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hτ
        hτ_lt
  -- Both residual pieces are bounded above by the same nonpositive old-support term.
  nlinarith [hscaledResidual, hselectorResidual]

/-- Helper for Theorem 6.2.3: compare the selector-bridge normal form at the actual new oracle
directly against the predicted dual model while the proof still has access to the Chapter 6
`oldSupport` and `selectorSlice` geometry. -/
theorem selectorBridgeForm_le_predictedDualModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hdifference_nonneg :
      0 ≤
        (φ uHat +
              adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
              (1 - τ) *
                (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
                  ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ))) -
            ((1 - τ) * φ uHat +
              τ * selectorSlice (uPlusOracle : E₂) -
              τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) := by
    -- Use the corrected residualized middle bridge instead of the false affine-gap helper.
    exact
      newOracleResidualizedModelDifference_nonneg
        problem
        hdualProx
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep
  have hresidualizedBridge :
      (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) +
          (1 - τ) *
            (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
              ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) := by
    -- Convert the audited nonnegativity statement into the residualized model inequality.
    exact
      selectorBridgeScalarCore_le_residualizedModel
        hdifference_nonneg
  have holdResidualNonpos :
      oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ) ≤
        0 := by
    -- Strong convexity of the old oracle slice keeps the residual term nonpositive.
    exact
      oldSupportResidual_nonpos
        problem
        hdualProx
        (xBar := xBar)
        (μ₂ := μ₂)
        uPlusOracle
  have hscaledResidualNonpos :
      (1 - τ) *
          (oldSupport (uPlusOracle : E₂) - oldSupport (uMuBar : E₂) +
            ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uPlusOracle : E₂)‖ ^ (2 : ℕ)) ≤
        0 := by
    -- The residual stays nonpositive after weighting by `1 - τ`.
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hτ_lt.le) holdResidualNonpos
  -- Drop the residualized old-support term to land in the plain predicted dual model owner.
  nlinarith [hresidualizedBridge, hscaledResidualNonpos]

/-- Helper for Theorem 6.2.3: after rewriting the explicit new-oracle core into the selector
bridge form, the already-proved affine-gap comparison removes the selector term without touching
the final quadratic-model bridge. -/
theorem newOracleExplicitCore_le_affineGapCore
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    φ uHat +
        τ *
          (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
        τ *
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂)) +
        τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        τ *
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hselectorBridgeForm :
      φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
        (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Normalize the explicit core into the selector owner exactly once before dropping the
    -- selector term with the affine upper model.
    exact
      newOracleExplicitCore_eq_selectorBridgeForm
        problem
        x₀
        hx₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
  have hbridgeToAffine :
      (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          τ *
            inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Once the selector bridge is explicit, the affine upper model is exactly the earlier helper.
    exact
      selectorBridgeForm_le_affineGapCore
        problem
        x₀
        hx₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
  -- The explicit new-oracle core now reaches the affine-gap core by rewriting and transitivity.
  calc
    φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
      (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := hselectorBridgeForm
    _ ≤
      φ uHat +
        τ *
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := hbridgeToAffine

/-- Helper for Theorem 6.2.3: route correction at the actual new oracle. The explicit scalar
core from the weighted-gap estimate should land directly in the plain predicted dual model owner. -/
theorem newOracleExplicitCore_le_predictedDualModelWithResidual
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    φ uHat +
        τ *
          (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
        τ *
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂)) +
        τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hselectorBridgeForm :
      φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
        (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Rewrite the explicit scalar core into the stable selector-bridge owner once.
    exact
      newOracleExplicitCore_eq_selectorBridgeForm
        problem
        x₀
        hx₀
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
  have hselectorBridge :
      (1 - τ) * φ uHat +
          τ * selectorSlice (uPlusOracle : E₂) -
          τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
    -- Apply the repaired selector-bridge theorem directly after the normalization step.
    exact
      selectorBridgeForm_le_predictedDualModel
        problem
        hdualProx
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep
  -- The explicit-core wrapper is now just rewrite plus the repaired selector bridge.
  calc
    φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) =
      (1 - τ) * φ uHat +
        τ * selectorSlice (uPlusOracle : E₂) -
        τ * inner ℝ (gradient φ (uHat : E₂)) ((uMuBar : E₂) - (uHat : E₂)) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := hselectorBridgeForm
    _ ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) :=
      hselectorBridge

/-- Helper for Theorem 6.2.3: route correction for the theorem-local wrapper with the legacy
name. At the actual new oracle, the weighted old certificate and selector slice now land directly
in the plain predicted dual model owner. -/
theorem weightedGapAndSelectorSliceAtNewOracle_le_predictedDualModel_withResidual
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet)
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let selectorSlice : E₂ → ℝ := fun w ↦
      problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
    (1 - τ) *
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
      τ * selectorSlice (uPlusOracle : E₂) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uMuBar := problem.dualOracleSolver xBar μ₂
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let oldSupport : E₂ → ℝ := fun w ↦
    problem.linearMap xBar w - problem.dualPenalty w - (μ₂ : ℝ) * problem.dualProxFunction w
  let selectorSlice : E₂ → ℝ := fun w ↦
    problem.smoothPart (x₀ uHat) + problem.linearMap (x₀ uHat) w - problem.dualPenalty w
  have hexplicitCore :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
        τ * selectorSlice (uPlusOracle : E₂) ≤
      φ uHat +
        τ *
          (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
        τ *
          inner ℝ
            (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
            ((uMuBar : E₂) - (uHat : E₂)) +
        τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
        ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) := by
    -- Reuse the proved normalization helper so the specialization only needs the new-oracle bridge.
    exact
      weightedGapAndSelectorSlice_le_explicitResidualCore
        problem
        x₀
        Lphi
        hgap
        hx₀
        hphi_hasGradientWithinAt
        hphi_lipschitz
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep
        uPlusOracle
  have hbridge :
      φ uHat +
          τ *
            (problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.linearMap (x₀ uHat) (uMuBar : E₂)) +
          τ *
            inner ℝ
              (gradientWithin problem.dualPenalty problem.dualSet (uHat : E₂))
              ((uMuBar : E₂) - (uHat : E₂)) +
          τ * (problem.dualPenalty uHat - problem.dualPenalty uPlusOracle) +
          ((μ₂ : ℝ) / 2) * ‖(uMuBar : E₂) - (uHat : E₂)‖ ^ (2 : ℕ) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
    -- The remaining owner change is the dedicated `uPlusOracle` bridge.
    exact
      newOracleExplicitCore_le_predictedDualModelWithResidual
        problem
        hdualProx
        x₀
        hx₀
        Lphi
        (xBar := xBar)
        (uBar := uBar)
        (μ₂ := μ₂)
        (τ := τ)
        hgradient_eq_selectedSlope
        hτ
        hτ_lt
        hstep
  -- Chain the explicit-core estimate with the dedicated new-oracle bridge.
  exact hexplicitCore.trans hbridge

/-- Helper for Theorem 6.2.3: the weighted old-gap term and the selector slice at the new oracle
should land in the quadratic model based at `\hat u`. -/
theorem weightedGapAndSelectorSliceAtNewOracle_le_predictedDualModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet)
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ)) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let μ₂Plus : {μ : ℝ // 0 < μ} :=
      ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
    let uMuBar := problem.dualOracleSolver xBar μ₂
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    (1 - τ) *
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
      τ *
        (problem.smoothPart (x₀ uHat) +
          problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle) ≤
      φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
  -- Route correction: the theorem-local wrapper with the legacy `_withResidual` name now exposes
  -- the exact plain-model statement needed here.
  exact
    weightedGapAndSelectorSliceAtNewOracle_le_predictedDualModel_withResidual
      problem
      hdualProx
      x₀
      Lphi
      hgap
      hx₀
      hphi_hasGradientWithinAt
      hphi_lipschitz
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep

/-- Helper for Theorem 6.2.3: the actual updated dual point dominates the quadratic model value
at the new oracle because `V(\hat u)` maximizes that model on the feasible dual set. -/
theorem newOracleModel_le_updatedDualPointModel
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x₀ : problem.dualSet → problem.primalSet)
    (V : problem.dualSet → problem.dualSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτIcc : τ ∈ Set.Icc (0 : ℝ) 1)
    {μ₂Plus : {μ : ℝ // 0 < μ}}
    (hV :
      IsAdjointGradientMappingOn
        problem.dualSet
        (fun u : E₂ ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        (Lphi : ℝ)
        V) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let xBarPlus :=
      updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
    let uBarPlus :=
      updatedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ hτIcc
    adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) ≤
      adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uBarPlus : E₂) := by
  -- Once the model is written at `\hat u`, the `IsMaxOn` property of `V` gives the comparison in
  -- one step.
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  exact (updatedDualPoint_isMaxOn
    problem.dualSet_convex
    (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂)
    V
    xBar
    uBar
    τ
    hτIcc
    hV) uPlusOracle.property

/-- Helper for Theorem 6.2.3: once the quadratic model is evaluated at the actual adjoint-gradient
update `\bar u_+ = V(\hat u)`, the lower smooth model of `φ` at `\hat u` upgrades it to the true
dual value `φ(\bar u_+)`. -/
theorem predictedDualModel_le_updatedDualValue
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (V : problem.dualSet → problem.dualSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
        (gradient
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet) :
    let φ : E₂ → ℝ := fun u : E₂ ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
    let hτIcc := tau_mem_Icc hτ hτ_lt
    let uHat :=
      predictedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
    let uBarPlus :=
      updatedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ hτIcc
    φ uHat +
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uBarPlus : E₂) ≤
      φ uBarPlus := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let uBarPlus :=
    updatedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ hτIcc
  have hlower :=
    (lowerQuadraticModel_of_hasGradientWithinAt_lipschitzOn
      hphi_hasGradientWithinAt
      hphi_lipschitz
      problem.dualSet_convex
      uHat.property
      uBarPlus.property)
  -- Rewrite the lower quadratic model exactly in the `adjointGradientMaximand` normal form.
  change
    φ uHat +
        (inner ℝ (gradient φ (uHat : E₂)) ((uBarPlus : E₂) - (uHat : E₂)) -
          ((Lphi : ℝ) / 2) * ‖(uBarPlus : E₂) - (uHat : E₂)‖ ^ (2 : ℕ)) ≤
      φ uBarPlus
  nlinarith [hlower]

-- Proof sketch: use convexity of `Q₂` and `Q₁` to keep `\hat u` and `\bar x_+` feasible, apply
-- the `μ₁ = 0` excessive-gap hypothesis for the actual Chapter 6 owners
-- `smoothedPrimalObjective` and `smoothedDualObjective`, use the canonical `argmin` and `argmax`
-- hypotheses for `x₀` and `u_{μ₂}`, and then use the source-facing owner
-- `IsAdjointGradientMappingOn` for the finite-real-part dual objective to see that
-- `\bar u_+ = V(\hat u)` lies in the canonical adjoint-gradient argmax set at `\hat u`,
-- together with
-- the step-size bound
-- `τ^2 / (1 - τ) ≤ μ₂ / L₂(φ)` to recover the updated inequality at smoothing parameter
-- `μ₂⁺ = (1 - τ) μ₂`.
-- Semantic recall check: `lean_leansearch` did not expose a more canonical owner than the local
-- Chapter 6 excessive-gap and adjoint-gradient APIs already used here.
/-- Theorem 6.2.3: in the chapter's implementable primal-dual setting, let `(\bar x, \bar u)`
satisfy the excessive-gap condition with `μ₁ = 0`, let `x₀` select the zero-smoothing primal
minimizer at every feasible dual point, and let `V` be the chapter adjoint-gradient update map
for the actual zero-smoothed dual objective `φ`, whose gradient exists on the feasible dual set
and is Lipschitz there with constant `L₂(φ)`. Assume in addition that the chosen selector `x₀`
is the Chapter 6 zero-smoothed minimizer selection identified by the dual-gradient formula
`∇φ(u) = A x₀(u) - ∇ \hat φ(u)` on the feasible dual set, and that the chapter dual prox function
is `1`-strongly convex on the feasible dual set. Set
`\hat u = (1 - τ) \bar u + τ u_{μ₂}(\bar x)`,
`\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`, and
`\bar u_+ = V(\hat u)`.
If `τ ∈ (0, 1)` satisfies
`τ^2 / (1 - τ) ≤ μ₂ / L₂(φ)`, then the updated pair `(\bar x_+, \bar u_+)` again satisfies the
excessive-gap condition with `μ₁ = 0` and smoothing parameter `μ₂⁺ = (1 - τ) μ₂`. -/
theorem excessive_gap_condition_preserved
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (x₀ : problem.dualSet → problem.primalSet) (V : problem.dualSet → problem.dualSet)
    (Lphi : NNReal)
    {xBar : problem.primalSet} {uBar : problem.dualSet} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : problem.primalSet ↦
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) x)
        (fun u : problem.dualSet ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hx₀ :
      ∀ u : problem.dualSet,
        (x₀ u : E₁) ∈
          argmin[problem.primalSet]
            (smoothedDualObjectiveMinimand problem.linearMap problem.smoothPart
              (fun _ : E₁ ↦ 0) 0 u))
    (hphi_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ problem.dualSet →
        HasGradientWithinAt
          (fun u : E₂ ↦
            extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            u)
          problem.dualSet
          u)
    (hphi_lipschitz :
      LipschitzOnWith Lphi
          (gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u))
        problem.dualSet)
    (hgradient_eq_selectedSlope :
      ∀ u : problem.dualSet,
        gradient
            (fun u : E₂ ↦
              extendedRealRealPart
                (smoothedDualObjective problem.linearMap problem.primalSet
                  problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
            (u : E₂) =
          (InnerProductSpace.toDual ℝ E₂).symm (problem.linearMap (x₀ u)) -
            gradientWithin problem.dualPenalty problem.dualSet (u : E₂))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        (μ₂ : ℝ) / (Lphi : ℝ))
    (hV :
      IsAdjointGradientMappingOn
        problem.dualSet
        (fun u : E₂ ↦
          extendedRealRealPart
            (smoothedDualObjective problem.linearMap problem.primalSet
              problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
        (Lphi : ℝ)
        V) :
    satisfiesExcessiveGapConditionWithMu1Zero
      (fun x : problem.primalSet ↦
        smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction
          (reducedDualSmoothing μ₂ τ) x)
      (fun u : problem.dualSet ↦
        extendedRealRealPart
          (smoothedDualObjective problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
      (updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ
        (tau_mem_Icc hτ hτ_lt))
      (updatedDualPoint problem.dualSet_convex
        (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ
        (tau_mem_Icc hτ hτ_lt)) := by
  let φ : E₂ → ℝ := fun u : E₂ ↦
    extendedRealRealPart
      (smoothedDualObjective problem.linearMap problem.primalSet
        problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u
  let hτIcc := tau_mem_Icc hτ hτ_lt
  let uHat :=
    predictedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let xBarPlus :=
    updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc
  let μ₂Plus : {μ : ℝ // 0 < μ} :=
    ⟨reducedDualSmoothing μ₂ τ, reducedDualSmoothing_pos μ₂.property hτ_lt⟩
  let uPlusOracle := problem.dualOracleSolver xBarPlus μ₂Plus
  let uBarPlus :=
    updatedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ hτIcc
  have hselector :
      problem.smoothPart (x₀ uHat) +
          problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
          problem.dualPenalty uPlusOracle ≤
        φ uHat +
          inner ℝ (gradient φ (uHat : E₂)) ((uPlusOracle : E₂) - (uHat : E₂)) := by
    -- Feed the predicted point and the actual new oracle into the dedicated selector interface.
    have hslice :
        problem.smoothPart (x₀ uHat) +
            problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle ≤
          extendedRealRealPart
              (smoothedDualObjective problem.linearMap problem.primalSet
                problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) uHat +
            inner ℝ
              (gradient
                (fun u : E₂ ↦
                  extendedRealRealPart
                    (smoothedDualObjective problem.linearMap problem.primalSet
                      problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
                (uHat : E₂))
              ((uPlusOracle : E₂) - (uHat : E₂)) := by
      exact selectorSliceAtPredictedPoint_le_selectedAffineModel
        problem
        x₀
        hx₀
        hgradient_eq_selectedSlope
    simpa [φ, uHat, xBarPlus, μ₂Plus, uPlusOracle] using hslice
  have hweighted :
      smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction
          (reducedDualSmoothing μ₂ τ) xBarPlus ≤
        (1 - τ) *
            smoothedPrimalObjective problem.linearMap problem.dualSet
              problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
          τ *
            (problem.smoothPart (x₀ uHat) +
              problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.dualPenalty uPlusOracle) := by
    exact updatedPrimalObjective_le_weightedGapAndSelectorSliceAtNewOracle problem x₀ hτ hτ_lt
  have hpredicted :
      (1 - τ) *
          smoothedPrimalObjective problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
        τ *
          (problem.smoothPart (x₀ uHat) +
            problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
            problem.dualPenalty uPlusOracle) ≤
        φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
    exact weightedGapAndSelectorSliceAtNewOracle_le_predictedDualModel
      problem
      hdualProx
      x₀
      Lphi
      hgap
      hx₀
      hphi_hasGradientWithinAt
      hphi_lipschitz
      hgradient_eq_selectedSlope
      hτ
      hτ_lt
      hstep
  have hmodel :
      adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) ≤
        adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uBarPlus : E₂) :=
    newOracleModel_le_updatedDualPointModel
      problem
      x₀
      V
      Lphi
      hτIcc
      hV
  have hdual :
      φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uBarPlus : E₂) ≤
        φ uBarPlus := by
    exact predictedDualModel_le_updatedDualValue
      problem
      V
      Lphi
      hτ
      hτ_lt
      hphi_hasGradientWithinAt
      hphi_lipschitz
  -- Route correction: the final theorem is now a pure transitivity chain through the three
  -- dedicated bridge lemmas, so the remaining blocker is isolated in the selector interface.
  exact (satisfiesExcessiveGapConditionWithMu1Zero_iff
    (fun x : problem.primalSet ↦
      smoothedPrimalObjective problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction
        (reducedDualSmoothing μ₂ τ) x)
    (fun u : problem.dualSet ↦
      extendedRealRealPart
        (smoothedDualObjective problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty (fun _ : E₁ ↦ 0) 0) u)
    (updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc)
    (updatedDualPoint problem.dualSet_convex
      (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) V xBar uBar τ hτIcc)).mpr <|
    calc
      smoothedPrimalObjective problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction
          (reducedDualSmoothing μ₂ τ)
          (updatedPrimalPoint problem.primalSet_convex problem.dualSet_convex x₀
            (fun x : problem.primalSet ↦ problem.dualOracleSolver x μ₂) xBar uBar τ hτIcc) ≤
        (1 - τ) *
            smoothedPrimalObjective problem.linearMap problem.dualSet
              problem.smoothPart problem.dualPenalty problem.dualProxFunction (μ₂ : ℝ) xBar +
          τ *
            (problem.smoothPart (x₀ uHat) +
              problem.linearMap (x₀ uHat) (uPlusOracle : E₂) -
              problem.dualPenalty uPlusOracle) := by
            simpa [hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle] using hweighted
      _ ≤ φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uPlusOracle : E₂) := by
            simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle] using hpredicted
      _ ≤ φ uHat +
          adjointGradientMaximand φ (Lphi : ℝ) (uHat : E₂) (uBarPlus : E₂) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left
                (by
                  simpa [φ, hτIcc, uHat, xBarPlus, μ₂Plus, uPlusOracle, uBarPlus] using hmodel)
                (φ uHat)
      _ ≤ φ uBarPlus := by
            simpa [φ, hτIcc, uHat, uBarPlus] using hdual

end Theorem

end StronglyConvexDualUpdate
