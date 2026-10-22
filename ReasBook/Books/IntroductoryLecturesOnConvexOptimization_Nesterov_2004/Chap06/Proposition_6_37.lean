/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

/-
Proposition 6.37 lies in the constrained minimization / approximate-solution domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner for constrained optimal values;
- `SetConstrainedMinimizationProblem.IsApproximateMinimizer` and
  `SetConstrainedMinimizationProblem.isApproximateMinimizer_iff` in
  `Chap01/Definition_1_3_7`, the canonical `ε`-suboptimality owner on a constrained problem;
- `PrimalConvexMinimizationProblem` in `Chap06/Definition_6_4`, which reuses the same owner
  abstraction and derives its optimization API through it.

Best owner abstraction:
- source-facing: Proposition 6.37's smoothing comparison theorem;
- core/canonical: `SetConstrainedMinimizationProblem.mk Q φ` together with its derived
  `optimalValue` and `IsApproximateMinimizer` API;
- bridge/view: the smoothing comparison, with the lower bound used globally on `Q` and the upper
  bound used only at the feasible comparison point `yBar`.

Primitive data:
- the feasible set `Q`;
- the original and smoothed objectives `φ` and `φμ`.
- the global lower smoothing estimate on `Q`;
- the upper smoothing estimate at `yBar`.

Derived API:
- `(SetConstrainedMinimizationProblem.mk Q φ).optimalValue`;
- `(SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar`;
- the corresponding smoothed-problem instances built from `φμ`.

This refinement removes the duplicate local owners `optimalValueOn` and
`IsEpsilonSolutionOn` and states the proposition directly with the Chapter 1 owner API.
-/

-- Proof sketch: use the upper smoothing bound at `yBar` to estimate `φ yBar` by
-- `φμ yBar + μ log n`, use the lower smoothing bound on `Q` to deduce
-- `((SetConstrainedMinimizationProblem.mk Q φμ).optimalValue :
--   EReal) ≤ (SetConstrainedMinimizationProblem.mk Q φ).optimalValue`,
-- and combine these with the assumed `ε / 2` smoothed approximate-minimizer property and the
-- budget bound `μ log n ≤ ε / 2`.
/-- Helper for Proposition 6.37: if the smoothed objective is pointwise below the original
objective on the feasible set, then the smoothed constrained optimal value is no larger than the
original constrained optimal value. -/
private lemma smoothed_optimalValue_le_original_optimalValue
    {Q : Set X} {φ φμ : X → ℝ}
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y) :
    (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue ≤
      (SetConstrainedMinimizationProblem.mk Q φ).optimalValue := by
  -- Compare the two owner problems on the same feasible set and apply the global lower estimate.
  simpa using
    (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (.mk Q φμ : SetConstrainedMinimizationProblem X)
      (.mk Q φ : SetConstrainedMinimizationProblem X)
      rfl
      happrox_lower)

/-- Helper for Proposition 6.37: the pointwise smoothing error at the certificate point and the
smoothed `ε / 2`-certificate together imply an `ε`-budget bound relative to the smoothed optimal
value. -/
private lemma certificate_value_le_smoothed_optimalValue_add_epsilon
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {μ ε : ℝ} {yBar : X}
    (happrox_upper : φ yBar ≤ φμ yBar + μ * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar)
    (hμ_budget : μ * Real.log (n : ℝ) ≤ ε / 2) :
    (φ yBar : EReal) ≤ (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue + ε := by
  rw [SetConstrainedMinimizationProblem.isApproximateMinimizer_iff] at hsmoothed
  have hhalf : ε / 2 + ε / 2 = ε := by
    ring
  have hhalfE : (ε / 2 : EReal) + (ε / 2 : EReal) = (ε : EReal) := by
    have hhalfE' : (((ε / 2 + ε / 2 : ℝ)) : EReal) = (ε : EReal) := by
      exact congrArg (fun t : ℝ => (t : EReal)) hhalf
    simpa only [EReal.coe_add] using hhalfE'
  -- Spend the smoothing budget at `yBar` on the real side before coercing once to `EReal`.
  have hpoint_real : φ yBar ≤ φμ yBar + ε / 2 := by
    linarith
  have hpoint :
      (φ yBar : EReal) ≤ (φμ yBar : EReal) + (ε / 2 : EReal) := by
    have hpoint' : (φ yBar : EReal) ≤ ((φμ yBar + ε / 2 : ℝ) : EReal) := by
      exact_mod_cast hpoint_real
    simpa [EReal.coe_add] using hpoint'
  -- Add the remaining `ε / 2` coming from the smoothed approximate-minimizer certificate.
  have hsmoothed_add :
      (φμ yBar : EReal) + (ε / 2 : EReal) ≤
        (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue +
          ((ε / 2 : EReal) + (ε / 2 : EReal)) := by
    -- Reassociate the certificate inequality so the half-budget identity can close the step.
    simpa [add_assoc, add_comm, add_left_comm] using
      add_le_add_left hsmoothed.2 (ε / 2 : EReal)
  calc
    (φ yBar : EReal) ≤ (φμ yBar : EReal) + (ε / 2 : EReal) := hpoint
    _ ≤ (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue +
        ((ε / 2 : EReal) + (ε / 2 : EReal)) := hsmoothed_add
    _ = (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue + ε := by
      rw [hhalfE]

/-- Helper for Proposition 6.37: the canonical choice `μ = ε / (2 log n)` spends exactly half of
the final accuracy budget. -/
private lemma canonical_mu_budget_eq_half_epsilon
    {n : ℕ} {ε : ℝ} (hlogn : Real.log (n : ℝ) ≠ 0) :
    ((ε / (2 * Real.log (n : ℝ))) * Real.log (n : ℝ)) = ε / 2 := by
  -- Clear the nonzero denominator and simplify the resulting scalar identity.
  field_simp [hlogn]

/-- Proposition 6.37: if `φμ` is a smoothing of `φ` on `Q` satisfying
`φμ(y) ≤ φ(y)` for every feasible `y` and `φ(yBar) ≤ φμ(yBar) + μ log n` at the feasible point
`yBar`, then any `ε / 2`-approximate minimizer of the smoothed problem is an `ε`-approximate
minimizer of the original problem whenever `μ log n ≤ ε / 2`. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {μ ε : ℝ} {yBar : X}
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper : φ yBar ≤ φμ yBar + μ * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar)
    (hμ_budget : μ * Real.log (n : ℝ) ≤ ε / 2) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := by
  -- First bound the certificate value by the smoothed optimal value plus the full `ε` budget.
  have hcertificate :
      (φ yBar : EReal) ≤ (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue + ε :=
    certificate_value_le_smoothed_optimalValue_add_epsilon happrox_upper hsmoothed hμ_budget
  rw [SetConstrainedMinimizationProblem.isApproximateMinimizer_iff] at hsmoothed ⊢
  refine ⟨hsmoothed.1, ?_⟩
  -- Then replace the smoothed optimal value by the larger original optimal value.
  have hoptimal :
      (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue ≤
        (SetConstrainedMinimizationProblem.mk Q φ).optimalValue :=
    smoothed_optimalValue_le_original_optimalValue happrox_lower
  -- Reorder the final `EReal` addition so the optimal-value comparison matches the target shape.
  have hoptimal_add :
      (SetConstrainedMinimizationProblem.mk Q φμ).optimalValue + ε ≤
        (SetConstrainedMinimizationProblem.mk Q φ).optimalValue + ε := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hoptimal (ε : EReal)
  exact hcertificate.trans hoptimal_add

-- Proof sketch: under `log n ≠ 0`, the special choice `μ = ε / (2 log n)` gives
-- `μ log n = ε / 2`, so the previous theorem applies directly.
/-- Choosing `μ = ε / (2 log n)` with `log n ≠ 0` forces the smoothing budget to equal `ε / 2`,
so if the lower smoothing estimate holds on `Q` and the upper estimate is available at `yBar`
with that specialized parameter, then an `ε / 2`-approximate minimizer of the smoothed problem is
already an `ε`-approximate minimizer of the original problem. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality_with_canonical_mu
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {ε : ℝ} {yBar : X}
    (hlogn : Real.log (n : ℝ) ≠ 0)
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper :
      φ yBar ≤ φμ yBar + (ε / (2 * Real.log (n : ℝ))) * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := by
  -- The canonical smoothing parameter saturates the admissible budget in the previous theorem.
  have hμ_budget :
      (ε / (2 * Real.log (n : ℝ))) * Real.log (n : ℝ) ≤ ε / 2 := by
    rw [canonical_mu_budget_eq_half_epsilon hlogn]
  exact isApproximateMinimizer_of_smoothedObjective_suboptimality
    happrox_lower happrox_upper hsmoothed hμ_budget

end
