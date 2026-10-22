/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 5.4.8.9 lies in the Chapter 5 box-constrained `ℓ_p` approximation / epigraph-lift
domain.

Sampled owner declarations:
- `Set.Icc` and `Set.mem_Icc`, the canonical closed-interval API for the scalar box bounds;
- `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  ambient owner and optimal-value API for constrained minimization;
- `functionalConstraintOptimalValue_eq_standardFormOptimalValue` in
  `Chap05/Proposition_5_3_6_1`, the local Chapter 5 pattern for proving equality of optimal
  values by comparing two `SetConstrainedMinimizationProblem` owners;
- `lpApproximationObjective` in `Definition_5_4_8_20`, the upstream owner of the residual
  objective.

Best owner abstraction:
- source-facing: the textbook box-constrained `ℓ_p` problem and its epigraph reformulation;
- core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem`, with the box encoded
  directly by coordinatewise scalar interval membership `x j ∈ Set.Icc (α j) (β j)`;
- bridge/view: `lpApproximationProblem` and `lpApproximationEpigraphProblem`.

Primitive data:
- the box endpoints `α`, `β`;
- the lifted decision triple `(x, τ⁽⁰⁾, τ⁽¹⁾, …, τ⁽ᵐ⁾)`.

Derived API:
- the original problem owner `lpApproximationProblem`;
- the lifted owner `lpApproximationEpigraphProblem`;
- the companion owner lemmas expanding their feasible sets and objective evaluations;
- the canonical lift of a feasible `x` to an epigraph-feasible decision point;
- the bridge inequality comparing the original objective value with the epigraph slack
  `τ⁽⁰⁾` at a feasible lifted point.

This refinement removes the theorem-local box and epigraph exact-interface wrappers and states the
main result directly as equality of the canonical Chapter 1 optimal values of the original and
lifted problems.
-/

/-- The original box-constrained `ℓ_p` approximation problem, packaged in the canonical Chapter 1
owner. -/
def lpApproximationProblem (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := {x | ∀ j : Fin n, x j ∈ Set.Icc (α j) (β j)}
  objective := lpApproximationObjective p a b

/-- The original owner has exactly the coordinatewise scalar-interval box as its feasible set. -/
@[simp] theorem lpApproximationProblem_feasibleSet
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    (lpApproximationProblem p a b α β).feasibleSet =
      {x | ∀ j : Fin n, x j ∈ Set.Icc (α j) (β j)} :=
  rfl

/-- Evaluating the original owner returns the `ℓ_p` approximation objective. -/
@[simp] theorem lpApproximationProblem_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β x : E) :
    lpApproximationProblem p a b α β x = lpApproximationObjective p a b x :=
  rfl

/-- A point is feasible for the original owner exactly when each coordinate lies between the
corresponding box bounds. -/
@[simp] theorem mem_lpApproximationProblem_feasibleSet_iff
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β x : E} :
    x ∈ (lpApproximationProblem p a b α β).feasibleSet ↔
      ∀ j : Fin n, α j ≤ x j ∧ x j ≤ β j := by
  simp [lpApproximationProblem, Set.mem_Icc]

/-- A decision variable for the epigraph reformulation of the box-constrained `ℓ_p`
approximation problem consists of the original point `x`, the objective slack `τ⁽⁰⁾`, and the
residual slacks `τ⁽¹⁾, …, τ⁽ᵐ⁾`. -/
abbrev LpApproximationEpigraphPoint (n m : ℕ) :=
  EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ)

namespace LpApproximationEpigraphPoint

variable {n m : ℕ}

/-- The original optimization variable `x ∈ ℝⁿ`. -/
abbrev point (decision : LpApproximationEpigraphPoint n m) : EuclideanSpace ℝ (Fin n) :=
  decision.1

/-- The auxiliary objective variable `τ⁽⁰⁾`. -/
abbrev objectiveSlack (decision : LpApproximationEpigraphPoint n m) : ℝ :=
  decision.2.1

/-- The residual epigraph variables `τ⁽¹⁾, …, τ⁽ᵐ⁾`. -/
abbrev residualSlack (decision : LpApproximationEpigraphPoint n m) : Fin m → ℝ :=
  decision.2.2

end LpApproximationEpigraphPoint

open LpApproximationEpigraphPoint

/-- The canonical Chapter 1 owner of the epigraph reformulation of the box-constrained `ℓ_p`
approximation problem. -/
def lpApproximationEpigraphProblem (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ)
    (α β : E) : SetConstrainedMinimizationProblem (LpApproximationEpigraphPoint n m) where
  feasibleSet := {decision |
    (∀ i : Fin m, |⟪a i, decision.point⟫ - b i| ^ p ≤ decision.residualSlack i) ∧
      (∑ i : Fin m, decision.residualSlack i) ≤ decision.objectiveSlack ∧
      decision.point ∈ (lpApproximationProblem p a b α β).feasibleSet}
  objective := objectiveSlack

-- Proof sketch: unfold `lpApproximationEpigraphProblem`; membership is exactly the
-- conjunction of the residual epigraph inequalities, the sum constraint
-- `∑ τ⁽ⁱ⁾ ≤ τ⁽⁰⁾`, and the box constraint on `x`.
/-- Membership in the feasible set of `lpApproximationEpigraphProblem p a b α β` is exactly the
conjunction of the pointwise epigraph inequalities, the aggregate slack inequality, and the box
constraint from the original owner. -/
@[simp] theorem mem_lpApproximationEpigraphProblem_feasibleSet_iff
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β : E}
    {decision : LpApproximationEpigraphPoint n m} :
    decision ∈ (lpApproximationEpigraphProblem p a b α β).feasibleSet ↔
      (∀ i : Fin m, |⟪a i, decision.point⟫ - b i| ^ p ≤ decision.residualSlack i) ∧
        (∑ i : Fin m, decision.residualSlack i) ≤ decision.objectiveSlack ∧
        decision.point ∈ (lpApproximationProblem p a b α β).feasibleSet :=
  Iff.rfl

/-- Evaluating the epigraph owner returns the auxiliary objective slack `τ⁽⁰⁾`. -/
@[simp] theorem lpApproximationEpigraphProblem_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E)
    (decision : LpApproximationEpigraphPoint n m) :
    lpApproximationEpigraphProblem p a b α β decision = decision.objectiveSlack :=
  rfl

/-- At every feasible epigraph point, the original `ℓ_p` objective at the projected point is
bounded above by the lifted slack `τ⁽⁰⁾`. -/
theorem lpApproximationObjective_le_objectiveSlack_of_mem_feasibleSet
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β : E}
    {decision : LpApproximationEpigraphPoint n m}
    (hdecision : decision ∈ (lpApproximationEpigraphProblem p a b α β).feasibleSet) :
    lpApproximationObjective p a b decision.point ≤ decision.objectiveSlack := by
  rcases mem_lpApproximationEpigraphProblem_feasibleSet_iff.mp hdecision with ⟨hres, hsum, _⟩
  exact le_trans (Finset.sum_le_sum fun i _ ↦ hres i) hsum

/-- Any feasible point of the original box-constrained problem admits the canonical epigraph
lift obtained by taking residual slacks equal to the pointwise residual powers and the objective
slack equal to their sum. -/
theorem lpApproximationEpigraphLift_mem_feasibleSet
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β x : E}
    (hx : x ∈ (lpApproximationProblem p a b α β).feasibleSet) :
    (x, lpApproximationObjective p a b x, fun i : Fin m ↦ |⟪a i, x⟫ - b i| ^ p) ∈
      (lpApproximationEpigraphProblem p a b α β).feasibleSet := by
  rw [mem_lpApproximationEpigraphProblem_feasibleSet_iff]
  refine ⟨?_, ?_, hx⟩
  · intro i
    exact le_rfl
  · simp [lpApproximationObjective]

-- Proof sketch: map any feasible `x` for the original box-constrained problem to the epigraph
-- point with `τ⁽ⁱ⁾ = |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p` and
-- `τ⁽⁰⁾ = ∑ᵢ |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`, which preserves the objective value. Conversely, project any
-- feasible epigraph point to its `x`-coordinate; the inequalities
-- `|⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p ≤ τ⁽ⁱ⁾` and `∑ᵢ τ⁽ⁱ⁾ ≤ τ⁽⁰⁾` imply that the original objective value is
-- bounded above by `τ⁽⁰⁾`. Comparing the two induced lower bounds on attainable objective values
-- yields equality of the infima.
/-- Theorem 5.4.8.9: the box-constrained `ℓ_p` approximation problem
`min_{α ≤ x ≤ β} \sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p` and its epigraph
reformulation with variables `τ⁽⁰⁾, τ⁽¹⁾, …, τ⁽ᵐ⁾` have the same canonical Chapter 1 optimal
value. -/
theorem lpApproximation_optimalValue_eq_epigraphOptimalValue
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    (lpApproximationProblem p a b α β).optimalValue =
      (lpApproximationEpigraphProblem p a b α β).optimalValue := by
  let problem := lpApproximationProblem p a b α β
  let epigraphProblem := lpApproximationEpigraphProblem p a b α β
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨decision, hdecision, rfl⟩
    rcases mem_lpApproximationEpigraphProblem_feasibleSet_iff.mp hdecision with ⟨_, _, hx⟩
    have hpoint : decision.point ∈ problem.feasibleSet := by
      simpa [problem] using hx
    have hproblem :
        problem.optimalValue ≤ (problem decision.point : EReal) := by
      simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hpoint
    have hvalue :
        (problem decision.point : EReal) ≤ (decision.objectiveSlack : EReal) := by
      have hvalue' :
          lpApproximationObjective p a b decision.point ≤ decision.objectiveSlack :=
        lpApproximationObjective_le_objectiveSlack_of_mem_feasibleSet hdecision
      exact_mod_cast hvalue'
    simpa [problem, epigraphProblem] using hproblem.trans hvalue
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    let decision : LpApproximationEpigraphPoint n m :=
      (x, lpApproximationObjective p a b x, fun i : Fin m ↦ |⟪a i, x⟫ - b i| ^ p)
    have hpoint : x ∈ problem.feasibleSet := by
      simpa [problem] using hx
    have hdecision : decision ∈ epigraphProblem.feasibleSet := by
      simpa [decision, epigraphProblem] using
        lpApproximationEpigraphLift_mem_feasibleSet hpoint
    have hepigraph :
        epigraphProblem.optimalValue ≤ (epigraphProblem decision : EReal) := by
      exact epigraphProblem.optimalValue_le_of_mem_feasibleSet hdecision
    simpa [problem, epigraphProblem, decision] using hepigraph

end
