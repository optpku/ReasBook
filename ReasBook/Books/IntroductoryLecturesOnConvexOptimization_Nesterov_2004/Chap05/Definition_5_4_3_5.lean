/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 5.4.3.5 lies in the Chapter 5 QCQP / logarithmic-barrier domain.

Sampled owner declarations in this domain:
* `strictConstraintSet` and `logarithmicBarrier` from `Chap01/Proposition_1_10_17`, the
  canonical finite-constraint strict-domain barrier owners;
* `analyticBarrierDomain`, `AnalyticBarrierPoint`, `analyticBarrier`, and
  `analyticBarrierAmbient` from `Chap03/Definition_3_62`, the chapter precedent for keeping the
  barrier on its strict-domain subtype and any raw formula only as a bridge;
* `QuadraticallyConstrainedQuadraticOptimizationProblem.feasibleSet` and
  `QuadraticallyConstrainedQuadraticOptimizationProblem.epigraphFeasibleSet` from
  `Definition_5_4_3_4`, the chapter QCQP owner and its nonstrict feasible-region API.

Source/core/bridge triage:
* source-facing: the strict QCQP feasible set, the strict QCQP epigraph feasible set, and the
  textbook QCQP epigraph logarithmic barrier;
* core/canonical: `strictConstraintSet` and `logarithmicBarrier` on the QCQP-induced slack
  families;
* bridge/view: the ambient formula `epigraphLogarithmicBarrierAmbient`.

Primitive data:
* the QCQP owner `problem`.

Derived API:
* the internal continuous slack families induced by `problem`;
* strict feasibility and strict epigraph feasibility;
* the strict-domain barrier
  `epigraphLogarithmicBarrier :
    C(problem.StrictEpigraphFeasiblePoint, ℝ)`;
* the raw-pair ambient bridge `epigraphLogarithmicBarrierAmbient`.

This file therefore extends the existing QCQP owner directly, rather than introducing a parallel
public raw barrier API in terms of arbitrary `q₀`, `q`, and `β`. -/

namespace QuadraticallyConstrainedQuadraticOptimizationProblem

private theorem quadraticFunction_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin (m + 1)) :
    Continuous (problem.quadraticFunction i) := by
  have hsymm : (problem.A i).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using (problem.A_posSemidef i).isHermitian
  exact
    (symmetric_quadratic_contDiff_and_gradient_lipschitz
      (problem.α i) (problem.a i) (problem.A i) hsymm).1.continuous

private theorem objective_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Continuous problem.objective :=
  problem.quadraticFunction_continuous 0

private theorem constraintFunction_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin m) :
    Continuous (problem.constraintFunction i) :=
  problem.quadraticFunction_continuous i.succ

private def strictFeasibleConstraints
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Fin m → C(Eₙ, ℝ) :=
  fun i ↦
    { toFun := problem.constraintFunction i
      continuous_toFun := problem.constraintFunction_continuous i } -
      ContinuousMap.const Eₙ (problem.β i)

/-- The strict feasible set `{x | qᵢ(x) < βᵢ}` of the QCQP constraints. -/
def strictFeasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Set Eₙ :=
  strictConstraintSet problem.strictFeasibleConstraints

/-- Membership in `problem.strictFeasibleSet` is exactly the family of strict constraint
inequalities `qᵢ(x) < βᵢ`. -/
@[simp] theorem mem_strictFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    x ∈ problem.strictFeasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x < problem.β i := by
  simp [strictFeasibleSet, strictFeasibleConstraints]

private def strictEpigraphConstraints
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Fin (m + 1) → C(Eₙ × ℝ, ℝ) :=
  Fin.cases
    { toFun := fun p ↦ problem.objective p.1 - p.2
      continuous_toFun := (problem.objective_continuous.comp continuous_fst).sub continuous_snd }
    (fun i ↦
      { toFun := fun p ↦ problem.constraintFunction i p.1 - problem.β i
        continuous_toFun :=
          ((problem.constraintFunction_continuous i).comp continuous_fst).sub continuous_const })

/-- The strict feasible region of the QCQP epigraph formulation, cut out by the positive slacks
`τ - q₀(x)` and `βᵢ - qᵢ(x)`. -/
def strictEpigraphFeasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Set (Eₙ × ℝ) :=
  strictConstraintSet problem.strictEpigraphConstraints

/-- The subtype of points in the strict QCQP epigraph barrier domain. This is the natural owner
carrier for the QCQP epigraph barrier. -/
abbrev StrictEpigraphFeasiblePoint
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :=
  {p : Eₙ × ℝ // p ∈ problem.strictEpigraphFeasibleSet}

-- Proof sketch: unfold `strictEpigraphFeasibleSet`; membership is exactly the conjunction of the
-- strict epigraph slack inequality for `q₀` and the strict slack inequalities for each `qᵢ`.
/-- Membership in the QCQP strict epigraph feasible region means that all defining slacks are
strictly positive. -/
theorem mem_strictEpigraphFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (p : Eₙ × ℝ) :
    p ∈ problem.strictEpigraphFeasibleSet ↔
      0 < p.2 - problem.objective p.1 ∧
        ∀ i : Fin m, 0 < problem.β i - problem.constraintFunction i p.1 := by
  simp [strictEpigraphFeasibleSet, strictEpigraphConstraints, Fin.forall_fin_succ, sub_pos]

/-- Definition 5.4.3.5: the logarithmic barrier for the QCQP epigraph feasible region
`{(x, τ) | 0 < τ - q₀(x) ∧ ∀ i, 0 < βᵢ - qᵢ(x)}` is
`(x, τ) ↦ -log (τ - q₀(x)) - ∑ i, log (βᵢ - qᵢ(x))`. -/
def epigraphLogarithmicBarrier
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    C(problem.StrictEpigraphFeasiblePoint, ℝ) :=
  logarithmicBarrier problem.strictEpigraphConstraints

/-- The ambient formula underlying `problem.epigraphLogarithmicBarrier`. It is only a bridge
view; the owner barrier is `problem.epigraphLogarithmicBarrier` on
`problem.StrictEpigraphFeasiblePoint`. -/
def epigraphLogarithmicBarrierAmbient
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Eₙ × ℝ → ℝ :=
  let _ : Fintype (Fin (m + 1)) := instFintype_nesterov
  fun p ↦
    -∑ j : Fin (m + 1), Real.log (-problem.strictEpigraphConstraints j p)

-- Proof sketch: unfold `epigraphLogarithmicBarrier`; the displayed expression is exactly its
-- defining formula.
/-- Evaluating the QCQP epigraph logarithmic barrier reproduces the sum of the negative
logarithms of the strict slacks. -/
@[simp] theorem epigraphLogarithmicBarrier_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (p : problem.StrictEpigraphFeasiblePoint) :
    problem.epigraphLogarithmicBarrier p =
      problem.epigraphLogarithmicBarrierAmbient p := by
  rw [epigraphLogarithmicBarrierAmbient, epigraphLogarithmicBarrier]
  exact logarithmicBarrier_apply (f := problem.strictEpigraphConstraints) (x := p)

-- Proof sketch: rewrite the pair `p` as `(x, τ)` and unfold
-- `epigraphLogarithmicBarrierAmbient`; this is exactly the textbook formula.
/-- The QCQP epigraph logarithmic barrier has the textbook coordinate formula
`F(x, τ) = -log (τ - q₀(x)) - \sum_i log (βᵢ - qᵢ(x))`. -/
theorem epigraphLogarithmicBarrier_apply_pair
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (x : Eₙ) (τ : ℝ)
    (h : (x, τ) ∈ problem.strictEpigraphFeasibleSet) :
    problem.epigraphLogarithmicBarrier ⟨(x, τ), h⟩ =
      -Real.log (τ - problem.objective x) -
        ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i x) := by
  letI : Fintype (Fin (m + 1)) := instFintype_nesterov
  rw [problem.epigraphLogarithmicBarrier_apply, epigraphLogarithmicBarrierAmbient]
  have huniv :
      (@Finset.univ (Fin (m + 1)) this) =
        @Finset.univ (Fin (m + 1)) (Fin.fintype (m + 1)) := by
    ext j
    simp
  have hsum :
      ∑ j : Fin (m + 1), Real.log (-(problem.strictEpigraphConstraints j (x, τ))) =
        Real.log (τ - problem.objective x) +
          ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i x) := by
    simpa [huniv, strictEpigraphConstraints, sub_eq_add_neg, add_comm] using
      (Fin.sum_univ_succ
        (f := fun j : Fin (m + 1) ↦ Real.log (-(problem.strictEpigraphConstraints j (x, τ)))))
  simpa [sub_eq_add_neg, add_comm] using congrArg Neg.neg hsum

end QuadraticallyConstrainedQuadraticOptimizationProblem

end
