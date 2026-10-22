/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Example_9_1.Objectives
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_12.GPCG

public section

noncomputable section

/-
Exercise 9.12.

The source exercise is procedural: apply the GPCG algorithm to the
two-dimensional test problem from `§9.4.2` for the shifted
Poisson-likelihood objective `(9.5)`.

The current repository snapshot already provides the backend objective
`example91LikelihoodFunctional` for `(9.5)` in the item-local foundation module
`Book.Ch9.Example_9_1.Objectives`. The concrete `§9.4.2` benchmark operator,
datum, initialization, projected-gradient step sizes, and stagewise quadratic
subproblem data for the GPCG inner conjugate-gradient phase are not yet
formalized, so this file remains a source-facing blocker that records the
intended exercise-level specialization through the item-owned GPCG owners
`GPCG.projectedStage`, `GPCG.cgRefinement`, `GPCG.iterates`, and
`GPCG.IsIterateSequence`.
-/

/- Exercise-level specialization of `(9.5)` to the two-dimensional `§9.4.2`
benchmark data. -/
namespace Exercise912

/-- The shifted Poisson-likelihood objective `(9.5)` for the two-dimensional
`§9.4.2` benchmark. -/
abbrev objective
    (forwardOperator942 : Matrix (Fin 2) (Fin 2) ℝ)
    (data942 : EuclideanSpace ℝ (Fin 2))
    (varianceShift942 regularization942 : ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  example91LikelihoodFunctional 2
    forwardOperator942 data942 varianceShift942 regularization942

/-- The GPCG outer iterates for Exercise 9.12, specialized to the
two-dimensional `§9.4.2` benchmark and the objective `(9.5)`. -/
abbrev iterates
    (projector942 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (quadraticMatrix942 :
      EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
    (linearTerm942 :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (projectedStepSizes942 : ℕ → ℝ)
    (innerSteps942 : ℕ → ℕ)
    (forwardOperator942 : Matrix (Fin 2) (Fin 2) ℝ)
    (data942 : EuclideanSpace ℝ (Fin 2))
    (varianceShift942 regularization942 : ℝ)
    (initialIterate942 : EuclideanSpace ℝ (Fin 2)) :
    ℕ → EuclideanSpace ℝ (Fin 2) :=
  GPCG.iterates projector942
    (objective forwardOperator942 data942 varianceShift942 regularization942)
    quadraticMatrix942 linearTerm942 projectedStepSizes942 innerSteps942
    initialIterate942

/-- A benchmark trajectory is valid when it satisfies the specialized GPCG
recurrence for Exercise 9.12. -/
abbrev isIterateSequence
    (projector942 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (quadraticMatrix942 :
      EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
    (linearTerm942 :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (projectedStepSizes942 : ℕ → ℝ)
    (innerSteps942 : ℕ → ℕ)
    (forwardOperator942 : Matrix (Fin 2) (Fin 2) ℝ)
    (data942 : EuclideanSpace ℝ (Fin 2))
    (varianceShift942 regularization942 : ℝ)
    (initialIterate942 : EuclideanSpace ℝ (Fin 2))
    (iterates942 : ℕ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  GPCG.IsIterateSequence projector942
    (objective forwardOperator942 data942 varianceShift942 regularization942)
    quadraticMatrix942 linearTerm942 projectedStepSizes942 innerSteps942
    initialIterate942 iterates942

end Exercise912

/- Exercise 9.12. The `§9.4.2` shifted-likelihood objective is the
two-dimensional specialization of `example91LikelihoodFunctional`. -/
#check Exercise912.objective

/- Exercise 9.12. Apply the GPCG algorithm to the two-dimensional `§9.4.2`
benchmark for the shifted Poisson-likelihood objective `(9.5)`.

The repository still lacks the concrete `§9.4.2` benchmark objects, the
projected-gradient step-size policy, and the stagewise quadratic-model
coefficients driving the inner conjugate-gradient phase. The `#check` below
therefore records the intended exercise-level specialization by applying the
source-facing GPCG iterate owner to the specialized `(9.5)` objective with all
remaining benchmark-specific stage data kept explicit. -/
#check Exercise912.iterates

/- Exercise 9.12. A benchmark trajectory is valid when it satisfies the GPCG
outer recurrence for the specialized `(9.5)` objective, with explicit
projected-gradient and inner conjugate-gradient stage data. -/
#check Exercise912.isIterateSequence

/- Backend anchors for the source-facing GPCG owner layer used above. -/
#check GPCG.projectedStage
#check GPCG.cgRefinement
#check GPCG.IsStep
#check GPCG.iterates
#check GPCG.IsIterateSequence

/- Backend owner for the shifted Poisson-likelihood objective `(9.5)`. -/
#check example91LikelihoodFunctional
