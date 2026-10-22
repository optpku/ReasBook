/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_2.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_10.LeastSquares
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_11.Hessians

public section

noncomputable section

namespace Exercise911

/-- Exercise 9.11 (1). The projected Newton iterate-sequence predicate for the
`§9.4.1` benchmark from Exercise 9.10, keeping the least-squares objective
`(9.2)` and replacing gradient projection by projected Newton. -/
abbrev leastSquaresIsIterateSequence
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n))
    (searchDirections941 : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ProjectedNewton.IsIterateSequence projector941
    (Exercise910.objective n forwardOperator941 data941 regularization941)
    (leastSquaresHessianMatrix n forwardOperator941 regularization941)
    stepSizes941 initialIterate941 searchDirections941

/-- `leastSquaresIsIterateSequence` is exactly the Exercise 9.10 benchmark
specialization of `ProjectedNewton.IsIterateSequence` with the least-squares
objective `(9.2)` and its constant Hessian bridge. -/
theorem leastSquaresIsIterateSequence_iff
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n))
    (searchDirections941 : ℕ → EuclideanSpace ℝ (Fin n)) :
    leastSquaresIsIterateSequence
        n projector941 stepSizes941 forwardOperator941 data941
        regularization941 initialIterate941 searchDirections941 ↔
      ProjectedNewton.IsIterateSequence projector941
        (Exercise910.objective n forwardOperator941 data941 regularization941)
        (leastSquaresHessianMatrix n forwardOperator941 regularization941)
        stepSizes941 initialIterate941 searchDirections941 := Iff.rfl

/-- Exercise 9.11 (2). The projected Newton iterate-sequence predicate on the
same `§9.4.1` benchmark data, with the least-squares objective `(9.2)` replaced
by the shifted Poisson-likelihood objective `(9.5)`. -/
abbrev likelihoodIsIterateSequence
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (varianceShift941 regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n))
    (searchDirections941 : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ProjectedNewton.IsIterateSequence projector941
    (example91LikelihoodFunctional n forwardOperator941 data941
      varianceShift941 regularization941)
    (likelihoodHessianMatrix n forwardOperator941 data941
      varianceShift941 regularization941)
    stepSizes941 initialIterate941 searchDirections941

/-- `likelihoodIsIterateSequence` is exactly the Exercise 9.11 projected Newton
specialization using the canonical shifted Poisson-likelihood objective owner
`example91LikelihoodFunctional` for `(9.5)` and the Hessian bridge
`Kᵀ D(f) K + α I`. -/
theorem likelihoodIsIterateSequence_iff
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (varianceShift941 regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n))
    (searchDirections941 : ℕ → EuclideanSpace ℝ (Fin n)) :
    likelihoodIsIterateSequence
        n projector941 stepSizes941 forwardOperator941 data941
        varianceShift941 regularization941 initialIterate941
        searchDirections941 ↔
      ProjectedNewton.IsIterateSequence projector941
        (example91LikelihoodFunctional n forwardOperator941 data941
          varianceShift941 regularization941)
        (likelihoodHessianMatrix n forwardOperator941 data941
          varianceShift941 regularization941)
        stepSizes941 initialIterate941 searchDirections941 := Iff.rfl

end Exercise911

/- Source-facing check for the clause (1) projected-Newton specialization of
the `§9.4.1` least-squares benchmark from Exercise 9.10. -/
#check Exercise911.leastSquaresIsIterateSequence

/- Backend owner for the shifted Poisson-likelihood objective `(9.5)` on the
inherited `§9.4.1` benchmark surface. -/
#check example91LikelihoodFunctional

/- Source-facing check for the clause (2) projected-Newton specialization after
replacing the least-squares objective `(9.2)` by `(9.5)`. -/
#check Exercise911.likelihoodIsIterateSequence

/- Backend anchors for the projected Newton owner, the inherited Exercise 9.10
least-squares objective, and the concrete Hessian bridges used above. -/
#check ProjectedNewton.IsIterateSequence
#check Exercise910.objective
#check Exercise911.leastSquaresHessianMatrix
#check Exercise911.likelihoodHessianMatrix
