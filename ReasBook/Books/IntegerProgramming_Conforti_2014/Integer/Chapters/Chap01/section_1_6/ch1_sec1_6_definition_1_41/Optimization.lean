/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Real.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_16.Algorithm
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_17.PolynomialBound
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem

@[expose] public section

universe u v

/-- An optimization problem may seek either the greatest or the least attainable objective value.
-/
inductive OptimizationSense where
  | max
  | min

/-- An optimization problem packages instances, feasible solutions, encoding-size data, an
objective-value function, and a choice of optimization direction. The theorem-level docstring
below carries the exact task label used by the proof pipeline for this file. -/
structure OptimizationProblem where
  Instance : Type u
  encodingSize : Instance → Nat
  Solution : Instance → Type v
  solutionEncodingSize : (i : Instance) → Solution i → Nat
  solutionExists : ∀ i : Instance, Nonempty (Solution i)
  objectiveValue : (i : Instance) → Solution i → ℝ
  goal : OptimizationSense

namespace OptimizationProblem

/-- Build an `OptimizationProblem` from its explicit instance family, feasible-solution family,
encoding-size data, objective-value function, and optimization sense. -/
def ofData
    (Instance : Type u)
    (encodingSize : Instance → Nat)
    (Solution : Instance → Type v)
    (solutionEncodingSize : (i : Instance) → Solution i → Nat)
    (solutionExists : ∀ i : Instance, Nonempty (Solution i))
    (objectiveValue : (i : Instance) → Solution i → ℝ)
    (goal : OptimizationSense) :
    OptimizationProblem where
  Instance := Instance
  encodingSize := encodingSize
  Solution := Solution
  solutionEncodingSize := solutionEncodingSize
  solutionExists := solutionExists
  objectiveValue := objectiveValue
  goal := goal

/-- Forgetting the objective data of `P` yields the underlying answer-family problem whose
admissible answers are the feasible solutions of each optimization instance. -/
def toProblem (P : OptimizationProblem) : Problem :=
  Problem.ofAnswerFamily P.Instance P.Solution

/-- Forgetting the objective data of an optimization problem built by `ofData` recovers the
answer-family problem on the same instance and feasible-solution families. -/
theorem ofData_toProblem
    (Instance : Type u)
    (encodingSize : Instance → Nat)
    (Solution : Instance → Type v)
    (solutionEncodingSize : (i : Instance) → Solution i → Nat)
    (solutionExists : ∀ i : Instance, Nonempty (Solution i))
    (objectiveValue : (i : Instance) → Solution i → ℝ)
    (goal : OptimizationSense) :
    (ofData
        Instance
        encodingSize
        Solution
        solutionEncodingSize
        solutionExists
        objectiveValue
        goal).toProblem =
      Problem.ofAnswerFamily Instance Solution := by
  -- Expanding both definitions shows that the forgetful view keeps exactly the instance
  -- family and feasible-solution family from the original data.
  rfl

/-- Expanding `P.toProblem` recovers the answer-family problem whose admissible answers are the
feasible solutions of `P`. -/
theorem toProblem_def
    (P : OptimizationProblem) :
    P.toProblem = Problem.ofAnswerFamily P.Instance P.Solution := by
  -- The definition of `toProblem` is already the desired answer-family problem.
  rfl

/-- A feasible solution `s` is within factor `α` of a feasible comparison solution `s'` when its
objective value satisfies the standard multiplicative approximation comparison for the goal of
`P`. Quantifying this relation over all feasible comparison solutions expresses comparison with
the optimum value. -/
def withinFactor
    (P : OptimizationProblem)
    (α : ℝ)
    (i : P.Instance)
    (s s' : P.Solution i) : Prop :=
  match P.goal with
  | OptimizationSense.max => P.objectiveValue i s' ≤ α * P.objectiveValue i s
  | OptimizationSense.min => P.objectiveValue i s ≤ α * P.objectiveValue i s'

/-- If `P` is a maximization problem, `P.withinFactor α i s s'` means that `s` attains a value
whose `α`-multiple dominates the value attained by `s'`. -/
theorem withinFactor_max_iff
    (P : OptimizationProblem)
    (α : ℝ)
    (i : P.Instance)
    (s s' : P.Solution i)
    (hgoal : P.goal = OptimizationSense.max) :
    P.withinFactor α i s s' ↔
      P.objectiveValue i s' ≤ α * P.objectiveValue i s := by
  -- Rewriting the optimization sense selects the maximization branch of `withinFactor`.
  simp [OptimizationProblem.withinFactor, hgoal]

/-- If `P` is a minimization problem, `P.withinFactor α i s s'` means that `s` has value at most
`α` times the value attained by `s'`. -/
theorem withinFactor_min_iff
    (P : OptimizationProblem)
    (α : ℝ)
    (i : P.Instance)
    (s s' : P.Solution i)
    (hgoal : P.goal = OptimizationSense.min) :
    P.withinFactor α i s s' ↔
      P.objectiveValue i s ≤ α * P.objectiveValue i s' := by
  -- Rewriting the optimization sense selects the minimization branch of `withinFactor`.
  simp [OptimizationProblem.withinFactor, hgoal]

/-- A feasible solution is optimal for `P` when it is within factor `1` of every feasible
comparison solution for the same instance. -/
def IsOptimalSolution
    (P : OptimizationProblem)
    (i : P.Instance)
    (s : P.Solution i) : Prop :=
  ∀ s' : P.Solution i, P.withinFactor 1 i s s'

/-- In a maximization problem, a factor-one comparison is exactly comparison with the
candidate's objective value. -/
theorem withinFactor_one_max_iff
    (P : OptimizationProblem)
    (i : P.Instance)
    (s s' : P.Solution i)
    (hgoal : P.goal = OptimizationSense.max) :
    P.withinFactor 1 i s s' ↔
      P.objectiveValue i s' ≤ P.objectiveValue i s := by
  -- Specialize the maximization computation rule, then remove multiplication by one.
  simpa only [one_mul] using
    (OptimizationProblem.withinFactor_max_iff P 1 i s s' hgoal)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_41/Optimization.lean.
If `P` is a maximization problem, `P.IsOptimalSolution i s` means that `s` has objective
value at least that of every feasible comparison solution. -/
theorem isOptimalSolution_max_iff
    (P : OptimizationProblem)
    (i : P.Instance)
    (s : P.Solution i)
    (hgoal : P.goal = OptimizationSense.max) :
    P.IsOptimalSolution i s ↔
      ∀ s' : P.Solution i, P.objectiveValue i s' ≤ P.objectiveValue i s := by
  -- Unfold optimality so that each feasible comparison can be handled independently.
  constructor
  · intro hs s'
    -- The factor-one computation rule turns the approximation comparison into domination.
    exact (P.withinFactor_one_max_iff i s s' hgoal).mp (hs s')
  · intro hs s'
    -- Conversely, domination supplies the required factor-one comparison for every solution.
    exact (P.withinFactor_one_max_iff i s s' hgoal).mpr (hs s')

/-- If `P` is a minimization problem, `P.IsOptimalSolution i s` means that `s` has objective
value at most that of every feasible comparison solution. -/
theorem isOptimalSolution_min_iff
    (P : OptimizationProblem)
    (i : P.Instance)
    (s : P.Solution i)
    (hgoal : P.goal = OptimizationSense.min) :
    P.IsOptimalSolution i s ↔
      ∀ s' : P.Solution i, P.objectiveValue i s ≤ P.objectiveValue i s' := by
  -- Unfolding optimality reduces the claim to the factor-`1` comparison in the
  -- minimization branch, and `simp` removes the `1 * _` normalization.
  simp [OptimizationProblem.IsOptimalSolution, OptimizationProblem.withinFactor, hgoal]

/-- An `α`-approximation algorithm for `P` is an algorithm for the feasible-solution family of
`P` whose runtime is polynomial in the instance encoding size and whose output is within factor
`α` of the optimum value, expressed by comparison with every feasible solution. -/
structure IsApproximationAlgorithm
    (P : OptimizationProblem)
    (α : ℝ)
    (A : Problem.Algorithm P.toProblem) : Prop where
  one_le_alpha : 1 ≤ α
  runtime_polynomial : Function.PolynomiallyBoundedByNat A.runTime P.encodingSize
  approximation_bound :
    ∀ i : P.Instance,
      ∀ s' : P.Solution i,
        P.withinFactor α i (A.solve i) s'

namespace IsApproximationAlgorithm

variable {P : OptimizationProblem} {α : ℝ} {A : Problem.Algorithm P.toProblem}

/-- Build `P.IsApproximationAlgorithm α A` from the three defining clauses: `α ≥ 1`,
polynomially bounded runtime, and the factor-`α` guarantee against every feasible comparison
solution. -/
def ofClauses
    (one_le_alpha : 1 ≤ α)
    (runtime_polynomial : Function.PolynomiallyBoundedByNat A.runTime P.encodingSize)
    (approximation_bound :
      ∀ i : P.Instance,
        ∀ s' : P.Solution i,
          P.withinFactor α i (A.solve i) s') :
    P.IsApproximationAlgorithm α A where
  one_le_alpha := one_le_alpha
  runtime_polynomial := runtime_polynomial
  approximation_bound := approximation_bound

end IsApproximationAlgorithm

end OptimizationProblem

end
