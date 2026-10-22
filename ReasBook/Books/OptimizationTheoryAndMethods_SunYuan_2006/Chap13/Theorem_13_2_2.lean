/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_2_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius

section

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin (me + mi))

-- Semantic recall: `lean_leansearch` timed out on this item. This file therefore follows the
-- verified local precedent from `Chapter13.Algorithm_13_2_1`, the mixed-constraint bridge pattern
-- from `Chapter09.Definition_9_1_extra_1`, and the accumulation-point KKT theorem shape from
-- `Chapter11.Theorem_11_5_5`.

namespace LinearTrustRegionProblem

/-- The combined Chapter 8 constraint family attached to `problem` uses the first `me` indices
for the equality residuals `Aeqᵀ x - beq` and the remaining `mi` indices for the inequality
residuals `Aineqᵀ x - bineq`. -/
def standardConstraint
    (problem : LinearTrustRegionProblem n me mi) (i : Fin (me + mi)) (x : Point) : ℝ :=
  match finSumFinEquiv.symm i with
  | Sum.inl j =>
      Matrix.mulVec (Matrix.transpose problem.equalityMatrix) x.ofLp j - problem.equalityRhs j
  | Sum.inr j =>
      Matrix.mulVec (Matrix.transpose problem.inequalityMatrix) x.ofLp j -
        problem.inequalityRhs j

/-- On the equality side, `standardConstraint` is the residual `aᵢᵀ x - bᵢ`. -/
theorem standardConstraint_castAdd_eq
    (problem : LinearTrustRegionProblem n me mi) (i : Fin me) (x : Point) :
    problem.standardConstraint (Fin.castAdd mi i) x =
      Matrix.mulVec (Matrix.transpose problem.equalityMatrix) x.ofLp i - problem.equalityRhs i :=
  by
  simp [LinearTrustRegionProblem.standardConstraint]

/-- On the inequality side, `standardConstraint` is the residual `aᵢᵀ x - bᵢ`, so the canonical
constraint convention `0 ≤ cᵢ(x)` matches the source inequality `bᵢ ≤ aᵢᵀ x`. -/
theorem standardConstraint_natAdd_eq
    (problem : LinearTrustRegionProblem n me mi) (i : Fin mi) (x : Point) :
    problem.standardConstraint (Fin.natAdd me i) x =
      Matrix.mulVec (Matrix.transpose problem.inequalityMatrix) x.ofLp i -
        problem.inequalityRhs i := by
  simp [LinearTrustRegionProblem.standardConstraint]

/-- Forgetting the matrix presentation of `problem` produces the canonical Chapter 8 standard
constrained optimization owner with contiguous equality and inequality blocks. -/
def toStandardConstrainedOptimizationProblem
    (problem : LinearTrustRegionProblem n me mi) :
    StandardConstrainedOptimizationProblem n (me + mi) where
  eqCount := me
  eqCount_le := Nat.le_add_right me mi
  objective := fun x ↦ problem.objective (WithLp.toLp 2 x)
  constraint := fun i x ↦ problem.standardConstraint i (WithLp.toLp 2 x)

/-- Pulling the Chapter 8 feasible set back along the Euclidean-space coordinate equivalence
recovers the original linearly constrained feasible set. -/
theorem toStandardConstrainedOptimizationProblem_feasibleSet
    (problem : LinearTrustRegionProblem n me mi) :
    (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
        problem.toStandardConstrainedOptimizationProblem.feasibleSet =
      problem.feasibleSet := sorry

/-- Forgetting further to the Chapter 1 owner reuses the canonical Chapter 8 bridge. -/
abbrev toConstrainedOptimizationProblem
    (problem : LinearTrustRegionProblem n me mi) :
    ConstrainedOptimizationProblem n (me + mi)
      problem.toStandardConstrainedOptimizationProblem.eqIndices
      problem.toStandardConstrainedOptimizationProblem.ineqIndices :=
  problem.toStandardConstrainedOptimizationProblem.toConstrainedOptimizationProblem

/-- Evaluating the canonical constrained-problem bridge at `x.ofLp` recovers the source
objective value `problem.objective x`. -/
@[simp] theorem toConstrainedOptimizationProblem_objective_apply
    (problem : LinearTrustRegionProblem n me mi) (x : Point) :
    problem.toConstrainedOptimizationProblem.objective x.ofLp = problem.objective x := by
  change problem.objective (WithLp.toLp 2 x.ofLp) = problem.objective x
  simp

/-- Evaluating a bridge constraint at `x.ofLp` recovers the source linear residual. -/
@[simp] theorem toConstrainedOptimizationProblem_constraint_apply
    (problem : LinearTrustRegionProblem n me mi) (i : Fin (me + mi)) (x : Point) :
    problem.toConstrainedOptimizationProblem.constraint i x.ofLp =
      problem.standardConstraint i x := by
  change problem.standardConstraint i (WithLp.toLp 2 x.ofLp) = problem.standardConstraint i x
  simp

/-- A Euclidean-space point is feasible for `problem.toConstrainedOptimizationProblem` exactly
when it is feasible for the original linearly constrained problem. -/
@[simp] theorem mem_toConstrainedOptimizationProblem_iff
    (problem : LinearTrustRegionProblem n me mi) (x : Point) :
    x.ofLp ∈ problem.toConstrainedOptimizationProblem ↔
      x ∈ problem.feasibleSet := by
  change
      x ∈ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
          problem.toStandardConstrainedOptimizationProblem.feasibleSet ↔
        x ∈ problem.feasibleSet
  rw [problem.toStandardConstrainedOptimizationProblem_feasibleSet]

end LinearTrustRegionProblem

namespace LinearTrustRegionMethod

/-- `HasAccumulationPointAt method xStar` means that the iterate sequence generated by active
stages of Algorithm 13.2.1 has `xStar` as an accumulation point, encoded by a strictly monotone
active subsequence converging to `xStar`. -/
def HasAccumulationPointAt
    (method : LinearTrustRegionMethod n me mi) (xStar : Point) : Prop :=
  ∃ φ : ℕ → ℕ,
    StrictMono φ ∧
      (∀ k : ℕ, method.active (φ k)) ∧
      Tendsto (fun k : ℕ ↦ method.iterate (φ k)) atTop (nhds xStar)

/-- `HasAccumulationPointAt method xStar` unfolds to the convergent active-subsequence
characterization of `xStar` as an accumulation point of the iterate sequence. -/
theorem hasAccumulationPointAt_iff
    (method : LinearTrustRegionMethod n me mi) (xStar : Point) :
    method.HasAccumulationPointAt xStar ↔
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          (∀ k : ℕ, method.active (φ k)) ∧
          Tendsto (fun k : ℕ ↦ method.iterate (φ k)) atTop (nhds xStar) := sorry

/-- `HasAccumulationPoint method` means that the iterate sequence generated by Algorithm 13.2.1
has at least one accumulation point. -/
def HasAccumulationPoint (method : LinearTrustRegionMethod n me mi) : Prop :=
  ∃ xStar : Point, method.HasAccumulationPointAt xStar

/-- `HasAccumulationPoint method` unfolds to existence of an active-subsequence accumulation
point. -/
theorem hasAccumulationPoint_iff
    (method : LinearTrustRegionMethod n me mi) :
    method.HasAccumulationPoint ↔
      ∃ xStar : Point,
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
            (∀ k : ℕ, method.active (φ k)) ∧
            Tendsto (fun k : ℕ ↦ method.iterate (φ k)) atTop (nhds xStar) := sorry

end LinearTrustRegionMethod

/-- The canonical Chapter 8 constrained optimization owner attached to the linearly constrained
problem recorded by `method`. -/
abbrev LinearTrustRegionMethod.constrainedOptimizationProblem
    (method : LinearTrustRegionMethod n me mi) :=
  method.problem.toConstrainedOptimizationProblem

open LinearTrustRegionProblem

/-- The source assumption `(13.2.10)` on Algorithm 13.2.1, formalized here as a uniform
Frobenius-norm bound on the Hessian approximations `(B_k)` recorded by `method`. -/
def HasSourceAssumption13210
    (method : LinearTrustRegionMethod n me mi) : Prop :=
  ∃ hessianBound : ℝ,
    0 ≤ hessianBound ∧
      ∀ k : ℕ, ‖method.hessianApproximation k‖ ≤ hessianBound

/-- Unfolding `HasSourceAssumption13210 method` gives the existence of one common nonnegative
Frobenius-norm bound for all Hessian approximations `method.hessianApproximation k`. -/
theorem hasSourceAssumption13210_iff
    (method : LinearTrustRegionMethod n me mi) :
    HasSourceAssumption13210 method ↔
      ∃ hessianBound : ℝ,
        0 ≤ hessianBound ∧
          ∀ k : ℕ, ‖method.hessianApproximation k‖ ≤ hessianBound :=
  Iff.rfl

#print axioms standardConstraint
#print axioms toStandardConstrainedOptimizationProblem

/-- Chapter13 Theorem 13.2.2: assume `method.problem.objective` is continuously differentiable on
the feasible set of the original linearly constrained problem, and assume `(13.2.10)`,
formalized here by `HasSourceAssumption13210 method`. If the iterate sequence `{x_k}` generated
by Algorithm 13.2.1 has at least one accumulation point, then one accumulation point of the
sequence is a KKT point of the original linearly constrained optimization problem, formalized by
the canonical Chapter 8 predicate on `method.problem.toConstrainedOptimizationProblem`. -/
theorem linearTrustRegionMethod_existsKKTAccumulationPoint
    (method : LinearTrustRegionMethod n me mi)
    (hObjectiveC1 :
      ContDiffOn ℝ 1 method.problem.objective method.problem.feasibleSet)
    (h13210 : HasSourceAssumption13210 method)
    (hAccum : method.HasAccumulationPoint) :
    ∃ xStar : Point,
      method.HasAccumulationPointAt xStar ∧
      ∃ lamStar : Multiplier,
        method.constrainedOptimizationProblem.IsKKTPoint xStar.ofLp lamStar.ofLp :=
  sorry

/-- Companion to Theorem 13.2.2: the same accumulation-point KKT conclusion remains available in
contexts where ambient differentiability of `method.problem.objective` at feasible points has also
been recorded explicitly. -/
theorem linearTrustRegionMethod_existsKKTAccumulationPoint_of_differentiableAtFeasible
    (method : LinearTrustRegionMethod n me mi)
    (hObjectiveC1 :
      ContDiffOn ℝ 1 method.problem.objective method.problem.feasibleSet)
    (hObjectiveDifferentiableAtFeasible :
      ∀ x ∈ method.problem.feasibleSet, DifferentiableAt ℝ method.problem.objective x)
    (h13210 : HasSourceAssumption13210 method)
    (hAccum : method.HasAccumulationPoint) :
    ∃ xStar : Point,
      method.HasAccumulationPointAt xStar ∧
      ∃ lamStar : Multiplier,
        method.constrainedOptimizationProblem.IsKKTPoint xStar.ofLp lamStar.ofLp :=
  let _ :
      ∀ x ∈ method.problem.feasibleSet, DifferentiableAt ℝ method.problem.objective x :=
    hObjectiveDifferentiableAtFeasible
  linearTrustRegionMethod_existsKKTAccumulationPoint method hObjectiveC1 h13210 hAccum

end
