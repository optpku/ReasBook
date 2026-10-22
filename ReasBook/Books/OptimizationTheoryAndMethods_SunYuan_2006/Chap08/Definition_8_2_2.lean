/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

noncomputable section

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: first-order linearized feasibility for constrained optimization problems
-- * inspected owners:
--   `ConstrainedOptimizationProblem.activeConstraintIndexSet` from `Definition_8_1_1`
--   mathlib's `fderiv`
--   `ConstrainedOptimizationProblem.LicqAt` from `Definition_8_2_10`
--   `ConstrainedOptimizationProblem.linearizedNullConstraintDirections`
--   from `Definition_8_3_2`
-- * owner abstraction chosen here:
--   `source-facing`: `IsLinearizedFeasibleDirectionAt`
--   `core/canonical`: `fderiv ℝ (problem.constraint i) xStar d` on `Point`
--   `bridge/view`: `euclideanObjective` and `euclideanConstraint` for downstream gradient files
-- * primitive data vs derived API:
--   the primitive first-order pairing is the Fréchet derivative of the original constraint on
--   `Point`; the Euclidean transport is derived bridge data and does not own the public pairing
--   API
-- This file keeps the source-facing feasible-direction predicate while reusing the chapter's
-- active-set owner and mathlib's derivative owner directly.

/-- Every constraint function of `problem` is differentiable at `xStar`. -/
def HasConstraintGradientsAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop :=
  ∀ i, DifferentiableAt ℝ (problem.constraint i) xStar

/-- Unfolding formula for `HasConstraintGradientsAt`. -/
@[simp] theorem hasConstraintGradientsAt_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.HasConstraintGradientsAt xStar ↔
      ∀ i, DifferentiableAt ℝ (problem.constraint i) xStar :=
  Iff.rfl

/-- Under `problem.HasConstraintGradientsAt xStar`, each constraint of `problem` is
differentiable at `xStar`. -/
theorem HasConstraintGradientsAt.differentiableAt
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point}
    (h : problem.HasConstraintGradientsAt xStar) (i : Fin m) :
    DifferentiableAt ℝ (problem.constraint i) xStar :=
  h i

/-- Every active constraint function of `problem` is differentiable at `xStar`. -/
def HasActiveConstraintGradientsAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop :=
  ∀ i ∈ problem.activeConstraintIndexSet xStar, DifferentiableAt ℝ (problem.constraint i) xStar

/-- Unfolding formula for `HasActiveConstraintGradientsAt`. -/
@[simp] theorem hasActiveConstraintGradientsAt_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.HasActiveConstraintGradientsAt xStar ↔
      ∀ i ∈ problem.activeConstraintIndexSet xStar,
        DifferentiableAt ℝ (problem.constraint i) xStar :=
  Iff.rfl

/-- Under `problem.HasActiveConstraintGradientsAt xStar`, each active constraint of `problem`
is differentiable at `xStar`. -/
theorem HasActiveConstraintGradientsAt.differentiableAt_of_mem
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point} {i : Fin m}
    (h : problem.HasActiveConstraintGradientsAt xStar)
    (hi : i ∈ problem.activeConstraintIndexSet xStar) :
    DifferentiableAt ℝ (problem.constraint i) xStar :=
  h i hi

/-- Differentiability of every constraint implies differentiability of every active constraint. -/
theorem HasConstraintGradientsAt.hasActiveConstraintGradientsAt
    {problem : ConstrainedOptimizationProblem n m E I} {xStar : Point}
    (h : problem.HasConstraintGradientsAt xStar) :
    problem.HasActiveConstraintGradientsAt xStar := by
  intro i hi
  exact h.differentiableAt i

/-- The objective of `problem`, transported to the Euclidean-space model used by mathlib's
gradient API. -/
def euclideanObjective
    (problem : ConstrainedOptimizationProblem n m E I) : EPoint → ℝ :=
  problem.objective ∘ EuclideanSpace.equiv (Fin n) ℝ

/-- The defining formula for `euclideanObjective`. -/
theorem euclideanObjective_eq
    (problem : ConstrainedOptimizationProblem n m E I) :
    problem.euclideanObjective =
      problem.objective ∘ EuclideanSpace.equiv (Fin n) ℝ :=
  rfl

/-- Evaluation formula for `euclideanObjective`. -/
@[simp] theorem euclideanObjective_apply
    (problem : ConstrainedOptimizationProblem n m E I) (x : EPoint) :
    problem.euclideanObjective x =
      problem.objective ((EuclideanSpace.equiv (Fin n) ℝ) x) :=
  rfl

/-- Differentiability of the original objective at `xStar` is equivalent to differentiability of
its Euclidean transport at `WithLp.toLp 2 xStar`. -/
theorem differentiableAt_euclideanObjective_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    DifferentiableAt ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) ↔
      DifferentiableAt ℝ problem.objective xStar := by
  have hcoord : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar) = xStar := by
    change (WithLp.toLp 2 xStar).ofLp = xStar
    exact WithLp.ofLp_toLp 2 xStar
  have hdiffIff :
      DifferentiableAt ℝ (problem.objective ∘ EuclideanSpace.equiv (Fin n) ℝ)
        (WithLp.toLp 2 xStar) ↔
        DifferentiableAt ℝ problem.objective
          ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) :=
    (EuclideanSpace.equiv (Fin n) ℝ).comp_right_differentiableAt_iff
  simpa [euclideanObjective, hcoord] using hdiffIff

/-- The `i`-th constraint of `problem`, transported to the Euclidean-space model used by
mathlib's gradient API. -/
def euclideanConstraint
    (problem : ConstrainedOptimizationProblem n m E I) (i : Fin m) : EPoint → ℝ :=
  problem.constraint i ∘ EuclideanSpace.equiv (Fin n) ℝ

/-- The defining formula for `euclideanConstraint`. -/
theorem euclideanConstraint_eq
    (problem : ConstrainedOptimizationProblem n m E I) (i : Fin m) :
    problem.euclideanConstraint i =
      problem.constraint i ∘ EuclideanSpace.equiv (Fin n) ℝ :=
  rfl

/-- Evaluation formula for `euclideanConstraint`. -/
@[simp] theorem euclideanConstraint_apply
    (problem : ConstrainedOptimizationProblem n m E I) (i : Fin m) (x : EPoint) :
    problem.euclideanConstraint i x =
      problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x) :=
  rfl

/-- Differentiability of the original `i`-th constraint at `xStar` is equivalent to
differentiability of its Euclidean transport at `WithLp.toLp 2 xStar`. -/
theorem differentiableAt_euclideanConstraint_iff
    (problem : ConstrainedOptimizationProblem n m E I) (i : Fin m) (xStar : Point) :
    DifferentiableAt ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) ↔
      DifferentiableAt ℝ (problem.constraint i) xStar := by
  have hcoord : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar) = xStar := by
    change (WithLp.toLp 2 xStar).ofLp = xStar
    exact WithLp.ofLp_toLp 2 xStar
  constructor
  · intro hdiffEuclidean
    have hdiffComp :
        DifferentiableAt ℝ ((problem.constraint i) ∘ EuclideanSpace.equiv (Fin n) ℝ)
          (WithLp.toLp 2 xStar) := by
      rwa [problem.euclideanConstraint_eq] at hdiffEuclidean
    have hdiffIff :
        DifferentiableAt ℝ ((problem.constraint i) ∘ EuclideanSpace.equiv (Fin n) ℝ)
          (WithLp.toLp 2 xStar) ↔
          DifferentiableAt ℝ (problem.constraint i)
            ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) :=
      (EuclideanSpace.equiv (Fin n) ℝ).comp_right_differentiableAt_iff
    have hdiff :
        DifferentiableAt ℝ (problem.constraint i)
          ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) :=
      hdiffIff.1 hdiffComp
    simpa [hcoord] using hdiff
  · intro hdiff
    have hdiff' :
        DifferentiableAt ℝ (problem.constraint i)
          ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) := by
      simpa [hcoord] using hdiff
    have hdiffIff :
        DifferentiableAt ℝ ((problem.constraint i) ∘ EuclideanSpace.equiv (Fin n) ℝ)
          (WithLp.toLp 2 xStar) ↔
          DifferentiableAt ℝ (problem.constraint i)
            ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) :=
      (EuclideanSpace.equiv (Fin n) ℝ).comp_right_differentiableAt_iff
    have hdiffComp :
        DifferentiableAt ℝ ((problem.constraint i) ∘ EuclideanSpace.equiv (Fin n) ℝ)
          (WithLp.toLp 2 xStar) :=
      hdiffIff.2 hdiff'
    rwa [problem.euclideanConstraint_eq]

/-- The first-order pairing `dᵀ ∇ c_i(xStar)` in the linearized feasibility conditions, owned
canonically by the Fréchet derivative of the original constraint on `Point`. -/
def linearizedConstraintPairing
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (i : Fin m) : ℝ :=
  fderiv ℝ (problem.constraint i) xStar d

/-- The point-space defining formula for `linearizedConstraintPairing`. -/
@[simp] theorem linearizedConstraintPairing_eq
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      fderiv ℝ (problem.constraint i) xStar d :=
  rfl

/-- `linearizedConstraintPairing` agrees with the Euclidean transport used by later
gradient-based Chapter 8 arguments. -/
theorem linearizedConstraintPairing_eq_euclideanConstraint
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      fderiv ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) :=
by
  have hcoordPoint (x : Point) : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  have hcomp :
      fderiv ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) =
        (fderiv ℝ (problem.constraint i) xStar).comp
          ((EuclideanSpace.equiv (Fin n) ℝ) : EPoint →L[ℝ] Point) := by
    have hcompEq :
        fderiv ℝ ((problem.constraint i) ∘ EuclideanSpace.equiv (Fin n) ℝ)
            (WithLp.toLp 2 xStar) =
          (fderiv ℝ (problem.constraint i) xStar).comp
            ((EuclideanSpace.equiv (Fin n) ℝ) : EPoint →L[ℝ] Point) :=
      (EuclideanSpace.equiv (Fin n) ℝ).comp_right_fderiv
    simpa [euclideanConstraint, hcoordPoint xStar] using
      hcompEq
  rw [linearizedConstraintPairing_eq]
  have happly :
      fderiv ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) =
        fderiv ℝ (problem.constraint i) xStar d := by
    simpa [ContinuousLinearMap.comp_apply, hcoordPoint d] using
      congrArg (fun g : EPoint →L[ℝ] ℝ ↦ g (WithLp.toLp 2 d)) hcomp
  simpa using happly.symm

/-- Chapter08 Definition 8.2.2: `d` is a linearized feasible direction of the feasible set of
`problem` at `xStar` when `xStar ∈ problem`, every active constraint of `problem` is
differentiable at `xStar`, every equality-constraint pairing `dᵀ ∇ c_i(xStar)` vanishes for
`i ∈ problem.eqIndices`, and every active inequality-constraint pairing is nonnegative for
`i ∈ problem.activeIneqIndexSet xStar`. -/
@[mk_iff isLinearizedFeasibleDirectionAt_iff]
class IsLinearizedFeasibleDirectionAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point) : Prop where
  feasiblePoint : xStar ∈ problem
  hasActiveConstraintGradientsAt : problem.HasActiveConstraintGradientsAt xStar
  eq_pairing_eq_zero :
    ∀ i ∈ problem.eqIndices, problem.linearizedConstraintPairing xStar d i = 0
  activeIneq_pairing_nonneg :
    ∀ i ∈ problem.activeIneqIndexSet xStar, 0 ≤ problem.linearizedConstraintPairing xStar d i

/-- `problem.IsLinearizedFeasibleDirectionAt xStar d` is a proposition. -/
instance instSubsingletonIsLinearizedFeasibleDirectionAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point) :
    Subsingleton (problem.IsLinearizedFeasibleDirectionAt xStar d) :=
  inferInstance

/-- The set of all linearized feasible directions at `xStar`. -/
def linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Set Point :=
  {d | problem.IsLinearizedFeasibleDirectionAt xStar d}

/-- Membership in `linearizedFeasibleDirectionSet` is exactly the linearized feasibility
predicate. -/
@[simp] theorem mem_linearizedFeasibleDirectionSet_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point) :
    d ∈ problem.linearizedFeasibleDirectionSet xStar ↔
      problem.IsLinearizedFeasibleDirectionAt xStar d :=
  Iff.rfl

/-- Explicit source-facing formula for membership in
`problem.linearizedFeasibleDirectionSet xStar`. -/
theorem mem_linearizedFeasibleDirectionSet_iff_explicit
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point) :
    d ∈ problem.linearizedFeasibleDirectionSet xStar ↔
      xStar ∈ problem ∧
        problem.HasActiveConstraintGradientsAt xStar ∧
          (∀ i ∈ problem.eqIndices, problem.linearizedConstraintPairing xStar d i = 0) ∧
            ∀ i ∈ problem.activeIneqIndexSet xStar,
              0 ≤ problem.linearizedConstraintPairing xStar d i := by
  rw [mem_linearizedFeasibleDirectionSet_iff, isLinearizedFeasibleDirectionAt_iff]

end ConstrainedOptimizationProblem
