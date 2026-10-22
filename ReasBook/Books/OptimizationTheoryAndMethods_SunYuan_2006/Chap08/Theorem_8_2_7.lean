/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_6

noncomputable section

open scoped BigOperators Gradient

section Chapter08Theorem827

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

namespace ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.7 uses the source constraint qualification `(8.2.19)` at `xStar`,
namely the equality `SFD(xStar, problem.feasibleSet) = LFD(xStar, problem.feasibleSet)` between
the Chapter 8 sequential and linearized feasible direction sets. -/
def ConstraintQualificationAt
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop :=
  posTangentConeAt problem.feasibleSet xStar =
    problem.linearizedFeasibleDirectionSet xStar

/-- Unfolding formula for `problem.ConstraintQualificationAt xStar`. -/
@[simp] theorem constraintQualificationAt_iff
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.ConstraintQualificationAt xStar ↔
      posTangentConeAt problem.feasibleSet xStar =
        problem.linearizedFeasibleDirectionSet xStar :=
  Iff.rfl

/-- The Lagrangian of `problem` and `lamStar`, transported to the Euclidean-space model used by
mathlib's gradient API. -/
def euclideanLagrangian
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (lamStar : Fin m → ℝ) :
    EPoint → ℝ :=
  fun x ↦ problem.lagrangian ((EuclideanSpace.equiv (Fin n) ℝ) x) lamStar

/-- `problem.euclideanLagrangian lamStar` is the Euclidean transport of the canonical Chapter 8
Lagrangian `problem.lagrangian · lamStar`. -/
theorem euclideanLagrangian_eq
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (lamStar : Fin m → ℝ) :
    problem.euclideanLagrangian lamStar =
      fun x : EPoint ↦
        problem.lagrangian ((EuclideanSpace.equiv (Fin n) ℝ) x) lamStar :=
  rfl

/-- Evaluating `problem.euclideanLagrangian lamStar` amounts to evaluating the canonical
Lagrangian at the corresponding point in `Fin n → ℝ`. -/
@[simp] theorem euclideanLagrangian_apply
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (lamStar : Fin m → ℝ) (x : EPoint) :
    problem.euclideanLagrangian lamStar x =
      problem.lagrangian ((EuclideanSpace.equiv (Fin n) ℝ) x) lamStar :=
  rfl

/-- The source formula for `problem.euclideanLagrangian lamStar`. -/
theorem euclideanLagrangian_eq_objective_sub_sum
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (lamStar : Fin m → ℝ) :
    problem.euclideanLagrangian lamStar =
      fun x : EPoint ↦
        problem.objective ((EuclideanSpace.equiv (Fin n) ℝ) x) -
          ∑ i : Fin m, lamStar i * problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x) :=
  rfl

/-- A multiplier vector `lamStar` is a KKT multiplier at `xStar` for `problem` when `xStar` is
feasible, the multipliers on inequality constraints are nonnegative, the Euclidean transport of
the Lagrangian is stationary at `xStar`, and complementary slackness holds. The equality and
inequality constraint equations are recovered from feasibility. -/
@[mk_iff]
class IsKKTPoint
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) : Prop where
  feasible : xStar ∈ problem
  dualFeasible : ∀ i ∈ problem.ineqIndices, 0 ≤ lamStar i
  stationarity : ∇ (problem.euclideanLagrangian lamStar) (WithLp.toLp 2 xStar) = 0
  complementarySlackness :
    ∀ i ∈ problem.ineqIndices, lamStar i * problem.constraint i xStar = 0

/-- `problem.IsKKTPoint xStar lamStar` is a proposition. -/
instance instSubsingletonIsKKTPoint
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    Subsingleton (problem.IsKKTPoint xStar lamStar) :=
  inferInstance

/-- A KKT point satisfies all equality constraints. -/
theorem IsKKTPoint.eq_constraints
    {problem : _root_.ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ}
    (h : problem.IsKKTPoint xStar lamStar) :
    ∀ i ∈ problem.eqIndices, problem.constraint i xStar = 0 := by
  intro i hi
  exact (problem.mem_iff xStar).1 h.feasible |>.1 i hi

/-- A KKT point satisfies all inequality constraints. -/
theorem IsKKTPoint.ineq_constraints
    {problem : _root_.ConstrainedOptimizationProblem n m E I}
    {xStar : Point} {lamStar : Fin m → ℝ}
    (h : problem.IsKKTPoint xStar lamStar) :
    ∀ i ∈ problem.ineqIndices, 0 ≤ problem.constraint i xStar := by
  exact (problem.mem_iff xStar).1 h.feasible |>.2

/-- Helper for Chapter08 Theorem 8.2.7: under the source constraint qualification, every
linearized feasible direction has a nonnegative first-order objective derivative at the local
minimizer `xStar`. -/
theorem objective_fderiv_nonneg_of_mem_linearizedFeasibleDirectionSet
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_cq : problem.ConstraintQualificationAt xStar)
    (hd : d ∈ problem.linearizedFeasibleDirectionSet xStar) :
    0 ≤ fderiv ℝ problem.objective xStar d := by
  -- Route correction: reuse the textbook local-minimum argument on the tangent cone that CQ
  -- identifies with the linearized feasible-direction set.
  have hd_tangent : d ∈ posTangentConeAt problem.feasibleSet xStar := by
    rw [h_cq]
    exact hd
  have hnonneg_within :
      0 ≤ fderivWithin ℝ problem.objective problem.feasibleSet xStar d :=
    h_localMin.fderivWithin_nonneg hd_tangent
  have hd_real : d ∈ tangentConeAt ℝ problem.feasibleSet xStar :=
    tangentConeAt_mono_field hd_tangent
  have hderiv_eq :
      fderiv ℝ problem.objective xStar d =
        fderivWithin ℝ problem.objective problem.feasibleSet xStar d := by
    simpa using
      (h_objective.hasFDerivAt.hasFDerivWithinAt).unique_on
        (h_objective.differentiableWithinAt.hasFDerivWithinAt) hd_real
  rw [hderiv_eq]
  exact hnonneg_within

/-- Helper for Chapter08 Theorem 8.2.7: the Euclidean transport of the objective has the same
directional derivative as the original objective after converting the direction with
`WithLp.toLp 2`. -/
theorem euclideanObjective_fderiv_eq
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) :
    fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) =
      fderiv ℝ problem.objective xStar d := by
  have hcoordPoint (x : Point) : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  have hcomp :
      fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) =
        (fderiv ℝ problem.objective xStar).comp
          ((EuclideanSpace.equiv (Fin n) ℝ) : EPoint →L[ℝ] Point) := by
    have hcompEq :
        fderiv ℝ (problem.objective ∘ EuclideanSpace.equiv (Fin n) ℝ)
            (WithLp.toLp 2 xStar) =
          (fderiv ℝ problem.objective xStar).comp
            ((EuclideanSpace.equiv (Fin n) ℝ) : EPoint →L[ℝ] Point) :=
      (EuclideanSpace.equiv (Fin n) ℝ).comp_right_fderiv
    simpa [euclideanObjective, hcoordPoint xStar] using hcompEq
  simpa [ContinuousLinearMap.comp_apply, hcoordPoint d] using
    congrArg (fun g : EPoint →L[ℝ] ℝ ↦ g (WithLp.toLp 2 d)) hcomp

/-- Helper for Chapter08 Theorem 8.2.7: the Chapter 8 linearized-constraint pairing is exactly
the Euclidean inner product with the gradient of the transported constraint. -/
theorem linearizedConstraintPairing_eq_inner_euclideanConstraintGradient
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      inner ℝ (WithLp.toLp 2 d)
        (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) := by
  calc
    problem.linearizedConstraintPairing xStar d i
        = fderiv ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) := by
            exact problem.linearizedConstraintPairing_eq_euclideanConstraint xStar d i
    _ = inner ℝ (WithLp.toLp 2 d)
          (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) := by
            simpa using
              (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanConstraint i)
                (x := WithLp.toLp 2 d) (y := WithLp.toLp 2 xStar)).symm

/-- Helper for Chapter08 Theorem 8.2.7: after rewriting the source linearized-feasibility
conditions through the Euclidean gradient API, the strict-descent system `(8.2.25)-(8.2.27)` has
no solution. -/
theorem euclidean_linearized_descent_system_eq_empty_of_constraintQualificationAt
    (problem : _root_.ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_cq : problem.ConstraintQualificationAt xStar) :
    descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar) ∩
        {u |
          (∀ i ∈ problem.eqIndices,
            inner ℝ u (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) = 0) ∧
          ∀ i ∈ problem.activeIneqIndexSet xStar,
            0 ≤ inner ℝ u (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar))} =
      (∅ : Set EPoint) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  let d : Point := u.ofLp
  have hu_toLp : WithLp.toLp 2 d = u := by
    rfl
  have hd_linearized : d ∈ problem.linearizedFeasibleDirectionSet xStar := by
    -- The Euclidean gradient equalities/inequalities are exactly the textbook linearized
    -- feasibility conditions for `d`.
    rw [problem.mem_linearizedFeasibleDirectionSet_iff_explicit]
    refine ⟨hxStar, h_constraints.hasActiveConstraintGradientsAt, ?_, ?_⟩
    · intro i hi
      rw [problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i,
        hu_toLp]
      exact hu.2.1 i hi
    · intro i hi
      rw [problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i,
        hu_toLp]
      exact hu.2.2 i hi
  have hnonneg :
      0 ≤ fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) u := by
    rw [← hu_toLp, problem.euclideanObjective_fderiv_eq xStar d]
    exact
      problem.objective_fderiv_nonneg_of_mem_linearizedFeasibleDirectionSet
        xStar d h_localMin h_objective h_cq hd_linearized
  have hdesc :
      fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) u < 0 := by
    have hdesc_inner :
        inner ℝ u (gradient problem.euclideanObjective (WithLp.toLp 2 xStar)) < 0 :=
      (mem_descentDirections_iff problem.euclideanObjective (WithLp.toLp 2 xStar) u).1 hu.1
    simpa using hdesc_inner
  exact not_lt_of_ge hnonneg hdesc

/-- Helper for Chapter08 Theorem 8.2.7: the Euclidean Lagrangian gradient is the objective
gradient minus the multiplier-weighted constraint-gradient sum. -/
theorem gradient_euclideanLagrangian_eq_objective_sub_sum
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lambda : Fin m → ℝ)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    ∇ (problem.euclideanLagrangian lambda) (WithLp.toLp 2 xStar) =
      gradient problem.euclideanObjective (WithLp.toLp 2 xStar) -
        ∑ i : Fin m, lambda i • gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) := by
  let xStarE : EPoint := WithLp.toLp 2 xStar
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective xStarE := by
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective
  have hconstraintE :
      ∀ i : Fin m, DifferentiableAt ℝ (problem.euclideanConstraint i) xStarE := by
    intro i
    exact (problem.differentiableAt_euclideanConstraint_iff i xStar).2 (h_constraints i)
  have hlag_eq :
      problem.euclideanLagrangian lambda =
        problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x := by
    ext x
    -- Route correction: use the textbook Lagrangian formula on the transported point and then
    -- rewrite each transported owner by its evaluation lemma.
    rw [problem.euclideanLagrangian_apply, problem.lagrangian_eq]
    simp [problem.euclideanObjective_apply, problem.euclideanConstraint_apply]
  have hsum :
      fderiv ℝ (∑ i : Fin m, fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x) xStarE =
        ∑ i : Fin m, fderiv ℝ (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x) xStarE := by
    -- Normalize the finite derivative sum before translating it to gradients.
    exact
      (fderiv_sum
        (u := Finset.univ)
        (A := fun i : Fin m ↦ fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x)
        (x := xStarE)
        (fun i _ ↦ (hconstraintE i).const_mul (lambda i)))
  apply ext_inner_left ℝ
  intro y
  calc
    inner ℝ y (gradient (problem.euclideanLagrangian lambda) xStarE)
        = fderiv ℝ (problem.euclideanLagrangian lambda) xStarE y := by
            simpa using
              (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanLagrangian lambda)
                (x := y) (y := xStarE))
    _ = (fderiv ℝ problem.euclideanObjective xStarE -
          ∑ i : Fin m, fderiv ℝ (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x) xStarE) y := by
            -- Rewrite the Euclidean Lagrangian into the objective-minus-constraint-sum form.
            rw [hlag_eq]
            rw [fderiv_sub hobjectiveE]
            · rw [hsum]
            · exact DifferentiableAt.sum fun i _ ↦ (hconstraintE i).const_mul (lambda i)
    _ = inner ℝ y (gradient problem.euclideanObjective xStarE) -
          ∑ i : Fin m,
            inner ℝ y (lambda i • gradient (problem.euclideanConstraint i) xStarE) := by
            rw [sub_apply]
            rw [show
              (∑ i : Fin m, fderiv ℝ (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x)
                xStarE) y =
                ∑ i : Fin m,
                  (fderiv ℝ (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x)
                    xStarE) y by
                simp]
            congr 1
            · simpa using
                (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanObjective)
                  (x := y) (y := xStarE))
            · apply Finset.sum_congr rfl
              intro i hi
              have hfun :
                  (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x) =
                    lambda i • problem.euclideanConstraint i := by
                ext x
                simp [smul_eq_mul]
              have hterm :
                  fderiv ℝ (fun x : EPoint ↦ lambda i * problem.euclideanConstraint i x) xStarE =
                    lambda i • fderiv ℝ (problem.euclideanConstraint i) xStarE := by
                change
                  fderiv ℝ
                    (fun x : EPoint ↦
                      lambda i * problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x))
                    xStarE =
                    lambda i • fderiv ℝ (problem.euclideanConstraint i) xStarE
                rw [show
                  (fun x : EPoint ↦
                    lambda i * problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x)) =
                    lambda i • problem.euclideanConstraint i by
                      ext x
                      simp [ConstrainedOptimizationProblem.euclideanConstraint_eq, smul_eq_mul]]
                simpa using
                  congrFun
                    (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (c := lambda i)
                      (f := problem.euclideanConstraint i))
                    xStarE
              rw [hterm, smul_apply]
              rw [inner_smul_right]
              simpa using
                congrArg
                  (fun r : ℝ => lambda i * r)
                  (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanConstraint i)
                    (x := y) (y := xStarE))
    _ = inner ℝ y
          (gradient problem.euclideanObjective xStarE -
            ∑ i : Fin m, lambda i • gradient (problem.euclideanConstraint i) xStarE) := by
            rw [inner_sub_right, inner_sum]

/-- Helper for Chapter08 Theorem 8.2.7: zero-extending the Farkas multipliers from the active
constraint set to all of `Fin m` converts the full-index gradient sum into the textbook split sum
over equality and active inequality constraints. -/
theorem zero_extended_active_constraint_multiplier_sum_eq_eq_add_active
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lam : Fin m → ℝ) {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (v : Fin m → V)
    [DecidablePred (fun i : Fin m ↦ i ∈ problem.activeConstraintIndexSet xStar)]
    [DecidablePred (fun i : Fin m ↦ i ∈ problem.eqIndices)]
    [DecidablePred (fun i : Fin m ↦ i ∈ problem.activeIneqIndexSet xStar)] :
    ∑ i : Fin m, (if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0) • v i =
      (∑ i : Fin m, if i ∈ problem.eqIndices then lam i • v i else 0) +
        ∑ i : Fin m, if i ∈ problem.activeIneqIndexSet xStar then lam i • v i else 0 := by
  classical
  have hdisjEqIneq :
      Disjoint problem.eqIndices problem.ineqIndices := by
    simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
      using problem.eqIndices_disjoint_ineqIndices
  have hdisj :
      Disjoint problem.eqIndices (problem.activeIneqIndexSet xStar) := by
    rw [Set.disjoint_left]
    intro i hi_eq hi_active
    exact
      Set.disjoint_left.mp hdisjEqIneq hi_eq
        ((problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active).1
  have hsplit :
      ∀ i : Fin m,
        (if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0) • v i =
          (if i ∈ problem.eqIndices then lam i • v i else 0) +
            if i ∈ problem.activeIneqIndexSet xStar then lam i • v i else 0 := by
    intro i
    by_cases hi_eq : i ∈ problem.eqIndices
    · have hi_not_active : i ∉ problem.activeIneqIndexSet xStar := by
        exact Set.disjoint_left.mp hdisj hi_eq
      have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
        rw [problem.activeConstraintIndexSet_def]
        exact Or.inl hi_eq
      -- Equality indices contribute exactly once because the active-inequality set is disjoint.
      simp [hi_eq, hi_not_active, hi_constraint]
    · by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
      · have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
          rw [problem.activeConstraintIndexSet_def]
          exact Or.inr hi_active
        -- Active inequality indices contribute exactly once through the second summand.
        simp [hi_eq, hi_active, hi_constraint]
      · have hi_not_constraint : i ∉ problem.activeConstraintIndexSet xStar := by
          rw [problem.activeConstraintIndexSet_def]
          simp [hi_eq, hi_active]
        -- Inactive indices contribute zero to both sides.
        simp [hi_eq, hi_active, hi_not_constraint]
  calc
    ∑ i : Fin m, (if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0) • v i
        = ∑ i : Fin m,
            ((if i ∈ problem.eqIndices then lam i • v i else 0) +
              if i ∈ problem.activeIneqIndexSet xStar then lam i • v i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hsplit i
    _ = (∑ i : Fin m, if i ∈ problem.eqIndices then lam i • v i else 0) +
          ∑ i : Fin m, if i ∈ problem.activeIneqIndexSet xStar then lam i • v i else 0 := by
            rw [Finset.sum_add_distrib]

end ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.7 (Karush-Kuhn-Tucker Theorem): under the standing differentiability
setup, if `xStar` is a feasible local minimizer of `problem` and the constraint qualification
`(8.2.19)` holds at `xStar`, then there exists a multiplier vector `lamStar` such that
`problem.IsKKTPoint xStar lamStar`. -/
theorem exists_isKKTPoint_of_isLocalMinOn_of_constraintQualificationAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_cq : problem.ConstraintQualificationAt xStar) :
    ∃ lamStar : Fin m → ℝ, problem.IsKKTPoint xStar lamStar := by
  classical
  -- Route correction: extend the multiplier on the full active-constraint set, not only on the
  -- active inequalities, so the equality-constraint Farkas terms survive in stationarity.
  let xStarE : EPoint := WithLp.toLp 2 xStar
  let gradC : Fin m → EPoint := fun i ↦ gradient (problem.euclideanConstraint i) xStarE
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective xStarE := by
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective
  have hdisjEqActive :
      Disjoint problem.eqIndices (problem.activeIneqIndexSet xStar) := by
    rw [Set.disjoint_left]
    intro i hi_eq hi_active
    exact
      Set.disjoint_left.mp
          (by
            simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
              using problem.eqIndices_disjoint_ineqIndices)
          hi_eq ((problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active).1
  have hdisjEqIneq :
      Disjoint problem.eqIndices problem.ineqIndices := by
    simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
      using problem.eqIndices_disjoint_ineqIndices
  have hEmpty :
      descentDirections problem.euclideanObjective xStarE ∩
          {u |
            (∀ i ∈ problem.eqIndices, inner ℝ u (gradC i) = 0) ∧
              ∀ i ∈ problem.activeIneqIndexSet xStar, 0 ≤ inner ℝ u (gradC i)} =
        (∅ : Set EPoint) := by
    simpa [xStarE, gradC] using
      problem.euclidean_linearized_descent_system_eq_empty_of_constraintQualificationAt
        xStar hxStar h_localMin h_objective h_constraints h_cq
  obtain ⟨lam, hlam_nonneg, hgrad_repr⟩ :=
    (descentDirections_inter_constraintGradientSystem_eq_empty_iff_exists_multiplier
      (X := EPoint) (ι := Fin m)
      problem.eqIndices (problem.activeIneqIndexSet xStar) hdisjEqActive
      problem.euclideanObjective xStarE (gradient problem.euclideanObjective xStarE) gradC
      hobjectiveE.hasGradientAt).1 hEmpty
  let lamStar : Fin m → ℝ :=
    fun i ↦ if i ∈ problem.activeConstraintIndexSet xStar then lam i else 0
  have hgrad_repr_full :
      gradient problem.euclideanObjective xStarE = ∑ i : Fin m, lamStar i • gradC i := by
    -- Move the subtype-indexed Farkas representation to the full active-constraint owner first,
    -- then zero-extend the multiplier on the full index set.
    let _ : Fintype ↑problem.eqIndices := Fintype.ofFinite ↑problem.eqIndices
    let _ : Fintype ↑(problem.activeIneqIndexSet xStar) :=
      Fintype.ofFinite ↑(problem.activeIneqIndexSet xStar)
    have heq_sum :
        (∑ i : problem.eqIndices, lam i • gradC i) =
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
            (fun i ↦ lam i • gradC i) := by
      calc
        (∑ i : problem.eqIndices, lam i • gradC i)
            = Finset.sum
                ((Finset.univ : Finset problem.eqIndices).map
                  (Function.Embedding.subtype (fun i : Fin m => i ∈ problem.eqIndices)))
                (fun i ↦ lam i • gradC i) := by
                  simp [Finset.sum_map]
        _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
              (fun i ↦ lam i • gradC i) := by
                rw [Finset.univ_map_subtype]
    have hactive_sum :
        (∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i) =
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
            (fun i ↦ lam i • gradC i) := by
      calc
        (∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i)
            = Finset.sum
                ((Finset.univ : Finset (problem.activeIneqIndexSet xStar)).map
                  (Function.Embedding.subtype
                    (fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)))
                (fun i ↦ lam i • gradC i) := by
                  simp [Finset.sum_map]
        _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
              (fun i ↦ lam i • gradC i) := by
                rw [Finset.univ_map_subtype]
    calc
      gradient problem.euclideanObjective xStarE
          = (∑ i : problem.eqIndices, lam i • gradC i) +
              ∑ i : problem.activeIneqIndexSet xStar, lam i • gradC i := hgrad_repr
      _ = Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.eqIndices)
            (fun i ↦ lam i • gradC i) +
          Finset.sum (Finset.univ.filter fun i : Fin m => i ∈ problem.activeIneqIndexSet xStar)
            (fun i ↦ lam i • gradC i) := by
            rw [heq_sum, hactive_sum]
      _ = (∑ i : Fin m, if i ∈ problem.eqIndices then lam i • gradC i else 0) +
            ∑ i : Fin m,
              if i ∈ problem.activeIneqIndexSet xStar then lam i • gradC i else 0 := by
            simp [Finset.sum_filter]
      _ = ∑ i : Fin m, lamStar i • gradC i := by
            symm
            simpa [lamStar] using
              (ConstrainedOptimizationProblem.zero_extended_active_constraint_multiplier_sum_eq_eq_add_active
                (problem := problem) (xStar := xStar) (lam := lam) (V := EPoint) gradC)
  have hnot_activeConstraint_of_not_activeIneq :
      ∀ ⦃i : Fin m⦄, i ∈ problem.ineqIndices →
        i ∉ problem.activeIneqIndexSet xStar →
          i ∉ problem.activeConstraintIndexSet xStar := by
    intro i hi_ineq hi_not_active hi_constraint
    rw [problem.activeConstraintIndexSet_def] at hi_constraint
    rcases hi_constraint with hi_eq | hi_active
    · exact Set.disjoint_left.mp hdisjEqIneq hi_eq hi_ineq
    · exact hi_not_active hi_active
  refine ⟨lamStar, ?_⟩
  refine
    { feasible := hxStar
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · intro i hi_ineq
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
        rw [problem.activeConstraintIndexSet_def]
        exact Or.inr hi_active
      -- On active inequalities the zero-extension agrees with the Farkas multiplier.
      simpa [lamStar, hi_constraint] using hlam_nonneg i hi_active
    · have hi_not_constraint :
          i ∉ problem.activeConstraintIndexSet xStar :=
        hnot_activeConstraint_of_not_activeIneq hi_ineq hi_active
      -- Inactive inequality multipliers are defined to be zero.
      simp [lamStar, hi_not_constraint]
  · -- The gradient identity and the sum-normalization helper reduce stationarity to Farkas.
    rw [problem.gradient_euclideanLagrangian_eq_objective_sub_sum xStar lamStar
      h_objective h_constraints]
    rw [hgrad_repr_full]
    simpa [gradC, xStarE] using sub_self (∑ i : Fin m, lamStar i • gradC i)
  · intro i hi_ineq
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · have hi_constraint : i ∈ problem.activeConstraintIndexSet xStar := by
        rw [problem.activeConstraintIndexSet_def]
        exact Or.inr hi_active
      have hi_zero : problem.constraint i xStar = 0 :=
        (problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active |>.2
      -- Active inequalities vanish at `xStar`, so complementary slackness is immediate.
      simp [lamStar, hi_constraint, hi_zero]
    · have hi_not_constraint :
          i ∉ problem.activeConstraintIndexSet xStar :=
        hnot_activeConstraint_of_not_activeIneq hi_ineq hi_active
      -- Inactive inequality multipliers are zero by definition.
      simp [lamStar, hi_not_constraint]

end Chapter08Theorem827
