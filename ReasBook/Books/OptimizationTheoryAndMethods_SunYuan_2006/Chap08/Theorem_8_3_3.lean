/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_7_6
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Filter InnerProductSpace
open scoped Gradient

section Chapter08Theorem833

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => Fin m → ℝ

namespace ConstrainedOptimizationProblem

-- Source-facing reuse:
-- * owner chain: `Definition_8_3_2` already provides the Chapter 8 constrained problem,
--   `sequentialNullConstraintDirections = S(xStar, lamStar)`, and
--   `linearizedNullConstraintDirections = G(xStar, lamStar)`
-- * source constraint qualification owner reused directly from `Theorem_8_2_7`:
--   `problem.ConstraintQualificationAt xStar`
-- * this file adds only the Lagrangian Hessian quadratic surface used in Theorem 8.3.3
-- * the Lagrangian owner is already `problem.euclideanLagrangian` upstream, so the Hessian is
--   expressed on that existing Euclidean transport instead of rebuilding a function-space model

/-- The Hessian of the Lagrangian with respect to `x`, represented as the Fréchet derivative of
the gradient of the Euclidean transport `problem.euclideanLagrangian lamStar` at `xStar`. -/
noncomputable abbrev lagrangianHessianAt
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier) : EPoint →L[ℝ] EPoint :=
  fderiv ℝ (gradient (problem.euclideanLagrangian lamStar)) (WithLp.toLp 2 xStar)

/-- The quadratic form `dᵀ ∇²ₓₓ L(xStar, lamStar) d` attached to
`problem.lagrangianHessianAt xStar lamStar`. -/
noncomputable abbrev lagrangianHessianQuadratic
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier) (d : Point) : ℝ :=
  inner ℝ (WithLp.toLp 2 d)
    (problem.lagrangianHessianAt xStar lamStar (WithLp.toLp 2 d))

/-- Unfolding formula for `lagrangianHessianQuadratic`. -/
theorem lagrangianHessianQuadratic_eq
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier) :
    problem.lagrangianHessianQuadratic xStar lamStar d =
      inner ℝ (WithLp.toLp 2 d)
        (problem.lagrangianHessianAt xStar lamStar (WithLp.toLp 2 d)) :=
  rfl

/-- Helper for Chapter08 Theorem 8.3.3: the Euclidean Lagrangian inherits the pointwise `C²`
regularity of the objective and the constraint functions at `xStar`. -/
lemma contDiffAt_euclideanLagrangian
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar) :
    ContDiffAt ℝ 2 (problem.euclideanLagrangian lamStar) (WithLp.toLp 2 xStar) := by
  have hcoordPoint (x : Point) :
      (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  -- Transport the objective regularity through the Euclidean coordinate equivalence.
  have hcoordObjective :
      ContDiffAt ℝ 2
        (fun x : EPoint ↦ problem.objective ((EuclideanSpace.equiv (Fin n) ℝ) x))
        (WithLp.toLp 2 xStar) := by
    have hObjectiveAt :
        ContDiffAt ℝ 2 problem.objective
          ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) := by
      simpa [hcoordPoint xStar] using h_objective
    exact hObjectiveAt.comp (WithLp.toLp 2 xStar) <|
      by
        simpa using
          (ContinuousLinearEquiv.contDiff
            (EuclideanSpace.equiv (Fin n) ℝ)).contDiffAt
  -- Each constraint term has the same transported regularity, and multiplying by `lamStar i`
  -- does not change the `C²` status.
  have hcoordConstraint :
      ∀ i : Fin m,
        ContDiffAt ℝ 2
          (fun x : EPoint ↦
            lamStar i * problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x))
          (WithLp.toLp 2 xStar) := by
    intro i
    have hConstraintAt :
        ContDiffAt ℝ 2 (problem.constraint i)
          ((EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar)) := by
      simpa [hcoordPoint xStar] using h_constraints i
    have hConstraintCoord :
        ContDiffAt ℝ 2
          (fun x : EPoint ↦ problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x))
          (WithLp.toLp 2 xStar) :=
      hConstraintAt.comp (WithLp.toLp 2 xStar) <|
        by
          simpa using
            (ContinuousLinearEquiv.contDiff
              (EuclideanSpace.equiv (Fin n) ℝ)).contDiffAt
    simpa [smul_eq_mul] using hConstraintCoord.const_smul (lamStar i)
  have hconstraintSum :
      ContDiffAt ℝ 2
        (fun x : EPoint ↦
          ∑ i ∈ Finset.univ,
            lamStar i * problem.constraint i ((EuclideanSpace.equiv (Fin n) ℝ) x))
        (WithLp.toLp 2 xStar) := by
    exact ContDiffAt.sum fun i _ ↦ hcoordConstraint i
  -- Expanding the Euclidean Lagrangian reduces the claim to the objective-minus-sum formula.
  simpa [problem.euclideanLagrangian_eq_objective_sub_sum] using
    hcoordObjective.sub hconstraintSum

/-- Helper for Chapter08 Theorem 8.3.3: the Euclidean Lagrangian is `C²` on some neighborhood
of the base point. -/
lemma exists_contDiffOn_euclideanLagrangian_nhds
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar) :
    ∃ s ∈ nhds (WithLp.toLp 2 xStar), ContDiffOn ℝ 2 (problem.euclideanLagrangian lamStar) s := by
  -- Upgrade the pointwise `C²` fact to a neighborhood-level `ContDiffOn` witness.
  exact
    (contDiffAt_euclideanLagrangian problem xStar lamStar h_objective h_constraints).contDiffOn
      le_rfl (by
        intro h
        simp at h)

/-- Helper for Chapter08 Theorem 8.3.3: a neighborhood-level `C²` witness can be shrunk to a
metric ball centered at the base point. -/
lemma exists_contDiffOn_ball_of_nhds
    {f : EPoint → ℝ} {x : EPoint}
    (hC2 : ∃ s ∈ nhds x, ContDiffOn ℝ 2 f s) :
    ∃ r > 0, ContDiffOn ℝ 2 f (Metric.ball x r) := by
  rcases hC2 with ⟨s, hsNhd, hsC2⟩
  -- Replace the abstract neighborhood by an explicit metric ball so the trace lemmas apply.
  rcases Metric.mem_nhds_iff.mp hsNhd with ⟨r, hr, hball⟩
  exact ⟨r, hr, hsC2.mono hball⟩

/-- Helper for Chapter08 Theorem 8.3.3: once the traced steps tend to `0`, the whole witness
segments eventually stay inside any fixed small ball around the base point. -/
lemma eventually_segment_subset_metric_ball
    {x : EPoint} {step : ℕ → EPoint} {r : ℝ}
    (hr : 0 < r)
    (hstep : Tendsto step atTop (nhds (0 : EPoint))) :
    ∀ᶠ k in atTop, segment ℝ x (x + step k) ⊆ Metric.ball x r := by
  have hsmall : ∀ᶠ k in atTop, step k ∈ Metric.ball (0 : EPoint) r := by
    exact hstep.eventually (Metric.ball_mem_nhds (0 : EPoint) hr)
  filter_upwards [hsmall] with k hk z hz
  rw [segment_eq_image' ℝ x (x + step k)] at hz
  rcases hz with ⟨t, ht, rfl⟩
  -- Parametrize the segment by `x + t • step k` and bound its distance by `‖step k‖`.
  have ht_abs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hk_norm : ‖step k‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hk
  have hdist :
      dist (x + t • step k) x ≤ ‖step k‖ := by
    calc
      dist (x + t • step k) x = ‖t • step k‖ := by
        simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
      _ = |t| * ‖step k‖ := norm_smul _ _
      _ ≤ ‖step k‖ := by
        nlinarith [norm_nonneg (step k)]
  have hball :
      x + t • step k ∈ Metric.ball x r := by
    simpa [Metric.mem_ball] using lt_of_le_of_lt hdist hk_norm
  simpa [sub_eq_add_neg, add_assoc] using hball

/-- Helper for Chapter08 Theorem 8.3.3: the diagonal Hessian quadratic form written via
`hessianAt` agrees with the diagonal value of `iteratedFDeriv ℝ 2` at a `C²` point. -/
lemma hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
    {f : EPoint → ℝ} {x y : EPoint}
    (hC2 : ContDiffAt ℝ 2 f x) :
    hessianQuadraticAt f x y = (iteratedFDeriv ℝ 2 f x) ![y, y] := by
  -- Route correction: specialize the compile-clean Chapter 5 bilinear bridge to the diagonal.
  exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt (f := f) hC2

/-- Helper for Chapter08 Theorem 8.3.3: the diagonal Hessian quadratic form written via
`fderiv ℝ (∇ f)` agrees with the diagonal value of `iteratedFDeriv ℝ 2 f` at a `C²` point. -/
lemma inner_fderiv_gradient_eq_iteratedFDeriv_diag_of_contDiffAt
    {f : EPoint → ℝ} {y u : EPoint}
    (hC2y : ContDiffAt ℝ 2 f y) :
    inner ℝ u ((fderiv ℝ (∇ f) y) u) = (iteratedFDeriv ℝ 2 f y) ![u, u] := by
  -- Route correction: reuse the canonical Chapter 3 Hessian-diagonal bridge instead of
  -- re-expanding the Riesz transport locally.
  simpa [hessianQuadraticAt, hessianAt, gradient] using
    hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
      (f := f) (x := y) (y := u) hC2y

/-- Helper for Chapter08 Theorem 8.3.3: the explicit Riesz-transport gradient field used by the
Chapter 2 trace lemmas has the same diagonal second-derivative value as `iteratedFDeriv ℝ 2`. -/
lemma inner_fderiv_toDualSymm_eq_iteratedFDeriv_diag_of_contDiffAt
    {f : EPoint → ℝ} {y u : EPoint}
    (hC2y : ContDiffAt ℝ 2 f y) :
    inner ℝ u
        ((fderiv ℝ
            (fun z ↦ (InnerProductSpace.toDual ℝ EPoint).symm (fderiv ℝ f z)) y) u) =
      (iteratedFDeriv ℝ 2 f y) ![u, u] := by
  -- The Chapter 2 trace API writes `gradient` through its explicit Riesz-transport definition.
  change inner ℝ u ((fderiv ℝ (∇ f) y) u) = (iteratedFDeriv ℝ 2 f y) ![u, u]
  exact
    inner_fderiv_gradient_eq_iteratedFDeriv_diag_of_contDiffAt
      (f := f) (y := y) (u := u) hC2y

/-- Helper for Chapter08 Theorem 8.3.3: intermediate points on a shrinking traced segment still
converge back to the base point, provided the trace parameters stay in `[0, 1]`. -/
lemma intermediate_trace_points_tendsto_base
    {x : EPoint} {step : ℕ → EPoint} {ξ : ℕ → ℝ}
    (hstep : Tendsto step atTop (nhds (0 : EPoint)))
    (hξ : ∀ k, ξ k ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun k ↦ x + ξ k • step k) atTop (nhds x) := by
  have hsmul0 : Tendsto (fun k ↦ ξ k • step k) atTop (nhds (0 : EPoint)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    -- Control the scaled steps by the unscaled norms, using `0 ≤ ξ k ≤ 1`.
    refine squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _) ?_
      (tendsto_zero_iff_norm_tendsto_zero.1 hstep)
    filter_upwards with k
    rcases hξ k with ⟨hξ0, hξ1⟩
    have habs : |ξ k| ≤ 1 := by
      rw [abs_of_nonneg hξ0]
      exact hξ1
    calc
      ‖ξ k • step k‖ = |ξ k| * ‖step k‖ := norm_smul _ _
      _ ≤ ‖step k‖ := by
        nlinarith [norm_nonneg (step k)]
  simpa [zero_add] using hsmul0.const_add x

/-- Helper for Chapter08 Theorem 8.3.3: continuity of `iteratedFDeriv ℝ 2` at the base point
propagates to the diagonal quadratic samples along convergent base points and directions. -/
lemma iteratedFDeriv_diag_tendsto_of_tendsto
    {f : EPoint → ℝ} {x u0 : EPoint} {z u : ℕ → EPoint}
    (hC2 : ContDiffAt ℝ 2 f x)
    (hz : Tendsto z atTop (nhds x))
    (hu : Tendsto u atTop (nhds u0)) :
    Tendsto (fun k ↦ (iteratedFDeriv ℝ 2 f (z k)) ![u k, u k]) atTop
      (nhds ((iteratedFDeriv ℝ 2 f x) ![u0, u0])) := by
  have hcontA : ContinuousAt (iteratedFDeriv ℝ 2 f) x :=
    hC2.continuousAt_iteratedFDeriv (by norm_num)
  have hpair :
      Tendsto (fun k ↦ ((iteratedFDeriv ℝ 2 f (z k)), u k)) atTop
        (nhds ((iteratedFDeriv ℝ 2 f x), u0)) := by
    exact Filter.Tendsto.prodMk_nhds (hcontA.tendsto.comp hz) hu
  have hcontEval :
      Continuous
        (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EPoint) ℝ × EPoint ↦
          p.1 ![p.2, p.2]) := by
    fun_prop
  change
    Tendsto
      ((fun p : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EPoint) ℝ × EPoint ↦
        p.1 ![p.2, p.2]) ∘
        fun k ↦ ((iteratedFDeriv ℝ 2 f (z k)), u k))
      atTop
      (nhds
        ((fun p : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EPoint) ℝ × EPoint ↦
          p.1 ![p.2, p.2]) ((iteratedFDeriv ℝ 2 f x), u0)))
  exact hcontEval.continuousAt.tendsto.comp hpair

/-- Helper for Chapter08 Theorem 8.3.3: the Hessian quadratic form agrees with the diagonal value
of `iteratedFDeriv ℝ 2` for the Euclidean Lagrangian. -/
lemma lagrangianHessianQuadratic_eq_iteratedFDeriv_two
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar) :
    problem.lagrangianHessianQuadratic xStar lamStar d =
      (iteratedFDeriv ℝ 2 (problem.euclideanLagrangian lamStar) (WithLp.toLp 2 xStar))
        ![WithLp.toLp 2 d, WithLp.toLp 2 d] := by
  have hC2 :
      ContDiffAt ℝ 2 (problem.euclideanLagrangian lamStar) (WithLp.toLp 2 xStar) :=
    contDiffAt_euclideanLagrangian problem xStar lamStar h_objective h_constraints
  -- Route correction: use the canonical Hessian-diagonal theorem for the Euclidean Lagrangian.
  simpa [ConstrainedOptimizationProblem.lagrangianHessianQuadratic,
    ConstrainedOptimizationProblem.lagrangianHessianAt, hessianQuadraticAt, hessianAt] using
    hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
      (f := problem.euclideanLagrangian lamStar)
      (x := WithLp.toLp 2 xStar) (y := WithLp.toLp 2 d) hC2

/-- Helper for Chapter08 Theorem 8.3.3: the multiplier-weighted constraint sum vanishes at a KKT
point. -/
lemma weighted_constraint_sum_eq_zero_at_kktPoint
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier)
    (h_kkt : problem.IsKKTPoint xStar lamStar) :
    ∑ i : Fin m, lamStar i * problem.constraint i xStar = 0 := by
  -- Split the sum into equality and inequality indices using the problem's partition.
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi_union : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
    simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
      using (show i ∈ E ∪ I from by
        rw [problem.eqIndices_union_ineqIndices]
        simp)
  rcases hi_union with hi_eq | hi_ineq
  · rw [h_kkt.eq_constraints i hi_eq, mul_zero]
  · exact h_kkt.complementarySlackness i hi_ineq

/-- Helper for Chapter08 Theorem 8.3.3: at a KKT point, the Euclidean Lagrangian value equals
the objective value. -/
lemma euclideanLagrangian_eq_objective_at_kktPoint
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier)
    (h_kkt : problem.IsKKTPoint xStar lamStar) :
    problem.euclideanLagrangian lamStar (WithLp.toLp 2 xStar) = problem.objective xStar := by
  have hcoord :
      (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 xStar) = xStar := by
    change (WithLp.toLp 2 xStar).ofLp = xStar
    exact WithLp.ofLp_toLp 2 xStar
  -- The KKT equalities collapse the weighted constraint correction term.
  rw [problem.euclideanLagrangian_apply, problem.lagrangian_eq, hcoord,
    problem.weighted_constraint_sum_eq_zero_at_kktPoint xStar lamStar h_kkt, sub_zero]

/-- Helper for Chapter08 Theorem 8.3.3: whenever the multiplier-weighted constraint sum vanishes
at `x`, the Euclidean Lagrangian equals the objective at `x`. -/
lemma euclideanLagrangian_eq_objective_of_weighted_constraint_sum_zero
    (problem : ConstrainedOptimizationProblem n m E I)
    (x : Point) (lamStar : Multiplier)
    (h_weighted :
      ∑ i : Fin m, lamStar i * problem.constraint i x = 0) :
    problem.euclideanLagrangian lamStar (WithLp.toLp 2 x) = problem.objective x := by
  have hcoord :
      (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  -- Rewrite the Lagrangian by its defining sum and then use the supplied vanishing identity.
  rw [problem.euclideanLagrangian_apply, problem.lagrangian_eq, hcoord, h_weighted, sub_zero]

/-- Helper for Chapter08 Theorem 8.3.3: the feasible witness points attached to a sequential null
constraint direction converge back to the base point `xStar`. -/
lemma tendsto_sequential_null_witness_steps
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (dSeq : ℕ → Point) (delta : ℕ → ℝ)
    (hseq :
      problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta) :
    Tendsto (fun k ↦ xStar + delta k • dSeq k) atTop (nhds xStar) := by
  rcases hseq with ⟨_, _, _, hdSeq, hdelta⟩
  -- The increments `delta k • dSeq k` tend to `0`, so translating by `xStar` yields the claim.
  have hsmul :
      Tendsto (fun k ↦ delta k • dSeq k) atTop (nhds ((0 : ℝ) • d)) := by
    exact hdelta.smul hdSeq
  have hzero : Tendsto (fun k ↦ delta k • dSeq k) atTop (nhds (0 : Point)) := by
    simpa [zero_smul] using hsmul
  simpa [zero_add] using hzero.const_add xStar

/-- Helper for Chapter08 Theorem 8.3.3: the local-minimum inequality holds eventually along a
sequential-null witness sequence. -/
lemma eventually_objective_le_along_sequential_null_witness
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (dSeq : ℕ → Point) (delta : ℕ → ℝ)
    (hseq :
      problem.IsSequentialNullConstraintDirectionSeq xStar lamStar d dSeq delta) :
    ∀ᶠ k in atTop, problem.objective xStar ≤ problem.objective (xStar + delta k • dSeq k) := by
  have hconstrained :
      IsConstrainedLocalMinOn problem.objective problem.feasibleSet xStar :=
    ⟨h_kkt.feasible, h_localMin⟩
  rcases
      (isConstrainedLocalMinOn_iff_exists_forall_mem_closedBall
        problem.objective problem.feasibleSet xStar).1 hconstrained with
    ⟨_, δ, hδ, hδball⟩
  have hsteps :
      Tendsto (fun k ↦ xStar + delta k • dSeq k) atTop (nhds xStar) :=
    problem.tendsto_sequential_null_witness_steps xStar d lamStar dSeq delta hseq
  have hball :
      ∀ᶠ k in atTop, xStar + delta k • dSeq k ∈ Metric.closedBall xStar δ := by
    exact hsteps.eventually (Metric.closedBall_mem_nhds xStar hδ)
  rcases hseq with ⟨_, hfeasible, _, _, _⟩
  -- Eventually the witness points are both feasible and contained in the local minimizing ball.
  filter_upwards [hball] with k hk
  exact hδball (xStar + delta k • dSeq k) ⟨hfeasible k, hk⟩

/-- Chapter08 Theorem 8.3.3 (1): if `xStar` is a local minimizer of `problem`, the objective and
every constraint are twice continuously differentiable at `xStar`, the constraint qualification
`(8.2.19)` holds at `xStar`, and `lamStar` is a KKT multiplier at `xStar`, then the Lagrangian
Hessian is nonnegative on every direction in the source set
`problem.sequentialNullConstraintDirections xStar lamStar = S(xStar, lamStar)`. -/
theorem secondOrderNecessaryCondition_on_sequentialNullConstraintDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar)
    (h_cq : problem.ConstraintQualificationAt xStar)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (hd : d ∈ problem.sequentialNullConstraintDirections xStar lamStar) :
    0 ≤ problem.lagrangianHessianQuadratic xStar lamStar d := by
  -- Unpack the source witness sequence encoded in `S(xStar, lamStar)`.
  rcases (problem.mem_sequentialNullConstraintDirections_iff_exists_seq xStar d lamStar).1 hd with
    ⟨_, _, dSeq, delta, hseq, hweighted⟩
  have hseq_saved := hseq
  rcases hseq with ⟨hdelta_pos, _, _, hdSeq, hdelta⟩
  let L : EPoint → ℝ := problem.euclideanLagrangian lamStar
  let xE : EPoint := WithLp.toLp 2 xStar
  let dE : EPoint := WithLp.toLp 2 d
  let dEk : ℕ → EPoint := fun k ↦ WithLp.toLp 2 (dSeq k)
  let step : ℕ → EPoint := fun k ↦ delta k • dEk k
  have hObjectiveEventually :
      ∀ᶠ k in atTop, problem.objective xStar ≤ problem.objective (xStar + delta k • dSeq k) :=
    problem.eventually_objective_le_along_sequential_null_witness
      xStar d lamStar h_localMin h_kkt dSeq delta hseq_saved
  have hBaseLagrangian :
      L xE = problem.objective xStar := by
    simpa [L, xE] using
      problem.euclideanLagrangian_eq_objective_at_kktPoint xStar lamStar h_kkt
  have hSeqLagrangian :
      ∀ k,
        L (WithLp.toLp 2 (xStar + delta k • dSeq k)) = problem.objective (xStar + delta k • dSeq k) := by
    intro k
    simpa [L] using
      problem.euclideanLagrangian_eq_objective_of_weighted_constraint_sum_zero
        (xStar + delta k • dSeq k) lamStar (hweighted k)
  have hHessianRewrite :
      problem.lagrangianHessianQuadratic xStar lamStar d = (iteratedFDeriv ℝ 2 L xE) ![dE, dE] := by
    simpa [L, xE, dE] using
      problem.lagrangianHessianQuadratic_eq_iteratedFDeriv_two
        xStar d lamStar h_objective h_constraints
  have hContDiffNhd :
      ∃ s ∈ nhds xE, ContDiffOn ℝ 2 L s := by
    simpa [L, xE] using
      problem.exists_contDiffOn_euclideanLagrangian_nhds
        xStar lamStar h_objective h_constraints
  have hdEk : Tendsto dEk atTop (nhds dE) := by
    have hcont : Continuous (fun y : Point ↦ WithLp.toLp 2 y) := by
      fun_prop
    exact hcont.tendsto _ |>.comp hdSeq
  have hstep : Tendsto step atTop (nhds (0 : EPoint)) := by
    -- The witness steps are `delta k • dSeq k`, transported to the Euclidean model.
    have hsmul : Tendsto (fun k ↦ delta k • dEk k) atTop (nhds ((0 : ℝ) • dE)) := by
      exact hdelta.smul hdEk
    simpa [step, zero_smul] using hsmul
  rcases exists_contDiffOn_ball_of_nhds hContDiffNhd with ⟨r, hr, hBallC2⟩
  have hSegmentEventually :
      ∀ᶠ k in atTop, segment ℝ xE (xE + step k) ⊆ Metric.ball xE r :=
    eventually_segment_subset_metric_ball hr hstep
  have hTaylorEventually :
      ∀ᶠ k in atTop,
        ∃ ξ : ℝ, ξ ∈ Set.uIoo (0 : ℝ) 1 ∧
          L (xE + step k) =
            L xE +
              (delta k ^ (2 : ℕ) / 2) *
                ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
    filter_upwards [hSegmentEventually] with k hsegment
    let φ : ℝ → ℝ := lineSearchObjective L xE (delta k • dEk k)
    have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
      simpa [φ, step] using
        unitIntervalTraceContDiffOn L xE (dEk k) (delta k) hsegment hBallC2
    obtain ⟨ξ, hξ, hTaylor⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := φ) (x := 1) (x₀ := 0) (n := 1) zero_ne_one hφC2
    have hξu : ξ ∈ Set.uIcc (0 : ℝ) 1 := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have hfirst :
        iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 =
          delta k * inner ℝ (∇ L xE) (dEk k) := by
      simpa [φ, step] using
        unitIntervalTraceFirstIteratedDerivZero L xE (dEk k) (delta k)
          (Metric.isOpen_ball) hsegment hBallC2
    have hstationary :
        ∇ L xE = 0 := by
      simpa [L, xE] using h_kkt.stationarity
    have hfirstZero :
        iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 = 0 := by
      rw [hfirst, hstationary]
      simp
    have htraceMem : xE + ξ • step k ∈ Metric.ball xE r := by
      simpa [step] using
        unitIntervalTraceMapsToDomain xE (dEk k) (delta k) hsegment hξu
    have hC2ξ : ContDiffAt ℝ 2 L (xE + ξ • step k) := by
      exact hBallC2.contDiffAt (Metric.isOpen_ball.mem_nhds htraceMem)
    have hsecond :
        iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ =
          delta k ^ (2 : ℕ) *
            ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
      calc
        iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ =
            delta k ^ (2 : ℕ) *
              inner ℝ (dEk k)
                ((fderiv ℝ
                    (fun z ↦ (InnerProductSpace.toDual ℝ EPoint).symm (fderiv ℝ L z))
                    (xE + ξ • (delta k • dEk k))) (dEk k)) := by
                  simpa [φ, step] using
                    unitIntervalTraceSecondIteratedDeriv L xE (dEk k) (delta k) ξ
                      (Metric.isOpen_ball) hsegment hBallC2 hξu
        _ =
            delta k ^ (2 : ℕ) *
              ((iteratedFDeriv ℝ 2 L (xE + ξ • (delta k • dEk k))) ![dEk k, dEk k]) := by
                have hC2ξ' : ContDiffAt ℝ 2 L (xE + ξ • (delta k • dEk k)) := by
                  simpa [step] using hC2ξ
                rw [inner_fderiv_toDualSymm_eq_iteratedFDeriv_diag_of_contDiffAt
                  (f := L) (y := xE + ξ • (delta k • dEk k)) (u := dEk k) hC2ξ']
        _ =
            delta k ^ (2 : ℕ) *
              ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
                simp [step]
    have hTaylor' :
        φ 1 = φ 0 + ((iteratedDeriv 2 φ ξ) / 2) := by
      -- Expand the order-one Taylor polynomial and use stationarity to kill the linear term.
      have hbase :
          φ 1 - taylorWithinEval φ 1 (Set.uIcc (0 : ℝ) 1) 0 1 =
            iteratedDeriv 2 φ ξ / 2 := by
        simpa [pow_two] using hTaylor
      rw [taylorWithinEval_succ, taylor_within_zero_eval] at hbase
      rw [hfirstZero] at hbase
      norm_num at hbase
      linarith
    have hContDiffAtξ : ContDiffAt ℝ 2 φ ξ := hφC2.contDiffAt (Icc_mem_nhds hξ.1 hξ.2)
    have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
    have hsecond' :
        iteratedDeriv 2 φ ξ =
          delta k ^ (2 : ℕ) * ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
      calc
        iteratedDeriv 2 φ ξ = iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ := by
          symm
          exact iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξu
        _ = delta k ^ (2 : ℕ) * ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) :=
          hsecond
    refine ⟨ξ, hξ, ?_⟩
    calc
      L (xE + step k) = φ 1 := by
        simp [φ, lineSearchObjective_apply, step]
      _ = φ 0 + iteratedDeriv 2 φ ξ / 2 := hTaylor'
      _ = L xE + ((delta k ^ (2 : ℕ) * ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k])) / 2) := by
        simp [φ, hsecond', lineSearchObjective_zero]
      _ = L xE + (delta k ^ (2 : ℕ) / 2) *
            ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
        ring
  have hJointEventually :
      ∀ᶠ k in atTop,
        problem.objective xStar ≤ problem.objective (xStar + delta k • dSeq k) ∧
          ∃ ξ : ℝ, ξ ∈ Set.uIoo (0 : ℝ) 1 ∧
            L (xE + step k) =
              L xE +
                (delta k ^ (2 : ℕ) / 2) *
                  ((iteratedFDeriv ℝ 2 L (xE + ξ • step k)) ![dEk k, dEk k]) := by
    filter_upwards [hObjectiveEventually, hTaylorEventually] with k hkObj hkTaylor
    exact ⟨hkObj, hkTaylor⟩
  rcases Filter.eventually_atTop.1 hJointEventually with ⟨N, hN⟩
  let ξ : ℕ → ℝ := fun k ↦
    if hk : N ≤ k then Classical.choose ((hN k hk).2) else 0
  let q : ℕ → ℝ := fun k ↦
    (iteratedFDeriv ℝ 2 L (xE + ξ k • step k)) ![dEk k, dEk k]
  have hξIcc : ∀ k, ξ k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    by_cases hk : N ≤ k
    · have hspec := Classical.choose_spec ((hN k hk).2)
      have hξ_eq : ξ k = Classical.choose ((hN k hk).2) := by
        simp [ξ, hk]
      have hspec' : 0 < ξ k ∧ ξ k < 1 := by
        rw [hξ_eq]
        simpa [min_eq_left zero_le_one, max_eq_right zero_le_one] using hspec.1
      exact ⟨le_of_lt hspec'.1, le_of_lt hspec'.2⟩
    · simp [ξ, hk]
  have hq_nonneg_eventually : ∀ᶠ k in atTop, q k ∈ Set.Ici (0 : ℝ) := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro k hk
    have hkObj : problem.objective xStar ≤ problem.objective (xStar + delta k • dSeq k) :=
      (hN k hk).1
    have hspec := Classical.choose_spec ((hN k hk).2)
    have hkTaylor :
        L (xE + step k) = L xE + (delta k ^ (2 : ℕ) / 2) * q k := by
      simpa [ξ, q, hk] using hspec.2
    have hstepEq :
        xE + step k = WithLp.toLp 2 (xStar + delta k • dSeq k) := by
      simp [xE, step, dEk, WithLp.toLp_add, WithLp.toLp_smul]
    have hvalue :
        L xE ≤ L (xE + step k) := by
      calc
        L xE = problem.objective xStar := hBaseLagrangian
        _ ≤ problem.objective (xStar + delta k • dSeq k) := hkObj
        _ = L (WithLp.toLp 2 (xStar + delta k • dSeq k)) := by
          symm
          exact hSeqLagrangian k
        _ = L (xE + step k) := by rw [← hstepEq]
    have hfactor_pos : 0 < delta k ^ (2 : ℕ) / 2 := by
      have : 0 < delta k := hdelta_pos k
      positivity
    have : 0 ≤ q k := by
      nlinarith [hvalue]
    exact this
  have hz :
      Tendsto (fun k ↦ xE + ξ k • step k) atTop (nhds xE) :=
    intermediate_trace_points_tendsto_base hstep hξIcc
  have hC2Base : ContDiffAt ℝ 2 L xE :=
    contDiffAt_euclideanLagrangian problem xStar lamStar h_objective h_constraints
  have hq_tendsto :
      Tendsto q atTop (nhds ((iteratedFDeriv ℝ 2 L xE) ![dE, dE])) := by
    exact iteratedFDeriv_diag_tendsto_of_tendsto hC2Base hz hdEk
  have hlimit_mem : (iteratedFDeriv ℝ 2 L xE) ![dE, dE] ∈ Set.Ici (0 : ℝ) :=
    isClosed_Ici.mem_of_tendsto hq_tendsto hq_nonneg_eventually
  have _ := h_cq
  rw [hHessianRewrite]
  exact hlimit_mem

/-- Chapter08 Theorem 8.3.3 (2): under the same hypotheses, if the source sets
`S(xStar, lamStar)` and `G(xStar, lamStar)` coincide, then the same Hessian nonnegativity
conclusion holds for every direction in
`problem.linearizedNullConstraintDirections xStar lamStar = G(xStar, lamStar)`. -/
theorem secondOrderNecessaryCondition_on_linearizedNullConstraintDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar)
    (h_cq : problem.ConstraintQualificationAt xStar)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (hSG :
      problem.sequentialNullConstraintDirections xStar lamStar =
        problem.linearizedNullConstraintDirections xStar lamStar)
    (hd : d ∈ problem.linearizedNullConstraintDirections xStar lamStar) :
    0 ≤ problem.lagrangianHessianQuadratic xStar lamStar d := by
  have hdS : d ∈ problem.sequentialNullConstraintDirections xStar lamStar := by
    rwa [hSG]
  exact secondOrderNecessaryCondition_on_sequentialNullConstraintDirections
    problem xStar d lamStar h_localMin h_objective h_constraints h_cq h_kkt hdS

end ConstrainedOptimizationProblem

end Chapter08Theorem833
