/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_14
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_18
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3

noncomputable section

open Filter InnerProductSpace
open scoped Gradient

section Chapter08Theorem834

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => Fin m → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: second-order sufficient conditions for constrained nonlinear programming
-- * source-facing owner in the chapter: `ConstrainedOptimizationProblem`
-- * inspected owner-chain declarations:
--   `ConstrainedOptimizationProblem.IsKKTPoint` and
--   `ConstrainedOptimizationProblem.linearizedNullConstraintDirections`
--   from `Definition_8_3_2`
-- * inspected theorem-local owner:
--   `ConstrainedOptimizationProblem.lagrangianHessianQuadratic`
--   from `Theorem_8_3_3`
-- * layer targeted here: source-facing theorem stated on the existing owner chain, not a new
--   wrapper or duplicate critical-cone API
-- * primitive data reused: constrained problem, feasible set, KKT pair, and
--   `linearizedNullConstraintDirections = G(xStar, lamStar)`
-- * derived API reused: `lagrangianHessianQuadratic`

/-- Helper for Chapter08 Theorem 8.3.4: at any feasible point, the Euclidean Lagrangian does not
exceed the objective value. -/
lemma lagrangian_le_objective_of_feasible
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar x : Point) (lamStar : Multiplier)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (hx : x ∈ problem.feasibleSet) :
    problem.euclideanLagrangian lamStar (WithLp.toLp 2 x) ≤ problem.objective x := by
  have hcoord :
      (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  have hx_feasible := (problem.mem_feasibleSet_iff x).1 hx
  have hweighted_nonneg :
      0 ≤ ∑ i : Fin m, lamStar i * problem.constraint i x := by
    refine Finset.sum_nonneg fun i _ ↦ ?_
    have hi_union : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
      simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
        using (show i ∈ E ∪ I from by
          rw [problem.eqIndices_union_ineqIndices]
          simp)
    rcases hi_union with hi_eq | hi_ineq
    · simp [hx_feasible.1 i hi_eq]
    · exact mul_nonneg (h_kkt.dualFeasible i hi_ineq) (hx_feasible.2 i hi_ineq)
  -- Expand the Lagrangian and use the nonnegativity of the weighted constraint correction.
  rw [problem.euclideanLagrangian_apply, problem.lagrangian_eq, hcoord]
  linarith

/-- Helper for Chapter08 Theorem 8.3.4: a nonzero linearized feasible direction whose objective
pairing is nonpositive must lie in `G(xStar, lamStar)`. -/
lemma mem_linearizedNullConstraintDirections_of_linearizedFeasible_of_objective_pairing_nonpos
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (hd_linearized : d ∈ problem.linearizedFeasibleDirectionSet xStar)
    (hd_nonzero : d ≠ 0)
    (h_objective_nonpos : fderiv ℝ problem.objective xStar d ≤ 0) :
    d ∈ problem.linearizedNullConstraintDirections xStar lamStar := by
  classical
  rcases (problem.mem_linearizedFeasibleDirectionSet_iff_explicit xStar d).1 hd_linearized with
    ⟨_, _, h_eq_pairing, h_active_nonneg⟩
  have hstationary :
      fderiv ℝ problem.objective xStar d =
        ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i :=
    stationarity_pairing_eq_weighted_constraint_sum h_kkt h_objective h_constraints
  have hterm_nonneg :
      ∀ i : Fin m, 0 ≤ lamStar i * problem.linearizedConstraintPairing xStar d i := by
    intro i
    have hi_union : i ∈ problem.eqIndices ∪ problem.ineqIndices := by
      simpa [ConstrainedOptimizationProblem.eqIndices, ConstrainedOptimizationProblem.ineqIndices]
        using (show i ∈ E ∪ I from by
          rw [problem.eqIndices_union_ineqIndices]
          simp)
    rcases hi_union with hi_eq | hi_ineq
    · rw [h_eq_pairing i hi_eq, mul_zero]
    · by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
      · exact mul_nonneg (h_kkt.dualFeasible i hi_ineq) (h_active_nonneg i hi_active)
      · have hi_not_eq : i ∉ problem.eqIndices := by
          intro hi_eq
          have hdisj : Disjoint problem.eqIndices problem.ineqIndices := by
            simpa [ConstrainedOptimizationProblem.eqIndices,
              ConstrainedOptimizationProblem.ineqIndices] using
              problem.eqIndices_disjoint_ineqIndices
          exact Set.disjoint_left.mp hdisj hi_eq hi_ineq
        have hi_not_constraint : i ∉ problem.activeConstraintIndexSet xStar := by
          rw [problem.activeConstraintIndexSet_def]
          simpa [hi_not_eq, hi_active]
        have hi_pos :
            0 < problem.constraint i xStar :=
          (problem.not_mem_activeConstraintIndexSet_iff h_kkt.feasible i).1 hi_not_constraint |>.2
        have hlam_zero : lamStar i = 0 := by
          exact
            (mul_eq_zero.mp (h_kkt.complementarySlackness i hi_ineq)).resolve_right hi_pos.ne'
        simp [hlam_zero]
  have hweighted_nonneg :
      0 ≤ ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i := by
    exact Finset.sum_nonneg fun i _ ↦ hterm_nonneg i
  have hweighted_nonpos :
      ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i ≤ 0 := by
    simpa [hstationary] using h_objective_nonpos
  have hweighted_zero :
      ∑ i : Fin m, lamStar i * problem.linearizedConstraintPairing xStar d i = 0 :=
    le_antisymm hweighted_nonpos hweighted_nonneg
  refine
    (problem.mem_linearizedNullConstraintDirections_iff xStar lamStar d).2
      ⟨hd_linearized, hd_nonzero, ?_⟩
  intro i hi_pos
  have hi_active :
      i ∈ problem.activeIneqIndexSet xStar :=
    (problem.mem_positiveActiveIneqIndexSet_iff xStar lamStar i).1 hi_pos |>.1
  have hlam_pos : 0 < lamStar i :=
    (problem.mem_positiveActiveIneqIndexSet_iff xStar lamStar i).1 hi_pos |>.2
  have hterm_le_zero :
      lamStar i * problem.linearizedConstraintPairing xStar d i ≤ 0 := by
    have hsingle :
        lamStar i * problem.linearizedConstraintPairing xStar d i ≤
          ∑ j : Fin m, lamStar j * problem.linearizedConstraintPairing xStar d j := by
      simpa using
        (Finset.single_le_sum
          (fun j _ ↦ hterm_nonneg j)
          (by simp : i ∈ Finset.univ))
    rw [hweighted_zero] at hsingle
    exact hsingle
  have hterm_zero :
      lamStar i * problem.linearizedConstraintPairing xStar d i = 0 :=
    le_antisymm hterm_le_zero (hterm_nonneg i)
  exact (mul_eq_zero.mp hterm_zero).resolve_left (ne_of_gt hlam_pos)

/-- Helper for Chapter08 Theorem 8.3.4: a sequence of upper Lagrangian comparisons along a
shrinking trace forces the limiting Hessian quadratic value to be nonpositive. -/
lemma lagrangianHessianQuadratic_nonpos_of_lagrangian_upper_along_trace
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar d : Point) (lamStar : Multiplier)
    (dSeq : ℕ → Point) (delta : ℕ → ℝ)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar)
    (h_delta_pos : ∀ k, 0 < delta k)
    (hdSeq : Tendsto dSeq atTop (nhds d))
    (hdelta : Tendsto delta atTop (nhds (0 : ℝ)))
    (h_upper :
      ∀ k,
        problem.euclideanLagrangian lamStar (WithLp.toLp 2 (xStar + delta k • dSeq k)) ≤
          problem.euclideanLagrangian lamStar (WithLp.toLp 2 xStar)) :
    problem.lagrangianHessianQuadratic xStar lamStar d ≤ 0 := by
  let L : EPoint → ℝ := problem.euclideanLagrangian lamStar
  let xE : EPoint := WithLp.toLp 2 xStar
  let dE : EPoint := WithLp.toLp 2 d
  let dEk : ℕ → EPoint := fun k ↦ WithLp.toLp 2 (dSeq k)
  let step : ℕ → EPoint := fun k ↦ delta k • dEk k
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
    -- The traced increments are the shrinking steps `delta k • dSeq k` in Euclidean coordinates.
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
      -- The zero first derivative is the Taylor expansion point for the contradiction trace.
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
      -- The linear Taylor term vanishes, so only the quadratic remainder remains.
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
  rcases Filter.eventually_atTop.1 hTaylorEventually with ⟨N, hN⟩
  let ξ : ℕ → ℝ := fun k ↦
    if hk : N ≤ k then Classical.choose (hN k hk) else 0
  let q : ℕ → ℝ := fun k ↦
    (iteratedFDeriv ℝ 2 L (xE + ξ k • step k)) ![dEk k, dEk k]
  have hξIcc : ∀ k, ξ k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    by_cases hk : N ≤ k
    · have hspec := Classical.choose_spec (hN k hk)
      have hξ_eq : ξ k = Classical.choose (hN k hk) := by
        simp [ξ, hk]
      have hspec' : 0 < ξ k ∧ ξ k < 1 := by
        rw [hξ_eq]
        simpa [min_eq_left zero_le_one, max_eq_right zero_le_one] using hspec.1
      exact ⟨le_of_lt hspec'.1, le_of_lt hspec'.2⟩
    · simp [ξ, hk]
  have hq_nonpos_eventually : ∀ᶠ k in atTop, q k ∈ Set.Iic (0 : ℝ) := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro k hk
    have hspec := Classical.choose_spec (hN k hk)
    have hkTaylor :
        L (xE + step k) = L xE + (delta k ^ (2 : ℕ) / 2) * q k := by
      simpa [ξ, q, hk] using hspec.2
    have hstepEq :
        xE + step k = WithLp.toLp 2 (xStar + delta k • dSeq k) := by
      simp [xE, step, dEk, WithLp.toLp_add, WithLp.toLp_smul]
    have hvalue :
        L (xE + step k) ≤ L xE := by
      calc
        L (xE + step k) = L (WithLp.toLp 2 (xStar + delta k • dSeq k)) := by
          rw [hstepEq]
        _ ≤ L (WithLp.toLp 2 xStar) := h_upper k
        _ = L xE := by
          simp [xE]
    have hfactor_pos : 0 < delta k ^ (2 : ℕ) / 2 := by
      have : 0 < delta k := h_delta_pos k
      positivity
    have : q k ≤ 0 := by
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
  have hlimit_mem : (iteratedFDeriv ℝ 2 L xE) ![dE, dE] ∈ Set.Iic (0 : ℝ) :=
    isClosed_Iic.mem_of_tendsto hq_tendsto hq_nonpos_eventually
  rw [hHessianRewrite]
  exact hlimit_mem

/-- Chapter08 Theorem 8.3.4: if `xStar` is a KKT point of `problem` with multiplier vector
`lamStar`, the objective and every constraint are twice continuously differentiable at `xStar`,
and the Lagrangian Hessian quadratic form is strictly positive on every direction in
`problem.linearizedNullConstraintDirections xStar lamStar = G(xStar, lamStar)`, then `xStar` is
a strict local minimizer of `problem.objective` on `problem.feasibleSet`. -/
theorem isStrictLocalMinOn_of_positive_lagrangianHessian_on_linearizedNullConstraintDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier)
    (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar)
    (h_positive :
      ∀ d ∈ problem.linearizedNullConstraintDirections xStar lamStar,
        0 < problem.lagrangianHessianQuadratic xStar lamStar d) :
    IsStrictLocalMinOn problem.objective problem.feasibleSet xStar := by
  have hxStar : xStar ∈ problem.feasibleSet := by
    simpa [problem.feasibleSet_eq_setOf_mem] using h_kkt.feasible
  have h_objective_diff : DifferentiableAt ℝ problem.objective xStar :=
    h_objective.differentiableAt (by norm_num)
  have h_constraints_diff : problem.HasConstraintGradientsAt xStar := by
    intro i
    exact (h_constraints i).differentiableAt (by norm_num)
  by_contra h_not
  rcases existsCounterexampleSequence_of_not_isStrictLocalMinOn hxStar h_not with ⟨xSeq, hxSeq⟩
  let badSet : Set Point :=
    problem.feasibleSet ∩ {x : Point | problem.objective x ≤ problem.objective xStar}
  have hxSeq_mem : ∀ k, xSeq k ∈ problem.feasibleSet := fun k ↦ (hxSeq k).1
  have hxSeq_ne : ∀ k, xSeq k ≠ xStar := fun k ↦ (hxSeq k).2.1
  have hxSeq_bound :
      ∀ k, ‖xSeq k - xStar‖ ≤ 1 / ((k : ℝ) + 1) := fun k ↦ (hxSeq k).2.2.1
  have hxSeq_le :
      ∀ k, problem.objective (xSeq k) ≤ problem.objective xStar := fun k ↦ (hxSeq k).2.2.2
  have hxSeq_bad : ∀ k, xSeq k ∈ badSet := fun k ↦ ⟨hxSeq_mem k, hxSeq_le k⟩
  have hxSeq_norm_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖) atTop (nhds (0 : ℝ)) := by
    -- The counterexample sequence lies in shrinking closed balls around `xStar`.
    refine squeeze_zero (fun k ↦ norm_nonneg _) hxSeq_bound tendsto_one_div_add_atTop_nhds_zero_nat
  have hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hxSeq_norm_tendsto
  rcases existsTendstoNormalizedDisplacementSubseq hxSeq_ne with ⟨d, hd_sphere, φ, hφ, hd_tendsto⟩
  have hsubseq_tendsto : Tendsto (xSeq ∘ φ) atTop (nhds xStar) :=
    hxSeq_tendsto.comp hφ.tendsto_atTop
  have hd_bad :
      d ∈ posTangentConeAt badSet xStar := by
    -- The normalized bad subsequence yields a tangent-cone direction of the bad set.
    refine memPosTangentConeAt_of_tendstoNormalizedDisplacement ?_ ?_ hsubseq_tendsto hd_tendsto
    · intro k
      exact hxSeq_bad (φ k)
    · intro k
      exact hxSeq_ne (φ k)
  have hd_feasible :
      d ∈ posTangentConeAt problem.feasibleSet xStar :=
    tangentConeAt_mono (fun x hx ↦ hx.1) hd_bad
  have hd_nonzero : d ≠ 0 := by
    have hd_norm : ‖d‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_sphere
    intro hd_zero
    simp [hd_zero] at hd_norm
  have hd_linearized :
      d ∈ problem.linearizedFeasibleDirectionSet xStar :=
    hasConstraintGradients_subset_linearizedFeasibleDirectionSet
      problem xStar h_kkt.feasible h_constraints_diff hd_feasible
  have h_localMax_bad : IsLocalMaxOn problem.objective badSet xStar := by
    -- On the bad set, the objective is globally bounded above by `problem.objective xStar`.
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.2
  have h_objective_nonpos :
      fderiv ℝ problem.objective xStar d ≤ 0 := by
    -- The local-maximum viewpoint on the bad set gives the nonpositive first-order pairing.
    exact h_localMax_bad.hasFDerivWithinAt_nonpos
      (h_objective_diff.hasFDerivAt.hasFDerivWithinAt) hd_bad
  have hd_null :
      d ∈ problem.linearizedNullConstraintDirections xStar lamStar := by
    -- KKT stationarity and the bad-set sign force the positive-active pairings to vanish.
    exact
      problem.mem_linearizedNullConstraintDirections_of_linearizedFeasible_of_objective_pairing_nonpos
        xStar d lamStar h_kkt h_objective_diff h_constraints_diff hd_linearized hd_nonzero
        h_objective_nonpos
  let delta : ℕ → ℝ := fun k ↦ ‖xSeq (φ k) - xStar‖
  let dSeq : ℕ → Point := fun k ↦ (delta k)⁻¹ • (xSeq (φ k) - xStar)
  have h_delta_pos : ∀ k, 0 < delta k := by
    intro k
    dsimp [delta]
    exact norm_pos_iff.2 (sub_ne_zero.2 (hxSeq_ne (φ k)))
  have hdSeq_tendsto : Tendsto dSeq atTop (nhds d) := by
    simpa [dSeq, delta] using hd_tendsto
  have hdelta_tendsto : Tendsto delta atTop (nhds (0 : ℝ)) := by
    change Tendsto ((fun k ↦ ‖xSeq k - xStar‖) ∘ φ) atTop (nhds (0 : ℝ))
    exact hxSeq_norm_tendsto.comp hφ.tendsto_atTop
  have htrace_eq : ∀ k, xStar + delta k • dSeq k = xSeq (φ k) := by
    intro k
    have hk_ne : delta k ≠ 0 := by
      exact ne_of_gt (h_delta_pos k)
    dsimp [delta, dSeq]
    rw [smul_smul, mul_inv_cancel₀ hk_ne, one_smul]
    simp [sub_eq_add_neg]
  have h_upper :
      ∀ k,
        problem.euclideanLagrangian lamStar (WithLp.toLp 2 (xStar + delta k • dSeq k)) ≤
          problem.euclideanLagrangian lamStar (WithLp.toLp 2 xStar) := by
    intro k
    -- The feasible counterexample sequence keeps both the objective and the Lagrangian
    -- below the base-point value.
    calc
      problem.euclideanLagrangian lamStar (WithLp.toLp 2 (xStar + delta k • dSeq k))
          = problem.euclideanLagrangian lamStar (WithLp.toLp 2 (xSeq (φ k))) := by
              rw [htrace_eq k]
      _ ≤ problem.objective (xSeq (φ k)) := by
            exact problem.lagrangian_le_objective_of_feasible xStar (xSeq (φ k)) lamStar h_kkt
              (hxSeq_mem (φ k))
      _ ≤ problem.objective xStar := hxSeq_le (φ k)
      _ = problem.euclideanLagrangian lamStar (WithLp.toLp 2 xStar) := by
            symm
            exact problem.euclideanLagrangian_eq_objective_at_kktPoint xStar lamStar h_kkt
  have h_hessian_nonpos :
      problem.lagrangianHessianQuadratic xStar lamStar d ≤ 0 := by
    -- Apply the sign-reversed Taylor expansion along the normalized counterexample trace.
    exact
      problem.lagrangianHessianQuadratic_nonpos_of_lagrangian_upper_along_trace
        xStar d lamStar dSeq delta h_kkt h_objective h_constraints h_delta_pos hdSeq_tendsto
        hdelta_tendsto h_upper
  exact (not_le_of_gt (h_positive d hd_null)) h_hessian_nonpos

end ConstrainedOptimizationProblem

end Chapter08Theorem834
