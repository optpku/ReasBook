/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_6_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Lemma_10_6_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_6_1
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Filter

section Chapter10Theorem1065

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `NonsmoothExactPenaltyMethod` in `Algorithm_10_6_4` is the chapter's algorithm owner.
-- * `StandardPenaltyProblem.SecondOrderSufficientCondition` in `Theorem_10_6_1` is the
--   chapter's canonical SOSC owner.
-- * `IsStrictLocalMinOn` in `Chapter08.Definition_8_1_3` is the canonical constrained strict
--   local-minimum owner.
-- * `StandardPenaltyProblem.nonsmoothExactPenalty` in `Definition_10_6_extra_1` is the
--   canonical exact-penalty owner already used by the algorithm layer.
-- This file therefore keeps only the convergence layer specific to Theorem 10.6.5.

/-- A point satisfying the Chapter 10 second-order sufficient condition is a strict local
minimizer of the constrained problem on its feasible set. -/
theorem isStrictLocalMinOn_of_secondOrderSufficientCondition
    (problem : StandardPenaltyProblem n m) {xStar : Point} {lamStar : ConstraintPoint}
    (h_sosc : problem.SecondOrderSufficientCondition xStar lamStar) :
    IsStrictLocalMinOn problem.objective problem.feasibleSet xStar := by
  -- Transport the Chapter 10 `C²` data to the canonical Chapter 8 bridge.
  have h_bridge_data :
      ContDiffAt ℝ 2 problem.toConstrainedOptimizationProblem.objective xStar.ofLp ∧
        ∀ i,
          ContDiffAt ℝ 2 (problem.toConstrainedOptimizationProblem.constraint i) xStar.ofLp :=
    toConstrainedOptimizationProblem_contDiffAt_data
      problem xStar h_sosc.objective_contDiffAt h_sosc.constraint_contDiffAt
  have h_positive :
      ∀ d ∈
          problem.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
            xStar.ofLp lamStar.ofLp,
        0 <
          problem.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
            xStar.ofLp lamStar.ofLp d := by
    intro d hd
    -- The Chapter 8 null-direction set sits inside the Chapter 10 linearized feasible set.
    have hd_feasible_bridge :
        d ∈ problem.toConstrainedOptimizationProblem.linearizedFeasibleDirectionSet xStar.ofLp :=
      ConstrainedOptimizationProblem.linearizedNullConstraintDirections_subset_linearizedFeasible
        problem.toConstrainedOptimizationProblem
        xStar.ofLp
        lamStar.ofLp
        hd
    have hd_feasible :
        WithLp.toLp 2 d ∈ problem.linearizedFeasibleDirectionSet xStar := by
      change d ∈
        problem.toConstrainedOptimizationProblem.linearizedFeasibleDirectionSet xStar.ofLp
      simpa using hd_feasible_bridge
    have hd_ne : WithLp.toLp 2 d ≠ 0 := by
      intro hd_zero
      have hd_zero' : d = 0 := by
        simpa using congrArg WithLp.ofLp hd_zero
      exact
        ((problem.toConstrainedOptimizationProblem.mem_linearizedNullConstraintDirections_iff
          xStar.ofLp lamStar.ofLp d).1 hd).2.1 hd_zero'
    -- Apply the source SOSC positivity on the transported direction.
    simpa [StandardPenaltyProblem.lagrangianHessianQuadratic_eq] using
      h_sosc.lagrangianHessianQuadratic_pos (WithLp.toLp 2 d) hd_feasible hd_ne
  have h_bridge_strict :
      IsStrictLocalMinOn
        problem.toConstrainedOptimizationProblem.objective
        problem.toConstrainedOptimizationProblem.feasibleSet
        xStar.ofLp :=
    ConstrainedOptimizationProblem.isStrictLocalMinOn_of_positive_lagrangianHessian_on_linearizedNullConstraintDirections
      problem.toConstrainedOptimizationProblem
      xStar.ofLp
      lamStar.ofLp
      h_sosc.isLagrangeMultiplier.toIsKKTPoint
      h_bridge_data.1
      h_bridge_data.2
      h_positive
  refine ⟨?_, ?_⟩
  · -- Feasibility transports directly across the mixed-constraint bridge.
    exact (problem.mem_toConstrainedOptimizationProblem_iff xStar).1 h_bridge_strict.mem
  · -- Transport the strict neighborhood comparison back through the `PiLp` homeomorphism.
    let e : Point ≃L[ℝ] (Fin n → ℝ) :=
      PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
    have h_image :
        e '' (problem.feasibleSet \ {xStar}) =
          problem.toConstrainedOptimizationProblem.feasibleSet \ {xStar.ofLp} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨hx_feasible, hx_ne⟩
        refine ⟨?_, ?_⟩
        · exact (problem.mem_toConstrainedOptimizationProblem_iff x).2 hx_feasible
        · intro h_eq
          have h_eq' : x = xStar := by
            simpa [e] using congrArg (WithLp.toLp 2) h_eq
          exact hx_ne h_eq'
      · intro hy
        refine ⟨e.symm y, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · exact
              (problem.mem_toConstrainedOptimizationProblem_iff (e.symm y)).1
                (by
                  simpa [ConstrainedOptimizationProblem.feasibleSet_eq_setOf_mem, e] using hy.1)
          · intro h_eq
            have h_eq' : y = xStar.ofLp := by
              have h_eq'' : WithLp.toLp 2 y = xStar := by
                simpa [e] using h_eq
              simpa using congrArg WithLp.ofLp h_eq''
            exact hy.2 h_eq'
        · exact e.apply_symm_apply y
    have h_embedding := e.toHomeomorph.isEmbedding
    have h_map :
        Filter.map e (nhdsWithin xStar (problem.feasibleSet \ {xStar})) =
          nhdsWithin (e xStar) (e '' (problem.feasibleSet \ {xStar})) :=
      h_embedding.map_nhdsWithin_eq _ _
    have h_eventually_bridge :
        {y : Fin n → ℝ |
            problem.toConstrainedOptimizationProblem.objective xStar.ofLp <
              problem.toConstrainedOptimizationProblem.objective y} ∈
          Filter.map e (nhdsWithin xStar (problem.feasibleSet \ {xStar})) := by
      rw [h_map, h_image]
      exact h_bridge_strict.eventually_lt
    -- Reinterpret the mapped event as the original strict comparison on `Point`.
    change
      e ⁻¹'
          {y : Fin n → ℝ |
            problem.toConstrainedOptimizationProblem.objective xStar.ofLp <
              problem.toConstrainedOptimizationProblem.objective y} ∈
        nhdsWithin xStar (problem.feasibleSet \ {xStar})
    simpa [e, StandardPenaltyProblem.toConstrainedOptimizationProblem_objective_apply]
      using h_eventually_bridge

/-- Under the strong-distance-kernel assumptions of Algorithm 10.6.4, if `xStar` satisfies the
Chapter 10 second-order sufficient condition for some multiplier vector, then `xStar` is a strict
local minimizer of the exact-penalty stage objective for all sufficiently large penalty
parameters. This is the source-facing strict-penalty conclusion used in the divergence branch of
Theorem 10.6.5, stated with the canonical unconstrained owner `IsStrictLocalMin`. -/
theorem exists_penaltyThreshold_for_isStrictLocalMin_nonsmoothExactPenalty
    (method : NonsmoothExactPenaltyMethod n m) {xStar : Point}
    (h_sosc :
      ∃ lamStar : ConstraintPoint, method.problem.SecondOrderSufficientCondition xStar lamStar) :
    ∃ σBar : ℝ,
      ∀ {σ : ℝ}, σBar < σ →
        IsStrictLocalMin
          (method.problem.nonsmoothExactPenalty method.penaltyKernel σ)
          xStar := by
  rcases h_sosc with ⟨lamStar, h_sosc⟩
  rcases IsStrongDistanceFunction.exists_pos_mul_l1Norm_le method.penaltyKernel with
    ⟨δ, hδ, h_lower_l1⟩
  refine ⟨‖lamStar‖∞ / δ, ?_⟩
  intro σ hσ
  have h_sigma : σ * δ > ‖lamStar‖∞ := by
    exact (div_lt_iff₀ hδ).mp hσ
  exact
    isStrictLocalMin_nonsmoothExactPenalty_of_secondOrderSufficientCondition
      method.problem xStar lamStar σ δ method.penaltyKernel h_sosc hδ h_lower_l1 h_sigma

namespace NonsmoothExactPenaltyMethod

/-- Helper for Chapter10 Theorem 10.6.5: `method.doesNotTerminateFinitely` means that every stage
`k ≥ 1` is reached, so Algorithm 10.6.4 never stops after finitely many reached stages. -/
def doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m) : Prop :=
  ∀ k, 1 ≤ k → method.reached k

/-- Helper for Chapter10 Theorem 10.6.5: unfolding `method.doesNotTerminateFinitely` gives the
pointwise nontermination condition that every stage `k ≥ 1` is reached. -/
theorem doesNotTerminateFinitely_iff
    (method : NonsmoothExactPenaltyMethod n m) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → method.reached k :=
  Iff.rfl

/-- Helper for Chapter10 Theorem 10.6.5: if Algorithm 10.6.4 does not terminate finitely, then
every stage `k ≥ 1` is reached. -/
theorem reached_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) (k : ℕ) (hk : 1 ≤ k) :
    method.reached k :=
  method.doesNotTerminateFinitely_iff.mp hNoTerminate k hk

/-- Helper for Chapter10 Theorem 10.6.5: if Algorithm 10.6.4 does not terminate finitely, then
every stage `k ≥ 1` fails the source stopping test. -/
theorem not_terminatedAt_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) {k : ℕ} (hk : 1 ≤ k) :
    ¬ method.terminatedAt k := by
  have hreached : method.reached k :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate k hk
  have hreachedSucc : method.reached (k + 1) :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate (k + 1)
      (Nat.succ_le_succ (Nat.zero_le k))
  -- The stage-successor characterization turns reachability of `k + 1` into nontermination at `k`.
  exact (method.reached_succ_iff_not_terminatedAt hk hreached).1 hreachedSucc

/-- Helper for Chapter10 Theorem 10.6.5: if no reached stage satisfies the stopping test, then
Algorithm 10.6.4 lies in the canonical nontermination regime. -/
lemma doesNotTerminateFinitely_of_no_reached_terminated_stage
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoStage : ¬ ∃ k : ℕ, 1 ≤ k ∧ method.reached k ∧ method.terminatedAt k) :
    method.doesNotTerminateFinitely := by
  -- Build the reached prefix inductively from the absence of any reached terminating stage.
  rw [method.doesNotTerminateFinitely_iff]
  intro k hk
  have hReachedAll : ∀ t : ℕ, method.reached (t + 1) := by
    intro t
    induction t with
    | zero =>
        simpa using method.reached_one
    | succ t ht =>
        have htt : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
        refine (method.reached_succ_iff_not_terminatedAt htt ht).2 ?_
        intro hterm
        exact hNoStage ⟨t + 1, htt, ht, hterm⟩
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  simpa [Nat.add_comm] using hReachedAll t

/-- Helper for Chapter10 Theorem 10.6.5: under the theorem hypotheses, any reached terminating
stage already yields a strict constrained local minimizer of the original problem. -/
theorem terminated_stage_isStrictLocalMinOn
    (method : NonsmoothExactPenaltyMethod n m)
    {k : ℕ} (hk : 1 ≤ k) (hreached : method.reached k) (hterm : method.terminatedAt k)
    (h_sosc :
      ∀ ⦃xStar : Point⦄,
        IsLocalMinOn method.problem.objective method.problem.feasibleSet xStar →
          ∃ lamStar : ConstraintPoint,
            method.problem.SecondOrderSufficientCondition xStar lamStar) :
    IsStrictLocalMinOn
      method.problem.objective
      method.problem.feasibleSet
      (method.subproblemSolution k) := by
  have h_zero :
      method.penaltyKernel
        (c⁽-⁾[method.problem] (method.subproblemSolution k)) = 0 := by
    -- Termination means the violation vector vanishes, so the strong-distance kernel also vanishes.
    rw [hterm]
    exact IsStrongDistanceFunction.apply_zero method.penaltyKernel
  have h_localPenalty :
      IsLocalMinOn
        (method.problem.nonsmoothExactPenalty method.penaltyKernel (method.penaltyParameter k))
        Set.univ
        (method.subproblemSolution k) :=
    (method.subproblemSolution_isMinimizer hk hreached).localize
  have h_localObjective :
      IsLocalMinOn
        method.problem.objective
        method.problem.feasibleSet
        (method.subproblemSolution k) :=
    isLocalMinOn_objective_on_feasibleSet_of_isLocalMinOn_nonsmoothExactPenalty
      method.problem
      method.penaltyKernel
      h_zero
      h_localPenalty
  rcases h_sosc h_localObjective with ⟨lamStar, h_stage_sosc⟩
  -- Apply the already proved SOSC-to-strict-local-min bridge at this terminating stage.
  exact isStrictLocalMinOn_of_secondOrderSufficientCondition method.problem h_stage_sosc

/-- Helper for Chapter10 Theorem 10.6.5: in the nonterminating regime, each update satisfies
`x_(k + 1) = x(σ_k)`. -/
theorem iterate_succ_eq_subproblemSolution_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) = method.subproblemSolution k := by
  have hreached : method.reached k :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate k hk
  exact method.iterate_update_eq hk hreached
    (method.not_terminatedAt_of_doesNotTerminateFinitely hNoTerminate hk)

/-- Helper for Chapter10 Theorem 10.6.5: in the nonterminating regime, the penalty parameter
updates geometrically as `σ_(k + 1) = 10 * σ_k`. -/
theorem penaltyParameter_succ_eq_ten_mul_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {k : ℕ} (hk : 1 ≤ k) :
    method.penaltyParameter (k + 1) = 10 * method.penaltyParameter k := by
  have hreached : method.reached k :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate k hk
  exact method.penaltyParameter_update_eq hk hreached
    (method.not_terminatedAt_of_doesNotTerminateFinitely hNoTerminate hk)

/-- Helper for Chapter10 Theorem 10.6.5: the strong-distance penalty kernel is nonnegative on
every violation vector. -/
theorem penaltyKernel_nonneg
    (method : NonsmoothExactPenaltyMethod n m)
    (c : ConstraintPoint) :
    0 ≤ method.penaltyKernel c := by
  -- Use the global `ℓ₁` lower bound from the strong-distance hypothesis.
  rcases IsStrongDistanceFunction.exists_pos_mul_l1Norm_le method.penaltyKernel with
    ⟨δ, hδ, hδle⟩
  have hl1Nonneg : 0 ≤ ‖c‖₁ := by
    rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  exact le_trans (mul_nonneg hδ.le hl1Nonneg) (hδle c)

/-- Helper for Chapter10 Theorem 10.6.5: in the nonterminating regime, the stage parameters obey
the geometric closed form `σ_k = 10^(k - 1) * σ₁` for every `k ≥ 1`. -/
theorem penaltyParameter_eq_pow_mul_initial_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {k : ℕ} (hk : 1 ≤ k) :
    method.penaltyParameter k =
      (10 : ℝ) ^ (k - 1) * method.initialPenaltyParameter := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  induction t with
  | zero =>
      -- The first stage uses the recorded initial penalty parameter.
      simpa [method.penaltyParameter_one]
  | succ t iht =>
      have hstage : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
      -- Each nonterminating step multiplies the previous stage parameter by `10`.
      calc
        method.penaltyParameter (1 + (t + 1))
            = method.penaltyParameter ((t + 1) + 1) := by simp [Nat.add_assoc, Nat.add_comm]
        _ = 10 * method.penaltyParameter (t + 1) :=
          method.penaltyParameter_succ_eq_ten_mul_of_doesNotTerminateFinitely
            hNoTerminate hstage
        _ = 10 * ((10 : ℝ) ^ ((t + 1) - 1) * method.initialPenaltyParameter) := by
          have iht' :
              method.penaltyParameter (t + 1) =
                (10 : ℝ) ^ ((t + 1) - 1) * method.initialPenaltyParameter := by
            simpa [Nat.add_comm] using
              (iht (by simpa using Nat.succ_le_succ (Nat.zero_le t)))
          rw [iht']
        _ = (10 : ℝ) ^ (t + 1) * method.initialPenaltyParameter := by
          simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ = (10 : ℝ) ^ ((1 + (t + 1)) - 1) * method.initialPenaltyParameter := by
          simp

/-- Helper for Chapter10 Theorem 10.6.5: if the iterate norms do not diverge to `+∞`, then a
bounded subsequence of the generated iterates has an accumulation point. -/
theorem exists_accumulationPoint_iterate_of_not_tendsto_norm_atTop
    (method : NonsmoothExactPenaltyMethod n m)
    (hNotTendsto :
      ¬ Tendsto (fun k : ℕ ↦ ‖method.iterate (k + 1)‖) atTop atTop) :
    ∃ xHat : Point, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xHat) := by
  rw [Filter.tendsto_atTop_atTop] at hNotTendsto
  push_neg at hNotTendsto
  rcases hNotTendsto with ⟨R, hR⟩
  have hFrequentlyBounded :
      ∃ᶠ k in atTop, method.iterate (k + 1) ∈ Metric.closedBall (0 : Point) (max R 0) := by
    rw [Filter.frequently_atTop]
    intro N
    rcases hR N with ⟨k, hNk, hkR⟩
    refine ⟨k, hNk, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (le_of_lt hkR) (le_max_left _ _)
  -- Extract the convergent subsequence from the frequently bounded iterates.
  rcases tendsto_subseq_of_frequently_bounded
      (Metric.isBounded_closedBall (x := (0 : Point)) (r := max R 0))
      hFrequentlyBounded with
    ⟨xHat, _hxHatClosure, φ, hφ, hxHat⟩
  refine ⟨xHat, φ, hφ, ?_⟩
  convert hxHat using 1
  funext k
  rfl

/-- Helper for Chapter10 Theorem 10.6.5: along any convergent subsequence of iterates in the
nonterminating regime, the accumulation point is feasible for the original constrained problem. -/
theorem accumulationPoint_mem_feasibleSet_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (hfeasible : Set.Nonempty method.problem.feasibleSet)
    (h_objectiveContDiff : ContDiff ℝ 2 method.problem.objective)
    (h_constraintContDiff : ∀ i, ContDiff ℝ 2 (method.problem.constraint i))
    (hNoTerminate : method.doesNotTerminateFinitely)
    {xHat : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxHat : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xHat)) :
    xHat ∈ method.problem.feasibleSet := by
  rcases hfeasible with ⟨xFeas, hxFeas⟩
  rcases IsStrongDistanceFunction.exists_pos_mul_l1Norm_le method.penaltyKernel with
    ⟨δ, hδ, hδle⟩
  let ψ : ℕ → ℕ := fun k ↦ φ (k + 1)
  have hψPos : ∀ k : ℕ, 1 ≤ ψ k := by
    intro k
    have hlt : φ 0 < φ (k + 1) := hφ (Nat.succ_pos k)
    dsimp [ψ]
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hxHatShift :
      Tendsto (fun k : ℕ ↦ method.iterate (ψ k + 1)) atTop (nhds xHat) := by
    -- Shift once so every stage index used below is at least `1`.
    convert hxHat.comp (Filter.tendsto_add_atTop_nat 1) using 1
    funext k
    rfl
  have hObjectiveTendsto :
      Tendsto
        (fun k : ℕ ↦ method.problem.objective (method.iterate (ψ k + 1)))
        atTop
        (nhds (method.problem.objective xHat)) :=
    h_objectiveContDiff.continuous.continuousAt.tendsto.comp hxHatShift
  let C : ℝ := max (method.problem.objective xFeas - method.problem.objective xHat + 1) 1
  have hObjectiveLower :
      ∀ᶠ k in atTop,
        method.problem.objective xHat - 1 <
          method.problem.objective (method.iterate (ψ k + 1)) := by
    exact hObjectiveTendsto.eventually (Ioi_mem_nhds (by linarith))
  have hPenaltyLower :
      ∀ k : ℕ,
        (10 : ℝ) ^ k * method.initialPenaltyParameter ≤ method.penaltyParameter (ψ k) := by
    intro k
    have hIndexLe : k + 1 ≤ ψ k := by
      simpa [ψ] using hφ.id_le (k + 1)
    have hPowIndex : k ≤ ψ k - 1 := by
      simpa using Nat.sub_le_sub_right hIndexLe 1
    rw [method.penaltyParameter_eq_pow_mul_initial_of_doesNotTerminateFinitely hNoTerminate
      (hψPos k)]
    have hPowLe :
        (10 : ℝ) ^ k ≤ (10 : ℝ) ^ (ψ k - 1) := by
      exact pow_le_pow_right₀ (by norm_num) hPowIndex
    exact mul_le_mul_of_nonneg_right hPowLe method.initialPenaltyParameterPos.le
  have hGeometricTendsto :
      Tendsto
        (fun k : ℕ ↦ (10 : ℝ) ^ k * method.initialPenaltyParameter)
        atTop
        atTop := by
    have hPowTendsto :
        Tendsto (fun k : ℕ ↦ (10 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)
    exact hPowTendsto.atTop_mul_const' method.initialPenaltyParameterPos
  have hPenaltyTendsto :
      Tendsto (fun k : ℕ ↦ method.penaltyParameter (ψ k)) atTop atTop :=
    Filter.tendsto_atTop_mono hPenaltyLower hGeometricTendsto
  have hStageBound :
      ∀ k : ℕ,
        method.penaltyParameter (ψ k) *
            method.penaltyKernel
              (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) ≤
          method.problem.objective xFeas -
            method.problem.objective (method.iterate (ψ k + 1)) := by
    intro k
    have hk : 1 ≤ ψ k := hψPos k
    have hkReached : method.reached (ψ k) :=
      method.reached_of_doesNotTerminateFinitely hNoTerminate (ψ k) hk
    have hIter :
        method.iterate (ψ k + 1) = method.subproblemSolution (ψ k) :=
      method.iterate_succ_eq_subproblemSolution_of_doesNotTerminateFinitely
        hNoTerminate hk
    have hMin :
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            (method.iterate (ψ k + 1)) ≤
          method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xFeas := by
      simpa [hIter] using
        (isMinOn_univ_iff.mp
          (method.subproblemSolution_isMinimizer hk hkReached)) xFeas
    have hFeasEq :
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xFeas =
          method.problem.objective xFeas :=
      method.problem.nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet
        method.penaltyKernel
        (method.penaltyParameter (ψ k))
        hxFeas
    rw [method.problem.nonsmoothExactPenalty_apply, hFeasEq] at hMin
    linarith
  have hPenaltyNumeratorBound :
      ∀ᶠ k in atTop,
        method.penaltyParameter (ψ k) *
            method.penaltyKernel
              (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) ≤ C := by
    filter_upwards [hObjectiveLower] with k hkLower
    have hDiffLt :
        method.problem.objective xFeas -
            method.problem.objective (method.iterate (ψ k + 1)) < C := by
      dsimp [C]
      have hAux :
          method.problem.objective xFeas -
              method.problem.objective (method.iterate (ψ k + 1)) <
            method.problem.objective xFeas - method.problem.objective xHat + 1 := by
        linarith
      have hMax :
          method.problem.objective xFeas - method.problem.objective xHat + 1 ≤ C := by
        dsimp [C]
        exact le_max_left _ _
      linarith
    exact le_trans (hStageBound k) (le_of_lt hDiffLt)
  have hPenaltyKernelLe :
      ∀ᶠ k in atTop,
        method.penaltyKernel
            (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) ≤
          C / method.penaltyParameter (ψ k) := by
    filter_upwards [hPenaltyNumeratorBound] with k hk
    have hkPos :
        0 < method.penaltyParameter (ψ k) :=
      method.penaltyParameterPos (ψ k) (hψPos k)
        (method.reached_of_doesNotTerminateFinitely hNoTerminate (ψ k) (hψPos k))
    exact (le_div_iff₀ hkPos).2 (by simpa [mul_comm] using hk)
  have hPenaltyKernelZero :
      Tendsto
        (fun k : ℕ ↦
          method.penaltyKernel
            (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))))
        atTop
        (nhds 0) := by
    -- The stagewise comparison with one feasible point forces the penalty term to vanish.
    refine squeeze_zero'
      (Eventually.of_forall fun k ↦
        method.penaltyKernel_nonneg
          (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))))
      hPenaltyKernelLe
      (hPenaltyTendsto.const_div_atTop C)
  have hViolationL1Zero :
      Tendsto
        (fun k : ℕ ↦ ‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁)
        atTop
        (nhds 0) := by
    have hScaledZero :
        Tendsto
          (fun k : ℕ ↦
            (1 / δ) *
              method.penaltyKernel
                (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))))
          atTop
          (nhds 0) := by
      simpa [one_div] using hPenaltyKernelZero.const_mul (1 / δ)
    have hL1Le :
        ∀ k : ℕ,
          ‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ ≤
            (1 / δ) *
              method.penaltyKernel
                (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) := by
      intro k
      have hLower :=
        hδle (c⁽-⁾[method.problem] (method.iterate (ψ k + 1)))
      have hScaled :=
        mul_le_mul_of_nonneg_left hLower (show 0 ≤ 1 / δ by positivity)
      simpa [mul_assoc, mul_left_comm, mul_comm, hδ.ne'] using hScaled
    exact
      squeeze_zero
        (fun _ ↦ by
          rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
          exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        hL1Le
        hScaledZero
  -- Compare the coordinatewise continuous limit with the vanishing violation subsequence.
  refine (method.problem.mem_iff_constraintViolation_eq_zero xHat).2 ?_
  ext i
  let u : ℕ → ℝ := fun k ↦ (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) i
  have hCoordUpper :
      ∀ k : ℕ, u k ≤ ‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ := by
    intro k
    have hAbsLe :
        |u k| ≤ ‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ := by
      rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
      simpa [u] using
        (Finset.single_le_sum
          (fun j _ ↦ abs_nonneg ((c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) j))
          (Finset.mem_univ i) :
          |(c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) i| ≤
            ∑ j, |(c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) j|)
    exact le_trans (le_abs_self (u k)) hAbsLe
  have hCoordLower :
      ∀ k : ℕ, -‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ ≤ u k := by
    intro k
    have hAbsLe :
        |u k| ≤ ‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ := by
      rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
      simpa [u] using
        (Finset.single_le_sum
          (fun j _ ↦ abs_nonneg ((c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) j))
          (Finset.mem_univ i) :
          |(c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) i| ≤
            ∑ j, |(c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) j|)
    calc
      -‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁ ≤ -|u k| := by
        gcongr
      _ ≤ u k := neg_abs_le (u k)
  have hCoordZero :
      Tendsto u atTop (nhds 0) := by
    have hNegL1Zero :
        Tendsto
          (fun k : ℕ ↦ -‖c⁽-⁾[method.problem] (method.iterate (ψ k + 1))‖₁)
          atTop
          (nhds 0) := by
      simpa using hViolationL1Zero.neg
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        hNegL1Zero
        hViolationL1Zero
        hCoordLower
        hCoordUpper
  have hCoordContinuous :
      Continuous fun x : Point ↦ (c⁽-⁾[method.problem] x) i := by
    by_cases hi : i.1 < method.problem.eqCount
    · simpa [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi] using
        (h_constraintContDiff i).continuous
    ·
      have hmin :
          Continuous fun x : Point ↦ min (method.problem.constraint i x) 0 :=
        (continuous_id.min continuous_const).comp
          ((h_constraintContDiff i).continuous :
            Continuous fun x : Point ↦ method.problem.constraint i x)
      simpa [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi] using hmin
  have hCoordLimit :
      Tendsto u atTop (nhds ((c⁽-⁾[method.problem] xHat) i)) :=
    hCoordContinuous.continuousAt.tendsto.comp hxHatShift
  exact tendsto_nhds_unique hCoordLimit hCoordZero

/-- Helper for Chapter10 Theorem 10.6.5: in the nonterminating regime, any accumulation point of
the iterate sequence is a local minimizer of the original constrained problem. -/
theorem accumulationPoint_isLocalMinOn_of_doesNotTerminateFinitely
    (method : NonsmoothExactPenaltyMethod n m)
    (h_objectiveContDiff : ContDiff ℝ 2 method.problem.objective)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {xHat : Point} (hxHatFeasible : xHat ∈ method.problem.feasibleSet)
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxHat : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xHat)) :
    IsLocalMinOn method.problem.objective method.problem.feasibleSet xHat := by
  let ψ : ℕ → ℕ := fun k ↦ φ (k + 1)
  have hxHatShift :
      Tendsto (fun k : ℕ ↦ method.iterate (ψ k + 1)) atTop (nhds xHat) := by
    -- Shift once so every stage index used below is positive.
    convert hxHat.comp (Filter.tendsto_add_atTop_nat 1) using 1
    funext k
    rfl
  have hObjectiveTendsto :
      Tendsto
        (fun k : ℕ ↦ method.problem.objective (method.iterate (ψ k + 1)))
        atTop
        (nhds (method.problem.objective xHat)) :=
    h_objectiveContDiff.continuous.continuousAt.tendsto.comp hxHatShift
  by_contra hNotMin
  have hNoBall :
      ¬ ∃ δ > 0,
          ∀ x : Point,
            x ∈ method.problem.feasibleSet ∩ Metric.closedBall xHat δ →
              method.problem.objective xHat ≤ method.problem.objective x := by
    intro hBall
    exact hNotMin
      ((isConstrainedLocalMinOn_iff_exists_forall_mem_closedBall
        method.problem.objective
        method.problem.feasibleSet
        xHat).2 ⟨hxHatFeasible, hBall⟩).2
  have hCounter :
      ∀ δ > 0, ∃ x : Point,
        x ∈ method.problem.feasibleSet ∩ Metric.closedBall xHat δ ∧
          method.problem.objective x < method.problem.objective xHat := by
    intro δ hδ
    by_contra hNoCounter
    apply hNoBall
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    by_contra hxLt
    exact hNoCounter ⟨x, hx, lt_of_not_ge hxLt⟩
  rcases hCounter 1 zero_lt_one with ⟨xNear, hxNear, hxNearObj⟩
  have hEventuallyGreater :
      ∀ᶠ k in atTop,
        method.problem.objective xNear <
          method.problem.objective (method.iterate (ψ k + 1)) := by
    exact hObjectiveTendsto.eventually (Ioi_mem_nhds hxNearObj)
  obtain ⟨k, hkEvent⟩ := hEventuallyGreater.exists
  have hkPos : 1 ≤ ψ k := by
    have hlt : φ 0 < φ (k + 1) := hφ (Nat.succ_pos k)
    dsimp [ψ]
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hkReached : method.reached (ψ k) :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate (ψ k) hkPos
  have hIter :
      method.iterate (ψ k + 1) = method.subproblemSolution (ψ k) :=
    method.iterate_succ_eq_subproblemSolution_of_doesNotTerminateFinitely
      hNoTerminate hkPos
  have hMin :
      method.problem.nonsmoothExactPenalty
          method.penaltyKernel
          (method.penaltyParameter (ψ k))
          (method.iterate (ψ k + 1)) ≤
        method.problem.nonsmoothExactPenalty
          method.penaltyKernel
          (method.penaltyParameter (ψ k))
          xNear := by
    simpa [hIter] using
      (isMinOn_univ_iff.mp (method.subproblemSolution_isMinimizer hkPos hkReached)) xNear
  have hPenaltyNonneg :
      0 ≤ method.penaltyParameter (ψ k) *
            method.penaltyKernel (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) := by
    have hkPenaltyPos :
        0 < method.penaltyParameter (ψ k) :=
      method.penaltyParameterPos (ψ k) hkPos hkReached
    exact mul_nonneg hkPenaltyPos.le
      (method.penaltyKernel_nonneg
        (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))))
  have hNearEq :
      method.problem.nonsmoothExactPenalty
          method.penaltyKernel
          (method.penaltyParameter (ψ k))
          xNear =
        method.problem.objective xNear :=
    method.problem.nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet
      method.penaltyKernel
      (method.penaltyParameter (ψ k))
      hxNear.1
  rw [method.problem.nonsmoothExactPenalty_apply, hNearEq] at hMin
  linarith

/-- `method.terminatesFinitelyAtStrictLocalMinimizer` means that some reached stage terminates and
its selected stagewise exact-penalty minimizer is a strict local minimizer of the original
constrained problem. -/
def terminatesFinitelyAtStrictLocalMinimizer
    (method : NonsmoothExactPenaltyMethod n m) : Prop :=
  ∃ k : ℕ,
    1 ≤ k ∧
      method.reached k ∧
        method.terminatedAt k ∧
          IsStrictLocalMinOn
            method.problem.objective
            method.problem.feasibleSet
            (method.subproblemSolution k)

/-- Unfolding `method.terminatesFinitelyAtStrictLocalMinimizer` gives the existence of a finite
terminating reached stage whose selected minimizer is a strict local minimizer of the constrained
problem. -/
theorem terminatesFinitelyAtStrictLocalMinimizer_iff
    (method : NonsmoothExactPenaltyMethod n m) :
    method.terminatesFinitelyAtStrictLocalMinimizer ↔
      ∃ k : ℕ,
        1 ≤ k ∧
          method.reached k ∧
            method.terminatedAt k ∧
              IsStrictLocalMinOn
                method.problem.objective
                method.problem.feasibleSet
                (method.subproblemSolution k) :=
  Iff.rfl

end NonsmoothExactPenaltyMethod

/-- Chapter10 Theorem 10.6.5: let `method` be Algorithm 10.6.4 and assume the objective
`method.problem.objective` and every constraint `method.problem.constraint i` are twice
continuously differentiable, and that the feasible set `method.problem.feasibleSet` is nonempty.
If every local minimizer of the constrained problem satisfies the Chapter 10 second-order
sufficient condition `(10.6.3)` with some multiplier vector, then either Algorithm 10.6.4
terminates finitely at a strict local minimizer of the original constrained problem, or the
generated iterate sequence satisfies `‖x_k‖ → ∞`. -/
theorem finiteTerminationAt_strictLocalMinimizer_or_iterateNorm_tendsto_atTop
    (method : NonsmoothExactPenaltyMethod n m)
    (h_objectiveContDiff : ContDiff ℝ 2 method.problem.objective)
    (h_constraintContDiff : ∀ i, ContDiff ℝ 2 (method.problem.constraint i))
    (hfeasible : Set.Nonempty method.problem.feasibleSet)
    (h_sosc :
      ∀ ⦃xStar : Point⦄,
        IsLocalMinOn method.problem.objective method.problem.feasibleSet xStar →
          ∃ lamStar : ConstraintPoint,
            method.problem.SecondOrderSufficientCondition xStar lamStar) :
    method.terminatesFinitelyAtStrictLocalMinimizer ∨
      Tendsto (fun k : ℕ ↦ ‖method.iterate (k + 1)‖) atTop atTop := by
  by_cases hStage : ∃ k : ℕ, 1 ≤ k ∧ method.reached k ∧ method.terminatedAt k
  · -- A reached terminating stage already gives the finite strict-local-minimizer branch.
    left
    rcases hStage with ⟨k, hk, hkReached, hkTerm⟩
    refine (method.terminatesFinitelyAtStrictLocalMinimizer_iff).2 ?_
    exact
      ⟨k, hk, hkReached, hkTerm,
        method.terminated_stage_isStrictLocalMinOn hk hkReached hkTerm h_sosc⟩
  · -- Route correction: rule out a bounded subsequence by extracting an accumulation point and
    -- deriving a strict exact-penalty contradiction there.
    right
    by_contra hNotTendsto
    have hNoTerminate :
        method.doesNotTerminateFinitely :=
      method.doesNotTerminateFinitely_of_no_reached_terminated_stage hStage
    rcases method.exists_accumulationPoint_iterate_of_not_tendsto_norm_atTop hNotTendsto with
      ⟨xHat, φ, hφ, hxHat⟩
    have hxHatFeasible :
        xHat ∈ method.problem.feasibleSet :=
      method.accumulationPoint_mem_feasibleSet_of_doesNotTerminateFinitely
        hfeasible
        h_objectiveContDiff
        h_constraintContDiff
        hNoTerminate
        hφ
        hxHat
    have hxHatLocal :
        IsLocalMinOn method.problem.objective method.problem.feasibleSet xHat :=
      method.accumulationPoint_isLocalMinOn_of_doesNotTerminateFinitely
        h_objectiveContDiff
        hNoTerminate
        hxHatFeasible
        hφ
        hxHat
    rcases h_sosc hxHatLocal with ⟨lamStar, hxHatSosc⟩
    rcases exists_penaltyThreshold_for_isStrictLocalMin_nonsmoothExactPenalty method
        ⟨lamStar, hxHatSosc⟩ with
      ⟨σBar, hStrict⟩
    let ψ : ℕ → ℕ := fun k ↦ φ (k + 1)
    have hψPos : ∀ k : ℕ, 1 ≤ ψ k := by
      intro k
      have hlt : φ 0 < φ (k + 1) := hφ (Nat.succ_pos k)
      dsimp [ψ]
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
    have hxHatShift :
        Tendsto (fun k : ℕ ↦ method.iterate (ψ k + 1)) atTop (nhds xHat) := by
      convert hxHat.comp (Filter.tendsto_add_atTop_nat 1) using 1
      funext k
      rfl
    have hPenaltyLower :
        ∀ k : ℕ,
          (10 : ℝ) ^ k * method.initialPenaltyParameter ≤ method.penaltyParameter (ψ k) := by
      intro k
      have hIndexLe : k + 1 ≤ ψ k := by
        simpa [ψ] using hφ.id_le (k + 1)
      have hPowIndex : k ≤ ψ k - 1 := by
        simpa using Nat.sub_le_sub_right hIndexLe 1
      rw [method.penaltyParameter_eq_pow_mul_initial_of_doesNotTerminateFinitely hNoTerminate
        (hψPos k)]
      exact
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hPowIndex)
          method.initialPenaltyParameterPos.le
    have hGeometricTendsto :
        Tendsto
          (fun k : ℕ ↦ (10 : ℝ) ^ k * method.initialPenaltyParameter)
          atTop
          atTop := by
      have hPowTendsto :
          Tendsto (fun k : ℕ ↦ (10 : ℝ) ^ k) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)
      exact hPowTendsto.atTop_mul_const' method.initialPenaltyParameterPos
    have hPenaltyTendsto :
        Tendsto (fun k : ℕ ↦ method.penaltyParameter (ψ k)) atTop atTop :=
      Filter.tendsto_atTop_mono hPenaltyLower hGeometricTendsto
    have hStrictBase :
        IsStrictLocalMin
          (method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1))
          xHat :=
      hStrict (by linarith)
    rcases
      (isStrictLocalMin_iff_exists_forall_norm_sub_lt
        (method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1))
        xHat).1 hStrictBase with
      ⟨δ, hδ, hδstrict⟩
    have hEventuallyLarge :
        ∀ᶠ k in atTop, σBar + 1 < method.penaltyParameter (ψ k) :=
      hPenaltyTendsto.eventually_gt_atTop (σBar + 1)
    have hEventuallyBall :
        ∀ᶠ k in atTop, ‖method.iterate (ψ k + 1) - xHat‖ < δ := by
      have hBall :
          Metric.ball xHat δ ∈ nhds xHat :=
        Metric.ball_mem_nhds xHat hδ
      refine (hxHatShift.eventually hBall).mono ?_
      intro k hk
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hk
    obtain ⟨k, hkLarge, hkBall⟩ := (hEventuallyLarge.and hEventuallyBall).exists
    have hkPos : 1 ≤ ψ k := hψPos k
    have hkReached : method.reached (ψ k) :=
      method.reached_of_doesNotTerminateFinitely hNoTerminate (ψ k) hkPos
    have hIter :
        method.iterate (ψ k + 1) = method.subproblemSolution (ψ k) :=
      method.iterate_succ_eq_subproblemSolution_of_doesNotTerminateFinitely
        hNoTerminate
        hkPos
    have hIterNe : method.iterate (ψ k + 1) ≠ xHat := by
      intro hEq
      have hxZero :
          c⁽-⁾[method.problem] xHat = 0 :=
        (method.problem.mem_iff_constraintViolation_eq_zero xHat).1 hxHatFeasible
      have hTerm : method.terminatedAt (ψ k) := by
        rw [method.terminatedAt_iff]
        have hIterZero :
            c⁽-⁾[method.problem] (method.iterate (ψ k + 1)) = 0 := by
          simpa [hEq] using hxZero
        simpa [hIter] using hIterZero
      exact (method.not_terminatedAt_of_doesNotTerminateFinitely hNoTerminate hkPos) hTerm
    have hMinAtXHat :
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            (method.iterate (ψ k + 1)) ≤
          method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xHat := by
      simpa [hIter] using
        (isMinOn_univ_iff.mp
          (method.subproblemSolution_isMinimizer hkPos hkReached)) xHat
    have hEqBase :
        method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1) xHat =
          method.problem.objective xHat :=
      method.problem.nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet
        method.penaltyKernel
        (σBar + 1)
        hxHatFeasible
    have hEqStage :
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xHat =
          method.problem.objective xHat :=
      method.problem.nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet
        method.penaltyKernel
        (method.penaltyParameter (ψ k))
        hxHatFeasible
    have hSigmaMonotone :
        method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1)
            (method.iterate (ψ k + 1)) ≤
          method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            (method.iterate (ψ k + 1)) := by
      rw [method.problem.nonsmoothExactPenalty_apply,
        method.problem.nonsmoothExactPenalty_apply]
      have hKernelNonneg :
          0 ≤ method.penaltyKernel
            (c⁽-⁾[method.problem] (method.iterate (ψ k + 1))) :=
        method.penaltyKernel_nonneg
          (c⁽-⁾[method.problem] (method.iterate (ψ k + 1)))
      nlinarith
    have hStrictStage :
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xHat <
          method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            (method.iterate (ψ k + 1)) := by
      calc
        method.problem.nonsmoothExactPenalty
            method.penaltyKernel
            (method.penaltyParameter (ψ k))
            xHat
            = method.problem.objective xHat := hEqStage
        _ = method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1) xHat := by
          symm
          exact hEqBase
        _ <
            method.problem.nonsmoothExactPenalty method.penaltyKernel (σBar + 1)
              (method.iterate (ψ k + 1)) :=
          hδstrict _ hIterNe hkBall
        _ ≤
            method.problem.nonsmoothExactPenalty
              method.penaltyKernel
              (method.penaltyParameter (ψ k))
              (method.iterate (ψ k + 1)) :=
          hSigmaMonotone
    exact (not_le_of_gt hStrictStage) hMinAtXHat

#print axioms isStrictLocalMinOn_of_secondOrderSufficientCondition
#print axioms exists_penaltyThreshold_for_isStrictLocalMin_nonsmoothExactPenalty
#print axioms NonsmoothExactPenaltyMethod.terminatesFinitelyAtStrictLocalMinimizer

end Chapter10Theorem1065
