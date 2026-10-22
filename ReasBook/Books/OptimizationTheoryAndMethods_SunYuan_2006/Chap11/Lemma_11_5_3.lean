/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_28
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Lemma_11_5_4
noncomputable section

open Filter

section Chapter11Lemma1153

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ

-- Domain sampling for this item:
-- * source-facing owner for arbitrary complete convex-set projection in this chapter:
--   `nearestPointProjection`.
-- * source-facing owners for the constraint geometry and quartering search method are reused from
--   `Algorithm_11_5_2`.
-- * canonical feasible-set completeness/convexity owners are reused from `Lemma_11_5_4`.
-- * bridge/view layer in this file: the projected trial path and acceptance predicate obtained by
--   specializing `nearestPointProjection` to the feasible set recorded by that method.
-- Primitive data here are the canonical feasible-set owner and the quartering-search method; the
-- projection point itself is derived from the chapter owner instead of being redefined locally.

namespace LinearlyConstrainedQuarteringSearchMethod

/-- The feasible set recorded by `method` is nonempty. -/
theorem feasibleSet_nonempty
    (method : LinearlyConstrainedQuarteringSearchMethod n m) :
    method.feasibleSet.Nonempty :=
  ⟨method.initialPoint, method.initialPoint_mem_feasibleSet⟩

/-- The feasible set recorded by `method` is complete. -/
theorem isComplete_feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod n m) :
    IsComplete method.feasibleSet := by
  simpa [LinearlyConstrainedQuarteringSearchMethod.feasibleSet] using
    isComplete_linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget

/-- The feasible set recorded by `method` is convex. -/
theorem convex_feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod n m) :
    Convex ℝ method.feasibleSet := by
  simpa [LinearlyConstrainedQuarteringSearchMethod.feasibleSet] using
    convex_linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget

/-- The nearest-point projection of `x` onto `method.feasibleSet` is feasible. -/
@[simp] theorem nearestPointProjection_mem_feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod n m) (x : Point) :
    nearestPointProjection
        method.feasibleSet
        method.feasibleSet_nonempty
        (isComplete_feasibleSet method)
        (convex_feasibleSet method)
        x ∈ method.feasibleSet := by
  exact
    nearestPointProjection_mem
      method.feasibleSet
      method.feasibleSet_nonempty
      (isComplete_feasibleSet method)
      (convex_feasibleSet method)
      x

/-- A feasible point is fixed by the nearest-point projection onto `method.feasibleSet`. -/
@[simp] theorem nearestPointProjection_feasibleSet_eq_self
    (method : LinearlyConstrainedQuarteringSearchMethod n m) {x : Point}
    (hx : x ∈ method.feasibleSet) :
    nearestPointProjection
        method.feasibleSet
        method.feasibleSet_nonempty
        (isComplete_feasibleSet method)
        (convex_feasibleSet method)
        x = x := by
  simpa using
    nearestPointProjection_eq_self
      method.feasibleSet
      method.feasibleSet_nonempty
      (isComplete_feasibleSet method)
      (convex_feasibleSet method)
      hx

/-- The projected-gradient trial point `P_X (x_k - α • gradient f (x_k))` determined by
`method` is feasible. -/
@[simp] theorem projectedTrialPoint_mem_feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (f : Point → ℝ) (k : ℕ) (α : ℝ) :
    nearestPointProjection
        method.feasibleSet
        method.feasibleSet_nonempty
        (isComplete_feasibleSet method)
        (convex_feasibleSet method)
        (method.iterate k - α • gradient f (method.iterate k)) ∈
      method.feasibleSet := by
  exact
    nearestPointProjection_mem_feasibleSet
      method
      (method.iterate k - α • gradient f (method.iterate k))

end LinearlyConstrainedQuarteringSearchMethod

/-- `IsLinearlyConstrainedProjectedTrialPath f method` means that the stagewise trial path of
Algorithm 11.5.2 for the objective `f` is exactly
`x_k(α) = P_X (x_k - α • gradient f (x_k))`. -/
def IsLinearlyConstrainedProjectedTrialPath
    (f : Point → ℝ) (method : LinearlyConstrainedQuarteringSearchMethod n m)
    : Prop :=
  ∀ k α, 1 ≤ k →
    method.trialPoint k α =
      nearestPointProjection
        method.feasibleSet
        method.feasibleSet_nonempty
        (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
        (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
        (method.iterate k - α • gradient f (method.iterate k))

/-- Unfolding `IsLinearlyConstrainedProjectedTrialPath f method` recovers the projected trial
path condition `x_k(α) = P_X (x_k - α • gradient f (x_k))` used in Algorithm 11.5.2. -/
theorem isLinearlyConstrainedProjectedTrialPath_iff
    (f : Point → ℝ) (method : LinearlyConstrainedQuarteringSearchMethod n m) :
    IsLinearlyConstrainedProjectedTrialPath f method ↔
      ∀ k α, 1 ≤ k →
        method.trialPoint k α =
          nearestPointProjection
            method.feasibleSet
            method.feasibleSet_nonempty
            (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
            (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
            (method.iterate k - α • gradient f (method.iterate k)) := by
  rfl

/-- The source Step `(11.5.13)` acceptance condition for `f` at stage `k` and trial step `α`
along the projected trial path of Algorithm 11.5.2. -/
def linearlyConstrainedAcceptanceCondition11513
    (f : Point → ℝ) (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (k : ℕ) (α : ℝ) : Prop :=
  let projectedTrialPoint :=
    nearestPointProjection
      method.feasibleSet
      method.feasibleSet_nonempty
      (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
      (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
      (method.iterate k - α • gradient f (method.iterate k))
  f projectedTrialPoint ≤
    f (method.iterate k) -
      method.μ / α * ‖projectedTrialPoint - method.iterate k‖ ^ (2 : ℕ)

/-- Unfolding `linearlyConstrainedAcceptanceCondition11513 f method k α` recovers the source
Step `(11.5.13)` sufficient-decrease test along the projected trial path. -/
theorem linearlyConstrainedAcceptanceCondition11513_iff
    (f : Point → ℝ) (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (k : ℕ) (α : ℝ) :
    linearlyConstrainedAcceptanceCondition11513 f method k α ↔
      let projectedTrialPoint :=
        nearestPointProjection
          method.feasibleSet
          method.feasibleSet_nonempty
          (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
          (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
          (method.iterate k - α • gradient f (method.iterate k))
      f projectedTrialPoint ≤
        f (method.iterate k) -
          method.μ / α * ‖projectedTrialPoint - method.iterate k‖ ^ (2 : ℕ) := by
  rfl

/-- Helper for Chapter11 Lemma 11.5.3: every accepted step size of the quartering search is
strictly positive because the Step-2 seed is bounded below by `γ > 0`. -/
lemma stepSize_pos
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    {k : ℕ} (hk : 1 ≤ k) :
    0 < method.stepSize k := by
  -- Rewrite the recorded step as the accepted quartered Step-2 seed.
  rw [LinearlyConstrainedQuarteringSearchMethod.stepSize_eq_trialStep method hk]
  rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
  rw [linearlyConstrainedQuarteringTrialStep_eq]
  -- The seed is at least `γ`, and the quartering denominator is positive.
  refine div_pos ?_ ?_
  · unfold linearlyConstrainedQuarteringTrialSeed
    exact lt_of_lt_of_le method.gamma_pos (le_max_right _ _)
  · exact pow_pos (by norm_num) _

/-- Helper for Chapter11 Lemma 11.5.3: every iterate with index at least `1` stays in the
feasible set because each update is a projected trial point. -/
lemma iterate_mem_feasibleSet
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method) :
    ∀ {k : ℕ}, 1 ≤ k → method.iterate k ∈ method.feasibleSet := by
  have hsucc : ∀ j : ℕ, method.iterate (j + 1) ∈ method.feasibleSet := by
    intro j
    cases j with
    | zero =>
        -- The first iterate is the given feasible starting point.
        simpa [LinearlyConstrainedQuarteringSearchMethod.iterate_one_eq_initialPoint] using
          method.initialPoint_mem_feasibleSet
    | succ j =>
        have hj : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
        -- Every later iterate is the projected trial point chosen at the previous stage.
        rw [LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hj]
        rw [h_projectedTrialPath (j + 1) (method.stepSize (j + 1)) hj]
        exact
          LinearlyConstrainedQuarteringSearchMethod.projectedTrialPoint_mem_feasibleSet
            method f (j + 1) (method.stepSize (j + 1))
  intro k hk
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk) with ⟨j, rfl⟩
  simpa [Nat.add_comm] using hsucc j

/-- Helper for Chapter11 Lemma 11.5.3: the accepted-step sufficient decrease makes the objective
drops `f(x_(k+1)) - f(x_(k+2))` tend to zero because the feasible objective values form a
bounded antitone real sequence. -/
lemma objective_drop_tendsto_zero
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_bddBelow : BddBelow (f '' method.feasibleSet))
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α) :
    Tendsto (fun k : ℕ ↦ f (method.iterate (k + 1)) - f (method.iterate (k + 2)))
      atTop (nhds 0) := by
  have h_iterate_mem :
      ∀ {k : ℕ}, 1 ≤ k → method.iterate k ∈ method.feasibleSet :=
    iterate_mem_feasibleSet f method h_projectedTrialPath
  have h_antitone : Antitone (fun k : ℕ ↦ f (method.iterate (k + 1))) := by
    refine antitone_nat_of_succ_le ?_
    intro k
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have haccepted :
        method.acceptedAt (k + 1) (method.stepSize (k + 1)) :=
      LinearlyConstrainedQuarteringSearchMethod.stepSize_accepted method hk
    have h_accepts_step :
        (1 ≤ k + 1 → method.acceptedAt (k + 1) (method.stepSize (k + 1))) ↔
          linearlyConstrainedAcceptanceCondition11513
            f method (k + 1) (method.stepSize (k + 1)) :=
      h_accepts_eq_11513 (k + 1) (method.stepSize (k + 1))
    have h11513 :
        linearlyConstrainedAcceptanceCondition11513
          f method (k + 1) (method.stepSize (k + 1)) :=
      h_accepts_step.1 (fun _ ↦ haccepted)
    have hdecrease :
        f (method.iterate (k + 2)) ≤
          f (method.iterate (k + 1)) -
            method.μ / method.stepSize (k + 1) *
              ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
      -- Rewrite the accepted projected trial point as the next iterate.
      simpa [linearlyConstrainedAcceptanceCondition11513,
        h_projectedTrialPath (k + 1) (method.stepSize (k + 1)) hk,
        LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h11513
    have hμ_nonneg : 0 ≤ method.μ := le_of_lt method.mu_mem.1
    have hstep_nonneg : 0 ≤ method.stepSize (k + 1) := le_of_lt (stepSize_pos method hk)
    have hnorm_sq_nonneg :
        0 ≤ ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
      positivity
    have hpenalty_nonneg :
        0 ≤ method.μ / method.stepSize (k + 1) *
          ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ^ (2 : ℕ) := by
      exact mul_nonneg (div_nonneg hμ_nonneg hstep_nonneg) hnorm_sq_nonneg
    exact le_trans hdecrease (sub_le_self _ hpenalty_nonneg)
  have h_range_bddBelow :
      BddBelow (Set.range (fun k : ℕ ↦ f (method.iterate (k + 1)))) := by
    rcases h_bddBelow with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hc ⟨method.iterate (k + 1), h_iterate_mem (Nat.succ_le_succ (Nat.zero_le k)), rfl⟩
  let l : ℝ := ⨅ k : ℕ, f (method.iterate (k + 1))
  have hl :
      Tendsto (fun k : ℕ ↦ f (method.iterate (k + 1))) atTop (nhds l) := by
    simpa [l] using tendsto_atTop_ciInf h_antitone h_range_bddBelow
  have hl_succ :
      Tendsto (fun k : ℕ ↦ f (method.iterate (k + 2))) atTop (nhds l) := by
    simpa [Nat.add_assoc] using (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  -- Subtract the shifted convergent objective sequence from the original one.
  simpa [Nat.add_assoc] using hl.sub hl_succ

/-- Helper for Chapter11 Lemma 11.5.3: once an accepted step is smaller than `γ`, it must come
from at least one quartering, so the immediately previous quartered trial step is exactly
`4 * α_k` and is still rejected. -/
lemma previous_quartered_step_rejected
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    {k : ℕ} (hk : 1 ≤ k)
    (hstep_lt_gamma : method.stepSize k < method.γ) :
    0 < method.quarteringCount k ∧
      let αbar := method.trialStepAt k (method.quarteringCount k - 1)
      αbar = 4 * method.stepSize k ∧ ¬ method.acceptedAt k αbar := by
  have hquarter_pos : 0 < method.quarteringCount k := by
    by_contra hnot_pos
    have hquarter_zero : method.quarteringCount k = 0 := Nat.eq_zero_of_not_pos hnot_pos
    have hstep_eq :
        method.stepSize k = method.trialStepAt k 0 := by
      simpa [hquarter_zero] using
        LinearlyConstrainedQuarteringSearchMethod.stepSize_eq_trialStep method hk
    have hgamma_le_seed : method.γ ≤ method.trialStepAt k 0 := by
      rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
      rw [linearlyConstrainedQuarteringTrialStep_eq]
      simp [linearlyConstrainedQuarteringTrialSeed]
    have hgamma_le_step : method.γ ≤ method.stepSize k := by
      exact hstep_eq ▸ hgamma_le_seed
    exact (not_lt_of_ge hgamma_le_step) hstep_lt_gamma
  have hpred_lt : method.quarteringCount k - 1 < method.quarteringCount k := by
    simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hquarter_pos)
  have hαbar_rejected :
      ¬ method.acceptedAt k (method.trialStepAt k (method.quarteringCount k - 1)) := by
    exact
      LinearlyConstrainedQuarteringSearchMethod.minimal_quarteringCount
        method hk hpred_lt
  have hαbar_eq :
      method.trialStepAt k (method.quarteringCount k - 1) = 4 * method.stepSize k := by
    let q : ℕ := method.quarteringCount k - 1
    have hquarter_eq :
        method.quarteringCount k = q + 1 := by
      calc
        method.quarteringCount k = (method.quarteringCount k - 1).succ := by
          exact (Nat.succ_pred_eq_of_pos hquarter_pos).symm
        _ = q + 1 := by simp [q, Nat.succ_eq_add_one]
    rw [LinearlyConstrainedQuarteringSearchMethod.stepSize_eq_trialStep method hk]
    rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
    rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
    rw [hquarter_eq]
    rw [linearlyConstrainedQuarteringTrialStep_eq]
    rw [linearlyConstrainedQuarteringTrialStep_eq]
    rw [pow_succ]
    have hpow_ne : (4 : ℝ) ^ q ≠ 0 := by positivity
    field_simp [hpow_ne]
    simp
  refine ⟨hquarter_pos, ?_⟩
  -- Package the previous rejected trial step with its exact quartering factor.
  dsimp
  exact ⟨hαbar_eq, hαbar_rejected⟩

/-- Helper for Chapter11 Lemma 11.5.3: relative to any feasible base iterate `x_k`, membership in
the equality-constrained feasible set is equivalent to lying in the kernel of the linear
constraint map after subtracting `x_k`. -/
lemma feasible_sub_mem_constraintKernel_iff
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    {xk y : Point}
    (hxk : xk ∈ method.feasibleSet) :
    y ∈ method.feasibleSet ↔
      y - xk ∈ LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose) := by
  let T : Point →ₗ[ℝ] ConstraintPoint := Matrix.toEuclideanLin method.constraintMatrix.transpose
  constructor
  · intro hy
    have hyT :
        T y = method.constraintTarget := by
      simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((method.mem_feasibleSet_iff y).1 hy)
    have hxkT :
        T xk = method.constraintTarget := by
      simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((method.mem_feasibleSet_iff xk).1 hxk)
    -- Subtract the two feasible constraint equations to move into the kernel.
    change T (y - xk) = 0
    rw [LinearMap.map_sub, hyT, hxkT, sub_self]
  · intro hy
    have hxkT :
        T xk = method.constraintTarget := by
      simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (WithLp.toLp 2) ((method.mem_feasibleSet_iff xk).1 hxk)
    have hy_sub : T (y - xk) = 0 := by
      simpa [T] using hy
    have hyT : T y = method.constraintTarget := by
      -- Recover the affine constraint equation by adding the feasible base point back.
      calc
        T y = T (y - xk + xk) := by abel
        _ = T (y - xk) + T xk := by rw [LinearMap.map_add]
        _ = method.constraintTarget := by simp [hy_sub, hxkT]
    exact (method.mem_feasibleSet_iff y).2 <| by
      simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg WithLp.ofLp hyT

/-- Helper for Chapter11 Lemma 11.5.3: the projected trial displacement stays in the kernel of
the linear equality constraints because both endpoints are feasible. -/
lemma projected_trial_displacement_mem_constraintKernel
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) (α : ℝ) :
    method.trialPoint k α - method.iterate k ∈
      LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose) := by
  have h_iterate_mem : method.iterate k ∈ method.feasibleSet :=
    iterate_mem_feasibleSet f method h_projectedTrialPath hk
  have h_trial_mem : method.trialPoint k α ∈ method.feasibleSet := by
    -- Rewrite the trial point by the projected-path hypothesis and use feasibility of projections.
    rw [h_projectedTrialPath k α hk]
    exact
      LinearlyConstrainedQuarteringSearchMethod.projectedTrialPoint_mem_feasibleSet
        method f k α
  -- Two feasible points differ by a kernel direction of the constraint map.
  exact
    (feasible_sub_mem_constraintKernel_iff
      (method := method)
      (xk := method.iterate k)
      (y := method.trialPoint k α)
      h_iterate_mem).1 h_trial_mem

/-- Helper for Chapter11 Lemma 11.5.3: the residual from the raw gradient step to its projected
displacement is orthogonal to every kernel direction. -/
lemma projected_trial_residual_mem_orthogonal
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) (α : ℝ) :
    ((-α • gradient f (method.iterate k)) - (method.trialPoint k α - method.iterate k)) ∈
      (LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose))ᗮ := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  let g := gradient f (method.iterate k)
  let x := method.iterate k - α • g
  let p :=
    nearestPointProjection
      method.feasibleSet
      method.feasibleSet_nonempty
      (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
      (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
      x
  let r := x - p
  have hproj : method.trialPoint k α = p := by
    -- Rewrite the trial point as the nearest-point projection used by the algorithm.
    simpa [x, g, p] using h_projectedTrialPath k α hk
  have hp_mem : p ∈ method.feasibleSet := by
    -- The nearest-point projection lands in the feasible set.
    dsimp [p]
    exact
      LinearlyConstrainedQuarteringSearchMethod.nearestPointProjection_mem_feasibleSet
        method x
  have hr_mem : r ∈ Kᗮ := by
    refine (Submodule.mem_orthogonal' K r).2 ?_
    intro d hd
    have hplus_mem : p + d ∈ method.feasibleSet := by
      -- Moving a feasible point by a kernel direction stays in the affine feasible set.
      refine
        (feasible_sub_mem_constraintKernel_iff
          (method := method)
          (xk := p)
          (y := p + d)
          hp_mem).2 ?_
      simpa [K]
    have hminus_delta : (p - d) - p = -d := by
      abel
    have hminus_mem : p - d ∈ method.feasibleSet := by
      -- The same affine-kernel description also handles the opposite direction.
      refine
        (feasible_sub_mem_constraintKernel_iff
          (method := method)
          (xk := p)
          (y := p - d)
          hp_mem).2 ?_
      rw [hminus_delta]
      exact K.neg_mem hd
    have hplus_le : inner ℝ r d ≤ 0 := by
      -- Projecting onto a convex set gives the variational inequality against `p + d`.
      simpa [r, p] using
        real_inner_sub_nearestPointProjection_le_zero
          method.feasibleSet
          method.feasibleSet_nonempty
          (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
          (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
          x
          (p + d)
          hplus_mem
    have hminus_le : inner ℝ r (-d) ≤ 0 := by
      -- Using `p - d` forces the opposite sign, so the pairing with `d` must vanish.
      simpa [r, p, hminus_delta] using
        real_inner_sub_nearestPointProjection_le_zero
          method.feasibleSet
          method.feasibleSet_nonempty
          (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
          (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
          x
          (p - d)
          hminus_mem
    have hnonneg : 0 ≤ inner ℝ r d := by
      exact neg_nonpos.mp (by simpa [inner_neg_right] using hminus_le)
    exact le_antisymm hplus_le hnonneg
  -- Re-express the abstract residual `r` in the source form `-α∇f(x_k) - (x_k(α) - x_k)`.
  simpa [K, r, x, p, g, hproj, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hr_mem

/-- Helper for Chapter11 Lemma 11.5.3: each projected trial displacement is the orthogonal
projection of the ambient gradient step onto the kernel of the linear constraints. -/
lemma projected_trial_displacement_eq_starProjection
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) (α : ℝ) :
    method.trialPoint k α - method.iterate k =
      (LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)).starProjection
        (-α • gradient f (method.iterate k)) := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  have hmem :
      method.trialPoint k α - method.iterate k ∈ K :=
    projected_trial_displacement_mem_constraintKernel f method h_projectedTrialPath hk α
  have horth :
      (-α • gradient f (method.iterate k)) - (method.trialPoint k α - method.iterate k) ∈ Kᗮ :=
    projected_trial_residual_mem_orthogonal f method h_projectedTrialPath hk α
  -- The kernel point with orthogonal residual is uniquely the star-projection.
  exact
    (Submodule.eq_starProjection_of_mem_orthogonal
      (K := K)
      (u := -α • gradient f (method.iterate k))
      (v := method.trialPoint k α - method.iterate k)
      hmem
      horth).symm

/-- Helper for Chapter11 Lemma 11.5.3: projected trial displacements scale homogeneously with the
trial step because they are orthogonal projections onto the kernel directions. -/
lemma projected_trial_displacement_homogeneous
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) (α β : ℝ) :
    β • (method.trialPoint k α - method.iterate k) =
      α • (method.trialPoint k β - method.iterate k) := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  -- Rewrite both displacements as kernel projections of scalar multiples of the gradient step.
  rw [projected_trial_displacement_eq_starProjection f method h_projectedTrialPath hk α]
  rw [projected_trial_displacement_eq_starProjection f method h_projectedTrialPath hk β]
  simp [smul_smul, mul_comm]

/-- Helper for Chapter11 Lemma 11.5.3: the last rejected quartered step has the same normalized
projected displacement as the accepted step, and its displacement norm is exactly four times the
accepted one. -/
lemma rejected_trial_ratio_eq
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k)
    (hquarter : 0 < method.quarteringCount k) :
    let αbar := method.trialStepAt k (method.quarteringCount k - 1)
    ‖method.trialPoint k αbar - method.iterate k‖ / αbar =
        ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k ∧
      ‖method.trialPoint k αbar - method.iterate k‖ =
        (αbar / method.stepSize k) * ‖method.iterate (k + 1) - method.iterate k‖ := by
  dsimp
  let αbar := method.trialStepAt k (method.quarteringCount k - 1)
  have hαbar_eq : αbar = 4 * method.stepSize k := by
    -- Consecutive quartered trial steps differ by the factor `4`.
    have hαbar_eq_raw :
        method.trialStepAt k (method.quarteringCount k - 1) = 4 * method.stepSize k := by
      let q : ℕ := method.quarteringCount k - 1
      have hquarter_eq :
          method.quarteringCount k = q + 1 := by
        calc
          method.quarteringCount k = (method.quarteringCount k - 1).succ := by
            exact (Nat.succ_pred_eq_of_pos hquarter).symm
          _ = q + 1 := by simp [q, Nat.succ_eq_add_one]
      rw [LinearlyConstrainedQuarteringSearchMethod.stepSize_eq_trialStep method hk]
      rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
      rw [LinearlyConstrainedQuarteringSearchMethod.trialStepAt_eq]
      rw [hquarter_eq]
      rw [linearlyConstrainedQuarteringTrialStep_eq]
      rw [linearlyConstrainedQuarteringTrialStep_eq]
      rw [pow_succ]
      have hpow_ne : (4 : ℝ) ^ q ≠ 0 := by positivity
      field_simp [hpow_ne]
      simp [q]
    simpa [αbar] using hαbar_eq_raw
  have hstep_pos : 0 < method.stepSize k := stepSize_pos method hk
  have hstep_ne : method.stepSize k ≠ 0 := ne_of_gt hstep_pos
  have hαbar_pos : 0 < αbar := by
    rw [hαbar_eq]
    positivity
  have haccepted_disp :
      method.trialPoint k (method.stepSize k) - method.iterate k =
        method.iterate (k + 1) - method.iterate k := by
    -- The accepted trial point is exactly the next iterate.
    rw [← LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk]
  have hscaled :
      αbar • (method.iterate (k + 1) - method.iterate k) =
        method.stepSize k • (method.trialPoint k αbar - method.iterate k) := by
    -- Homogeneity transfers the accepted displacement to the previous quartered one.
    simpa [αbar, haccepted_disp] using
      projected_trial_displacement_homogeneous
        f method h_projectedTrialPath hk (method.stepSize k) αbar
  have hvector_eq :
      method.trialPoint k αbar - method.iterate k =
        (αbar / method.stepSize k) • (method.iterate (k + 1) - method.iterate k) := by
    -- Divide the homogeneous identity by the positive accepted step size.
    have hscaled' := congrArg ((method.stepSize k)⁻¹ • ·) hscaled
    simpa [div_eq_mul_inv, smul_smul, hstep_ne, mul_comm, mul_left_comm, mul_assoc] using
      hscaled'.symm
  have hnorm_eq :
      ‖method.trialPoint k αbar - method.iterate k‖ =
        (αbar / method.stepSize k) * ‖method.iterate (k + 1) - method.iterate k‖ := by
    -- Taking norms records the exact scaling of the rejected displacement.
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hαbar_pos, abs_of_pos hstep_pos] using
      congrArg norm hvector_eq
  have hratio_eq :
      ‖method.trialPoint k αbar - method.iterate k‖ / αbar =
        ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k := by
    -- Cancel the same positive factor `αbar` on both sides of the norm identity.
    rw [hnorm_eq]
    field_simp [hstep_ne, ne_of_gt hαbar_pos]
  exact ⟨hratio_eq, hnorm_eq⟩

/-- Helper for Chapter11 Lemma 11.5.3: the projected trial displacement satisfies the source
projection variational identity, hence the norm-square-over-step lower bound used in `(11.5.27)`. -/
lemma projected_trial_projection_inner_lower_bound
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 < α) :
    ‖method.trialPoint k α - method.iterate k‖ ^ (2 : ℕ) / α ≤
      -inner ℝ (method.trialPoint k α - method.iterate k) (gradient f (method.iterate k)) := by
  let K : Submodule ℝ Point :=
    LinearMap.ker (Matrix.toEuclideanLin method.constraintMatrix.transpose)
  let δ := method.trialPoint k α - method.iterate k
  let v := -α • gradient f (method.iterate k)
  have hδ : δ = K.starProjection v := by
    -- Rewrite the projected displacement by the star-projection identity just established.
    simpa [K, δ, v] using
      projected_trial_displacement_eq_starProjection f method h_projectedTrialPath hk α
  have hδ_mem : δ ∈ K := by
    rw [hδ]
    exact Submodule.starProjection_apply_mem K v
  have hδ_self : K.starProjection δ = δ := by
    exact (Submodule.starProjection_eq_self_iff (K := K)).2 hδ_mem
  have hproj_proj : K.starProjection (K.starProjection v) = K.starProjection v := by
    exact
      (Submodule.starProjection_eq_self_iff (K := K)).2
        (Submodule.starProjection_apply_mem K v)
  have hinner_eq : inner ℝ δ δ = inner ℝ δ v := by
    -- Self-adjointness of the orthogonal projection turns the projected vector against `v`
    -- into its inner product with itself.
    simpa [hδ, hproj_proj, real_inner_comm] using
      (Submodule.inner_starProjection_left_eq_right (K := K) v (K.starProjection v))
  have hnumerator :
      ‖δ‖ ^ (2 : ℕ) = -α * inner ℝ δ (gradient f (method.iterate k)) := by
    -- The projection identity converts the norm square into the source pairing with `-α ∇f(x_k)`.
    calc
      ‖δ‖ ^ (2 : ℕ) = inner ℝ δ δ := by
        exact (real_inner_self_eq_norm_sq δ).symm
      _ = inner ℝ δ v := hinner_eq
      _ = -α * inner ℝ δ (gradient f (method.iterate k)) := by
        simpa [v] using
          (real_inner_smul_right δ (gradient f (method.iterate k)) (-α))
  have hquotient :
      ‖δ‖ ^ (2 : ℕ) / α = -inner ℝ δ (gradient f (method.iterate k)) := by
    -- Dividing the exact numerator identity by the positive step size gives the source equality.
    rw [hnumerator]
    field_simp [ne_of_gt hα]
  exact le_of_eq (by simpa [δ] using hquotient)

/-- Helper for Chapter11 Lemma 11.5.3: once a rejected trial step satisfies the source upper
model `f(x_k(α)) ≤ f(x_k) + ⟪Δ, ∇ f(x_k)⟫ + ε ‖Δ‖`, the projection lower bound and a
normalized-ratio lower bound force the Step `(11.5.13)` acceptance inequality. -/
lemma rejected_trial_acceptance_of_upper_model
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) {α ε δ : ℝ} (hα : 0 < α)
    (hmodel :
      f (method.trialPoint k α) ≤
        f (method.iterate k) +
          inner ℝ (method.trialPoint k α - method.iterate k) (gradient f (method.iterate k)) +
            ε * ‖method.trialPoint k α - method.iterate k‖)
    (hratio :
      δ ≤ ‖method.trialPoint k α - method.iterate k‖ / α)
    (hε : ε ≤ (1 - method.μ) * δ) :
    linearlyConstrainedAcceptanceCondition11513 f method k α := by
  let Δ := method.trialPoint k α - method.iterate k
  have hΔ_nonneg : 0 ≤ ‖Δ‖ := norm_nonneg _
  have h_one_sub_mu_nonneg : 0 ≤ 1 - method.μ := by
    exact sub_nonneg.mpr (le_of_lt method.mu_mem.2)
  have hproj :
      ‖Δ‖ ^ (2 : ℕ) / α ≤ -inner ℝ Δ (gradient f (method.iterate k)) := by
    -- The projected-trial variational inequality gives the source lower bound on
    -- `-⟪Δ, ∇ f(x_k)⟫`.
    simpa [Δ] using
      projected_trial_projection_inner_lower_bound
        f method h_projectedTrialPath hk hα
  have hratio_mul :
      δ * ‖Δ‖ ≤ ‖Δ‖ ^ (2 : ℕ) / α := by
    -- Multiply the normalized-ratio lower bound by the displacement norm.
    have hratio' : α * δ ≤ ‖Δ‖ := by
      simpa [Δ, mul_comm] using (le_div_iff₀ hα).mp hratio
    have hscaled :
        α * δ * ‖Δ‖ ≤ ‖Δ‖ ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_right hratio' hΔ_nonneg
    exact
      (le_div_iff₀ hα).2 <|
        by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hεterm :
      ε * ‖Δ‖ ≤ ((1 - method.μ) / α) * ‖Δ‖ ^ (2 : ℕ) := by
    -- The same ratio lower bound upgrades the `ε ‖Δ‖` remainder into the missing
    -- `(1 - μ) / α * ‖Δ‖²` Armijo slack.
    have hεterm₁ :
        ε * ‖Δ‖ ≤ ((1 - method.μ) * δ) * ‖Δ‖ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hε hΔ_nonneg
    have hεterm₂ :
        ((1 - method.μ) * δ) * ‖Δ‖ ≤
          (1 - method.μ) * (‖Δ‖ ^ (2 : ℕ) / α) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hratio_mul h_one_sub_mu_nonneg
    exact le_trans hεterm₁ <|
      by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hεterm₂
  have hmodel' :
      f (method.trialPoint k α) ≤
        f (method.iterate k) - method.μ / α * ‖Δ‖ ^ (2 : ℕ) := by
    -- Combine the linear upper model with the projection lower bound and the slack estimate.
    have hinner :
        inner ℝ Δ (gradient f (method.iterate k)) ≤ -(‖Δ‖ ^ (2 : ℕ) / α) := by
      simpa only [neg_neg] using (neg_le_neg hproj)
    have hsum :
        inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖ ≤
          -(method.μ / α) * ‖Δ‖ ^ (2 : ℕ) := by
      calc
        inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖
            ≤ -(‖Δ‖ ^ (2 : ℕ) / α) + (((1 - method.μ) / α) * ‖Δ‖ ^ (2 : ℕ)) := by
                exact add_le_add hinner hεterm
        _ = -(method.μ / α) * ‖Δ‖ ^ (2 : ℕ) := by
              ring
    have hmodel'' :
        f (method.trialPoint k α) ≤
          f (method.iterate k) +
            (inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖) := by
      simpa [Δ, add_assoc] using hmodel
    have htail :
        f (method.iterate k) +
            (inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖) ≤
          f (method.iterate k) - method.μ / α * ‖Δ‖ ^ (2 : ℕ) := by
      have htail' :
          f (method.iterate k) +
              (inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖) ≤
            f (method.iterate k) + (-(method.μ / α) * ‖Δ‖ ^ (2 : ℕ)) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hsum (f (method.iterate k))
      calc
        f (method.iterate k) +
            (inner ℝ Δ (gradient f (method.iterate k)) + ε * ‖Δ‖)
            ≤ f (method.iterate k) + (-(method.μ / α) * ‖Δ‖ ^ (2 : ℕ)) := htail'
        _ = f (method.iterate k) - method.μ / α * ‖Δ‖ ^ (2 : ℕ) := by
              ring
    exact le_trans hmodel'' htail
  -- Rewrite the source projected point back to `method.trialPoint k α`.
  rw [linearlyConstrainedAcceptanceCondition11513]
  simpa [Δ, h_projectedTrialPath k α hk]
    using hmodel'

/-- Helper for Chapter11 Lemma 11.5.3: if the accepted displacement ratios do not tend to `0`,
one can extract a strictly monotone stage subsequence with a fixed positive lower ratio bound. -/
lemma bad_ratio_subsequence
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_not_tendsto :
      ¬ Tendsto
        (fun k : ℕ ↦
          ‖method.iterate (k + 2) - method.iterate (k + 1)‖ / method.stepSize (k + 1))
        atTop
        (nhds 0)) :
    ∃ δ > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j : ℕ,
        δ ≤
          ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ /
            method.stepSize (φ j + 1) := by
  let ratio : ℕ → ℝ :=
    fun k : ℕ ↦
      ‖method.iterate (k + 2) - method.iterate (k + 1)‖ / method.stepSize (k + 1)
  rw [Metric.tendsto_atTop] at h_not_tendsto
  push Not at h_not_tendsto
  rcases h_not_tendsto with ⟨δ, hδ, hbad⟩
  have h_freq : ∃ᶠ n in atTop, δ ≤ dist (ratio n) 0 :=
    (Filter.frequently_atTop).2 hbad
  obtain ⟨φ, hφmono, hφbad⟩ := Filter.extraction_of_frequently_atTop h_freq
  refine ⟨δ, hδ, φ, hφmono, ?_⟩
  intro j
  have hratio_nonneg : 0 ≤ ratio (φ j) := by
    refine div_nonneg (norm_nonneg _) ?_
    exact le_of_lt <|
      stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (φ j)))
  have hstep_abs :
      |method.stepSize (φ j + 1)| = method.stepSize (φ j + 1) := by
    exact abs_of_pos <|
      stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (φ j)))
  -- The extracted frequent tail gives the fixed positive lower bound on the normalized step.
  simpa [ratio, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hratio_nonneg, hstep_abs] using
    hφbad j

/-- Helper for Chapter11 Lemma 11.5.3: a bad subsequence with uniformly positive accepted ratio
forces both the accepted displacements and the accepted step sizes to vanish along that
subsequence. -/
lemma bad_ratio_subsequence_forces_small_steps
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_bddBelow : BddBelow (f '' method.feasibleSet))
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α)
    {δ : ℝ} (hδ : 0 < δ)
    {φ : ℕ → ℕ} (hφmono : StrictMono φ)
    (h_lower :
      ∀ j : ℕ,
        δ ≤
          ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ /
            method.stepSize (φ j + 1)) :
    Tendsto
        (fun j : ℕ ↦ ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖)
        atTop
        (nhds 0) ∧
      Tendsto
        (fun j : ℕ ↦ method.stepSize (φ j + 1))
        atTop
        (nhds 0) := by
  let drop : ℕ → ℝ :=
    fun k : ℕ ↦ f (method.iterate (k + 1)) - f (method.iterate (k + 2))
  let disp : ℕ → ℝ :=
    fun k : ℕ ↦ ‖method.iterate (k + 2) - method.iterate (k + 1)‖
  have h_drop_zero :=
    objective_drop_tendsto_zero f method h_bddBelow h_projectedTrialPath h_accepts_eq_11513
  have h_drop_subseq :
      Tendsto (fun j : ℕ ↦ drop (φ j)) atTop (nhds 0) := by
    exact h_drop_zero.comp hφmono.tendsto_atTop
  have h_drop_lower :
      ∀ j : ℕ, method.μ * δ * disp (φ j) ≤ drop (φ j) := by
    intro j
    let k : ℕ := φ j + 1
    have hk : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le (φ j))
    have h_accepts_step :
        (1 ≤ k → method.acceptedAt k (method.stepSize k)) ↔
          linearlyConstrainedAcceptanceCondition11513
            f method k (method.stepSize k) :=
      h_accepts_eq_11513 k (method.stepSize k)
    have h11513 :
        linearlyConstrainedAcceptanceCondition11513
          f method k (method.stepSize k) :=
      h_accepts_step.1
        (fun _ ↦ LinearlyConstrainedQuarteringSearchMethod.stepSize_accepted method hk)
    have hdecrease :
        f (method.iterate (k + 1)) +
            method.μ / method.stepSize k *
              ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) ≤
          f (method.iterate k) := by
      have hproj_eq :
          method.iterate (k + 1) =
            nearestPointProjection
              method.feasibleSet
              method.feasibleSet_nonempty
              (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
              (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
              (method.iterate k - method.stepSize k • gradient f (method.iterate k)) := by
        rw [LinearlyConstrainedQuarteringSearchMethod.iterate_succ_eq_trialPoint method hk]
        simpa [sub_eq_add_neg] using h_projectedTrialPath k (method.stepSize k) hk
      have hdecrease' :
          f (method.iterate (k + 1)) ≤
            f (method.iterate k) -
              method.μ / method.stepSize k *
                ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) := by
        have h11513' := h11513
        rw [linearlyConstrainedAcceptanceCondition11513] at h11513'
        rw [show
              nearestPointProjection
                  method.feasibleSet
                  method.feasibleSet_nonempty
                  (LinearlyConstrainedQuarteringSearchMethod.isComplete_feasibleSet method)
                  (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
                  (method.iterate k - method.stepSize k • gradient f (method.iterate k)) =
                method.iterate (k + 1) from hproj_eq.symm] at h11513'
        -- First rewrite the accepted projected point into the next iterate.
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h11513'
      -- Rewrite the accepted projected trial point as the next iterate at stage `k`.
      linarith
    have h_ratio_scaled :
        method.μ * δ * ‖method.iterate (k + 1) - method.iterate k‖ ≤
          method.μ / method.stepSize k *
            ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) := by
      have hscale_nonneg :
          0 ≤ method.μ * ‖method.iterate (k + 1) - method.iterate k‖ := by
        exact mul_nonneg (le_of_lt method.mu_mem.1) (norm_nonneg _)
      have hscaled := mul_le_mul_of_nonneg_left (h_lower j) hscale_nonneg
      simpa [k, disp, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hscaled
    have h_penalty_le :
        method.μ / method.stepSize k *
            ‖method.iterate (k + 1) - method.iterate k‖ ^ (2 : ℕ) ≤
          f (method.iterate k) - f (method.iterate (k + 1)) := by
      linarith
    have h_bound_k :
        method.μ * δ * ‖method.iterate (k + 1) - method.iterate k‖ ≤
          f (method.iterate k) - f (method.iterate (k + 1)) :=
      le_trans h_ratio_scaled h_penalty_le
    simpa [k, drop, disp, Nat.add_assoc] using h_bound_k
  have h_disp_zero :
      Tendsto (fun j : ℕ ↦ disp (φ j)) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hcoef_pos : 0 < method.μ * δ := mul_pos method.mu_mem.1 hδ
    have hbound_pos : 0 < method.μ * δ * ε := mul_pos hcoef_pos hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_drop_subseq (method.μ * δ * ε) hbound_pos
    refine ⟨N, ?_⟩
    intro j hj
    have hdrop_nonneg : 0 ≤ drop (φ j) := by
      exact le_trans (by positivity) (h_drop_lower j)
    have hdrop_small : drop (φ j) < method.μ * δ * ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hdrop_nonneg] using hN j hj
    have hdisp_small :
        method.μ * δ * disp (φ j) < method.μ * δ * ε :=
      lt_of_le_of_lt (h_drop_lower j) hdrop_small
    have hdisp_lt : disp (φ j) < ε :=
      lt_of_mul_lt_mul_left hdisp_small hcoef_pos.le
    simpa [disp, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdisp_lt
  have h_step_zero :
      Tendsto (fun j : ℕ ↦ method.stepSize (φ j + 1)) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hbound_pos : 0 < δ * ε := mul_pos hδ hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_disp_zero (δ * ε) hbound_pos
    refine ⟨N, ?_⟩
    intro j hj
    have hstep_pos :
        0 < method.stepSize (φ j + 1) := by
      exact stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (φ j)))
    have hdisp_small :
        disp (φ j) < δ * ε := by
      simpa [disp, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hN j hj
    have hstep_scaled :
        δ * method.stepSize (φ j + 1) ≤ disp (φ j) := by
      exact (le_div_iff₀ hstep_pos).mp (h_lower j)
    have hstep_small_scaled :
        δ * method.stepSize (φ j + 1) < δ * ε :=
      lt_of_le_of_lt hstep_scaled hdisp_small
    have hstep_small :
        method.stepSize (φ j + 1) < ε :=
      lt_of_mul_lt_mul_left hstep_small_scaled hδ.le
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hstep_pos.le] using hstep_small
  exact ⟨h_disp_zero, h_step_zero⟩

/-- Helper for Chapter11 Lemma 11.5.3: uniform continuity of the ambient gradient on the feasible
set gives the corresponding operator-norm deviation bound for the dual gradient field along every
short feasible segment. -/
lemma feasible_gradient_functional_deviation_bound
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_uniformContinuousOn : UniformContinuousOn (gradient f) method.feasibleSet) :
    ∀ ε > 0, ∃ η > 0, ∀ {x y : Point},
      x ∈ method.feasibleSet →
      y ∈ method.feasibleSet →
      ‖y - x‖ < η →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
            InnerProductSpace.toDual ℝ Point (gradient f x)‖ ≤ ε := by
  rw [Metric.uniformContinuousOn_iff] at h_uniformContinuousOn
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ := h_uniformContinuousOn ε hε
  refine ⟨η, hη_pos, ?_⟩
  intro x y hx hy hxy t ht
  have hzt_mem : x + t • (y - x) ∈ method.feasibleSet := by
    -- Convexity keeps the whole feasible segment inside the affine constraint set.
    exact
      (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method).add_smul_sub_mem
        hx hy ht
  have hzt_dist :
      dist (x + t • (y - x)) x < η := by
    have ht_abs : |t| ≤ 1 := by
      simpa [abs_of_nonneg ht.1] using ht.2
    have hnorm_le :
        ‖t • (y - x)‖ ≤ ‖y - x‖ := by
      calc
        ‖t • (y - x)‖ = |t| * ‖y - x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖y - x‖ := by
              exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
        _ = ‖y - x‖ := by ring
    have hdist_le :
        dist (x + t • (y - x)) x ≤ ‖y - x‖ := by
      simpa [dist_eq_norm] using hnorm_le
    exact lt_of_le_of_lt hdist_le hxy
  have hgrad_dist :
      dist (gradient f (x + t • (y - x))) (gradient f x) < ε :=
    hη (x + t • (y - x)) hzt_mem x hx hzt_dist
  have hgrad_norm :
      ‖gradient f (x + t • (y - x)) - gradient f x‖ < ε := by
    simpa [dist_eq_norm] using hgrad_dist
  -- `toDual` preserves norms, so the same bound holds for the derivative field used later.
  have hdual_dist :
      ‖InnerProductSpace.toDual ℝ Point
          (gradient f (x + t • (y - x)) - gradient f x)‖ < ε := by
    rw [(InnerProductSpace.toDual ℝ Point).norm_map]
    exact hgrad_norm
  have htoDual_sub :
      InnerProductSpace.toDual ℝ Point
          (gradient f (x + t • (y - x)) - gradient f x) =
        InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
          InnerProductSpace.toDual ℝ Point (gradient f x) := by
    exact
      (InnerProductSpace.toDual ℝ Point).map_sub
        (gradient f (x + t • (y - x)))
        (gradient f x)
  exact le_of_lt <| by
    rw [← htoDual_sub]
    exact hdual_dist

/-- Helper for Chapter11 Lemma 11.5.3: once `f` is ambient differentiable at a feasible point,
the ambient gradient induces the correct Gateaux derivative on the feasible affine set. -/
lemma ambient_gradient_gateaux_on_feasible_set
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    {z : Point}
    (_hz : z ∈ method.feasibleSet)
    (h_diffAt : DifferentiableAt ℝ f z) :
    IsGateauxDerivativeWithinAt ℝ method.feasibleSet f z
      (InnerProductSpace.toDual ℝ Point (gradient f z)) := by
  intro d
  -- The ambient Fréchet derivative restricts to every within-feasible directional derivative.
  exact (h_diffAt.hasGradientAt.hasFDerivAt.hasLineDerivAt d).hasLineDerivWithinAt
    method.feasibleSet

/-- Helper for Chapter11 Lemma 11.5.3: if `f` is ambient differentiable at every feasible point,
the Chapter 1 segment remainder theorem gives the source-style uniform first-order remainder bound
along all short feasible segments. -/
lemma feasible_segment_first_order_remainder_bound
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffOn : ∀ z ∈ method.feasibleSet, DifferentiableAt ℝ f z)
    (h_uniformContinuousOn : UniformContinuousOn (gradient f) method.feasibleSet) :
    ∀ ε > 0, ∃ η > 0, ∀ {x y : Point},
      x ∈ method.feasibleSet →
      y ∈ method.feasibleSet →
      ‖y - x‖ < η →
      ‖f y - f x - inner ℝ (y - x) (gradient f x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ :=
    feasible_gradient_functional_deviation_bound f method h_uniformContinuousOn ε hε
  refine ⟨η, hη_pos, ?_⟩
  intro x y hx hy hxy
  have hGateaux :
      ∀ z ∈ method.feasibleSet,
        IsGateauxDerivativeWithinAt ℝ method.feasibleSet f z
          (InnerProductSpace.toDual ℝ Point (gradient f z)) := by
    intro z hz
    -- The derivative field for the Chapter 1 remainder theorem is the ambient gradient field.
    exact ambient_gradient_gateaux_on_feasible_set f method hz (h_diffOn z hz)
  have hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
            InnerProductSpace.toDual ℝ Point (gradient f x)‖ ≤ ε := by
    intro t ht
    -- The previously proved uniform-continuity estimate already controls the whole segment.
    exact hη hx hy hxy t ht
  have hremainder :
      ‖f y - f x -
          (InnerProductSpace.toDual ℝ Point (gradient f x)) (y - x)‖ ≤
        ε * ‖y - x‖ := by
    -- Apply the chapter remainder owner on the convex feasible affine set.
    exact
      norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
        (D := method.feasibleSet)
        (F := f)
        (F' := fun z => InnerProductSpace.toDual ℝ Point (gradient f z))
        (x := x)
        (y := y)
        (z := x)
        (C := ε)
        (LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method)
        hGateaux
        hbound
        hy
        hx
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hremainder

/-- Helper for Chapter11 Lemma 11.5.3: the uniform feasible-segment remainder bound yields the
one-sided first-order upper model used in the rejected-step contradiction. -/
lemma uniform_feasible_segment_first_order_upper_model
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_diffOn : ∀ z ∈ method.feasibleSet, DifferentiableAt ℝ f z)
    (h_uniformContinuousOn : UniformContinuousOn (gradient f) method.feasibleSet) :
    ∀ ε > 0, ∃ η > 0, ∀ {x y : Point},
      x ∈ method.feasibleSet →
      y ∈ method.feasibleSet →
      ‖y - x‖ < η →
      f y ≤ f x + inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖ := by
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ :=
    feasible_segment_first_order_remainder_bound
      f method h_diffOn h_uniformContinuousOn ε hε
  refine ⟨η, hη_pos, ?_⟩
  intro x y hx hy hxy
  have hremainder :
      ‖f y - f x - inner ℝ (y - x) (gradient f x)‖ ≤ ε * ‖y - x‖ :=
    hη hx hy hxy
  have hscalar_bound :
      f y - f x - inner ℝ (y - x) (gradient f x) ≤ ε * ‖y - x‖ := by
    -- The scalar remainder is bounded above by its absolute value.
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hremainder)
  have hsub_le :
      f y - f x ≤ inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖ := by
    linarith
  have hfinal :
      f y ≤ f x + (inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖) := by
    linarith
  simpa [add_assoc, add_left_comm, add_comm] using hfinal

/-- Helper for Chapter11 Lemma 11.5.3: at an ambient differentiability point, the first-order
Taylor remainder is uniformly dominated by `ε ‖y - x‖` on a small neighborhood of `x`. This is
the pointwise version of the source estimate `(11.5.28)`. -/
lemma feasible_segment_first_order_upper_model
    (f : Point → ℝ)
    {x : Point}
    (h_diffAt : DifferentiableAt ℝ f x) :
    ∀ ε > 0, ∃ η > 0, ∀ {y : Point},
      ‖y - x‖ < η →
      f y ≤ f x + inner ℝ (y - x) (gradient f x) + ε * ‖y - x‖ := by
  -- Route correction: under the assumptions currently available in this file, the uniformly
  -- valid source model must be reduced first to the correct pointwise differentiability claim.
  intro ε hε
  have h_tendsto :
      Tendsto
        (fun y : Point ↦
          ‖y - x‖⁻¹ * ‖f y - f x - inner ℝ (gradient f x) (y - x)‖)
        (nhds x)
        (nhds 0) := by
    -- The differentiability of `f` at `x` gives the little-o Taylor remainder ratio.
    simpa [real_inner_comm] using
      (hasGradientAt_iff_tendsto (f := f) (f' := gradient f x) (x := x)).1 h_diffAt.hasGradientAt
  rw [Metric.tendsto_nhds] at h_tendsto
  have hnear := h_tendsto ε hε
  rcases Metric.mem_nhds_iff.1 hnear with ⟨η, hη_pos, hη⟩
  refine ⟨η, hη_pos, ?_⟩
  intro y hy
  have hy_ball : y ∈ Metric.ball x η := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hratio_lt :
      ‖y - x‖⁻¹ * ‖f y - f x - inner ℝ (gradient f x) (y - x)‖ < ε := by
    have := hη hy_ball
    have hratio_nonneg :
        0 ≤ ‖y - x‖⁻¹ * ‖f y - f x - inner ℝ (gradient f x) (y - x)‖ := by
      positivity
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hratio_nonneg] using this
  have hnorm_bound :
      ‖f y - f x - inner ℝ (gradient f x) (y - x)‖ ≤ ε * ‖y - x‖ := by
    by_cases hdist : ‖y - x‖ = 0
    · have hyx : y = x := by
        exact sub_eq_zero.mp (norm_eq_zero.mp hdist)
      subst hyx
      simp
    · have hdist_pos : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hdist)
      have hdiv_lt :
          ‖f y - f x - inner ℝ (gradient f x) (y - x)‖ / ‖y - x‖ < ε := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hratio_lt
      have hbound_lt :
          ‖f y - f x - inner ℝ (gradient f x) (y - x)‖ <
            ε * ‖y - x‖ := by
        exact (div_lt_iff₀ hdist_pos).1 hdiv_lt
      exact le_of_lt hbound_lt
  have hscalar_bound :
      f y - f x - inner ℝ (gradient f x) (y - x) ≤ ε * ‖y - x‖ := by
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hnorm_bound)
  have hsub_le :
      f y - f x ≤ ε * ‖y - x‖ + inner ℝ (gradient f x) (y - x) := by
    exact (sub_le_iff_le_add).1 hscalar_bound
  have hfinal :
      f y ≤ f x + (ε * ‖y - x‖ + inner ℝ (gradient f x) (y - x)) := by
    linarith
  simpa [real_inner_comm, add_assoc, add_left_comm, add_comm] using hfinal

/-- Helper for Chapter11 Lemma 11.5.3: a projected trial step whose normalized displacement is at
least `δ` forces the ambient gradient norm at the base iterate to be at least `δ`. -/
lemma projected_trial_gradient_norm_lower_bound
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    {k : ℕ} (hk : 1 ≤ k) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hratio : δ ≤ ‖method.trialPoint k α - method.iterate k‖ / α) :
    δ ≤ ‖gradient f (method.iterate k)‖ := by
  let Δ := method.trialPoint k α - method.iterate k
  have hΔ_nonneg : 0 ≤ ‖Δ‖ := norm_nonneg _
  have hΔ_pos : 0 < ‖Δ‖ := by
    have hscaled : α * δ ≤ ‖Δ‖ := by
      simpa [Δ, mul_comm] using (le_div_iff₀ hα).mp hratio
    exact lt_of_lt_of_le (mul_pos hα hδ) hscaled
  have hproj :
      ‖Δ‖ ^ (2 : ℕ) / α ≤ -inner ℝ Δ (gradient f (method.iterate k)) := by
    -- The source projection inequality controls the directional pairing from below.
    simpa [Δ] using
      projected_trial_projection_inner_lower_bound
        f method h_projectedTrialPath hk hα
  have hinner_le :
      -inner ℝ Δ (gradient f (method.iterate k)) ≤
        ‖Δ‖ * ‖gradient f (method.iterate k)‖ := by
    -- Cauchy-Schwarz turns the pairing into a gradient-norm upper bound.
    exact le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
  have hquotient :
      ‖Δ‖ / α ≤ ‖gradient f (method.iterate k)‖ := by
    have hupper :
        ‖Δ‖ ^ (2 : ℕ) / α ≤ ‖Δ‖ * ‖gradient f (method.iterate k)‖ :=
      le_trans hproj hinner_le
    have hupper' :
        (‖Δ‖ / α) * ‖Δ‖ ≤ ‖gradient f (method.iterate k)‖ * ‖Δ‖ := by
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper
    exact le_of_mul_le_mul_right (by simpa [mul_comm] using hupper') hΔ_pos
  exact le_trans hratio hquotient

/-- Helper for Chapter11 Lemma 11.5.3: once the ambient gradient is uniformly continuous on the
feasible set and its norm at the base point is bounded below by `δ`, the source upper model holds
uniformly on all sufficiently short feasible displacements with coefficient `(1 - μ) δ`. -/
lemma uniform_feasible_upper_model_of_gradient_norm_lower_bound
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_uniformContinuousOn : UniformContinuousOn (gradient f) method.feasibleSet)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ {x y : Point},
      x ∈ method.feasibleSet →
      y ∈ method.feasibleSet →
      δ ≤ ‖gradient f x‖ →
      ‖y - x‖ < η →
      f y ≤
        f x + inner ℝ (y - x) (gradient f x) + ((1 - method.μ) * δ) * ‖y - x‖ := by
  let ε : ℝ := min ((1 - method.μ) * δ) (δ / 2)
  have hε_pos : 0 < ε := by
    -- Choose a uniform modulus that simultaneously controls the model remainder and keeps the
    -- nearby feasible gradients away from zero.
    refine lt_min ?_ ?_
    · exact mul_pos (sub_pos.mpr method.mu_mem.2) hδ
    · positivity
  have hε_le_model : ε ≤ (1 - method.μ) * δ := min_le_left _ _
  have hε_le_half : ε ≤ δ / 2 := min_le_right _ _
  obtain ⟨η, hη_pos, hη⟩ :=
    feasible_gradient_functional_deviation_bound f method h_uniformContinuousOn ε hε_pos
  refine ⟨η, hη_pos, ?_⟩
  intro x y hx hy hgrad_lower hxy
  let D : Set Point := method.feasibleSet ∩ Metric.ball x η
  have hxD : x ∈ D := by
    refine ⟨hx, ?_⟩
    simpa [D, Metric.mem_ball] using hη_pos
  have hyD : y ∈ D := by
    refine ⟨hy, ?_⟩
    simpa [D, Metric.mem_ball, dist_eq_norm] using hxy
  have hGateaux :
      ∀ z ∈ D,
        IsGateauxDerivativeWithinAt ℝ D f z
          (InnerProductSpace.toDual ℝ Point (gradient f z)) := by
    intro z hz
    have hz_feasible : z ∈ method.feasibleSet := hz.1
    have hzx : ‖z - x‖ < η := by
      simpa [D, Metric.mem_ball, dist_eq_norm] using hz.2
    have hdual_dev :
        ‖InnerProductSpace.toDual ℝ Point (gradient f z) -
            InnerProductSpace.toDual ℝ Point (gradient f x)‖ ≤ ε := by
      simpa using hη hx hz_feasible hzx 1 (by simp)
    have htoDual_sub :
        InnerProductSpace.toDual ℝ Point (gradient f z - gradient f x) =
          InnerProductSpace.toDual ℝ Point (gradient f z) -
            InnerProductSpace.toDual ℝ Point (gradient f x) := by
      exact
        (InnerProductSpace.toDual ℝ Point).map_sub (gradient f z) (gradient f x)
    have hgrad_dev :
        ‖gradient f z - gradient f x‖ ≤ ε := by
      have hgrad_dev' :
          ‖InnerProductSpace.toDual ℝ Point (gradient f z - gradient f x)‖ ≤ ε := by
        rw [htoDual_sub]
        exact hdual_dev
      rwa [(InnerProductSpace.toDual ℝ Point).norm_map] at hgrad_dev'
    have hgrad_dev_rev :
        ‖gradient f x - gradient f z‖ ≤ ε := by
      simpa [norm_sub_rev] using hgrad_dev
    have hnorm_lower :
        δ / 2 ≤ ‖gradient f z‖ := by
      have htriangle :
          ‖gradient f x‖ ≤ ‖gradient f x - gradient f z‖ + ‖gradient f z‖ := by
        simpa [sub_eq_add_neg, add_assoc] using
          (norm_add_le (gradient f x - gradient f z) (gradient f z))
      linarith
    have hgrad_nonzero : gradient f z ≠ 0 := by
      intro hz_zero
      have : (δ / 2 : ℝ) ≤ 0 := by simpa [hz_zero] using hnorm_lower
      linarith
    have hdiffAt : DifferentiableAt ℝ f z := by
      by_contra h_not_diff
      exact hgrad_nonzero <| by
        simpa using
          (gradient_eq_zero_of_not_differentiableAt (𝕜 := ℝ) (f := f) (x := z) h_not_diff)
    -- Nonvanishing of `gradient f` on the short feasible neighborhood upgrades the within-set
    -- derivative data to the ambient-gradient Gateaux formula needed by the segment theorem.
    intro d
    exact
      (ambient_gradient_gateaux_on_feasible_set f method hz_feasible hdiffAt d).mono
        (by intro w hw; exact hw.1)
  have hremainder :
      ‖f y - f x - inner ℝ (y - x) (gradient f x)‖ ≤ ε * ‖y - x‖ := by
    have hbound :
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖InnerProductSpace.toDual ℝ Point (gradient f (x + t • (y - x))) -
              InnerProductSpace.toDual ℝ Point (gradient f x)‖ ≤ ε := by
      intro t ht
      exact hη hx hy hxy t ht
    have hremainder' :
        ‖f y - f x -
            (InnerProductSpace.toDual ℝ Point (gradient f x)) (y - x)‖ ≤
          ε * ‖y - x‖ := by
      -- Restrict the segment theorem to the short feasible neighborhood where the ambient
      -- gradient is known to be the true derivative field.
      exact
        norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
          (D := D)
          (F := f)
          (F' := fun z => InnerProductSpace.toDual ℝ Point (gradient f z))
          (x := x)
          (y := y)
          (z := x)
          (C := ε)
          ((LinearlyConstrainedQuarteringSearchMethod.convex_feasibleSet method).inter
            (convex_ball x η))
          hGateaux
          hbound
          hyD
          hxD
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hremainder'
  have hscalar_bound :
      f y - f x - inner ℝ (y - x) (gradient f x) ≤ ε * ‖y - x‖ := by
    -- Pass from the norm control on the remainder to the one-sided model inequality.
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hremainder)
  have hmodel_bound :
      ε * ‖y - x‖ ≤ ((1 - method.μ) * δ) * ‖y - x‖ := by
    exact mul_le_mul_of_nonneg_right hε_le_model (norm_nonneg _)
  have hsub_le :
      f y - f x ≤ inner ℝ (y - x) (gradient f x) + ((1 - method.μ) * δ) * ‖y - x‖ := by
    linarith
  have hfinal :
      f y ≤
        f x + (inner ℝ (y - x) (gradient f x) + ((1 - method.μ) * δ) * ‖y - x‖) := by
    linarith
  simpa [add_assoc, add_left_comm, add_comm] using hfinal

/-- Chapter11 Lemma 11.5.3: assume `f` is continuously differentiable and bounded below on the
feasible set `method.feasibleSet`. If `gradient f` is uniformly continuous on that feasible set,
and the stagewise trial path of the Algorithm 11.5.2 owner `method` is the projected path
`IsLinearlyConstrainedProjectedTrialPath f method`, and the Step-3 predicate
`method.acceptedAt k α` is exactly the source acceptance test
`linearlyConstrainedAcceptanceCondition11513 f method k α`, then the iterates generated by
Algorithm 11.5.2 satisfy `‖x_(k + 1) - x_k‖ / α_k ⟶ 0` as `k ⟶ ∞`. -/
theorem linearlyConstrainedQuarteringSearchMethod_tendsto_norm_sub_div_stepSize_to_zero
    (f : Point → ℝ)
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (h_contDiffOn : ContDiffOn ℝ 1 f method.feasibleSet)
    (h_bddBelow : BddBelow (f '' method.feasibleSet))
    (h_uniformContinuousOn : UniformContinuousOn (gradient f) method.feasibleSet)
    (h_projectedTrialPath : IsLinearlyConstrainedProjectedTrialPath f method)
    (h_accepts_eq_11513 :
      ∀ k α, 1 ≤ k →
        method.acceptedAt k α ↔
          linearlyConstrainedAcceptanceCondition11513 f method k α) :
    Tendsto
      (fun k : ℕ ↦ ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k)
      atTop
      (nhds 0) := by
  -- Keep the source smoothness hypothesis explicitly available while closing the contradiction.
  have _ : ContDiffOn ℝ 1 f method.feasibleSet := h_contDiffOn
  -- Route correction: first close the source telescoping half of the contradiction argument and
  -- isolate the remaining geometric contradiction behind the rejected-step and remainder helpers.
  by_contra h_not_tendsto
  let ratio : ℕ → ℝ :=
    fun k : ℕ ↦ ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k
  have h_iterate_mem :
      ∀ {k : ℕ}, 1 ≤ k → method.iterate k ∈ method.feasibleSet :=
    iterate_mem_feasibleSet f method h_projectedTrialPath
  have h_drop_zero :=
    objective_drop_tendsto_zero f method h_bddBelow h_projectedTrialPath h_accepts_eq_11513
  have h_not_tendsto_shift :
      ¬ Tendsto
        (fun k : ℕ ↦
          ‖method.iterate (k + 2) - method.iterate (k + 1)‖ / method.stepSize (k + 1))
        atTop
        (nhds 0) := by
    intro h_shift
    have h_ratio_tail :
        Tendsto (fun k : ℕ ↦ ratio (k + 1)) atTop (nhds 0) := by
      simpa [ratio, Nat.add_assoc] using h_shift
    exact h_not_tendsto ((Filter.tendsto_add_atTop_iff_nat 1).1 h_ratio_tail)
  obtain ⟨δ, hδ, φ, hφmono, hφbad⟩ :=
    bad_ratio_subsequence method h_not_tendsto_shift
  have h_small_steps :=
    bad_ratio_subsequence_forces_small_steps
      f method h_bddBelow h_projectedTrialPath h_accepts_eq_11513 hδ hφmono hφbad
  have h_disp_subseq_zero :
      Tendsto
        (fun j : ℕ ↦ ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖)
        atTop
        (nhds 0) :=
    h_small_steps.1
  have h_step_subseq_zero :
      Tendsto
        (fun j : ℕ ↦ method.stepSize (φ j + 1))
        atTop
        (nhds 0) :=
    h_small_steps.2
  have h_step_lt_gamma_eventually :
      ∀ᶠ j in atTop, method.stepSize (φ j + 1) < method.γ := by
    -- The accepted step sizes on the bad subsequence tend to `0`, so they are eventually
    -- smaller than the Step-2 lower seed `γ`.
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 h_step_subseq_zero method.γ method.gamma_pos
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro j hj
    have hstep_pos :
        0 < method.stepSize (φ j + 1) := by
      exact stepSize_pos method (Nat.succ_le_succ (Nat.zero_le (φ j)))
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hstep_pos.le] using hN j hj
  have h_rejected_transfer_eventually :
      ∀ᶠ j in atTop,
        let k := φ j + 1
        let αbar := method.trialStepAt k (method.quarteringCount k - 1)
        δ ≤ ‖method.trialPoint k αbar - method.iterate k‖ / αbar ∧
          αbar = 4 * method.stepSize k ∧
          ¬ method.acceptedAt k αbar ∧
          ‖method.trialPoint k αbar - method.iterate k‖ =
            4 * ‖method.iterate (k + 1) - method.iterate k‖ := by
    filter_upwards [h_step_lt_gamma_eventually] with j hj
    let k : ℕ := φ j + 1
    have hk : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le (φ j))
    rcases previous_quartered_step_rejected (method := method) hk hj with
      ⟨hquarter, hαbar_eq, hαbar_rejected⟩
    let αbar : ℝ := method.trialStepAt k (method.quarteringCount k - 1)
    have hratio_pair :
        ‖method.trialPoint k αbar - method.iterate k‖ / αbar =
            ‖method.iterate (k + 1) - method.iterate k‖ / method.stepSize k ∧
          ‖method.trialPoint k αbar - method.iterate k‖ =
            (αbar / method.stepSize k) * ‖method.iterate (k + 1) - method.iterate k‖ := by
      simpa [αbar] using
        rejected_trial_ratio_eq f method h_projectedTrialPath hk hquarter
    have hδ_transfer :
        δ ≤ ‖method.trialPoint k αbar - method.iterate k‖ / αbar := by
      calc
        δ ≤
            ‖method.iterate (k + 1) - method.iterate k‖ /
              method.stepSize k := by
              simpa [k] using hφbad j
        _ = ‖method.trialPoint k αbar - method.iterate k‖ / αbar := by
              simpa using hratio_pair.1.symm
    have hnorm_eq :
        ‖method.trialPoint k αbar - method.iterate k‖ =
          4 * ‖method.iterate (k + 1) - method.iterate k‖ := by
      have hstep_ne : method.stepSize k ≠ 0 := ne_of_gt (stepSize_pos method hk)
      have hαbar_eq' : αbar = 4 * method.stepSize k := by
        simpa [αbar] using hαbar_eq
      calc
        ‖method.trialPoint k αbar - method.iterate k‖ =
            (αbar / method.stepSize k) *
              ‖method.iterate (k + 1) - method.iterate k‖ := hratio_pair.2
        _ = ((4 * method.stepSize k) / method.stepSize k) *
              ‖method.iterate (k + 1) - method.iterate k‖ := by
              rw [hαbar_eq']
        _ = 4 * ‖method.iterate (k + 1) - method.iterate k‖ := by
              field_simp [hstep_ne]
    dsimp [k, αbar]
    exact ⟨hδ_transfer, hαbar_eq, hαbar_rejected, hnorm_eq⟩
  -- The source-faithful telescoping half is now complete:
  -- the bad-ratio extraction gives a stage-safe subsequence, and the accepted decrease forces
  -- both the accepted displacements and the accepted step sizes on that subsequence to vanish.
  --
  -- The previous rejected quartered steps now carry the same positive normalized displacement
  -- lower bound, and their displacements are exactly four times the accepted subsequence norms.
  -- The final contradiction now stays within the current theorem statement: the ratio lower bound
  -- forces a uniform positive lower bound on `‖gradient f (x_k)‖`, and uniform continuity then
  -- supplies a short feasible neighborhood where the ambient gradient remains nonzero and hence
  -- gives the correct first-order model for the rejected quartered step.
  obtain ⟨η, hη_pos, hη_model⟩ :=
    uniform_feasible_upper_model_of_gradient_norm_lower_bound
      f method h_uniformContinuousOn hδ
  have h_small_disp_eventually :
      ∀ᶠ j in atTop,
        ‖method.iterate (φ j + 2) - method.iterate (φ j + 1)‖ < η / 4 := by
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 h_disp_subseq_zero (η / 4) (by positivity)
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro j hj
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hN j hj
  have h_rejected_accepted_eventually :
      ∀ᶠ j in atTop,
        let k := φ j + 1
        let αbar := method.trialStepAt k (method.quarteringCount k - 1)
        method.acceptedAt k αbar := by
    filter_upwards
      [h_rejected_transfer_eventually, h_small_disp_eventually]
      with j hj_rejected hj_small
    let k : ℕ := φ j + 1
    let αbar : ℝ := method.trialStepAt k (method.quarteringCount k - 1)
    have hk : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le (φ j))
    rcases hj_rejected with ⟨hδ_ratio, hαbar_eq, hαbar_rejected, hnorm_eq⟩
    have hx : method.iterate k ∈ method.feasibleSet := h_iterate_mem hk
    have hy : method.trialPoint k αbar ∈ method.feasibleSet := by
      rw [h_projectedTrialPath k αbar hk]
      exact
        LinearlyConstrainedQuarteringSearchMethod.projectedTrialPoint_mem_feasibleSet
          method f k αbar
    have hαbar_eq' : αbar = 4 * method.stepSize k := by
      simpa [k, αbar] using hαbar_eq
    have hαbar_pos : 0 < αbar := by
      have hstep_pos : 0 < method.stepSize k := stepSize_pos method hk
      rw [hαbar_eq']
      nlinarith
    have hgrad_lower :
        δ ≤ ‖gradient f (method.iterate k)‖ := by
      -- The rejected-step ratio lower bound already forces a nontrivial ambient gradient.
      exact
        projected_trial_gradient_norm_lower_bound
          f method h_projectedTrialPath hk hαbar_pos hδ hδ_ratio
    have hdisp_lt : ‖method.trialPoint k αbar - method.iterate k‖ < η := by
      rw [hnorm_eq]
      nlinarith
    have hmodel :
        f (method.trialPoint k αbar) ≤
          f (method.iterate k) +
            inner ℝ (method.trialPoint k αbar - method.iterate k)
              (gradient f (method.iterate k)) +
              ((1 - method.μ) * δ) * ‖method.trialPoint k αbar - method.iterate k‖ := by
      -- Apply the uniform short-step upper model at the rejected quartered step.
      exact hη_model hx hy hgrad_lower hdisp_lt
    have hacceptance :
        linearlyConstrainedAcceptanceCondition11513 f method k αbar := by
      -- The source Armijo acceptance test follows from the upper model and ratio bound.
      exact
        rejected_trial_acceptance_of_upper_model
          f method h_projectedTrialPath hk hαbar_pos hmodel hδ_ratio le_rfl
    have haccepted_iff :
        (1 ≤ k → method.acceptedAt k αbar) ↔
          linearlyConstrainedAcceptanceCondition11513 f method k αbar :=
      h_accepts_eq_11513 k αbar
    exact (haccepted_iff.2 hacceptance) hk
  have h_eventually_false : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards
      [h_rejected_transfer_eventually, h_rejected_accepted_eventually]
      with j hj_rejected hj_accepted
    exact hj_rejected.2.2.1 hj_accepted
  rcases Filter.eventually_atTop.1 h_eventually_false with ⟨N, hN⟩
  exact hN N le_rfl

#print axioms nearestPointProjection

end Chapter11Lemma1153
