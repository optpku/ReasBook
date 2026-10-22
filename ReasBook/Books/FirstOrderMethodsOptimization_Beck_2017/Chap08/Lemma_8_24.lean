/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ)
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

-- Proof sketch: strengthen the target inequality by keeping the nonnegative terminal term
-- Keep `(1 / 2) ‖x^{k+1} - xStar‖²` on the left. Induct on `k`, combining with the induction
-- the one-step inequality from Lemma 8.11 at index `k + 1`, and split the sums over
-- `Finset.range (k + 2)` using `Finset.sum_range_succ`.
private theorem projected_subgradient_method_weighted_objective_gap_sum_with_remainder_le
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k]))
    (h_stepsize_nonneg : ∀ n, 0 ≤ t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
        (1 / 2 : ℝ) * ‖x̄[k + 1] - xStar‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) := by
  induction k with
  | zero =>
      have hstep :=
        projected_subgradient_method_fundamental_inequality
          h_problem h_subgrad hxStar 0 (h_stepsize_nonneg 0)
      have hbase :
          t 0 * ((f x̄[0]).toReal - fOpt) + (1 / 2 : ℝ) * ‖x̄[1] - xStar‖ ^ 2 ≤
            (1 / 2 : ℝ) * ‖x̄[0] - xStar‖ ^ 2 +
              (1 / 2 : ℝ) * ((t 0) ^ 2 * ‖g 0 (x[0])‖ ^ 2) := by
        nlinarith
      simpa [projected_subgradient_method_zero] using hbase
  | succ k ih =>
      have hstep :=
        projected_subgradient_method_fundamental_inequality
          h_problem h_subgrad hxStar (k + 1)
          (h_stepsize_nonneg (k + 1))
      have hstep' :
          t (k + 1) * ((f x̄[k + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x̄[k + 2] - xStar‖ ^ 2 ≤
            (1 / 2 : ℝ) * ‖x̄[k + 1] - xStar‖ ^ 2 +
              (1 / 2 : ℝ) * ((t (k + 1)) ^ 2 * ‖g (k + 1) (x[k + 1])‖ ^ 2) := by
        nlinarith
      calc
        Finset.sum (Finset.range (k + 2)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
            (1 / 2 : ℝ) * ‖x̄[k + 2] - xStar‖ ^ 2 =
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
            (t (k + 1) * ((f x̄[k + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x̄[k + 2] - xStar‖ ^ 2) := by
            rw [Finset.sum_range_succ]
            ring
        _ ≤ (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
            ((1 / 2 : ℝ) *
                Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) +
              (1 / 2 : ℝ) * ((t (k + 1)) ^ 2 * ‖g (k + 1) (x[k + 1])‖ ^ 2)) := by
            nlinarith [ih, hstep']
        _ = (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
            (1 / 2 : ℝ) *
              Finset.sum (Finset.range (k + 2)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
            ring_nf

-- Proof sketch: apply `projected_subgradient_method_fundamental_inequality` for each
-- `n ∈ Finset.range (k + 1)`, sum the resulting inequalities, and use telescoping on the squared
-- distance terms. Then drop the nonnegative final term `‖x[k + 1] - xStar‖^2 / 2`.
/-- Lemma 8.24: under Assumption 8.7 and nonnegative stepsizes, the stepsize-weighted cumulative
objective gap along the projected subgradient iterates up to step `k` is bounded by one half of
the initial squared distance to an optimal point plus one half of the accumulated squared
subgradient norms. -/
theorem projected_subgradient_method_weighted_objective_gap_sum_le
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k]))
    (h_stepsize_nonneg : ∀ n, 0 ≤ t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) ≤
      (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) := by
  have haux :=
    projected_subgradient_method_weighted_objective_gap_sum_with_remainder_le
      f C XStar fOpt h_problem g t x0 h_subgrad h_stepsize_nonneg hxStar k
  have hremainder_nonneg :
      0 ≤ (1 / 2 : ℝ) * ‖x̄[k + 1] - xStar‖ ^ 2 := by
    refine mul_nonneg ?_ (sq_nonneg ‖x̄[k + 1] - xStar‖)
    norm_num
  nlinarith

end
