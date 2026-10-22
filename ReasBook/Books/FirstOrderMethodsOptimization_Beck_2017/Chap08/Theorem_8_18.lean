/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_10
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open Metric

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.18 is `source-facing`: it is a complexity guarantee for the concrete projected
subgradient iterates generated under Polyak's stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the running-best
objective owner `best_achieved_function_value`, the standing problem assumptions
`IsConstrainedConvexProblem`, the bound package `SubgradientNormBoundOn`, and the pointwise
stepsize rule `polyak_stepsize`. Since `projected_subgradient_method` takes an explicit sequence
`t : ℕ → ℝ`, the Polyak rule is recorded as a trajectory-wise compatibility hypothesis
`h_polyak` rather than by introducing a second state-dependent algorithm wrapper. -/

-- Proof sketch: apply the fundamental inequality from Lemma 8.11 to `xStar ∈ XStar`, then use
-- `h_polyak` to rewrite `t k` as Polyak's quotient and use `h_bound.norm_le` on the chosen
-- subgradient `toDualMap ℝ E (g k (x[k]))` to obtain the one-step decrease
-- `((f (x[k] : E)).toReal - fOpt)^2 / h_bound.L_f^2`. Summing these inequalities telescopes to a
-- bound on the squared objective gaps, and comparing each term with the running minimum
-- `best_achieved_function_value` yields the standard estimate
-- `f_best - fOpt ≤ h_bound.L_f * infDist (x0 : E) XStar / √(k + 1)`. The displayed lower bound on
-- `k` then implies the target `ε`-accuracy bound.
/-- Theorem 8.18: under Assumptions 8.7 and 8.12, if the projected subgradient method uses
Polyak's stepsize rule along the generated trajectory, then every index `k` with
`h_bound.L_f^2 d_{X^*}(x^0)^2 / ε^2 - 1 ≤ k` guarantees that the best objective value attained up
to iteration `k` differs from the optimum by at most `ε`. -/
theorem projected_subgradient_best_value_gap_le_epsilon_of_polyak_stepsize
    (ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n])))
    (hk :
      h_bound.L_f ^ (2 : ℕ) * infDist (x0 : E) XStar ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ)) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤ ε :=
  by
    -- Rewrite the strong-dual selection into the subdifferential form used by Theorem 8.13.
    have h_subgrad' :
        ∀ n,
          (toDualMap ℝ E (g n (x[n])) : Module.Dual ℝ E) ∈ subdifferential f (x[n] : E) := by
      intro n
      simpa [mem_strongDualSubdifferential] using h_subgrad n
    -- Theorem 8.13 already packages the source-faithful telescoping argument into a rate bound.
    have h_rate :
        best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤
          h_bound.L_f * infDist (x0 : E) XStar / Real.sqrt (k + 1) := by
      exact projected_subgradient_method_best_value_gap_le_of_polyak_stepsize
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) h_bound h_subgrad' h_polyak k
    -- The displayed lower bound on `k` is exactly the scalar inequality needed to close the rate.
    have h_eps_rate :
        h_bound.L_f * infDist (x0 : E) XStar / Real.sqrt (k + 1) ≤ ε := by
      let M : ℝ := h_bound.L_f * infDist (x0 : E) XStar
      have hM_nonneg : 0 ≤ M := by
        exact mul_nonneg h_bound.L_f_pos.le infDist_nonneg
      have hM_sq :
          M ^ (2 : ℕ) = h_bound.L_f ^ (2 : ℕ) * infDist (x0 : E) XStar ^ (2 : ℕ) := by
        dsimp [M]
        ring
      have hkM : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
        rw [hM_sq]
        exact hk
      have h_div : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
        nlinarith
      have h_num : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
        rw [div_le_iff₀ (by positivity : 0 < ε ^ (2 : ℕ))] at h_div
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_div
      have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
        apply Real.sqrt_pos.2
        positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
      have h_right_nonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
        exact mul_nonneg hε.le hsqrt_nonneg
      have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
        simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity))
      have h_sq : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
        nlinarith [h_num, hsqrt_sq]
      have h_mul : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
        nlinarith [h_sq, hM_nonneg, h_right_nonneg]
      have h_rate_M : M / Real.sqrt ((k : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ hsqrt_pos]
        simpa [mul_comm] using h_mul
      simpa [M] using h_rate_M
    -- A single transitivity step closes the complexity claim.
    exact h_rate.trans h_eps_rate

end
