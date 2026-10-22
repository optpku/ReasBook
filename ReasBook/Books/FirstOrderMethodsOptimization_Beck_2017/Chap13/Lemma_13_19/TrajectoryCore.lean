/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_17
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_18
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.ExactTrajectory

-- Theorem-local low-level trajectory API for Lemma 13.19.

noncomputable section

open Matrix
open scoped BigOperators

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

variable {Q : positiveDefiniteMatrices n} {b : Fin n → ℝ} {a : Fin l → Fin n → ℝ}
variable {x : ℕ → polytope_quadratic_feasible_set a} {i : ℕ → Fin l}

local notation "d[" k "]" =>
  polytope_quadratic_conditional_gradient_direction a (x k) (i k)
local notation "λ[" k "]" =>
  polytope_quadratic_exact_line_search_ratio Q b (x k) (d[k])
local notation "κ[" k "]" =>
  dotProduct (d[k]) (Q *ᵥ d[k])

section

variable
  {v0 : stdSimplex ℝ (Fin l)} {xStar : Fin n → ℝ}

local notation "Ω" => convexHull ℝ (Set.range a)
local notation "f_q" => polytope_quadratic_objective Q b
local notation "f_opt" => EReal.toReal (polytope_quadratic_optimal_value Q b a)
local notation "gap[" k "]" => f_q (x k : E) - f_opt

namespace Lemma_13_19_TrajectoryCore

/-- Helper for Lemma 13.19: the clipped quadratic ratio lies in the canonical exact-line-search
set on the segment from `xᵏ` to the chosen vertex. -/
theorem is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory_exact_line_search
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 ∈
      conditional_gradient_exact_line_search_stepsizes
        (polytope_quadratic_objective Q b).toEReal
        (x k) (a (i k)) :=
  polytope_quadratic_ratio_clip_mem_conditional_gradient_exact_line_search_stepsizes
    (htraj.directional_derivative_neg k)

/-- Helper for Lemma 13.19: exact line search makes the quadratic objective nonincreasing along
the trajectory. -/
theorem polytope_quadratic_exact_line_search_objective_nonincreasing
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x (k + 1)) ≤
      polytope_quadratic_objective Q b (x k) := by
  -- Compare the exact-line-search minimizer against the admissible trial value `t = 0`.
  have hstep :=
    is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory_exact_line_search
      (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k
  rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at hstep
  rcases hstep with ⟨_, hmin⟩
  have hcompare := hmin 0 (by simp)
  have hcompare' :
      (polytope_quadratic_objective Q b (x (k + 1)) : EReal) ≤
        polytope_quadratic_objective Q b (x k) := by
    simpa [htraj.step_eq k, polytope_quadratic_conditional_gradient_update_eq,
      polytope_quadratic_conditional_gradient_direction_eq] using hcompare
  exact_mod_cast hcompare'

/-- Helper for Lemma 13.19: the objective values along the trajectory form an antitone sequence. -/
theorem polytope_quadratic_exact_line_search_objective_antitone
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    Antitone (fun k : ℕ ↦ f_q (x k : E)) := by
  exact antitone_nat_of_succ_le fun k ↦
    polytope_quadratic_exact_line_search_objective_nonincreasing
      (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k

/-- Helper for Lemma 13.19: every objective value along the trajectory stays below the initial
one. -/
theorem polytope_quadratic_exact_line_search_objective_le_initial
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x k) ≤
      polytope_quadratic_objective Q b (x 0) := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      -- Chain the one-step descent bound with the induction hypothesis.
      exact le_trans
        (polytope_quadratic_exact_line_search_objective_nonincreasing
          (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k)
        hk

/-- Helper for Lemma 13.19: the clipped exact-line-search stepsize never reaches the endpoint
`t = 1`. -/
theorem polytope_quadratic_exact_line_search_clipped_stepsize_lt_one
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 < 1 := by
  by_contra hlt
  have hge : 1 ≤ min (λ[k]) 1 := by
    linarith
  have hclip_eq : min (λ[k]) 1 = 1 := le_antisymm (min_le_right _ _) hge
  -- If the clip were active at `1`, the next iterate would be the chosen vertex.
  have hstep_vertex : (x (k + 1) : E) = a (i k) := by
    rw [htraj.step_eq k, polytope_quadratic_conditional_gradient_update_eq]
    dsimp only
    rw [hclip_eq, polytope_quadratic_conditional_gradient_direction_eq]
    simp
  -- Monotonicity then contradicts the strict initial sublevel inequality at that vertex.
  have hvertex_le :
      polytope_quadratic_objective Q b (a (i k)) ≤
        polytope_quadratic_objective Q b (x 0) := by
    simpa [hstep_vertex] using
      polytope_quadratic_exact_line_search_objective_le_initial
        (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj (k + 1)
  have hvertex_lt :
      polytope_quadratic_objective Q b (x 0) <
        polytope_quadratic_objective Q b (a (i k)) :=
    hinit.objective_lt_vertex (i k)
  linarith

/-- Helper for Lemma 13.19: the exact-line-search clip is inactive, so the algorithmic stepsize
equals the quadratic ratio `λ_k`. -/
theorem polytope_quadratic_exact_line_search_stepsize_eq_ratio
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 = λ[k] := by
  by_cases hle : λ[k] ≤ 1
  · -- Once the ratio is at most `1`, the clip is inactive by definition.
    exact min_eq_left hle
  · have hclip_lt :
        min (λ[k]) 1 < 1 :=
      polytope_quadratic_exact_line_search_clipped_stepsize_lt_one
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k
    have hclip_eq : min (λ[k]) 1 = 1 := min_eq_right (le_of_not_ge hle)
    linarith

/-- Helper for Lemma 13.19: the one-step quadratic objective decrease is given by the exact
textbook identity. -/
theorem polytope_quadratic_exact_line_search_objective_step_eq
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x (k + 1)) =
      polytope_quadratic_objective Q b (x k) -
        (1 / 2 : ℝ) * κ[k] * (λ[k]) ^ (2 : ℕ) := by
  have hstep_eq :
      (x (k + 1) : E) = (x k : E) + λ[k] • d[k] := by
    rw [htraj.step_eq k, polytope_quadratic_conditional_gradient_update_eq]
    dsimp only
    rw [polytope_quadratic_exact_line_search_stepsize_eq_ratio
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k]
  have hd_ne : d[k] ≠ 0 := by
    intro hd
    have hderiv_nonneg :
        0 ≤
          polytope_quadratic_conditional_gradient_directional_derivative
            Q b a (x k) (i k) := by
      rw [polytope_quadratic_conditional_gradient_directional_derivative_eq, hd]
      simp
    linarith [htraj.directional_derivative_neg k]
  have hκ_ne : κ[k] ≠ 0 := by
    have hκ_pos : 0 < κ[k] := by
      simpa using Q.2.dotProduct_mulVec_pos hd_ne
    linarith
  have hratio_mul :
      λ[k] * κ[k] = -dotProduct d[k] (Q *ᵥ (x k : E) + b) := by
    rw [polytope_quadratic_exact_line_search_ratio_eq, div_eq_mul_inv]
    calc
      (-dotProduct d[k] (Q *ᵥ (x k : E) + b) * (κ[k])⁻¹) * κ[k]
          = -dotProduct d[k] (Q *ᵥ (x k : E) + b) * ((κ[k])⁻¹ * κ[k]) := by ring
      _ = -dotProduct d[k] (Q *ᵥ (x k : E) + b) := by
          rw [inv_mul_cancel₀ hκ_ne, mul_one]
  have hlinear_term :
      λ[k] * dotProduct d[k] (Q *ᵥ (x k : E) + b) =
        -κ[k] * (λ[k]) ^ (2 : ℕ) := by
    have hα :
        dotProduct d[k] (Q *ᵥ (x k : E) + b) = -(λ[k] * κ[k]) := by
      linarith
    rw [hα]
    ring
  -- Expand the quadratic objective along the search line and collapse the linear term.
  calc
    polytope_quadratic_objective Q b (x (k + 1))
        = polytope_quadratic_objective Q b ((x k : E) + λ[k] • d[k]) := by
            rw [hstep_eq]
    _ = polytope_quadratic_objective Q b (x k) +
          λ[k] * dotProduct d[k] (Q *ᵥ (x k : E) + b) +
          (((λ[k]) ^ (2 : ℕ)) / 2) * κ[k] := by
            rw [polytope_quadratic_objective_add_smul_direction_eq
              (Q := Q) (b := b) (x := (x k : E)) (d := d[k]) (t := λ[k])]
    _ = polytope_quadratic_objective Q b (x k) +
          (-κ[k] * (λ[k]) ^ (2 : ℕ)) +
          (((λ[k]) ^ (2 : ℕ)) / 2) * κ[k] := by
            rw [hlinear_term]
    _ = polytope_quadratic_objective Q b (x k) -
          (1 / 2 : ℝ) * κ[k] * (λ[k]) ^ (2 : ℕ) := by
            ring

/-- Helper for Lemma 13.19: every constrained optimizer attains the canonical optimal value
`f_opt`. -/
theorem polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
    {y : Fin n → ℝ}
    (hy :
      y ∈ constrained_problem_solutions (polytope_quadratic_problem Q b a) Ω) :
    polytope_quadratic_optimal_value Q b a = f_q y := by
  have hy_data : y ∈ Ω ∧ IsMinOn (polytope_quadratic_problem Q b a) Ω y := by
    simpa using hy
  have hy_min : IsMinOn (polytope_quadratic_problem Q b a) Set.univ y := by
    -- Route correction: move from the constrained owner on `Ω` to the canonical univ owner before
    -- identifying the `sInf` optimal value.
    rw [isMinOn_univ_iff]
    intro z
    by_cases hz : z ∈ Ω
    · simpa [polytope_quadratic_problem_of_mem Q b a hy_data.1,
        polytope_quadratic_problem_of_mem Q b a hz] using hy_data.2 hz
    · rw [polytope_quadratic_problem_of_mem Q b a hy_data.1,
        polytope_quadratic_problem_of_not_mem Q b a hz]
      simp
  have hglb :
      IsGLB (Set.range (polytope_quadratic_problem Q b a))
        (polytope_quadratic_problem Q b a y) := by
    simpa using hy_min.isGLB (by simp : y ∈ (Set.univ : Set E))
  rw [polytope_quadratic_optimal_value_eq_sInf]
  calc
    sInf (Set.range (polytope_quadratic_problem Q b a)) =
        polytope_quadratic_problem Q b a y :=
      hglb.csInf_eq (Set.range_nonempty _)
    _ = f_q y := by
      simpa [hy_data.1] using polytope_quadratic_problem_of_mem Q b a hy_data.1

/-- Helper for Lemma 13.19: every iterate stays above the canonical optimal value. -/
theorem polytope_quadratic_objective_gap_nonneg
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (k : ℕ) :
    0 ≤ gap[k] := by
  have hxStar_data : xStar ∈ Ω ∧ IsMinOn (polytope_quadratic_problem Q b a) Ω xStar := by
    simpa using hboundary.mem_constrained_problem_solutions
  have hxk : (x k : E) ∈ Ω := (x k).property
  have hle : f_q xStar ≤ f_q (x k : E) := by
    -- Compare the feasible iterate with the boundary optimizer inside the constrained problem.
    have hleE := hxStar_data.2 hxk
    change polytope_quadratic_problem Q b a xStar ≤
      polytope_quadratic_problem Q b a (x k : E) at hleE
    rw [polytope_quadratic_problem_of_mem Q b a hxStar_data.1,
      polytope_quadratic_problem_of_mem Q b a hxk] at hleE
    exact_mod_cast hleE
  have hopt_eq : f_opt = f_q xStar := by
    have hraw := polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
      (Q := Q) (b := b) (a := a) hboundary.mem_constrained_problem_solutions
    exact (congrArg EReal.toReal hraw).trans (EReal.toReal_coe _)
  linarith

/-- Helper for Lemma 13.19: distinct points have strictly smaller objective at their midpoint
than the average of the endpoint objectives. -/
theorem polytope_quadratic_objective_midpoint_lt_avg
    {y z : Fin n → ℝ} (hyz : y ≠ z) :
    f_q (midpoint ℝ y z) < (f_q y + f_q z) / 2 := by
  let d : E := z - y
  have hd : d ≠ 0 := by
    -- The midpoint inequality is strict precisely because the displacement is nonzero.
    dsimp [d]
    exact sub_ne_zero.mpr hyz.symm
  have hκpos : 0 < dotProduct d (Q *ᵥ d) := by
    simpa [d] using Q.2.dotProduct_mulVec_pos hd
  have hmid_eq : midpoint ℝ y z = y + (1 / 2 : ℝ) • d := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    dsimp [d]
    module
  have hz_eq : z = y + (1 : ℝ) • d := by
    simp [d]
  have hmid_formula :
      f_q (midpoint ℝ y z) =
        f_q y +
          (1 / 2 : ℝ) * dotProduct d (Q *ᵥ y + b) +
          (((1 / 2 : ℝ) ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) := by
    rw [hmid_eq]
    simpa [d] using
      (polytope_quadratic_objective_add_smul_direction_eq
        (Q := Q) (b := b) (x := y) (d := d) (t := (1 / 2 : ℝ)))
  have hz_formula :
      f_q z =
        f_q y +
          dotProduct d (Q *ᵥ y + b) +
          (((1 : ℝ) ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) := by
    rw [hz_eq]
    simpa [d] using
      (polytope_quadratic_objective_add_smul_direction_eq
        (Q := Q) (b := b) (x := y) (d := d) (t := (1 : ℝ)))
  rw [hmid_formula, hz_formula]
  have hcurv_pos : 0 < (1 / 8 : ℝ) * dotProduct d (Q *ᵥ d) := by
    nlinarith
  nlinarith

/-- Helper for Lemma 13.19: the boundary optimizer is the unique constrained optimizer on `Ω`. -/
theorem polytope_quadratic_eq_boundary_optimizer_of_mem_constrained_problem_solutions
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    {y : Fin n → ℝ}
    (hy :
      y ∈ constrained_problem_solutions (polytope_quadratic_problem Q b a) Ω) :
    y = xStar := by
  by_contra hy_ne
  have hxStar_data : xStar ∈ Ω ∧ IsMinOn (polytope_quadratic_problem Q b a) Ω xStar := by
    simpa using hboundary.mem_constrained_problem_solutions
  have hy_data : y ∈ Ω ∧ IsMinOn (polytope_quadratic_problem Q b a) Ω y := by
    simpa using hy
  have hmid_mem : midpoint ℝ y xStar ∈ Ω := by
    exact (convex_convexHull ℝ (Set.range a)).midpoint_mem hy_data.1 hxStar_data.1
  have hy_eq : f_q y = f_q xStar := by
    have hyopt := polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
      (Q := Q) (b := b) (a := a) hy
    have hxopt := polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
      (Q := Q) (b := b) (a := a) hboundary.mem_constrained_problem_solutions
    exact_mod_cast hyopt.symm.trans hxopt
  have hmid_lt :
      f_q (midpoint ℝ y xStar) < f_q xStar := by
    have hstrict :=
      polytope_quadratic_objective_midpoint_lt_avg
        (Q := Q) (b := b) (y := y) (z := xStar) hy_ne
    rw [hy_eq] at hstrict
    simpa using hstrict
  have hmid_ge :
      f_q xStar ≤ f_q (midpoint ℝ y xStar) := by
    -- Any feasible midpoint cannot improve on the optimal boundary solution.
    have hmidE := hxStar_data.2 hmid_mem
    change polytope_quadratic_problem Q b a xStar ≤
      polytope_quadratic_problem Q b a (midpoint ℝ y xStar) at hmidE
    rw [polytope_quadratic_problem_of_mem Q b a hxStar_data.1,
      polytope_quadratic_problem_of_mem Q b a hmid_mem] at hmidE
    exact_mod_cast hmidE
  exact (not_lt_of_ge hmid_ge) hmid_lt

end Lemma_13_19_TrajectoryCore

end

end
