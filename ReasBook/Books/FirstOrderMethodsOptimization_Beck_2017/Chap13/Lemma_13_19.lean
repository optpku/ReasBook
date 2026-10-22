/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_5
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_17
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_18
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_16
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.ClusterConvergence
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.CurvatureLowerBound
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.InteriorWeightedSum
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.PartialSumsDivergence
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.SimplexWeights
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.TrajectoryCore
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.TrajectoryWeights

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- `prompt_add/` is absent in this workspace, so the statement design is checked directly against
the existing Chapter 13 owners.

This item is `source-facing`: it records the exact-line-search behavior of the concrete finite-hull
quadratic conditional-gradient method from Algorithm 13.5, under Assumptions 13.17 and 13.18. The
relevant canonical owners already present in the project are:

- `polytope_quadratic_objective`, `polytope_quadratic_problem`, and
  `polytope_quadratic_feasible_set` for the quadratic model `f_q`, constrained problem `(13.32)`,
  and feasible polytope `Ω`;
- `unconstrained_problem_solutions (polytope_quadratic_vertex_linear_objective Q b a (x k))`,
  `polytope_quadratic_conditional_gradient_direction`,
  `polytope_quadratic_exact_line_search_ratio`, and
  `conditional_gradient_exact_line_search_stepsizes` from Algorithm 13.5 and Definition 13.6 for
  the one-step data `i_k`, `dᵏ`, the explicit quadratic ratio `λ_k`, and the canonical exact
  line-search owner on the segment from `xᵏ` to `a_{i_k}`;
- `IsBoundaryNonExtremeOptimalSolution` and `IsStrictVertexSublevelInitialPoint` for the standing
  assumptions from 13.17 and 13.18.

Following the existing Algorithm 13.1 / 13.2 pattern, the public owner here is therefore a
trajectory predicate on explicit sequences of iterates and chosen vertex indices. The per-iterate
direction `dᵏ`, ratio `λ_k`, and curvature `(dᵏ)^T Q dᵏ` are derived directly from the canonical
Algorithm 13.5 owners, while exact line search is recorded through the chapter owner
`conditional_gradient_exact_line_search_stepsizes` rather than through a second local stepsize
family. -/

variable {Q : positiveDefiniteMatrices n} {b : Fin n → ℝ} {a : Fin l → Fin n → ℝ}
variable {x : ℕ → polytope_quadratic_feasible_set a} {i : ℕ → Fin l}

local notation "d[" k "]" =>
  polytope_quadratic_conditional_gradient_direction a (x k) (i k)
local notation "λ[" k "]" =>
  polytope_quadratic_exact_line_search_ratios Q b a x i k
local notation "κ[" k "]" =>
  dotProduct (d[k]) (Q *ᵥ d[k])

-- The trajectory predicate itself is owned by the extracted theorem-local core helper module
-- `Lemma_13_19.TrajectoryCore`, so the target file only keeps the source-facing results.

-- Proof sketch: apply the canonical Algorithm 13.5 bridge from a negative directional derivative
-- to exact line search on the segment from `xᵏ` to `a_{i_k}`.
/-- At each index `k`, the clipped quadratic ratio belongs to the canonical exact-line-search set
on `[xᵏ, a_{i_k}]`. -/
theorem is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory_exact_line_search
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 ∈
      conditional_gradient_exact_line_search_stepsizes
        (polytope_quadratic_objective Q b).toEReal
        (x k) (a (i k)) :=
  Lemma_13_19_TrajectoryCore.is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory_exact_line_search
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k

/-- Every exact-line-search trajectory step is an admissible Algorithm 13.5 one-step move. -/
theorem exact_line_search_trajectory_step_polytope_quadratic_conditional_gradient_one_step
    (htraj : is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_conditional_gradient_one_step Q b a (x k) (x (k + 1)) := by
  -- The trajectory update is exactly the nonterminal branch of Algorithm 13.5.
  have hnext :
      x (k + 1) =
        polytope_quadratic_conditional_gradient_next_iterate Q b a (x k) (i k)
          (htraj.directional_derivative_neg k) := by
    ext j
    simp [polytope_quadratic_conditional_gradient_next_iterate, htraj.step_eq k]
  exact hnext.symm ▸
    polytope_quadratic_conditional_gradient_update_one_step
      (htraj.argmin_mem k) (htraj.directional_derivative_neg k)

section

variable
  {v0 : stdSimplex ℝ (Fin l)} {xStar : Fin n → ℝ}

local notation "Ω" => convexHull ℝ (Set.range a)
local notation "f_q" => polytope_quadratic_objective Q b
local notation "f_opt" => EReal.toReal (polytope_quadratic_optimal_value Q b a)
local notation "gap[" k "]" => f_q (x k : E) - f_opt

-- The public barycentric-weight owner is imported from `TrajectoryWeights`; keeping a second
-- declaration here would duplicate the same recursive object and obscure its trajectory data.

local notation "v[" k "]" =>
  polytope_quadratic_exact_line_search_weights
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 : Fin l → ℝ) k

/-- Helper for Lemma 13.19: exact line search makes the quadratic objective nonincreasing along
the trajectory. -/
theorem polytope_quadratic_exact_line_search_objective_nonincreasing
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x (k + 1)) ≤
      polytope_quadratic_objective Q b (x k) :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_nonincreasing
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k

/-- Helper for Lemma 13.19: every trajectory objective value stays below the initial one. -/
theorem polytope_quadratic_exact_line_search_objective_le_initial
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x k) ≤
      polytope_quadratic_objective Q b (x 0) :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_le_initial
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k

/-- Helper for Lemma 13.19: the exact-line-search clip never reaches the endpoint `t = 1`. -/
theorem polytope_quadratic_exact_line_search_clipped_stepsize_lt_one
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 < 1 :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_clipped_stepsize_lt_one
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k

-- Proof sketch: argue by induction on `k`. The starting point `x⁰` is in `interior Ω` by
-- Assumption 13.18 together with the standalone nonempty-interior hypothesis `hΩ`. For the step,
-- use the exact-line-search bound `t_k < 1` from part `(2)` and the line-segment interior
-- principle along the segment from `xᵏ` to the chosen vertex `a_{i_k}`.
/-- Lemma 13.19 (1): every iterate of the exact-line-search polytope quadratic conditional-gradient
trajectory lies in the interior of `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_exact_line_search_iterate_mem_interior
    (hΩ : (interior Ω).Nonempty)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    (x k : E) ∈ interior Ω := by
  induction k with
  | zero =>
      -- Assumption 13.18 puts the starting point in `interior Ω`.
      simpa using hinit.mem_interior_feasible_set hΩ
  | succ k hk =>
      have hvertex : a (i k) ∈ Ω := by
        exact subset_convexHull ℝ (Set.range a) ⟨i k, rfl⟩
      have hstep :
          (x (k + 1) : E) = λ[k] • a (i k) + (1 - λ[k]) • (x k : E) := by
        -- Rewrite the update using the inactive-clip identity from part `(2)`.
        rw [htraj.step_eq k, polytope_quadratic_conditional_gradient_update_eq]
        dsimp only
        rw [Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_stepsize_eq_ratio
            (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k,
          polytope_quadratic_conditional_gradient_direction_eq]
        change (x k : E) +
            polytope_quadratic_exact_line_search_ratio Q b (x k) (a (i k) - (x k : E)) •
              (a (i k) - (x k : E)) =
          polytope_quadratic_exact_line_search_ratio Q b (x k) (a (i k) - (x k : E)) •
              a (i k) +
            (1 - polytope_quadratic_exact_line_search_ratio Q b (x k)
              (a (i k) - (x k : E))) • (x k : E)
        module
      have hcombo :
          λ[k] • a (i k) + (1 - λ[k]) • (x k : E) ∈ interior Ω := by
        -- A positive amount of the interior iterate keeps the next point in the interior segment.
        exact (convex_convexHull ℝ (Set.range a)).combo_self_interior_mem_interior
          hvertex hk
          (Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_ratio_nonneg
            (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k)
          (sub_pos.mpr
            (Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_ratio_lt_one
              (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k))
          (by ring)
      exact hstep ▸ hcombo

-- Proof sketch: if the clipped stepsize at some `k` were `1`, then the next iterate would be the
-- vertex `a_{i_k}`. By Assumption 13.18 and objective monotonicity along the trajectory, this
-- would contradict the strict initial sublevel relation. Hence the exact-line-search clip is
-- inactive, so `t_k = λ_k`.
/-- Lemma 13.19 (2): at every iteration, the exact-line-search clip is inactive, so the algorithmic
stepsize equals the ratio `λ_k` from equation `(13.34)`. -/
theorem polytope_quadratic_exact_line_search_stepsize_eq_ratio
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    min (λ[k]) 1 = λ[k] :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_stepsize_eq_ratio
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k

-- Proof sketch: combine part `(2)` with the fact that the clip `t_k = min {λ_k, 1}` is inactive.
-- Since the update does not take the endpoint vertex, the ratio must satisfy `λ_k < 1`.
/-- Lemma 13.19 (3): the exact-line-search ratio satisfies `λ_k < 1` at every iteration. -/
theorem polytope_quadratic_exact_line_search_ratio_lt_one
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    λ[k] < 1 := by
  -- Rewrite the clipped stepsize using the inactive-clip identity and inherit the strict bound.
  rw [← polytope_quadratic_exact_line_search_stepsize_eq_ratio
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k]
  exact
    polytope_quadratic_exact_line_search_clipped_stepsize_lt_one
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k

-- Proof sketch: the trajectory only gives the clipped update
-- `xᵏ⁺¹ = xᵏ + min {λ_k, 1} dᵏ`. Under Assumption 13.18, part `(2)` shows that this clip is
-- inactive, so `xᵏ⁺¹ = xᵏ + λ_k dᵏ`. Expanding the quadratic objective at that update and then
-- substituting the defining ratio identity
-- `λ_k = -⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)` collapses the linear term.
/-- Lemma 13.19 (4): under Assumption 13.18, the exact-line-search clip is inactive, so the
quadratic objective decrease along one step is
`f_q(xᵏ⁺¹) = f_q(xᵏ) - (1 / 2) * ((dᵏ)^T Q dᵏ) * λ_k^2`. -/
theorem polytope_quadratic_exact_line_search_objective_step_eq
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    polytope_quadratic_objective Q b (x (k + 1)) =
      polytope_quadratic_objective Q b (x k) -
        (1 / 2 : ℝ) * κ[k] * (λ[k]) ^ (2 : ℕ) :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_step_eq
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k

/-- Helper for Lemma 13.19: the exact-line-search ratio is nonnegative along the trajectory. -/
theorem polytope_quadratic_exact_line_search_ratio_nonneg
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (k : ℕ) :
    0 ≤ λ[k] :=
  Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_ratio_nonneg
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k

/-- Helper for Lemma 13.19: every constrained optimizer attains the canonical optimal value
`f_opt`. -/
theorem polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
    {y : Fin n → ℝ}
    (hy :
      y ∈ constrained_problem_solutions (polytope_quadratic_problem Q b a) Ω) :
    polytope_quadratic_optimal_value Q b a = f_q y :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_optimal_value_eq_of_mem_constrained_problem_solutions
    (Q := Q) (b := b) (a := a) hy

/-- Helper for Lemma 13.19: every iterate has nonnegative objective gap above the optimal value
`f_opt`. -/
theorem polytope_quadratic_objective_gap_nonneg
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (k : ℕ) :
    0 ≤ gap[k] :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_objective_gap_nonneg
    (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) hboundary k

/-- Helper for Lemma 13.19: distinct points have strictly smaller quadratic objective at their
midpoint than the average of their endpoint values. -/
theorem polytope_quadratic_objective_midpoint_lt_avg
    {y z : Fin n → ℝ} (hyz : y ≠ z) :
    f_q (midpoint ℝ y z) < (f_q y + f_q z) / 2 :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_objective_midpoint_lt_avg
    (Q := Q) (b := b) hyz

/-- Helper for Lemma 13.19: the boundary optimizer `xStar` is the unique constrained optimizer of
the positive-definite quadratic problem on `Ω`. -/
theorem polytope_quadratic_eq_boundary_optimizer_of_mem_constrained_problem_solutions
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    {y : Fin n → ℝ}
    (hy :
      y ∈ constrained_problem_solutions (polytope_quadratic_problem Q b a) Ω) :
    y = xStar :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_eq_boundary_optimizer_of_mem_constrained_problem_solutions
    (Q := Q) (b := b) (a := a) (xStar := xStar) hboundary hy

/-- Helper for Lemma 13.19: the boundary optimizer `xStar` cannot coincide with any vertex
`a_j`, because every vertex lies strictly above the initial objective value while `xStar` is
optimal on `Ω`. -/
theorem polytope_quadratic_boundary_optimizer_ne_vertex
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (j : Fin l) :
    a j ≠ xStar :=
  Lemma_13_19_Curvature.polytope_quadratic_boundary_optimizer_ne_vertex
    (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) (v0 := v0) hboundary hinit j

/-- Helper for Lemma 13.19: the boundary optimizer `xStar` stays a positive distance away from the
finite vertex set `{a_j}`. -/
theorem exists_pos_vertex_distance_lower_bound_at_boundary_optimizer
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0) :
    ∃ ε > 0, ∀ j : Fin l, ε ≤ ‖a j - xStar‖ :=
  Lemma_13_19_Curvature.exists_pos_vertex_distance_lower_bound_at_boundary_optimizer
    (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) (v0 := v0) hboundary hinit

/-- Helper for Lemma 13.19: every cluster point of the feasible iterate sequence remains in the
finite convex-hull feasible set `Ω`. -/
theorem polytope_quadratic_cluster_point_mem_feasible_set
    {a : Fin l → Fin n → ℝ}
    {x : ℕ → polytope_quadratic_feasible_set a}
    {xBar : Fin n → ℝ}
    (hxBar : MapClusterPt xBar Filter.atTop (fun k ↦ (x k : E))) :
    xBar ∈ convexHull ℝ (Set.range a) :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_cluster_point_mem_feasible_set
    (a := a) (x := x) hxBar

/-- Helper for Lemma 13.19: a trajectory cluster point admits a convergent subsequence along which
the chosen minimizing vertex index is constant. -/
theorem polytope_quadratic_constant_argmin_subseq_of_mapClusterPt
    {a : Fin l → Fin n → ℝ}
    {x : ℕ → polytope_quadratic_feasible_set a}
    {i : ℕ → Fin l}
    {xBar : Fin n → ℝ}
    (hxBar : MapClusterPt xBar Filter.atTop (fun k ↦ (x k : E))) :
    ∃ ψ : ℕ → ℕ, ∃ j : Fin l,
      StrictMono ψ ∧
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar) ∧
      ∀ m, i (ψ m) = j :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_constant_argmin_subseq_of_mapClusterPt
    (a := a) (x := x) (i := i) hxBar

/-- Helper for Lemma 13.19: if a convergent subsequence has a constant minimizing vertex index,
that vertex index still minimizes the limiting vertex-linearization at the cluster point. -/
theorem polytope_quadratic_vertex_argmin_at_cluster_point_of_constant_argmin_subseq
    {xBar : Fin n → ℝ} {ψ : ℕ → ℕ} {j : Fin l}
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (hψtendsto :
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar))
    (hconst : ∀ m, i (ψ m) = j) :
    j ∈ unconstrained_problem_solutions
      (polytope_quadratic_vertex_linear_objective Q b a xBar) :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_vertex_argmin_at_cluster_point_of_constant_argmin_subseq
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj hψtendsto hconst

/-- Helper for Lemma 13.19: the quadratic objective values form an antitone sequence along an
exact-line-search trajectory. -/
theorem polytope_quadratic_exact_line_search_objective_antitone
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    Antitone (fun k : ℕ ↦ f_q (x k : E)) :=
  Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_antitone
    (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj

/-- Helper for Lemma 13.19: a negative limiting directional derivative along a constant-index
cluster subsequence forces a uniform objective drop on that subsequence. -/
theorem polytope_quadratic_uniform_objective_drop_of_negative_cluster_derivative
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    {xBar : Fin n → ℝ} {ψ : ℕ → ℕ} {j : Fin l}
    (hψtendsto :
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar))
    (hconst : ∀ m, i (ψ m) = j)
    (hneg :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xBar j < 0) :
    ∃ c > 0, ∃ N, ∀ m ≥ N,
      f_q (x (ψ m + 1) : E) ≤ f_q (x (ψ m) : E) - c :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_uniform_objective_drop_of_negative_cluster_derivative
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0)
    hinit htraj hψtendsto hconst hneg

/-- Helper for Lemma 13.19: every constant-index cluster subsequence has nonnegative limiting
directional derivative. -/
theorem polytope_quadratic_directional_derivative_nonneg_at_cluster_point_of_constant_argmin_subseq
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    {xBar : Fin n → ℝ} {ψ : ℕ → ℕ} {j : Fin l}
    (hψmono : StrictMono ψ)
    (hψtendsto :
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar))
    (hconst : ∀ m, i (ψ m) = j) :
    0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xBar j :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_directional_derivative_nonneg_at_cluster_point_of_constant_argmin_subseq
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
    hboundary hinit htraj hψmono hψtendsto hconst

/-- Helper for Lemma 13.19: every cluster point of an exact-line-search trajectory is the boundary
optimizer `xStar`. -/
theorem polytope_quadratic_cluster_point_eq_boundary_optimizer_of_exact_trajectory
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    {xBar : Fin n → ℝ}
    (hxBar : MapClusterPt xBar Filter.atTop (fun k ↦ (x k : E))) :
    xBar = xStar :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_cluster_point_eq_boundary_optimizer_of_exact_trajectory
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
    hboundary hinit htraj hxBar

/-- Helper for Lemma 13.19: every barycentric weight vector along the exact-line-search trajectory
remains in the standard simplex. -/
theorem polytope_quadratic_exact_line_search_weights_mem_stdSimplex
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    ∀ k, v[k] ∈ stdSimplex ℝ (Fin l)
  :=
  Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_weights_mem_stdSimplex
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj

/-- Helper for Lemma 13.19: every iterate is the weighted sum of the vertices with the recursively
generated barycentric coefficients `v[k]`. -/
theorem polytope_quadratic_exact_line_search_iterate_eq_weighted_sum
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    ∀ k, (x k : E) = ∑ j, v[k] j • a j :=
  Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_iterate_eq_weighted_sum
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj

/-- Helper for Lemma 13.19: every barycentric coordinate stays above the initial coordinate times
the complementary product `∏_{n<k} (1 - λ[n])`. -/
theorem polytope_quadratic_exact_line_search_weights_prod_lower_bound
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    ∀ k j, (∏ n ∈ Finset.range k, (1 - λ[n])) * v0 j ≤ v[k] j
  :=
  Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_weights_prod_lower_bound
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj

/-- Helper for Lemma 13.19: if the exact-line-search ratios were summable, then every barycentric
coordinate would stay uniformly positive along the trajectory. -/
theorem polytope_quadratic_exact_line_search_weights_lower_bound_of_summable
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (hs : Summable (fun k ↦ λ[k])) :
    ∃ δ > 0, ∀ k j, δ * v0 j ≤ v[k] j :=
  Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_weights_lower_bound_of_summable
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj hs

/-- Helper for Lemma 13.19: a strictly positive simplex-weighted combination of the vertices lies
in the interior of the finite convex hull whenever that convex hull has nonempty interior. -/
theorem strictly_positive_stdSimplex_weighted_sum_mem_interior_convexHull
    {w : Fin l → ℝ}
    (hΩ : (interior Ω).Nonempty)
    (hw : w ∈ stdSimplex ℝ (Fin l))
    (hwPos : ∀ j, 0 < w j) :
    (∑ j, w j • a j) ∈ interior Ω :=
  Lemma_13_19_InteriorWeights.strictly_positive_stdSimplex_weighted_sum_mem_interior_convexHull
    (a := a) hΩ hw hwPos

/-- Helper for Lemma 13.19: the exact-line-search iterates converge to the unique boundary
optimizer because every subsequence has a further subsequence converging to the same cluster
point `xStar`. -/
theorem polytope_quadratic_iterates_tendsto_boundary_optimizer
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    Filter.Tendsto (fun k ↦ (x k : E)) Filter.atTop (nhds xStar) :=
  Lemma_13_19_ClusterConvergence.polytope_quadratic_iterates_tendsto_boundary_optimizer
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
    hboundary hinit htraj

-- Proof sketch: if the partial sums of `λ_k` were bounded above, then the complementary products
-- `∏ (1 - λ_k)` would stay uniformly away from `0` by Lemma 13.16. The induced simplex-weight
-- recursion would then force a limit representation of an optimal point by strictly positive
-- barycentric coordinates, contradicting the boundary part of Assumption 13.17.
/-- Lemma 13.19 (5): the partial sums of the exact-line-search ratios `λ_k` diverge to `+∞`. -/
theorem polytope_quadratic_exact_line_search_ratio_partialSums_tendsto_atTop
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    Filter.Tendsto
      (fun m : ℕ ↦
        Finset.sum (Finset.range (m + 1)) fun k ↦ λ[k])
      Filter.atTop Filter.atTop :=
  Lemma_13_19_PartialSumsDivergence.polytope_quadratic_exact_line_search_ratio_partialSums_tendsto_atTop
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
    hboundary hinit htraj

/-- Helper for Lemma 13.19: a positive-definite quadratic form dominates the Euclidean square norm
by a uniform positive constant. -/
theorem exists_pos_quadratic_form_lower_bound_of_posDef :
    ∃ γ > 0, ∀ d : E, γ * ‖d‖ ^ (2 : ℕ) ≤ dotProduct d (Q *ᵥ d) :=
  Lemma_13_19_Curvature.exists_pos_quadratic_form_lower_bound_of_posDef
    (Q := Q)

-- Proof sketch: positive definiteness gives `(dᵏ)^T Q dᵏ ≥ γ ‖dᵏ‖²` for
-- `γ = λ_min(Q) > 0`. Assumption 13.17 prevents the optimal point from being a vertex, so after
-- finitely many steps every iterate stays a fixed positive distance from each vertex; combine
-- that tail estimate with the finitely many initial values.
/-- Lemma 13.19 (6): the directional curvatures `((dᵏ)^T Q dᵏ)` are uniformly bounded below by a
positive constant. -/
theorem exists_pos_polytope_quadratic_directional_curvature_lower_bound
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : E) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    ∃ β > 0, ∀ k : ℕ, β ≤ κ[k] :=
  Lemma_13_19_Curvature.exists_pos_polytope_quadratic_directional_curvature_lower_bound
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
    hboundary hinit htraj

end

end
