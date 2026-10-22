/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.TrajectoryCore

-- Theorem-local cluster-point and convergence helpers for Lemma 13.19.

noncomputable section

open Filter Matrix
open scoped BigOperators Topology

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

namespace Lemma_13_19_ClusterConvergence

/-- Helper for Lemma 13.19: every cluster point of the feasible iterate sequence remains in the
finite convex-hull feasible set `Ω`. -/
theorem polytope_quadratic_cluster_point_mem_feasible_set
    {a : Fin l → E}
    {x : ℕ → polytope_quadratic_feasible_set a}
    {xBar : Fin n → ℝ}
    (hxBar : MapClusterPt xBar Filter.atTop (fun k ↦ (x k : E))) :
    xBar ∈ convexHull ℝ (Set.range a) := by
  -- Closedness of the finite convex hull traps every subsequential limit of feasible iterates.
  have hfinite : (Set.range a : Set E).Finite := Set.finite_range a
  have hclosed : IsClosed (convexHull ℝ (Set.range a)) := hfinite.isClosed_convexHull ℝ
  exact hclosed.mem_of_mapClusterPt hxBar (Filter.Eventually.of_forall fun k ↦ (x k).property)

/-- Helper for Lemma 13.19: a trajectory cluster point admits a convergent subsequence along which
the chosen minimizing vertex index is constant. -/
theorem polytope_quadratic_constant_argmin_subseq_of_mapClusterPt
    {a : Fin l → E}
    {x : ℕ → polytope_quadratic_feasible_set a}
    {i : ℕ → Fin l}
    {xBar : Fin n → ℝ}
    (hxBar : MapClusterPt xBar Filter.atTop (fun k ↦ (x k : E))) :
    ∃ ψ : ℕ → ℕ, ∃ j : Fin l,
      StrictMono ψ ∧
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar) ∧
      ∀ m, i (ψ m) = j := by
  obtain ⟨ψ0, hψ0mono, hψ0tendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  obtain ⟨j, hjInf⟩ := Finite.exists_infinite_fiber (fun m : ℕ ↦ i (ψ0 m))
  have hjOften : ∀ N, ∃ m > N, i (ψ0 m) = j := by
    intro N
    have hjSetInf :
        (((fun m : ℕ ↦ i (ψ0 m)) ⁻¹' {j}) : Set ℕ).Infinite :=
      Set.infinite_coe_iff.mp hjInf
    rcases hjSetInf.exists_gt N with ⟨m, hm_mem, hm_gt⟩
    exact ⟨m, hm_gt, hm_mem⟩
  obtain ⟨φ, hφmono, hφconst⟩ := Nat.exists_strictMono_subsequence hjOften
  refine ⟨ψ0 ∘ φ, j, hψ0mono.comp hφmono, ?_, ?_⟩
  · -- Refining to a strict subsequence preserves convergence to the same cluster point.
    simpa [Function.comp] using hψ0tendsto.comp hφmono.tendsto_atTop
  · -- The refined subsequence stays in the selected infinite fiber, so its index is constant.
    intro m
    simpa [Function.comp] using hφconst m

/-- Helper for Lemma 13.19: if a convergent subsequence has a constant minimizing vertex index,
that vertex index still minimizes the limiting vertex-linearization at the cluster point. -/
theorem polytope_quadratic_vertex_argmin_at_cluster_point_of_constant_argmin_subseq
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    {xBar : Fin n → ℝ} {ψ : ℕ → ℕ} {j : Fin l}
    (hψtendsto :
      Filter.Tendsto (fun m ↦ (x (ψ m) : E)) Filter.atTop (nhds xBar))
    (hconst : ∀ m, i (ψ m) = j) :
    j ∈ unconstrained_problem_solutions
      (polytope_quadratic_vertex_linear_objective Q b a xBar) := by
  -- Route correction: separate the source limit passage for the fixed minimizing index from the
  -- later objective-drop contradiction for the directional derivative.
  refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
  intro q
  let φj : E → ℝ := fun y ↦ polytope_quadratic_vertex_linear_objective Q b a y j
  let φq : E → ℝ := fun y ↦ polytope_quadratic_vertex_linear_objective Q b a y q
  have hφj_cont : Continuous φj := by
    -- The limiting vertex-linearization is a continuous affine functional of the iterate.
    dsimp [φj, polytope_quadratic_vertex_linear_objective]
    exact
      continuous_const.dotProduct
        ((continuous_const.matrix_mulVec continuous_id).add continuous_const)
  have hφq_cont : Continuous φq := by
    -- The same continuity argument applies to every comparison vertex `q`.
    dsimp [φq, polytope_quadratic_vertex_linear_objective]
    exact
      continuous_const.dotProduct
        ((continuous_const.matrix_mulVec continuous_id).add continuous_const)
  have hφj_tendsto :
      Filter.Tendsto (fun m ↦ φj (x (ψ m) : E)) Filter.atTop (nhds (φj xBar)) :=
    (hφj_cont.tendsto xBar).comp hψtendsto
  have hφq_tendsto :
      Filter.Tendsto (fun m ↦ φq (x (ψ m) : E)) Filter.atTop (nhds (φq xBar)) :=
    (hφq_cont.tendsto xBar).comp hψtendsto
  have hineq :
      ∀ m, φj (x (ψ m) : E) ≤ φq (x (ψ m) : E) := by
    intro m
    -- Each subsequence iterate inherits the discrete vertex argmin inequality from the trajectory.
    have hmineq :=
      (mem_unconstrained_problem_solutions_iff_forall_le.mp (htraj.argmin_mem (ψ m))) q
    simpa [φj, φq, hconst m] using hmineq
  -- Passing the pointwise inequalities to the limit preserves the minimizing relation at `xBar`.
  simpa [φj, φq] using
    le_of_tendsto_of_tendsto' hφj_tendsto hφq_tendsto hineq

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
      f_q (x (ψ m + 1) : E) ≤ f_q (x (ψ m) : E) - c := by
  let g : E → ℝ :=
    fun y ↦ polytope_quadratic_conditional_gradient_directional_derivative Q b a y j
  let curv : E → ℝ := fun y ↦ dotProduct (a j - y) (Q *ᵥ (a j - y))
  have hg_cont : Continuous g := by
    -- The limiting directional derivative is a continuous polynomial in the iterate.
    dsimp [g, polytope_quadratic_conditional_gradient_directional_derivative,
      polytope_quadratic_conditional_gradient_direction]
    exact
      (continuous_const.sub continuous_id).dotProduct
        ((continuous_const.matrix_mulVec continuous_id).add continuous_const)
  have hcurv_cont : Continuous curv := by
    -- The curvature term is the associated positive-definite quadratic form.
    dsimp [curv]
    exact
      (continuous_const.sub continuous_id).dotProduct
        (continuous_const.matrix_mulVec (continuous_const.sub continuous_id))
  let ε : ℝ := -(g xBar) / 2
  have hε_pos : 0 < ε := by
    -- Half of the negative limiting derivative is a positive descent margin.
    dsimp [ε, g] at *
    linarith
  have hg_tendsto :
      Filter.Tendsto (fun m ↦ g (x (ψ m) : E)) Filter.atTop (nhds (g xBar)) :=
    (hg_cont.tendsto xBar).comp hψtendsto
  have hg_eventually :
      ∀ᶠ m : ℕ in Filter.atTop, g (x (ψ m) : E) < -ε := by
    have hg_lt : g xBar < -ε := by
      dsimp [ε]
      linarith
    exact hg_tendsto.eventually (Iio_mem_nhds hg_lt)
  have hcurv_nonneg_xBar : 0 ≤ curv xBar := by
    -- Positive semidefiniteness makes the quadratic form nonnegative at the limit point.
    simpa [curv] using Q.2.posSemidef.dotProduct_mulVec_nonneg (a j - xBar)
  let C : ℝ := curv xBar + 1
  have hC_pos : 0 < C := by
    -- The uniform curvature upper bound is strictly positive by construction.
    dsimp [C]
    linarith
  have hcurv_tendsto :
      Filter.Tendsto (fun m ↦ curv (x (ψ m) : E)) Filter.atTop (nhds (curv xBar)) :=
    (hcurv_cont.tendsto xBar).comp hψtendsto
  have hcurv_eventually :
      ∀ᶠ m : ℕ in Filter.atTop, curv (x (ψ m) : E) < C := by
    have hcurv_lt : curv xBar < C := by
      dsimp [C]
      linarith
    exact hcurv_tendsto.eventually (Iio_mem_nhds hcurv_lt)
  let c : ℝ := ε ^ (2 : ℕ) / (2 * C)
  have hc_pos : 0 < c := by
    -- The fixed descent amount is positive because both `ε` and `C` are positive.
    dsimp [c]
    positivity
  have hdrop_eventually :
      ∀ᶠ m : ℕ in Filter.atTop,
        f_q (x (ψ m + 1) : E) ≤ f_q (x (ψ m) : E) - c := by
    -- Route correction: instead of trying to certify stationarity directly, extract a fixed drop
    -- from the negative limiting directional derivative and the exact quadratic step formula.
    filter_upwards [hg_eventually, hcurv_eventually] with m hm_g hm_curv
    have hm_idx : i (ψ m) = j := hconst m
    have hcurv_eq : κ[ψ m] = curv (x (ψ m) : E) := by
      simp [curv, hm_idx, polytope_quadratic_conditional_gradient_direction_eq]
    have hd_ne : d[ψ m] ≠ 0 := by
      -- A zero direction would make the directional derivative vanish, contradicting the trajectory.
      intro hd
      have hzero :
          polytope_quadratic_conditional_gradient_directional_derivative
              Q b a (x (ψ m)) (i (ψ m)) = 0 := by
        rw [polytope_quadratic_conditional_gradient_directional_derivative_eq, hd]
        simp
      linarith [htraj.directional_derivative_neg (ψ m)]
    have hcurv_pos :
        0 < curv (x (ψ m) : E) := by
      rw [← hcurv_eq]
      exact Q.2.dotProduct_mulVec_pos hd_ne
    have hratio_eq :
        λ[ψ m] = -g (x (ψ m) : E) / curv (x (ψ m) : E) := by
      rw [polytope_quadratic_exact_line_search_ratio_eq]
      simp [g, curv, hm_idx, polytope_quadratic_conditional_gradient_direction_eq]
    have hnum_lower : ε ≤ -g (x (ψ m) : E) := by
      linarith
    have hden_upper : curv (x (ψ m) : E) ≤ C := le_of_lt hm_curv
    have hdrop_lower :
        c ≤ (1 / 2 : ℝ) * κ[ψ m] * (λ[ψ m]) ^ (2 : ℕ) := by
      rw [hratio_eq, hcurv_eq]
      dsimp [c]
      have hrewrite :
          (1 / 2 : ℝ) * curv (x (ψ m) : E) *
              (-g (x (ψ m) : E) / curv (x (ψ m) : E)) ^ (2 : ℕ) =
            (-g (x (ψ m) : E)) ^ (2 : ℕ) / (2 * curv (x (ψ m) : E)) := by
        field_simp [hcurv_pos.ne']
      rw [hrewrite]
      have hnum_sq : ε ^ (2 : ℕ) ≤ (-g (x (ψ m) : E)) ^ (2 : ℕ) := by
        nlinarith
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * C) (by positivity :
        0 < 2 * curv (x (ψ m) : E))).2
      exact
        (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hden_upper (by positivity : (0 : ℝ) ≤ 2))
            (sq_nonneg ε)).trans
          (mul_le_mul_of_nonneg_right hnum_sq (by positivity : (0 : ℝ) ≤ 2 * C))
    have hstep_eq :=
      Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_step_eq
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj (ψ m)
    -- The exact quadratic step identity converts the curvature lower bound into a fixed drop.
    rw [hstep_eq]
    linarith
  rcases Filter.eventually_atTop.mp hdrop_eventually with ⟨N, hN⟩
  exact ⟨c, hc_pos, N, fun m hm ↦ hN m hm⟩

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
    0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xBar j := by
  by_contra hneg
  have hneg' :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xBar j < 0 :=
    lt_of_not_ge hneg
  obtain ⟨c, hc_pos, N, hdrop⟩ :=
    polytope_quadratic_uniform_objective_drop_of_negative_cluster_derivative
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0)
      hinit htraj hψtendsto hconst hneg'
  have hantitone :=
    Lemma_13_19_TrajectoryCore.polytope_quadratic_exact_line_search_objective_antitone
      (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj
  have hiter :
      ∀ m : ℕ,
        f_q (x (ψ (N + m)) : E) ≤ f_q (x (ψ N) : E) - (m : ℝ) * c := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        have hdrop_m :
            f_q (x (ψ (N + m) + 1) : E) ≤
              f_q (x (ψ (N + m)) : E) - c :=
          hdrop (N + m) (Nat.le_add_right N m)
        have hpsi_step :
            ψ (N + m) + 1 ≤ ψ (N + m + 1) := by
          exact Nat.succ_le_of_lt (hψmono (Nat.lt_succ_self (N + m)))
        have hmono_step :
            f_q (x (ψ (N + m + 1)) : E) ≤
              f_q (x (ψ (N + m) + 1) : E) :=
          hantitone hpsi_step
        -- Propagate the one-step fixed drop to the next subsequence term by monotonicity.
        have hnext :
            f_q (x (ψ (N + m + 1)) : E) ≤
              (f_q (x (ψ N) : E) - (m : ℝ) * c) - c :=
          hmono_step.trans (hdrop_m.trans (sub_le_sub_right hm c))
        rw [Nat.cast_succ]
        convert hnext using 1 <;> ring
  obtain ⟨m, hm⟩ := exists_nat_gt (gap[ψ N] / c)
  have hgap_nonneg_tail :
      0 ≤ gap[ψ (N + m)] :=
    Lemma_13_19_TrajectoryCore.polytope_quadratic_objective_gap_nonneg
      (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) hboundary (ψ (N + m))
  have hgap_upper :
      gap[ψ (N + m)] ≤ gap[ψ N] - (m : ℝ) * c := by
    -- Translate the objective decrease estimate into the gap language by subtracting `f_opt`.
    linarith [hiter m]
  have hgap_neg :
      gap[ψ N] - (m : ℝ) * c < 0 := by
    exact sub_neg.mpr ((div_lt_iff₀ hc_pos).mp hm)
  linarith

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
    xBar = xStar := by
  obtain ⟨ψ, j, hψmono, hψtendsto, hconst⟩ :=
    polytope_quadratic_constant_argmin_subseq_of_mapClusterPt
      (a := a) (x := x) (i := i) hxBar
  have hxBar_mem :
      xBar ∈ Ω :=
    polytope_quadratic_cluster_point_mem_feasible_set (a := a) (x := x) hxBar
  have hj_argmin :
      j ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xBar) :=
    polytope_quadratic_vertex_argmin_at_cluster_point_of_constant_argmin_subseq
      (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj hψtendsto hconst
  have hderiv_nonneg :
      0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xBar j :=
    polytope_quadratic_directional_derivative_nonneg_at_cluster_point_of_constant_argmin_subseq
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
      hboundary hinit htraj hψmono hψtendsto hconst
  have hxBar_min_univ :
      IsMinOn (polytope_quadratic_problem Q b a) Set.univ xBar :=
    polytope_quadratic_isMinOn_of_nonneg_directional_derivative
      (Q := Q) (b := b) (a := a) (xk := xBar) (i := j) hxBar_mem hj_argmin hderiv_nonneg
  have hxBar_min_Ω :
      IsMinOn (polytope_quadratic_problem Q b a) Ω xBar := by
    -- Restrict the global constrained optimality certificate back to the feasible set `Ω`.
    rw [isMinOn_iff] at hxBar_min_univ ⊢
    intro y hy
    exact hxBar_min_univ y (Set.mem_univ y)
  have hxBar_sol :
      xBar ∈ constrained_problem_solutions (polytope_quadratic_problem Q b a) Ω := by
    simpa [mem_constrained_problem_solutions_iff] using ⟨hxBar_mem, hxBar_min_Ω⟩
  -- Route correction: once the limiting derivative is shown nonnegative, the source stationary
  -- step collapses to uniqueness of the constrained optimizer supplied by Assumption 13.17.
  exact
    Lemma_13_19_TrajectoryCore.polytope_quadratic_eq_boundary_optimizer_of_mem_constrained_problem_solutions
      (Q := Q) (b := b) (a := a) (xStar := xStar) hboundary hxBar_sol

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
    Filter.Tendsto (fun k ↦ (x k : E)) Filter.atTop (nhds xStar) := by
  -- Every subsequence stays in the compact feasible polytope, so it has a convergent subsubsequence.
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  have hfreq : ∃ᶠ m : ℕ in Filter.atTop, (x (ns m) : E) ∈ Ω := by
    exact (Filter.Eventually.of_forall fun m ↦ (x (ns m)).property).frequently
  rcases ((Set.finite_range a).isCompact_convexHull ℝ).exists_mapClusterPt_of_frequently hfreq with
    ⟨y, hyΩ, hyCluster⟩
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hyCluster
  have hyCluster_orig : MapClusterPt y Filter.atTop (fun k ↦ (x k : E)) :=
    hyCluster.of_comp hns
  have hyEq :
      y = xStar :=
    polytope_quadratic_cluster_point_eq_boundary_optimizer_of_exact_trajectory
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
      hboundary hinit htraj hyCluster_orig
  exact ⟨ψ, by simpa [Function.comp, hyEq] using hψtendsto⟩

end Lemma_13_19_ClusterConvergence

end

end
