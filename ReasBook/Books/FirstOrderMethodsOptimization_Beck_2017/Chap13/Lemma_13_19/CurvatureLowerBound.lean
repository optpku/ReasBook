/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.ClusterConvergence

-- Theorem-local curvature lower-bound helpers for Lemma 13.19.

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
local notation "κ[" k "]" =>
  dotProduct (d[k]) (Q *ᵥ d[k])

section

variable
  {v0 : stdSimplex ℝ (Fin l)} {xStar : Fin n → ℝ}

local notation "Ω" => convexHull ℝ (Set.range a)
local notation "f_q" => polytope_quadratic_objective Q b

namespace Lemma_13_19_Curvature

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
    a j ≠ xStar := by
  intro hj
  have hxStar_data : xStar ∈ Ω ∧ IsMinOn (polytope_quadratic_problem Q b a) Ω xStar := by
    simpa using hboundary.mem_constrained_problem_solutions
  have hxStar_le_x0 :
      f_q xStar ≤ f_q (x 0 : E) := by
    -- Compare the optimal boundary point with the initial feasible iterate.
    have hle := hxStar_data.2 (x 0).property
    change polytope_quadratic_problem Q b a xStar ≤
      polytope_quadratic_problem Q b a (x 0 : E) at hle
    rw [polytope_quadratic_problem_of_mem Q b a hxStar_data.1,
      polytope_quadratic_problem_of_mem Q b a (x 0).property] at hle
    exact EReal.coe_le_coe_iff.mp hle
  have hx0_lt_xStar :
      f_q (x 0 : E) < f_q xStar := by
    -- The strict-vertex-sublevel hypothesis transfers to `xStar` through the assumed equality.
    simpa [hj] using hinit.objective_lt_vertex j
  linarith

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
    ∃ ε > 0, ∀ j : Fin l, ε ≤ ‖a j - xStar‖ := by
  classical
  by_cases hnonempty : Nonempty (Fin l)
  · let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun j : Fin l ↦ ‖a j - xStar‖)
    have hε_pos : 0 < ε := by
      -- Every individual vertex distance is positive, so their finite minimum is positive.
      refine (Finset.lt_inf'_iff Finset.univ_nonempty).2 ?_
      intro j hj
      have hj_ne :
          a j ≠ xStar :=
        polytope_quadratic_boundary_optimizer_ne_vertex
          (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) (v0 := v0)
          hboundary hinit j
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hj_ne)
    refine ⟨ε, hε_pos, ?_⟩
    intro j
    exact Finset.inf'_le _ (Finset.mem_univ j)
  · haveI : IsEmpty (Fin l) := not_nonempty_iff.mp hnonempty
    have hsum : (∑ j : Fin l, v0 j) = 1 := stdSimplex.sum_eq_one v0
    simp at hsum

/-- Helper for Lemma 13.19: a positive-definite quadratic form dominates the Euclidean square norm
by a uniform positive constant. -/
theorem exists_pos_quadratic_form_lower_bound_of_posDef :
    ∃ γ > 0, ∀ d : E, γ * ‖d‖ ^ (2 : ℕ) ≤ dotProduct d (Q *ᵥ d) := by
  by_cases hsub : Subsingleton E
  · have hzero : ∀ d : E, d = 0 := fun d ↦ hsub.elim d 0
    refine ⟨1, zero_lt_one, ?_⟩
    intro d
    -- In the trivial space, the inequality is immediate because every direction vanishes.
    simp [hzero d]
  · let φ : E → ℝ := fun d ↦ dotProduct d (Q *ᵥ d)
    haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    have hφ_cont : Continuous φ := by
      -- The quadratic form is continuous because it is bilinear in the vector argument.
      dsimp [φ]
      exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    have hsphere_nonempty : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨u, hu_sphere, hu_min⟩ :=
      (isCompact_sphere (0 : E) 1).exists_isMinOn hsphere_nonempty hφ_cont.continuousOn
    let γ : ℝ := φ u
    have hu_ne : u ≠ 0 := by
      -- A point on the unit sphere cannot be the zero vector.
      rw [Metric.mem_sphere, dist_eq_norm] at hu_sphere
      have hu_norm : ‖u‖ = 1 := by simpa using hu_sphere
      exact norm_ne_zero_iff.mp (hu_norm.symm ▸ one_ne_zero)
    have hγ_pos : 0 < γ := by
      -- Positive definiteness makes the quadratic form strictly positive on the unit sphere.
      dsimp [γ, φ]
      simpa using Q.2.dotProduct_mulVec_pos hu_ne
    refine ⟨γ, hγ_pos, ?_⟩
    intro d
    by_cases hd : d = 0
    · -- The zero direction satisfies the coercive lower bound trivially.
      simp [hd]
    · have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
      let u' : E := (‖d‖)⁻¹ • d
      have hu'_sphere : u' ∈ Metric.sphere (0 : E) 1 := by
        -- Normalize a nonzero direction to the unit sphere.
        rw [Metric.mem_sphere, dist_eq_norm]
        dsimp [u']
        have hd_norm_ne : ‖d‖ ≠ 0 := ne_of_gt hd_norm_pos
        simp [norm_smul, hd_norm_ne]
      have hmin :
          γ ≤ φ u' := by
        -- The unit-sphere minimum bounds the normalized direction from below.
        exact (isMinOn_iff.mp hu_min) u' hu'_sphere
      have hscale :
          φ u' = (‖d‖)⁻¹ * (‖d‖)⁻¹ * φ d := by
        -- Normalization factors out two copies of `‖d‖⁻¹` from the quadratic form.
        dsimp [φ, u']
        simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        ring
      have hbound :
          γ ≤ (‖d‖)⁻¹ * (‖d‖)⁻¹ * φ d := by
        rw [hscale] at hmin
        exact hmin
      have hbound' :
          γ * ‖d‖ ^ (2 : ℕ) ≤ φ d := by
        have hd_norm_ne : ‖d‖ ≠ 0 := ne_of_gt hd_norm_pos
        rw [show ‖d‖ ^ (2 : ℕ) = ‖d‖ * ‖d‖ by ring]
        have hmul :
            γ * (‖d‖ * ‖d‖) ≤ ((‖d‖)⁻¹ * (‖d‖)⁻¹ * φ d) * (‖d‖ * ‖d‖) := by
          exact mul_le_mul_of_nonneg_right hbound (by positivity)
        have hright :
            ((‖d‖)⁻¹ * (‖d‖)⁻¹ * φ d) * (‖d‖ * ‖d‖) = φ d := by
          field_simp [hd_norm_ne]
        simpa [φ, hright] using hmul
      simpa [γ, φ] using hbound'

/-- Helper for Lemma 13.19: the directional curvatures `((dᵏ)^T Q dᵏ)` are uniformly bounded
below by a positive constant. -/
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
    ∃ β > 0, ∀ k : ℕ, β ≤ κ[k] := by
  obtain ⟨γ, hγ_pos, hγ_bound⟩ :=
    exists_pos_quadratic_form_lower_bound_of_posDef (Q := Q)
  obtain ⟨ε, hε_pos, hε_le⟩ :=
    exists_pos_vertex_distance_lower_bound_at_boundary_optimizer
      (Q := Q) (b := b) (a := a) (x := x) (xStar := xStar) (v0 := v0) hboundary hinit
  have hxtendsto :
      Filter.Tendsto (fun k ↦ (x k : E)) Filter.atTop (nhds xStar) :=
    Lemma_13_19_ClusterConvergence.polytope_quadratic_iterates_tendsto_boundary_optimizer
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
      hboundary hinit htraj
  have hdist_tendsto :
      Filter.Tendsto (fun k ↦ ‖(x k : E) - xStar‖) Filter.atTop (nhds 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp hxtendsto
  have htail :
      ∀ᶠ k : ℕ in Filter.atTop, ‖(x k : E) - xStar‖ < ε / 2 := by
    -- Convergence to `xStar` makes the whole tail stay within the `ε / 2` ball.
    have hε_half_pos : 0 < ε / 2 := by positivity
    exact hdist_tendsto.eventually (Iio_mem_nhds hε_half_pos)
  rcases Filter.eventually_atTop.mp htail with ⟨N, hN⟩
  let η : ℝ := min (ε / 2) (Finset.inf' (Finset.range (N + 1)) (by simp) fun k ↦ ‖d[k]‖)
  have hη_pos : 0 < η := by
    -- Combine the positive tail separation with the finitely many initial positive direction norms.
    refine lt_min ?_ ?_
    · positivity
    · exact (Finset.lt_inf'_iff (by simp)).2 fun k hk ↦ by
        have hd_ne : d[k] ≠ 0 := by
          intro hd
          have hzero :
              polytope_quadratic_conditional_gradient_directional_derivative
                Q b a (x k) (i k) = 0 := by
            rw [polytope_quadratic_conditional_gradient_directional_derivative_eq, hd]
            simp
          linarith [htraj.directional_derivative_neg k]
        exact norm_pos_iff.mpr hd_ne
  refine ⟨γ * η ^ (2 : ℕ), by positivity, ?_⟩
  intro k
  have hη_le_norm : η ≤ ‖d[k]‖ := by
    by_cases hk : k ≤ N
    · exact le_trans (min_le_right _ _) (Finset.inf'_le _ (by simpa using hk))
    · have hNk : N ≤ k := Nat.le_of_not_ge hk
      have htailk : ‖(x k : E) - xStar‖ < ε / 2 := hN k hNk
      have htriangle :
          ‖a (i k) - xStar‖ ≤ ‖d[k]‖ + ‖(x k : E) - xStar‖ := by
        simpa [polytope_quadratic_conditional_gradient_direction_eq, dist_eq_norm] using
          (dist_triangle (a (i k)) (x k : E) xStar)
      have htailnorm : ε / 2 ≤ ‖d[k]‖ := by
        linarith [hε_le (i k), htriangle]
      exact le_trans (min_le_left _ _) htailnorm
  have hη_sq : η ^ (2 : ℕ) ≤ ‖d[k]‖ ^ (2 : ℕ) := by
    nlinarith [hη_le_norm, norm_nonneg d[k]]
  have hcurv : γ * ‖d[k]‖ ^ (2 : ℕ) ≤ κ[k] := by
    simpa using hγ_bound (d[k])
  nlinarith

end Lemma_13_19_Curvature

end

end
