/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_26
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_36

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Example 6.37 is `source-facing` in the Chapter 6 epigraph/projection domain: the textbook
object is the Lorentz cone `{(x, t) | ‖x‖ ≤ t}`, viewed canonically as
`realEpigraph (norm_penalty 1)`.

Domain sampling for this file uses the owner chain

- `realEpigraph` from Chapter 2 for the epigraph view,
- `norm_penalty` and `prox_norm_penalty_eq_singleton_shrinkage` from Example 6.19 for the norm
  penalty and its radial proximal singleton,
- `P[...]` from Theorem 6.24 for the set-valued projection owner,
- `projection_mapping_realEpigraph_eq_singleton_of_mem` from Theorem 6.36 for the canonical
  feasible-branch epigraph projection theorem.

Theorem 6.36 is a related finite-dimensional `bridge/view`, but its ambient assumptions are
strictly stronger than the Hilbert-space statement kept here. So this file should not collapse its
main theorem into that bridge; it should keep the stronger source-facing projection formula while
reusing the canonical owners above and avoiding any separate Lorentz-cone `def`. -/

-- Proof sketch: unfold `realEpigraph` and `norm_penalty`; the membership condition reduces
-- definitionally to `((‖x‖ : ℝ) : EReal) ≤ t`, which is equivalent to `‖x‖ ≤ t`.
/-- A pair `(x, t)` belongs to the Lorentz cone exactly when it lies in the real epigraph of the
norm, equivalently when `‖x‖ ≤ t`. -/
@[simp] theorem mem_realEpigraph_norm_penalty_one_iff (x : E) (t : ℝ) :
    (x, t) ∈ realEpigraph (norm_penalty 1) ↔ ‖x‖ ≤ t := by
  simp [realEpigraph, norm_penalty]

-- Proof sketch: this is the norm-specialized feasible branch of the canonical epigraph projection
-- theorem from Theorem 6.36, rewritten using `norm_penalty_apply`.
/-- If `(x, s)` already lies in the Lorentz cone `realEpigraph (norm_penalty 1)`, then its
projection onto that cone is the singleton `{(x, s)}`. This is the norm specialization of the
canonical feasible-branch epigraph projection theorem. -/
theorem projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_mem
    (x : E) (s : ℝ) (hxs : ‖x‖ ≤ s) :
    P[realEpigraph (norm_penalty 1)] (x, s) = {(x, s)} := by
  have hepigraph :
      realEpigraph (norm_penalty 1) = realEpigraph (fun y : E ↦ ((‖y‖ : ℝ) : EReal)) := by
    ext p
    simp [realEpigraph, norm_penalty]
  rw [hepigraph]
  simpa using
    projection_mapping_realEpigraph_eq_singleton_of_mem
      (fun y : E ↦ ‖y‖) x s hxs

section

variable [InnerProductSpace ℝ E]

/-- Helper for Example 6.37: the Lorentz cone `realEpigraph (norm_penalty 1)` is convex because it
is the epigraph of the convex norm function. -/
lemma convex_realEpigraph_norm_penalty_one :
    Convex ℝ (realEpigraph (norm_penalty 1 : E → EReal)) := by
  -- Rewrite to the ordinary real-valued epigraph of the norm, where convexity is standard.
  have hnorm : ConvexOn ℝ Set.univ (fun y : E ↦ ‖y‖) :=
    convexOn_norm convex_univ
  have hepigraph : Convex ℝ {p : E × ℝ | p.1 ∈ Set.univ ∧ ‖p.1‖ ≤ p.2} :=
    hnorm.convex_epigraph
  simpa [realEpigraph, norm_penalty] using hepigraph

/-- Helper for Example 6.37: in the branch `s < -‖x‖`, the origin is the unique projection of
`(x, s)` onto the Lorentz cone. -/
theorem projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_neg_branch
    (x : E) (s : ℝ) (hzero : s < -‖x‖) :
    P[realEpigraph (norm_penalty 1)] (x, s) = {((0 : E), (0 : ℝ))} := by
  have hs_neg : s < 0 := by
    linarith [norm_nonneg x, hzero]
  have hx_lt : ‖x‖ < -s := by
    linarith
  have hzero_mem : ((0 : E), (0 : ℝ)) ∈ realEpigraph (norm_penalty 1) := by
    -- The origin lies on the boundary of the cone.
    simp
  have hzero_proj : ((0 : E), (0 : ℝ)) ∈ P[realEpigraph (norm_penalty 1)] (x, s) := by
    -- Every feasible cone point has second coordinate `t ≥ 0`, so its distance from `(x, s)` is
    -- at least `-s`; the origin attains exactly that distance.
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hzero_mem, ?_⟩
    intro z hz
    rcases z with ⟨y, t⟩
    rw [mem_realEpigraph_norm_penalty_one_iff] at hz
    have ht_nonneg : 0 ≤ t := le_trans (norm_nonneg y) hz
    have hts_nonneg : 0 ≤ t - s := by
      linarith
    have hcoord : -s ≤ |t - s| := by
      rw [abs_of_nonneg hts_nonneg]
      linarith
    have hdist_lower : -s ≤ ‖(y, t) - (x, s)‖ := by
      have hnorm_prod : ‖(y, t) - (x, s)‖ = max ‖y - x‖ |t - s| := by
        simp [Prod.norm_def]
      rw [hnorm_prod]
      exact le_trans hcoord (le_max_right _ _)
    have hzero_dist : ‖((0 : E), (0 : ℝ)) - (x, s)‖ = -s := by
      have hnorm_prod : ‖((0 : E), (0 : ℝ)) - (x, s)‖ = max ‖x‖ |s| := by
        simp [Prod.norm_def]
      rw [hnorm_prod, abs_of_neg hs_neg, max_eq_right (le_of_lt hx_lt)]
    rw [hzero_dist]
    exact hdist_lower
  ext z
  constructor
  · intro hz_proj
    rcases z with ⟨y, t⟩
    rw [Set.mem_singleton_iff]
    have hy_mem : (y, t) ∈ realEpigraph (norm_penalty 1) :=
      (mem_projection_mapping_iff.mp hz_proj).1
    rw [mem_realEpigraph_norm_penalty_one_iff] at hy_mem
    have ht_nonneg : 0 ≤ t := le_trans (norm_nonneg y) hy_mem
    have hy_min : IsMinOn (fun z ↦ ‖z - (x, s)‖) (realEpigraph (norm_penalty 1)) (y, t) :=
      (mem_projection_mapping_iff.mp hz_proj).2
    have hdist_le : ‖(y, t) - (x, s)‖ ≤ ‖((0 : E), (0 : ℝ)) - (x, s)‖ := by
      exact (isMinOn_iff.mp hy_min) _ hzero_mem
    have hts_nonneg : 0 ≤ t - s := by
      linarith
    have hcoord : -s ≤ |t - s| := by
      rw [abs_of_nonneg hts_nonneg]
      linarith
    have hdist_lower : -s ≤ ‖(y, t) - (x, s)‖ := by
      have hnorm_prod : ‖(y, t) - (x, s)‖ = max ‖y - x‖ |t - s| := by
        simp [Prod.norm_def]
      rw [hnorm_prod]
      exact le_trans hcoord (le_max_right _ _)
    have hzero_dist : ‖((0 : E), (0 : ℝ)) - (x, s)‖ = -s := by
      have hnorm_prod : ‖((0 : E), (0 : ℝ)) - (x, s)‖ = max ‖x‖ |s| := by
        simp [Prod.norm_def]
      rw [hnorm_prod, abs_of_neg hs_neg, max_eq_right (le_of_lt hx_lt)]
    have hdist_eq : ‖(y, t) - (x, s)‖ = -s := by
      rw [hzero_dist] at hdist_le
      exact le_antisymm hdist_le hdist_lower
    have habs_eq : |t - s| = -s := by
      have habs_le : |t - s| ≤ -s := by
        rw [← hdist_eq]
        have hnorm_prod : ‖(y, t) - (x, s)‖ = max ‖y - x‖ |t - s| := by
          simp [Prod.norm_def]
        rw [hnorm_prod]
        exact le_max_right _ _
      exact le_antisymm habs_le hcoord
    have ht_zero : t = 0 := by
      rw [abs_of_nonneg hts_nonneg] at habs_eq
      linarith
    have hy_zero_norm : ‖y‖ = 0 := by
      have hy_le_zero : ‖y‖ ≤ 0 := by
        simpa [ht_zero] using hy_mem
      exact le_antisymm hy_le_zero (norm_nonneg y)
    have hy_zero : y = 0 := norm_eq_zero.mp hy_zero_norm
    exact Prod.ext hy_zero ht_zero
  · intro hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hzero_proj

/-- Helper for Example 6.37: the balanced active-branch point lies in the Lorentz cone whenever
`(x, s)` is infeasible but not in the negative branch. -/
theorem active_branch_candidate_mem_realEpigraph_norm_penalty_one
    (x : E) (s : ℝ) (hfeas : ¬ ‖x‖ ≤ s) (hzero : ¬ s < -‖x‖) :
    ((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2) ∈ realEpigraph (norm_penalty 1) := by
  -- The branch assumptions give `-‖x‖ ≤ s < ‖x‖`, so the balancing coefficient is well-defined
  -- and nonnegative.
  have hs_lt : s < ‖x‖ := lt_of_not_ge hfeas
  have hs_ge : -‖x‖ ≤ s := not_lt.mp hzero
  have hx_pos : 0 < ‖x‖ := by
    by_contra h
    have hx_zero : ‖x‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg x)
    have hs_nonneg : 0 ≤ s := by
      simpa [hx_zero] using hs_ge
    linarith
  have hcoeff_nonneg : 0 ≤ (‖x‖ + s) / (2 * ‖x‖) := by
    have hnum_nonneg : 0 ≤ ‖x‖ + s := by
      linarith
    have hden_nonneg : 0 ≤ 2 * ‖x‖ := by
      positivity
    exact div_nonneg hnum_nonneg hden_nonneg
  have hnorm_eq :
      ‖(((‖x‖ + s) / (2 * ‖x‖)) • x : E)‖ = (‖x‖ + s) / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
    field_simp [hx_pos.ne']
  -- The constructed point sits exactly on the cone boundary `‖u‖ = t`.
  rw [mem_realEpigraph_norm_penalty_one_iff]
  rw [hnorm_eq]

/-- Helper for Example 6.37: every point of the Lorentz cone is at distance at least
`(‖x‖ - s) / 2` from `(x, s)` in the ambient max norm. -/
theorem lorentz_cone_distance_lower_bound
    (x y : E) (s t : ℝ)
    (hy : (y, t) ∈ realEpigraph (norm_penalty 1)) :
    (‖x‖ - s) / 2 ≤ ‖(y, t) - (x, s)‖ := by
  rw [mem_realEpigraph_norm_penalty_one_iff] at hy
  -- Feasibility gives `‖y‖ ≤ t`, so the triangle inequality yields the horizontal lower bound.
  have hfirst : ‖x‖ - t ≤ ‖x - y‖ := by
    have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖(x - y) + y‖ := by
          abel_nf
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    linarith
  -- The vertical coordinate contributes `t - s`.
  have hsecond : t - s ≤ |t - s| := by
    simpa [abs_sub_comm] using (neg_le_abs (s - t))
  have hnorm_prod : ‖(y, t) - (x, s)‖ = max ‖y - x‖ |t - s| := by
    simp [Prod.norm_def]
  rw [hnorm_prod, norm_sub_rev]
  have hmax_first : ‖x‖ - t ≤ max ‖x - y‖ |t - s| := by
    exact le_trans hfirst (le_max_left _ _)
  have hmax_second : t - s ≤ max ‖x - y‖ |t - s| := by
    exact le_trans hsecond (le_max_right _ _)
  linarith

/-- Helper for Example 6.37: on the active branch, the balanced boundary point is exactly
`(‖x‖ - s) / 2` away from `(x, s)` in the ambient max norm. -/
theorem active_branch_candidate_distance_eq_half_gap
    (x : E) (s : ℝ) (hfeas : ¬ ‖x‖ ≤ s) (hzero : ¬ s < -‖x‖) :
    ‖(x, s) - ((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2)‖ = (‖x‖ - s) / 2 := by
  -- The branch assumptions again give `-‖x‖ ≤ s < ‖x‖`, so the balance point is valid.
  have hs_lt : s < ‖x‖ := lt_of_not_ge hfeas
  have hs_ge : -‖x‖ ≤ s := not_lt.mp hzero
  have hx_pos : 0 < ‖x‖ := by
    by_contra h
    have hx_zero : ‖x‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg x)
    have hs_nonneg : 0 ≤ s := by
      simpa [hx_zero] using hs_ge
    linarith
  let a : ℝ := (‖x‖ + s) / (2 * ‖x‖)
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    field_simp [hx_pos.ne']
    linarith
  have hx_sub : x - (a • x : E) = (1 - a) • x := by
    simp [sub_eq_add_neg, add_smul]
  have hfirst :
      ‖x - (a • x : E)‖ = (‖x‖ - s) / 2 := by
    have hone_minus_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
    rw [hx_sub, norm_smul, Real.norm_of_nonneg hone_minus_nonneg]
    dsimp [a]
    field_simp [hx_pos.ne']
    ring
  have hsecond_nonneg : 0 ≤ ((‖x‖ + s) / 2) - s := by
    linarith
  have hsecond :
      |((‖x‖ + s) / 2) - s| = (‖x‖ - s) / 2 := by
    rw [abs_of_nonneg hsecond_nonneg]
    ring
  -- The horizontal and vertical errors are equal at the balancing point.
  have hnorm_prod :
      ‖(x, s) - ((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2)‖ =
        max ‖x - (((‖x‖ + s) / (2 * ‖x‖)) • x : E)‖ |s - (‖x‖ + s) / 2| := by
    simp [Prod.norm_def]
  rw [hnorm_prod, hfirst, abs_sub_comm, hsecond]
  simp

/-- Helper for Example 6.37: on the active branch `-‖x‖ ≤ s < ‖x‖`, the balanced boundary point
is the unique projection of `(x, s)` onto the Lorentz cone. -/
theorem projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_active_branch
    (x : E) (s : ℝ) (hfeas : ¬ ‖x‖ ≤ s) (hzero : ¬ s < -‖x‖) :
    P[realEpigraph (norm_penalty 1)] (x, s) =
      {((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2)} := by
  let C : Set (E × ℝ) := realEpigraph (norm_penalty 1 : E → EReal)
  let t0 : ℝ := (‖x‖ + s) / 2
  let y0 : E := (((‖x‖ + s) / (2 * ‖x‖)) • x)
  let p : E × ℝ := ((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2)
  have hs_lt : s < ‖x‖ := lt_of_not_ge hfeas
  have hs_ge : -‖x‖ ≤ s := not_lt.mp hzero
  have hx_pos : 0 < ‖x‖ := by
    by_contra h
    have hx_zero : ‖x‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg x)
    have hs_nonneg : 0 ≤ s := by
      simpa [hx_zero] using hs_ge
    linarith
  have ht0_nonneg : 0 ≤ t0 := by
    dsimp [t0]
    linarith
  have ht0_lt : t0 < ‖x‖ := by
    dsimp [t0]
    linarith
  have hp_mem : p ∈ C := by
    -- The candidate lies on the cone boundary.
    simpa [C, p] using
      active_branch_candidate_mem_realEpigraph_norm_penalty_one x s hfeas hzero
  have hp_dist : ‖p - (x, s)‖ = (‖x‖ - s) / 2 := by
    simpa [p, norm_sub_rev] using
      active_branch_candidate_distance_eq_half_gap x s hfeas hzero
  have hp_proj : p ∈ P[C] (x, s) := by
    -- The global lower bound is sharp at `p`, so `p` minimizes the distance to the cone.
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hp_mem, ?_⟩
    intro z hz
    rw [hp_dist]
    exact lorentz_cone_distance_lower_bound x z.1 s z.2 hz
  ext z
  constructor
  · intro hz
    rcases z with ⟨y, t⟩
    rw [Set.mem_singleton_iff]
    have hy_memC : (y, t) ∈ C := (mem_projection_mapping_iff.mp hz).1
    have hy_mem : (y, t) ∈ realEpigraph (norm_penalty 1) := by
      simpa [C] using hy_memC
    rw [mem_realEpigraph_norm_penalty_one_iff] at hy_memC
    have hy_min : IsMinOn (fun z ↦ ‖z - (x, s)‖) C (y, t) :=
      (mem_projection_mapping_iff.mp hz).2
    have hdist_le : ‖(y, t) - (x, s)‖ ≤ ‖p - (x, s)‖ := by
      exact (isMinOn_iff.mp hy_min) _ hp_mem
    have hdist_eq : ‖(y, t) - (x, s)‖ = (‖x‖ - s) / 2 := by
      rw [hp_dist] at hdist_le
      exact le_antisymm hdist_le (lorentz_cone_distance_lower_bound x y s t hy_mem)
    have hnorm_prod : ‖(y, t) - (x, s)‖ = max ‖y - x‖ |t - s| := by
      simp [Prod.norm_def]
    have hy_dist_le : ‖x - y‖ ≤ (‖x‖ - s) / 2 := by
      rw [← hdist_eq, hnorm_prod, norm_sub_rev]
      exact le_max_left _ _
    have ht_dist_le : |t - s| ≤ (‖x‖ - s) / 2 := by
      rw [← hdist_eq, hnorm_prod]
      exact le_max_right _ _
    have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖(x - y) + y‖ := by
          abel_nf
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    have hnorm_lower : ‖x‖ - t ≤ (‖x‖ - s) / 2 := by
      linarith
    have hts_lower : t - s ≤ (‖x‖ - s) / 2 := by
      have hts_abs : t - s ≤ |t - s| := by
        simpa [abs_sub_comm] using (neg_le_abs (s - t))
      exact le_trans hts_abs ht_dist_le
    have hnorm_eq : ‖x‖ - t = (‖x‖ - s) / 2 := by
      linarith
    have hts_eq : t - s = (‖x‖ - s) / 2 := by
      linarith
    have ht_eq : t = t0 := by
      dsimp [t0]
      linarith
    have hy_dist_eq : ‖x - y‖ = (‖x‖ - s) / 2 := by
      have hy_dist_lower : (‖x‖ - s) / 2 ≤ ‖x - y‖ := by
        linarith
      exact le_antisymm hy_dist_le hy_dist_lower
    have hy_ball : y ∈ Metric.closedBall (0 : E) t0 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, ht_eq] using hy_memC
    have hy_proj_ball : y ∈ P[Metric.closedBall (0 : E) t0] x := by
      -- Once the optimal height is fixed, the horizontal component minimizes distance to the
      -- closed ball of radius `t0`.
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨hy_ball, ?_⟩
      intro u hu
      have hu_ball : ‖u‖ ≤ t0 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have hu_lower : ‖x‖ - t0 ≤ ‖x - u‖ := by
        have htri_u : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := by
          calc
            ‖x‖ = ‖(x - u) + u‖ := by
              abel_nf
            _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
        linarith
      have hy_ball_dist : ‖x - y‖ = ‖x‖ - t0 := by
        calc
          ‖x - y‖ = (‖x‖ - s) / 2 := hy_dist_eq
          _ = ‖x‖ - t0 := by
            dsimp [t0]
            ring
      have hy_ball_dist' : ‖y - x‖ = ‖x‖ - t0 := by
        simpa [norm_sub_rev] using hy_ball_dist
      rw [hy_ball_dist']
      simpa [norm_sub_rev] using hu_lower
    have hy_closedBall_eq :
        y = (0 : E) + (t0 / max ‖x - (0 : E)‖ t0) • (x - (0 : E)) := by
      have hclosedBall :
          P[Metric.closedBall (0 : E) t0] x =
            {(0 : E) + (t0 / max ‖x - (0 : E)‖ t0) • (x - (0 : E))} :=
        projection_mapping_closedBall_eq_singleton_radialRetraction (0 : E) x t0 ht0_nonneg
      rw [hclosedBall] at hy_proj_ball
      exact Set.mem_singleton_iff.mp hy_proj_ball
    have hmax : max ‖x - (0 : E)‖ t0 = ‖x‖ := by
      rw [sub_zero, max_eq_left (le_of_lt ht0_lt)]
    have hmax' : max ‖x‖ t0 = ‖x‖ := by
      simpa [sub_zero] using hmax
    have hcoeff_eq : t0 / ‖x‖ = (‖x‖ + s) / (2 * ‖x‖) := by
      dsimp [t0]
      field_simp [hx_pos.ne']
    have hy_eq' : y = (t0 / ‖x‖) • x := by
      simp [sub_zero, zero_add] at hy_closedBall_eq
      rw [hmax'] at hy_closedBall_eq
      exact hy_closedBall_eq
    have hy_eq : y = y0 := by
      calc
        y = (t0 / ‖x‖) • x := hy_eq'
        _ = (((‖x‖ + s) / (2 * ‖x‖)) • x) := by rw [hcoeff_eq]
        _ = y0 := by rfl
    have hp_eq : (y, t) = p := by
      simp [p, y0, t0, hy_eq, ht_eq]
    simpa [p] using hp_eq
  · intro hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hp_proj

-- Proof sketch: the feasible branch is the specialized singleton theorem
-- `projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_mem`. On the infeasible
-- branch, the projection point is determined by the radial proximal singleton from Example 6.19
-- for the norm penalty. Simplifying that singleton yields the remaining two textbook regimes:
-- `(0, 0)` when `s < -‖x‖`, and the active-constraint formula otherwise.
/-- Example 6.37: for the Lorentz cone
`{(x, t) ∈ E × ℝ | ‖x‖ ≤ t} = realEpigraph (norm_penalty 1)`, the orthogonal projection of
`(x, s)` onto that cone is the singleton given by the textbook piecewise formula: it is
`(((‖x‖ + s) / (2 ‖x‖)) • x, (‖x‖ + s) / 2)` when `|s| ≤ ‖x‖`, `(0, 0)` when
`s < -‖x‖`, and `(x, s)` when `‖x‖ ≤ s`. This explicit formula is stated at the real
inner-product-space level, with no finite-dimensional hypothesis in the public API. -/
theorem projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_piecewise
    (x : E) (s : ℝ) :
    P[realEpigraph (norm_penalty 1)] (x, s) =
      {if hfeas : ‖x‖ ≤ s then
        (x, s)
      else if hzero : s < -‖x‖ then
        (0, 0)
      else
        ((((‖x‖ + s) / (2 * ‖x‖)) • x), (‖x‖ + s) / 2)} := by
  -- Route correction: Theorem 6.36's prox/root branch is blocked by the ambient product norm, so
  -- this proof works directly with the Lorentz-cone geometry in the product max norm.
  by_cases hfeas : ‖x‖ ≤ s
  · -- Feasible points project to themselves.
    rw [dif_pos hfeas]
    exact projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_mem x s hfeas
  · rw [dif_neg hfeas]
    by_cases hzero : s < -‖x‖
    · -- Deep negative points project to the origin.
      rw [dif_pos hzero]
      exact projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_neg_branch x s hzero
    · -- Otherwise the balanced boundary point realizes the sharp lower bound.
      rw [dif_neg hzero]
      exact
        projection_mapping_realEpigraph_norm_penalty_one_eq_singleton_of_active_branch
          x s hfeas hzero

end

end
