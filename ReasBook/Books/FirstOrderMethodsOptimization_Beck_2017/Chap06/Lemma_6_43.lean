/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open AffineMap

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 6.43 is `source-facing` in the Chapter 6 proximal-operator API: the textbook computes the
proximal operator of the distance penalty to a nonempty closed convex set. Domain sampling uses the
 project complete-subset bridge `metricProjectionOfComplete`, its ray identity
`metricProjection_add_smul_sub_metricProjection_eq`, and the canonical affine owner
`AffineMap.lineMap`. The main theorem is `source-facing`, while `metricProjectionOfComplete` is
the point-projection `bridge/view` owner for complete subsets and the older `Pp[...]` notation is
only a separate `bridge/view`.
The primitive data are the set `C`, its nonempty/complete/convex hypotheses, the scalar `lam`, and
the base point `x`; the explicit projected point and affine combination are derived API and should
be stated directly through those owners. -/

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C)

local notation "P" => metricProjectionOfComplete C hC_nonempty hC_complete hC_convex

-- Proof sketch: apply the second prox theorem to `f = fun y ↦ ((lam * infDist y C : ℝ) : EReal)`.
-- Proof sketch: the distance-penalty proximal objective is controlled by the residual
-- `y - P y`. The candidate point is obtained by applying the earlier norm-penalty shrinkage
-- formula to the residual `x - P x`, then translating back from `P x`. A projection-ray lemma
-- keeps `P x` as the projection of that candidate, and a lower-bound decomposition introduces a
-- nonnegative defect term measuring the motion of the projection point from `P x` to `P y`.

/-- Helper for Lemma 6.43: points on the ray leaving `P x` in the direction of `x - P x`
keep the same metric projection onto `C`. -/
theorem metricProjection_eq_along_projection_ray
    (x : E) (t : ℝ) (ht : 0 ≤ t) :
    P ((P x : E) + t • (x - P x)) = P x := by
  let y : E := (P x : E) + t • (x - P x)
  have hPx : (P x : E) ∈ C := (P x).2
  -- The projection inequality at `x` transfers to every point on the projection ray.
  have hy_Px : ∀ w ∈ C, inner ℝ (y - P x) (w - P x) ≤ 0 := by
    intro w hw
    have hx :=
      inner_sub_metricProjectionOfComplete_le_zero
        C hC_nonempty hC_complete hC_convex x w hw
    have hy : y - P x = t • (x - P x) := by
      dsimp [y]
      abel
    rw [hy, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht hx
  have hPx_min : ‖y - P x‖ = ⨅ z : C, ‖y - z‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex hPx).2 hy_Px
  have hPy_min : ‖y - P y‖ = ⨅ z : C, ‖y - z‖ := by
    simpa [y] using
      norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex y
  have hPy : ∀ w ∈ C, inner ℝ (y - P y) (w - P y) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex (P y).2).1 hPy_min
  have h1 : inner ℝ (y - P y) (P x - P y) ≤ 0 := hPy (P x) hPx
  have h2 : inner ℝ (y - P x) (P y - P x) ≤ 0 := hy_Px (P y) (P y).2
  -- Comparing the two variational inequalities forces the projection points to coincide.
  have hnorm : ‖(P y : E) - P x‖ ^ 2 ≤ 0 := by
    calc
      ‖(P y : E) - P x‖ ^ 2 = inner ℝ ((P y : E) - P x) ((P y : E) - P x) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ ((y - P x) - (y - P y)) ((P y : E) - P x) := by
        congr 1
        abel
      _ = inner ℝ (y - P x) ((P y : E) - P x) - inner ℝ (y - P y) ((P y : E) - P x) := by
        rw [inner_sub_left]
      _ ≤ 0 := by
        have h1' : 0 ≤ inner ℝ (y - P y) ((P y : E) - P x) := by
          have h1'' : inner ℝ (y - P y) (-(((P y : E) - P x))) ≤ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
          rw [inner_neg_right] at h1''
          linarith
        linarith
  have hzero : ‖(P y : E) - P x‖ = 0 := by
    nlinarith [sq_nonneg ‖(P y : E) - P x‖, hnorm]
  apply Subtype.ext
  exact sub_eq_zero.mp <| norm_eq_zero.mp hzero

/-- Helper for Lemma 6.43: the distance-penalty proximal objective is bounded below by the
radial residual objective centered at `P x`, together with the nonnegative defect term measuring
the displacement of the projection point. -/
theorem infDist_prox_objective_lower_bound_by_projection_residual
    (lam : ℝ) (x y : E) :
    (lam * ‖y - P y‖ : ℝ)
        + (1 / 2 : ℝ) * ‖(y - P y) - (x - P x)‖ ^ 2
        + (1 / 2 : ℝ) * ‖((P y : E) - P x)‖ ^ 2
      ≤
      (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
  let a : E := (y - P y) - (x - P x)
  let b : E := (P y : E) - P x
  have hy_dist : infDist y C = ‖y - P y‖ := by
    calc
      infDist y C = dist y (P y) := by
        simpa using
          infDist_eq_dist_metricProjectionOfComplete C hC_nonempty hC_complete hC_convex y
      _ = ‖y - P y‖ := by rw [dist_eq_norm]
  have hx_proj :=
    inner_sub_metricProjectionOfComplete_le_zero
      C hC_nonempty hC_complete hC_convex x (P y) (P y).2
  have hy_proj :=
    inner_sub_metricProjectionOfComplete_le_zero
      C hC_nonempty hC_complete hC_convex y (P x) (P x).2
  have hy_proj' : 0 ≤ inner ℝ (y - P y) ((P y : E) - P x) := by
    have hy_proj'' : inner ℝ (y - P y) (-(((P y : E) - P x))) ≤ 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_proj
    rw [inner_neg_right] at hy_proj''
    linarith
  have hcross : 0 ≤ inner ℝ a b := by
    have hcross' :
        0 ≤ inner ℝ (y - P y) b - inner ℝ (x - P x) b := by
      dsimp [b]
      linarith
    simpa [a, b, inner_sub_left] using hcross'
  have hyx : y - x = a + b := by
    dsimp [a, b]
    abel
  have hnorm :
      ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
    calc
      ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
        nlinarith
      _ = ‖a + b‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = ‖y - x‖ ^ 2 := by rw [hyx]
  have hhalf :
      (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
  have hmain :
      (lam * ‖y - P y‖ : ℝ)
          + (1 / 2 : ℝ) * ‖a‖ ^ 2
          + (1 / 2 : ℝ) * ‖b‖ ^ 2
        ≤
        (lam * ‖y - P y‖ : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    have hmain' :
        (lam * ‖y - P y‖ : ℝ)
            + (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2)
          ≤
          (lam * ‖y - P y‖ : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hhalf (lam * ‖y - P y‖)
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using hmain'
  -- Replacing `infDist y C` by the realized projection distance gives the stated lower bound.
  simpa [a, b, hy_dist] using hmain

/-- Helper for Lemma 6.43: the projection-centered shrinkage candidate is exactly the textbook
piecewise point on the segment from `x` to `P x`. -/
theorem distance_prox_candidate_eq_piecewise_target
    (lam : ℝ) (x : E) :
    (P x : E) + (1 - lam / max ‖x - P x‖ lam) • (x - P x) =
      if lam < infDist x C then
        lineMap x (P x) (lam / infDist x C)
      else
        P x := by
  have hpdist : ‖x - P x‖ = infDist x C := by
    calc
      ‖x - P x‖ = dist x (P x) := by rw [dist_eq_norm]
      _ = infDist x C := by
        simpa using
          (infDist_eq_dist_metricProjectionOfComplete C hC_nonempty hC_complete hC_convex x).symm
  by_cases hlt : lam < infDist x C
  · have hmax : max ‖x - P x‖ lam = ‖x - P x‖ := by
      rw [hpdist, max_eq_left (le_of_lt hlt)]
    -- On the active branch, the shrinkage point is the affine interpolation from `x` to `P x`.
    rw [if_pos hlt, hmax, hpdist, AffineMap.lineMap_apply_module]
    rw [smul_sub]
    module
  · have hdist_le : infDist x C ≤ lam := le_of_not_gt hlt
    have hmax : max ‖x - P x‖ lam = lam := by
      rw [hpdist, max_eq_right hdist_le]
    by_cases hlam_zero : lam = 0
    · have hdist_zero : infDist x C = 0 := by
        have hdist_nonneg : 0 ≤ infDist x C := infDist_nonneg
        linarith
      have hx_eq_proj : x = P x := by
        have hnorm_zero : ‖x - P x‖ = 0 := by simpa [hpdist] using hdist_zero
        exact sub_eq_zero.mp <| norm_eq_zero.mp hnorm_zero
      have hproj_fix : P (P x) = P x := by
        simpa using
          metricProjection_eq_along_projection_ray
            C hC_nonempty hC_complete hC_convex x 0 le_rfl
      rw [if_neg hlt]
      rw [hmax, hlam_zero]
      rw [hx_eq_proj, hproj_fix, sub_self, smul_zero, add_zero]
    · have hcoeff_zero : 1 - lam / max ‖x - P x‖ lam = 0 := by
        rw [hmax, div_self hlam_zero, sub_self]
      rw [if_neg hlt]
      simp [hcoeff_zero]

/-- Lemma 6.43: if `C` is a nonempty complete convex subset of a real inner product space and
`0 ≤ λ`, then the proximal mapping of the distance penalty `y ↦ λ d_C(y)` at `x` is the
singleton given by the textbook piecewise formula, written in canonical projection-ray form: when
`λ < d_C(x)` it is `lineMap x (P_C x) (λ / d_C(x))`, equivalently
`P_C(x) + (1 - λ / d_C(x)) (x - P_C(x))`, and when `d_C(x) ≤ λ` it is `P_C(x)`. Here `d_C(x)`
is written as `Metric.infDist x C`, and `P_C` denotes the canonical metric projection onto a
nonempty complete convex set. The textbook closed-subset-of-a-complete-space formulation is the
downstream specialization obtained from `IsClosed.isComplete`. The endpoint `λ = 0` is included
canonically: if `x ∉ C`, then the first branch becomes `lineMap x (P_C x) 0 = x`, while if
`x ∈ C`, then both branches reduce to `x`. -/
theorem prox_infDist_eq_singleton_piecewise_metricProjection
    (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)] x =
      {if lam < infDist x C then
        lineMap x (P x) (lam / infDist x C)
      else
        P x} := by
  by_cases hlam_zero : lam = 0
  · subst lam
    have hprox :
        prox[fun y : E ↦ (((0 : ℝ) * infDist y C : ℝ) : EReal)] x = {x} := by
      simpa using (prox_zero_eq_singleton x)
    rw [hprox]
    apply congrArg Set.singleton
    have hpiece :=
      distance_prox_candidate_eq_piecewise_target
        C hC_nonempty hC_complete hC_convex 0 x
    simpa using hpiece
  have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_zero)
  let p : E := P x
  let v : E := (1 - lam / max ‖x - p‖ lam) • (x - p)
  let u : E := p + v
  have hpdist : ‖x - p‖ = infDist x C := by
    calc
      ‖x - p‖ = dist x (P x) := by
        rw [show p = (P x : E) by rfl, dist_eq_norm]
      _ = infDist x C := by
        simpa using
          (infDist_eq_dist_metricProjectionOfComplete C hC_nonempty hC_complete hC_convex x).symm
  have hv_prox :
      prox[norm_penalty lam] (x - p) = {v} := by
    simpa [p, v] using prox_norm_penalty_eq_singleton_shrinkage lam hlam_pos (x - p)
  have hv_mem : v ∈ prox[norm_penalty lam] (x - p) := by
    rw [hv_prox]
    simp
  have hv_min :
      ∀ z : E,
        (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2
          ≤
          (lam * ‖z‖ : ℝ) + (1 / 2 : ℝ) * ‖z - (x - p)‖ ^ 2 := by
    intro z
    have hv_min_ereal :
        proximal_objective (norm_penalty lam) (x - p) v ≤
          proximal_objective (norm_penalty lam) (x - p) z := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hv_mem
      exact hv_mem z
    have hv_min_real :
        (((lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 : ℝ) : EReal)
          ≤
          (((lam * ‖z‖ : ℝ) + (1 / 2 : ℝ) * ‖z - (x - p)‖ ^ 2 : ℝ) : EReal) := by
      simpa [proximal_objective_apply, norm_penalty_apply]
        using hv_min_ereal
    exact_mod_cast hv_min_real
  have hcoeff_nonneg : 0 ≤ 1 - lam / max ‖x - p‖ lam := by
    have hmax_nonneg : 0 ≤ max ‖x - p‖ lam := le_trans hlam (le_max_right _ _)
    have hdiv_le_one : lam / max ‖x - p‖ lam ≤ 1 := by
      by_cases hmax_zero : max ‖x - p‖ lam = 0
      · have hlam_zero : lam = 0 := by
          have : lam ≤ 0 := by simpa [hmax_zero] using (le_max_right ‖x - p‖ lam)
          linarith
        simp [hlam_zero]
      · have hmax_pos : 0 < max ‖x - p‖ lam := by
          exact lt_of_le_of_ne hmax_nonneg (by simpa [eq_comm] using hmax_zero)
        exact (div_le_one hmax_pos).2 (le_max_right ‖x - p‖ lam)
    linarith
  have hPu : P u = P x := by
    -- The candidate lies on the projection ray from `P x` through `x`.
    simpa [p, u, v] using
      metricProjection_eq_along_projection_ray
        C hC_nonempty hC_complete hC_convex x
        (1 - lam / max ‖x - p‖ lam)
        hcoeff_nonneg
  have hu_obj_eq :
      (lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2
        =
        (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 := by
    have hu_dist : infDist u C = ‖u - p‖ := by
      calc
        infDist u C = dist u (P u) := by
          simpa using
            infDist_eq_dist_metricProjectionOfComplete C hC_nonempty hC_complete hC_convex u
        _ = dist u (P x) := by rw [hPu]
        _ = ‖u - p‖ := by rw [show p = (P x : E) by rfl, dist_eq_norm]
    have hu_sub_p : u - p = v := by
      dsimp [u]
      abel
    have hu_sub_x : u - x = v - (x - p) := by
      dsimp [u]
      abel
    rw [hu_dist, hu_sub_p, hu_sub_x]
  have hu_mem :
      u ∈ prox[fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    let r : E := y - P y
    have hv_le_r :
        (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2
          ≤
          (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 :=
      hv_min r
    have hr_le_obj :
        (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2
          ≤
          (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
      have hdefect_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖((P y : E) - p)‖ ^ 2 := by positivity
      have hlower :
          (lam * ‖r‖ : ℝ)
              + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2
              + (1 / 2 : ℝ) * ‖((P y : E) - p)‖ ^ 2
            ≤
            (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
        simpa [p, r] using
          infDist_prox_objective_lower_bound_by_projection_residual
            C hC_nonempty hC_complete hC_convex lam x y
      linarith
    have hu_le_real :
        (lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2
          ≤
          (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
      calc
        (lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2
            = (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 := hu_obj_eq
        _ ≤ (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 := hv_le_r
        _ ≤ (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := hr_le_obj
    have hu_le_ereal :
        (((lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2 : ℝ) : EReal)
          ≤
          (((lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 : ℝ) : EReal) := by
      exact_mod_cast hu_le_real
    simpa [proximal_objective_apply] using hu_le_ereal
  have hu_min :
      ∀ y : E,
        proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x u ≤
          proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x y := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu_mem
    exact hu_mem
  have hprox_singleton :
      prox[fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)] x = {u} := by
    ext y
    constructor
    · intro hy
      let q : E := P y
      let r : E := y - P y
      have hy_min :
          ∀ z : E,
            proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x y ≤
              proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x z := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
        exact hy
      have hy_eq_u :
          proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x y =
            proximal_objective (fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)) x u :=
        le_antisymm (hy_min u) (hu_min y)
      have hy_eq_u_real :
          (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2
            =
            (lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2 := by
        have hy_eq_u_ereal :
            (((lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 : ℝ) : EReal)
              =
              (((lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2 : ℝ) : EReal) := by
          simpa [proximal_objective_apply] using hy_eq_u
        exact_mod_cast hy_eq_u_ereal
      have hlower :
          (lam * ‖r‖ : ℝ)
              + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2
              + (1 / 2 : ℝ) * ‖q - p‖ ^ 2
            ≤
            (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
        simpa [p, q, r] using
          infDist_prox_objective_lower_bound_by_projection_residual
            C hC_nonempty hC_complete hC_convex lam x y
      have hdefect_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖q - p‖ ^ 2 := by positivity
      have hupper :
          (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 + (1 / 2 : ℝ) * ‖q - p‖ ^ 2
            ≤
            (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 := by
        calc
          (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 + (1 / 2 : ℝ) * ‖q - p‖ ^ 2
              ≤
              (lam * infDist y C : ℝ) + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := hlower
          _ = (lam * infDist u C : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2 := hy_eq_u_real
          _ = (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 := hu_obj_eq
      have hv_le_r :
          (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2
            ≤
            (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 :=
        hv_min r
      have hr_eq_v_value :
          (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2
            =
            (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2 := by
        linarith
      have hdefect_zero : (1 / 2 : ℝ) * ‖q - p‖ ^ 2 = 0 := by
        linarith
      have hq_eq_p : q = p := by
        have hnorm_zero : ‖q - p‖ = 0 := by
          nlinarith [sq_nonneg ‖q - p‖, hdefect_zero]
        exact sub_eq_zero.mp <| norm_eq_zero.mp hnorm_zero
      have hr_mem :
          r ∈ prox[norm_penalty lam] (x - p) := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro z
        have hz : (lam * ‖v‖ : ℝ) + (1 / 2 : ℝ) * ‖v - (x - p)‖ ^ 2
            ≤ (lam * ‖z‖ : ℝ) + (1 / 2 : ℝ) * ‖z - (x - p)‖ ^ 2 :=
          hv_min z
        have hr_real :
            (lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2
              ≤
              (lam * ‖z‖ : ℝ) + (1 / 2 : ℝ) * ‖z - (x - p)‖ ^ 2 := by
          linarith [hr_eq_v_value, hz]
        have hr_ereal :
            (((lam * ‖r‖ : ℝ) + (1 / 2 : ℝ) * ‖r - (x - p)‖ ^ 2 : ℝ) : EReal)
              ≤
              (((lam * ‖z‖ : ℝ) + (1 / 2 : ℝ) * ‖z - (x - p)‖ ^ 2 : ℝ) : EReal) := by
          exact_mod_cast hr_real
        simpa [proximal_objective_apply, norm_penalty_apply] using hr_ereal
      have hr_eq_v : r = v := by
        rw [hv_prox] at hr_mem
        simpa using hr_mem
      rw [Set.mem_singleton_iff]
      calc
        y = q + r := by
          dsimp [q, r]
          abel
        _ = p + v := by rw [hq_eq_p, hr_eq_v]
        _ = u := by rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hu_mem
  have hu_piecewise :
      u =
        if lam < infDist x C then
          lineMap x (P x) (lam / infDist x C)
        else
          P x := by
    simpa [p, u, v] using
      distance_prox_candidate_eq_piecewise_target C hC_nonempty hC_complete hC_convex lam x
  calc
    prox[fun y : E ↦ ((lam * infDist y C : ℝ) : EReal)] x = {u} := hprox_singleton
    _ = {if lam < infDist x C then lineMap x (P x) (lam / infDist x C) else P x} := by
      rw [hu_piecewise]

end
