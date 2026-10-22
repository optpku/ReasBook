/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_6
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_13
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_13
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_17
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Corollary_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} {m : ℕ}

-- Proof sketch: choose a point in the total intersection and project its membership proof to the
-- chosen coordinate `i`.
/-- A nonempty total intersection of a finite family gives a nonempty witness in each member of
the family. -/
theorem family_nonempty_of_iInter_nonempty {S : Fin m → Set E}
    (hinter : (⋂ i, S i).Nonempty) :
    ∀ i, (S i).Nonempty := by
  -- The canonical Chapter 8 helper already projects an intersection witness to each coordinate.
  exact set_nonempty_of_nonempty_iInter hinter

end

section

open Metric
open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} [Nonempty (Fin m)]
variable {S : Fin m → Set E}
variable (hS_closed : ∀ i, IsClosed (S i)) (hS_convex : ∀ i, Convex ℝ (S i))
variable (hinter : (⋂ i, S i).Nonempty)
variable (i : ℕ → E → Fin m) (x0 : E)

local notation "hS_nonempty" => family_nonempty_of_iInter_nonempty hinter
local notation "x" =>
  greedy_projection_method S hS_nonempty hS_closed hS_convex i x0

/-- Helper for Theorem 8.21: the max-distance objective is globally `1`-Lipschitz. -/
theorem lipschitzWith_convex_feasibility_max_distance :
    LipschitzWith 1 (convex_feasibility_max_distance S) := by
  -- The finite maximum inherits the one-sided triangle inequality from each branch distance.
  refine LipschitzWith.of_le_add (f := convex_feasibility_max_distance S) ?_
  intro u v
  rw [convex_feasibility_max_distance_apply, convex_feasibility_max_distance_apply]
  refine Finset.sup'_le
    (s := (Finset.univ : Finset (Fin m)))
    (H := Finset.univ_nonempty)
    (f := fun j ↦ infDist u (S j)) ?_
  intro j hj
  exact le_trans
    (show infDist u (S j) ≤ infDist v (S j) + dist u v from Metric.infDist_le_infDist_add_dist)
    (add_le_add_left
      (Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
        (f := fun l ↦ infDist v (S l)) (Finset.mem_univ j))
      _)

/-- Helper for Theorem 8.21: the greedy step direction is the normalized residual to the selected
set, with the zero branch at points already lying in that set. -/
def selected_projection_direction (z : E) (j : Fin m) : E :=
  if h0 : infDist z (S j) = 0 then
    0
  else
    (infDist z (S j))⁻¹ •
      (z -
        metricProjection (S j) (hS_nonempty j) (hS_closed j) (hS_convex j) z)

/-- Helper for Theorem 8.21: the selected projection direction is a strong-dual subgradient of the
single active distance branch. -/
theorem selected_projection_direction_mem_strongDualSubdifferential_infDist
    (z : E) (j : Fin m) :
    toDualMap ℝ E (selected_projection_direction (S := S) hS_closed hS_convex hinter z j) ∈
      strongDualSubdifferential (fun y : E ↦ (infDist y (S j) : EReal)) z := by
  -- A real-valued branch subgradient is exactly the affine lower-support inequality for `infDist`.
  rw [mem_strongDualSubdifferential, mem_subdifferential, is_subgradient_at_coe_iff]
  by_cases hzero : infDist z (S j) = 0
  · -- At distance zero, the selected direction vanishes and only nonnegativity remains.
    intro y
    simpa [selected_projection_direction, hzero] using
      (Metric.infDist_nonneg : 0 ≤ infDist y (S j))
  · let p : E :=
      metricProjection (S j) (hS_nonempty j) (hS_closed j) (hS_convex j) z
    let r : E := z - p
    have hd_nonneg : 0 ≤ infDist z (S j) :=
      (Metric.infDist_nonneg : 0 ≤ infDist z (S j))
    have hd_pos : 0 < infDist z (S j) := by
      exact lt_of_le_of_ne hd_nonneg (by simpa [eq_comm] using hzero)
    have hdist : infDist z (S j) = ‖r‖ := by
      simpa [p, r, dist_eq_norm] using
        infDist_eq_dist_metricProjection
          (S j) (hS_nonempty j) (hS_closed j) (hS_convex j) z
    intro y
    refine (Metric.le_infDist (hS_nonempty j)).2 ?_
    intro q hq
    have hproj :
        inner ℝ r (q - p) ≤ 0 := by
      simpa [p, r] using
        inner_sub_metricProjection_le_zero
          (S j) (hS_nonempty j) (hS_closed j) (hS_convex j) z q hq
    have hsplit : y - z = (y - q) + (q - p) - r := by
      simp [p, r]
    have hinner :
        inner ℝ r (y - z) ≤ ‖r‖ * ‖y - q‖ - ‖r‖ ^ (2 : ℕ) := by
      -- Split the displacement through the projection point and use the projection inequality.
      calc
        inner ℝ r (y - z)
            = inner ℝ r ((y - q) + (q - p) - r) := by
                rw [hsplit]
        _ = inner ℝ r (y - q) + inner ℝ r (q - p) - inner ℝ r r := by
              simp [sub_eq_add_neg, inner_add_right, add_assoc]
        _ ≤ inner ℝ r (y - q) - inner ℝ r r := by
              nlinarith
        _ ≤ ‖r‖ * ‖y - q‖ - ‖r‖ ^ (2 : ℕ) := by
              nlinarith [real_inner_le_norm r (y - q), real_inner_self_eq_norm_sq r]
    have hinv_nonneg : 0 ≤ (infDist z (S j))⁻¹ :=
      inv_nonneg.mpr hd_nonneg
    have hscaled :
        (infDist z (S j))⁻¹ * inner ℝ r (y - z) ≤
          (infDist z (S j))⁻¹ * (‖r‖ * ‖y - q‖ - ‖r‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hinner hinv_nonneg
    have hsel :
        selected_projection_direction (S := S) hS_closed hS_convex hinter z j =
          ((infDist z (S j))⁻¹ : ℝ) • r := by
      simp [selected_projection_direction, hzero, p, r]
    calc
      infDist z (S j) +
          ((toDualMap ℝ E (selected_projection_direction (S := S) hS_closed hS_convex hinter z j))
            (y - z) : ℝ)
          = infDist z (S j) +
              inner ℝ (((infDist z (S j))⁻¹ : ℝ) • r) (y - z) := by
                rw [hsel]
                rfl
      _ = infDist z (S j) + (infDist z (S j))⁻¹ * inner ℝ r (y - z) := by
            rw [real_inner_smul_left]
      _ ≤ infDist z (S j) +
            (infDist z (S j))⁻¹ * (‖r‖ * ‖y - q‖ - ‖r‖ ^ (2 : ℕ)) := by
              linarith
      _ = ‖y - q‖ := by
            have hr_ne : ‖r‖ ≠ 0 := by
              simpa [hdist] using hzero
            rw [hdist, pow_two]
            calc
              ‖r‖ + ‖r‖⁻¹ * (‖r‖ * ‖y - q‖ - ‖r‖ * ‖r‖)
                  = ‖r‖ + (‖r‖⁻¹ * ‖r‖) * ‖y - q‖ - (‖r‖⁻¹ * ‖r‖) * ‖r‖ := by
                      ring
              _ = ‖y - q‖ := by
                    have hmul :
                        ‖r‖⁻¹ * (‖r‖ * ‖y - q‖) = ‖y - q‖ := by
                      rw [← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
                    have hmul_r :
                        ‖r‖⁻¹ * ‖r‖ * ‖r‖ = ‖r‖ := by
                      rw [inv_mul_cancel₀ hr_ne, one_mul]
                    nlinarith
      _ = dist y q := by
            rw [dist_eq_norm]

/-- Helper for Theorem 8.21: when `j` is a farthest set from `x`, the selected projection
direction is a strong-dual subgradient of the max-distance objective. -/
theorem selected_farthest_direction_mem_strongDualSubdifferential_max_distance
    (z : E) (j : Fin m) (hj : ∀ l : Fin m, infDist z (S l) ≤ infDist z (S j)) :
    toDualMap ℝ E
      (selected_projection_direction (S := S) hS_closed hS_convex hinter z j) ∈
      strongDualSubdifferential
        (fun y : E ↦ (convex_feasibility_max_distance S y : EReal)) z := by
  -- Lift the active branch directly through the finite-max formula for the objective.
  rw [mem_strongDualSubdifferential, mem_subdifferential, is_subgradient_at_coe_iff]
  have hbranch :
      ∀ y : E,
        infDist y (S j) ≥
          infDist z (S j) +
            (((toDualMap ℝ E
              (selected_projection_direction (S := S) hS_closed hS_convex hinter z j) :
                StrongDual ℝ E) : Module.Dual ℝ E) (y - z) : ℝ) := by
    simpa [mem_strongDualSubdifferential, mem_subdifferential, is_subgradient_at_coe_iff] using
      selected_projection_direction_mem_strongDualSubdifferential_infDist
        (S := S) (hS_closed := hS_closed) (hS_convex := hS_convex) (hinter := hinter) z j
  have hzmax : convex_feasibility_max_distance S z = infDist z (S j) := by
    rw [convex_feasibility_max_distance_apply]
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le
        (s := (Finset.univ : Finset (Fin m)))
        (H := Finset.univ_nonempty)
        (f := fun l ↦ infDist z (S l)) ?_
      intro l hl
      exact hj l
    · exact Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
        (f := fun l ↦ infDist z (S l)) (Finset.mem_univ j)
  intro y
  have hymax : infDist y (S j) ≤ convex_feasibility_max_distance S y := by
    rw [convex_feasibility_max_distance_apply]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
      (f := fun l ↦ infDist y (S l)) (Finset.mem_univ j)
  calc
    convex_feasibility_max_distance S y
        ≥ infDist y (S j) := hymax
    _ ≥ infDist z (S j) +
          (((toDualMap ℝ E
            (selected_projection_direction (S := S) hS_closed hS_convex hinter z j) :
              StrongDual ℝ E) : Module.Dual ℝ E) (y - z) : ℝ) := hbranch y
    _ = convex_feasibility_max_distance S z +
          (((toDualMap ℝ E
            (selected_projection_direction (S := S) hS_closed hS_convex hinter z j) :
              StrongDual ℝ E) : Module.Dual ℝ E) (y - z) : ℝ) := by
          rw [hzmax]

/-- Helper for Theorem 8.21: every strong-dual subgradient of the max-distance objective has norm
at most `1`. -/
theorem norm_one_of_mem_strongDualSubdifferential_max_distance
    {z : E} {g : StrongDual ℝ E}
    (hg : g ∈
      strongDualSubdifferential
        (fun y : E ↦ (convex_feasibility_max_distance S y : EReal)) z) :
    ‖g‖ ≤ 1 := by
  -- The branch-wise subgradient inequality and the global Lipschitz estimate give pointwise dual
  -- bounds, which are exactly the operator-norm bound.
  rw [mem_strongDualSubdifferential, mem_subdifferential, is_subgradient_at_coe_iff] at hg
  have hpointwise : ∀ v : E, |g v| ≤ ‖v‖ := by
    intro v
    have hplus_sub : g v ≤
        convex_feasibility_max_distance S (z + v) - convex_feasibility_max_distance S z := by
      have hsub :
          convex_feasibility_max_distance S z + g v ≤
            convex_feasibility_max_distance S (z + v) := by
        simpa using hg (z + v)
      linarith
    have hplus_lip :
        convex_feasibility_max_distance S (z + v) -
            convex_feasibility_max_distance S z ≤ ‖v‖ := by
      have hdist :=
        (lipschitzWith_convex_feasibility_max_distance (S := S)).dist_le_mul (z + v) z
      have habs :
          |convex_feasibility_max_distance S (z + v) -
              convex_feasibility_max_distance S z| ≤ ‖v‖ := by
        simpa [dist_eq_norm] using hdist
      exact (abs_le.mp habs).2
    have hminus_sub : -g v ≤
        convex_feasibility_max_distance S (z - v) - convex_feasibility_max_distance S z := by
      have hsub :
          convex_feasibility_max_distance S z + g (-v) ≤
            convex_feasibility_max_distance S (z - v) := by
        simpa [sub_eq_add_neg] using hg (z - v)
      have hsub' : g (-v) ≤
          convex_feasibility_max_distance S (z - v) - convex_feasibility_max_distance S z := by
        linarith
      simpa using hsub'
    have hminus_lip :
        convex_feasibility_max_distance S (z - v) -
            convex_feasibility_max_distance S z ≤ ‖v‖ := by
      have hdist :=
        (lipschitzWith_convex_feasibility_max_distance (S := S)).dist_le_mul (z - v) z
      have habs :
          |convex_feasibility_max_distance S (z - v) -
              convex_feasibility_max_distance S z| ≤ ‖v‖ := by
        simpa [dist_eq_norm, sub_eq_add_neg] using hdist
      exact (abs_le.mp habs).2
    exact abs_le.2 ⟨by linarith [hminus_sub.trans hminus_lip], hplus_sub.trans hplus_lip⟩
  refine ContinuousLinearMap.opNorm_le_bound g zero_le_one ?_
  intro v
  simpa [Real.norm_eq_abs] using hpointwise v

/-- Helper for Theorem 8.21: the norm bound package on `Set.univ` uses the universal estimate
`‖g‖ ≤ 1` for every strong-dual subgradient. -/
theorem convex_feasibility_max_distance_subgradient_norm_bound_on_univ_norm_le
    {z : E} {g : StrongDual ℝ E}
    (_hz : z ∈ Set.univ)
    (hg : g ∈
      strongDualSubdifferential
        (fun y : E ↦ (convex_feasibility_max_distance S y : EReal)) z) :
    ‖g‖ ≤ 1 := by
  -- On `Set.univ` there is no feasibility restriction, so the closing norm-one lemma applies
  -- verbatim.
  exact norm_one_of_mem_strongDualSubdifferential_max_distance (S := S) hg

/-- Helper for Theorem 8.21: the max-distance convex-feasibility objective with feasible set
`Set.univ` has optimal set `⋂ j, S j` and optimal value `0`. -/
theorem convex_feasibility_max_distance_problem_on_univ :
    (∀ i, IsClosed (S i)) →
    (∀ i, Convex ℝ (S i)) →
    (⋂ j, S j).Nonempty →
    IsConstrainedConvexProblem
      (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
      Set.univ (⋂ j, S j) 0 := by
  intro hclosed hconvex hinter'
  -- Package the source max-distance problem directly in the chapter projected-subgradient format.
  refine
    { ne_bot := fun y ↦ by simp
      effective_domain_nonempty := by
        simpa [effective_domain] using (Set.univ_nonempty : (Set.univ : Set E).Nonempty)
      closed := ?_
      convex := ?_
      feasible_nonempty := Set.univ_nonempty
      feasible_closed := isClosed_univ
      feasible_convex := convex_univ
      feasible_subset_interior_effective_domain := ?_
      optimal_set_eq := ?_
      optimal_set_nonempty := hinter'
      optimal_value_isGLB := ?_ }
  · -- The objective is 1-Lipschitz, hence continuous and lower semicontinuous.
    have hcont : Continuous (convex_feasibility_max_distance S) := by
      exact (lipschitzWith_convex_feasibility_max_distance (S := S)).continuous
    exact continuous_real_isClosed hcont
  · -- Convexity comes from finite sup of the convex distance branches.
    have hconvOn : ConvexOn ℝ Set.univ (convex_feasibility_max_distance S) := by
      let F : Fin m → E → ℝ := fun j y ↦ infDist y (S j)
      have hsup :
          ConvexOn ℝ Set.univ
            ((Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty F) := by
        refine Finset.sup'_induction
          (s := (Finset.univ : Finset (Fin m)))
          (H := Finset.univ_nonempty)
          (f := F)
          (p := fun f : E → ℝ => ConvexOn ℝ Set.univ f)
          (fun f hf g hg ↦ ConvexOn.sup hf hg) ?_
        intro j hj
        let P : E → E := fun y ↦
          metricProjection (S j) (family_nonempty_of_iInter_nonempty hinter' j)
            (hclosed j) (hconvex j) y
        rw [ConvexOn]
        refine ⟨convex_univ, ?_⟩
        intro u hu v hv a b ha hb hab
        have hp :
            a • P u + b • P v ∈ S j :=
          (hconvex j)
            (show P u ∈ S j by
              exact (metricProjection (S j) (family_nonempty_of_iInter_nonempty hinter' j)
                (hclosed j) (hconvex j) u).property)
            (show P v ∈ S j by
              exact (metricProjection (S j) (family_nonempty_of_iInter_nonempty hinter' j)
                (hclosed j) (hconvex j) v).property)
            ha hb hab
        have hdist_x :
            infDist u (S j) = dist u (P u) := by
          simpa [P] using
            infDist_eq_dist_metricProjection
              (S j) (family_nonempty_of_iInter_nonempty hinter' j)
              (hclosed j) (hconvex j) u
        have hdist_y :
            infDist v (S j) = dist v (P v) := by
          simpa [P] using
            infDist_eq_dist_metricProjection
              (S j) (family_nonempty_of_iInter_nonempty hinter' j)
              (hclosed j) (hconvex j) v
        calc
          infDist (a • u + b • v) (S j)
              ≤ dist (a • u + b • v) (a • P u + b • P v) :=
                Metric.infDist_le_dist_of_mem hp
          _ = ‖a • (u - P u) + b • (v - P v)‖ := by
                rw [dist_eq_norm]
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul]
          _ ≤ ‖a • (u - P u)‖ + ‖b • (v - P v)‖ :=
                norm_add_le _ _
          _ = a * ‖u - P u‖ + b * ‖v - P v‖ := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
          _ = a * infDist u (S j) + b * infDist v (S j) := by
                rw [hdist_x, hdist_y, dist_eq_norm, dist_eq_norm]
      have hEq :
          ((Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty F) =
            convex_feasibility_max_distance S := by
        funext y
        simp [F, convex_feasibility_max_distance_apply, Finset.sup'_apply]
      simpa [hEq] using hsup
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp
    · simpa [effective_domain] using hconvOn
  · -- The real-valued objective is finite everywhere, so the effective domain is all of `E`.
    intro y hy
    simp [effective_domain]
  · -- Minimizers of the max-distance problem are exactly the points in the intersection.
    ext y
    constructor
    · intro hy
      refine ⟨Set.mem_univ y, ?_⟩
      have hyreal :
          IsMinOn (convex_feasibility_max_distance S) Set.univ y :=
        (isMinOn_convex_feasibility_max_distance_iff_mem_iInter
          (S := S) hclosed hinter').2 hy
      rw [isMinOn_univ_iff] at hyreal ⊢
      intro z
      exact EReal.coe_le_coe (hyreal z)
    · rintro ⟨hyu, hymin⟩
      have hyreal : IsMinOn (convex_feasibility_max_distance S) Set.univ y := by
        rw [isMinOn_univ_iff] at hymin ⊢
        intro z
        exact EReal.coe_le_coe_iff.mp (hymin z)
      exact
        (isMinOn_convex_feasibility_max_distance_iff_mem_iInter
          (S := S) hclosed hinter').1 hyreal
  · -- `0` is a lower bound by nonnegativity, and an intersection point realizes the value `0`.
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with ⟨y, -, rfl⟩
      show (0 : EReal) ≤ (convex_feasibility_max_distance S y : EReal)
      exact_mod_cast convex_feasibility_max_distance_nonneg S y
    · intro b hb
      rcases hinter' with ⟨y, hy⟩
      have hy_image :
          ((0 : ℝ) : EReal) ∈
            (fun z : E ↦ (convex_feasibility_max_distance S z : EReal)) '' Set.univ := by
        refine ⟨y, Set.mem_univ y, ?_⟩
        exact congrArg (fun r : ℝ ↦ (r : EReal))
          (convex_feasibility_max_distance_eq_zero_of_mem_iInter S hy)
      exact hb hy_image

/-- Helper for Theorem 8.21: the max-distance objective admits the Chapter 8 norm-bound package on
`Set.univ` with constant `L_f = 1`. -/
def convex_feasibility_max_distance_subgradient_norm_bound_on_univ :
    SubgradientNormBoundOn
      (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
      Set.univ :=
  { L_f := 1
    L_f_pos := zero_lt_one
    norm_le := convex_feasibility_max_distance_subgradient_norm_bound_on_univ_norm_le (S := S) }

/-- Helper for Theorem 8.21: the packaged subgradient bound for the max-distance objective stores
the source constant `L_f = 1`. -/
theorem convex_feasibility_max_distance_subgradient_norm_bound_on_univ_L_f :
    (convex_feasibility_max_distance_subgradient_norm_bound_on_univ (S := S)).L_f = 1 := by
  -- The structure field was defined with `L_f := 1`.
  rfl

/-- Helper for Theorem 8.21: the greedy projection trajectory can be viewed as a projected
subgradient trajectory on `Set.univ` using a selected strong-dual subgradient of the max-distance
objective and Polyak's stepsize rule. -/
theorem greedy_projection_polyak_bridge
    (hgreedy : greedy_projection_method_is_admissible S hS_nonempty hS_closed hS_convex i x0) :
    ∃ g : ℕ → Set.univ → E, ∃ t : ℕ → ℝ,
      (∀ k,
        toDualMap ℝ E (g k ⟨x k, Set.mem_univ _⟩) ∈
          strongDualSubdifferential
            (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
            (x k)) ∧
      (∀ k,
        t k =
          polyak_stepsize
            (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
            0 (x k) (g k ⟨x k, Set.mem_univ _⟩)) ∧
      projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ g t
        ⟨x0, Set.mem_univ x0⟩ =
        fun k ↦ ⟨x k, Set.mem_univ _⟩ := by
  let g : ℕ → ↥(Set.univ : Set E) → E := fun k (_ : ↥(Set.univ : Set E)) ↦
    selected_projection_direction (S := S) hS_closed hS_convex hinter (x k) (i k (x k))
  let t : ℕ → ℝ := fun k ↦
    polyak_stepsize
      (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
      0 (x k) (g k ⟨x k, Set.mem_univ _⟩)
  have huniv_proj :
      ∀ y : E,
        (metricProjection Set.univ Set.univ_nonempty isClosed_univ convex_univ y : E) = y := by
    intro y
    simpa [projectionPoint] using
      projectionPoint_eq_self_of_mem Set.univ Set.univ_nonempty isClosed_univ convex_univ
        (by simp)
  refine ⟨g, t, ?_, ?_, ?_⟩
  · intro k
    -- The admissible greedy index is farthest, so its selected direction is a max-objective
    -- subgradient at the current iterate.
    simpa [g] using
      selected_farthest_direction_mem_strongDualSubdifferential_max_distance
        (S := S) (hS_closed := hS_closed) (hS_convex := hS_convex) (hinter := hinter)
        (z := x k) (j := i k (x k))
        (fun l ↦ greedy_projection_method_selected_set_farthest hgreedy k l)
  · intro k
    -- The stepsize sequence was defined to be Polyak's rule at the greedy iterate.
    rfl
  · -- Compare the two recursions step-by-step.
    funext n
    induction n with
    | zero =>
        simp [projected_subgradient_method_zero, greedy_projection_method_zero]
    | succ k hk =>
        apply Subtype.ext
        have hk_val :
            ((projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
              g t ⟨x0, Set.mem_univ x0⟩ k : Set.univ) : E) = x k := by
          simpa using congrArg Subtype.val hk
        rw [projected_subgradient_method_succ, greedy_projection_method_succ, hk_val, huniv_proj]
        let jk : Fin m := i k (x k)
        let p : E :=
          metricProjection (S jk) (hS_nonempty jk) (hS_closed jk) (hS_convex jk) (x k)
        by_cases hzero : infDist (x k) (S jk) = 0
        · -- If the active distance is zero, both updates fix the current iterate.
          have hxk_mem : x k ∈ S jk := by
            exact ((hS_closed jk).mem_iff_infDist_zero (hS_nonempty jk)).2 hzero
          have hp_eq : p = x k := by
            simpa [p] using
              projectionPoint_eq_self_of_mem (S jk) (hS_nonempty jk) (hS_closed jk)
                (hS_convex jk) hxk_mem
          simp [g, t, selected_projection_direction, hzero, polyak_stepsize_zero, jk, p, hp_eq]
        · -- When the active distance is positive, the Polyak step exactly cancels the normalized
          -- residual and lands on the selected metric projection.
          have hd_nonneg : 0 ≤ infDist (x k) (S jk) :=
            (Metric.infDist_nonneg : 0 ≤ infDist (x k) (S jk))
          have hd_pos : 0 < infDist (x k) (S jk) := by
            exact lt_of_le_of_ne hd_nonneg (by simpa [eq_comm] using hzero)
          have hdist : infDist (x k) (S jk) = ‖x k - p‖ := by
            simpa [p, dist_eq_norm] using
              infDist_eq_dist_metricProjection
                (S jk) (hS_nonempty jk) (hS_closed jk) (hS_convex jk) (x k)
          have hg_norm : ‖g k ⟨x k, Set.mem_univ _⟩‖ = 1 := by
            calc
              ‖g k ⟨x k, Set.mem_univ _⟩‖
                  = ‖(infDist (x k) (S jk))⁻¹ • (x k - p)‖ := by
                      simp [g, jk, p, selected_projection_direction, hzero]
              _ = |(infDist (x k) (S jk))⁻¹| * ‖x k - p‖ := by
                    rw [norm_smul, Real.norm_eq_abs]
              _ = (infDist (x k) (S jk))⁻¹ * infDist (x k) (S jk) := by
                    rw [abs_of_nonneg (inv_nonneg.mpr hd_nonneg), hdist]
              _ = 1 := by
                    simpa using inv_mul_cancel₀ hzero
          have hg_ne : g k ⟨x k, Set.mem_univ _⟩ ≠ 0 := by
            intro hg0
            have : ‖g k ⟨x k, Set.mem_univ _⟩‖ = 0 := by
              simpa [hg0]
            rw [hg_norm] at this
            norm_num at this
          have hactive :
              convex_feasibility_max_distance S (x k) = infDist (x k) (S jk) := by
            rw [convex_feasibility_max_distance_apply]
            refine le_antisymm ?_ ?_
            · refine Finset.sup'_le
                (s := (Finset.univ : Finset (Fin m)))
                (H := Finset.univ_nonempty)
                (f := fun l ↦ infDist (x k) (S l)) ?_
              intro l hl
              exact greedy_projection_method_selected_set_farthest hgreedy k l
            · simpa [jk] using
                (Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
                  (f := fun l ↦ infDist (x k) (S l)) (Finset.mem_univ jk))
          have ht_eq' : t k = convex_feasibility_max_distance S (x k) := by
            simp [t, polyak_stepsize_of_ne_zero _ _ _ _ hg_ne, hg_norm]
          have ht_eq : t k = infDist (x k) (S jk) := by
            exact ht_eq'.trans hactive
          rw [ht_eq]
          simp [g, jk, p, selected_projection_direction, hzero, smul_smul, hzero]


/- Theorem 8.21 is `source-facing`: it states the complexity bound and convergence conclusion for
the concrete greedy projection iterates. The owner abstractions already present in the chapter are
the recursive sequence `greedy_projection_method`, the admissibility predicate
`greedy_projection_method_is_admissible`, and the max-distance objective
`convex_feasibility_max_distance`. The theorem is therefore stated directly on those owners, with
the family-wise nonemptiness derived from the nonempty intersection instead of being exposed as a
separate public hypothesis. -/

-- Proof sketch: identify the greedy projection method with the projected subgradient method for
-- `convex_feasibility_max_distance S` on the feasible set `univ`, use the admissibility
-- hypothesis to match the greedy index rule with a subgradient choice satisfying Polyak's rule,
-- and then specialize Theorem 8.13(c) together with the identification of the optimal set
-- `X^* = ⋂ i, S i`.
/-- Theorem 8.21 (1): source part (a). For the greedy projection algorithm, the best value of the
max-distance objective attained among the first `k + 1` iterates is at most
`d_{⋂ i, S_i}(x^0) / √(k + 1)`. -/
theorem greedy_projection_method_best_max_distance_le
    (hgreedy : greedy_projection_method_is_admissible S hS_nonempty hS_closed hS_convex i x0)
    (k : ℕ) :
    best_achieved_function_value (convex_feasibility_max_distance S) x k ≤
      infDist x0 (⋂ j, S j) / Real.sqrt (k + 1) := by
  -- Route correction: the main theorem is now reduced to the chapter-level Polyak rate theorem,
  -- with the remaining work isolated in the explicit bridge helper above.
  obtain ⟨g, t, hsubgrad, hpolyak, htraj⟩ :=
    greedy_projection_polyak_bridge
      (S := S) (hS_closed := hS_closed) (hS_convex := hS_convex)
      (hinter := hinter) (i := i) (x0 := x0) hgreedy
  have hsubgrad' :
      ∀ n,
        (toDualMap ℝ E
            (g n
              (projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
                g t ⟨x0, Set.mem_univ x0⟩ n)) :
          Module.Dual ℝ E) ∈
            subdifferential
              (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
              ((projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
                g t ⟨x0, Set.mem_univ x0⟩ n : Set.univ) : E) := by
    intro n
    simpa [htraj, mem_strongDualSubdifferential] using hsubgrad n
  have hpolyak' :
      ∀ n,
        t n =
          polyak_stepsize
            (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
            0
            ((projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
              g t ⟨x0, Set.mem_univ x0⟩ n : Set.univ) : E)
            (g n
              (projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
                g t ⟨x0, Set.mem_univ x0⟩ n)) := by
    intro n
    simpa [htraj] using hpolyak n
  have hrate :=
    projected_subgradient_method_best_value_gap_le_of_polyak_stepsize
      (f := fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
      (C := Set.univ) (XStar := ⋂ j, S j) (fOpt := 0)
      (h_problem := convex_feasibility_max_distance_problem_on_univ
        (S := S) hS_closed hS_convex hinter)
      (g := g) (t := t) (x0 := ⟨x0, Set.mem_univ x0⟩)
      (h_norm := convex_feasibility_max_distance_subgradient_norm_bound_on_univ
        (S := S))
      hsubgrad' hpolyak' k
  simpa [htraj, convex_feasibility_max_distance_apply,
    convex_feasibility_max_distance_subgradient_norm_bound_on_univ_L_f (S := S)] using hrate

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ} [Nonempty (Fin m)]
variable {S : Fin m → Set E}
variable (hS_closed : ∀ i, IsClosed (S i)) (hS_convex : ∀ i, Convex ℝ (S i))
variable (hinter : (⋂ i, S i).Nonempty)
variable (i : ℕ → E → Fin m) (x0 : E)

local notation "hS_nonempty" => family_nonempty_of_iInter_nonempty hinter
local notation "x" =>
  greedy_projection_method S hS_nonempty hS_closed hS_convex i x0

-- Proof sketch: use the same reduction to the projected subgradient method for the
-- max-distance objective, then apply Theorem 8.17 to obtain convergence of the whole trajectory to
-- an optimal point. Finally rewrite the optimal set of the max-distance problem as the
-- intersection `⋂ i, S i`.
/-- Theorem 8.21 (2): source part (b). The greedy projection sequence converges to a point in the
intersection `⋂ i, S i`. -/
theorem greedy_projection_method_tendsto_point_in_intersection
    (hgreedy : greedy_projection_method_is_admissible S hS_nonempty hS_closed hS_convex i x0) :
    ∃ xStar : E,
      xStar ∈ ⋂ j, S j ∧
        Filter.Tendsto x Filter.atTop (nhds xStar) := by
  -- Route correction: with `Theorem_8_17` importable, the source proof closes by the same
  -- greedy-to-Polyak bridge used in part (a), followed by a direct specialization of
  -- the projected-subgradient convergence theorem.
  obtain ⟨g, t, hsubgrad, hpolyak, htraj⟩ :=
    greedy_projection_polyak_bridge
      (S := S) (hS_closed := hS_closed) (hS_convex := hS_convex)
      (hinter := hinter) (i := i) (x0 := x0) hgreedy
  have hsubgrad' :
      ∀ n,
        InnerProductSpace.toDualMap ℝ E
            (g n
              (projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
                g t ⟨x0, Set.mem_univ x0⟩ n)) ∈
          strongDualSubdifferential
            (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
            ((projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
              g t ⟨x0, Set.mem_univ x0⟩ n : Set.univ) : E) := by
    intro n
    simpa [htraj] using hsubgrad n
  have hpolyak' :
      ∀ n,
        t n =
          polyak_stepsize
            (fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
            0
            ((projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
              g t ⟨x0, Set.mem_univ x0⟩ n : Set.univ) : E)
            (g n
              (projected_subgradient_method Set.univ Set.univ_nonempty isClosed_univ convex_univ
                g t ⟨x0, Set.mem_univ x0⟩ n)) := by
    intro n
    simpa [htraj] using hpolyak n
  obtain ⟨xStar, hxStar, hxTendsto⟩ :=
    projected_subgradient_method_tendsto_point_in_optimal_set_of_polyak_stepsize
      (f := fun y : E ↦ (convex_feasibility_max_distance S y : EReal))
      (C := Set.univ) (XStar := ⋂ j, S j) (fOpt := 0)
      (h_problem := convex_feasibility_max_distance_problem_on_univ
        (S := S) hS_closed hS_convex hinter)
      (h_bound := convex_feasibility_max_distance_subgradient_norm_bound_on_univ (S := S))
      (g := g) (t := t) (x0 := ⟨x0, Set.mem_univ x0⟩) hsubgrad' hpolyak'
  refine ⟨xStar, hxStar, ?_⟩
  -- Rewriting through the trajectory identity turns projected-subgradient convergence back into
  -- convergence of the greedy projection iterates.
  simpa [htraj] using hxTendsto

end
