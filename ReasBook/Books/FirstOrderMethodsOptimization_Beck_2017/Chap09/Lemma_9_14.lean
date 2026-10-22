/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace (toDualMap)

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- Lemma 9.14 is `source-facing`: the main entry is the fixed-horizon running-best mirror-descent
gap bound for a concrete trajectory. The canonical owners already exist in Chapter 8 and Chapter 9:
`IsConstrainedConvexProblem`, `IsBregmanPotentialOn`, `SubgradientNormBoundOn`,
`is_mirror_descent_trajectory`, `B[ω]`, `best_achieved_function_value`, and the one-step estimate
`mirror_descent_fundamental_inequality`. The summed weighted-gap inequality below is a companion
API exposing the canonical intermediate form used to derive the ratio bound. -/

/-- Helper for Lemma 9.14: every positive-stepsize prefix sum `∑_{n=0}^N t n` is strictly
positive. -/
private lemma positiveStepsizePrefixSum_pos
    (h_stepsize_pos : ∀ n, 0 < t n) (N : ℕ) :
    0 < Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := by
  -- The initial positive stepsize already appears in every finite prefix.
  have hmem : 0 ∈ Finset.range (N + 1) := by
    simp
  have hle :
      t 0 ≤ Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := by
    simpa using
      (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_stepsize_pos n)) hmem)
  exact lt_of_lt_of_le (h_stepsize_pos 0) hle

omit [CompleteSpace E] in
/-- Helper for Lemma 9.14: a Euclidean subgradient of the real-valued lift `y ↦ (f y).toReal`
induces a strong-dual subgradient of the original extended-real-valued objective `f`. -/
private lemma toDualMap_mem_subdifferential_of_mem_euclideanSubdifferentialAt_toReal
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {y v : E} (hy : y ∈ effective_domain f)
    (hv : v ∈ euclideanSubdifferentialAt (fun z ↦ (f z).toReal) y) :
    (toDualMap ℝ E v : Module.Dual ℝ E) ∈ subdifferential f y := by
  -- Rewrite Euclidean membership into the owner subgradient inequality on `f.toReal`.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hv
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hy, ?_⟩
  intro z hz
  -- Finite values on the effective domain let the real inequality lift back to `EReal`.
  have hy_top : f y ≠ ⊤ := ne_of_lt hy
  have hz_top : f z ≠ ⊤ := ne_of_lt hz
  have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
  have hz_bot : f z ≠ ⊥ := h_problem.ne_bot z
  have hvz : (f z).toReal ≥ (f y).toReal + inner ℝ v (z - y) := hv z
  have hvzE :
      (((f y).toReal + inner ℝ v (z - y) : ℝ) : EReal) ≤
        (((f z).toReal : ℝ) : EReal) := by
    exact EReal.coe_le_coe (by simpa [ge_iff_le] using hvz)
  simpa [InnerProductSpace.toDualMap_apply_apply, EReal.coe_toReal hy_top hy_bot,
    EReal.coe_toReal hz_top hz_bot, EReal.coe_add, ge_iff_le] using hvzE

/-- Helper for Lemma 9.14: every selected mirror-descent subgradient has norm at most
`h_bound.L_f`. -/
private lemma mirrorDescentSelectedSubgradient_norm_le
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (n : ℕ) :
    ‖g n‖ ≤ h_bound.L_f := by
  -- Convert the Euclidean selected subgradient into the owner strong-dual subgradient surface.
  have hx_feasible : x n ∈ C := h_traj.mem_feasible_set n
  have hx_dom : x n ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hx_feasible)
  have hstrong :
      (toDualMap ℝ E (g n) : Module.Dual ℝ E) ∈ subdifferential f (x n) :=
    toDualMap_mem_subdifferential_of_mem_euclideanSubdifferentialAt_toReal
      (h_problem := h_problem) hx_dom (h_traj.subgradient_mem n)
  simpa [mem_strongDualSubdifferential] using h_bound.norm_le hx_feasible hstrong

/-- Helper for Lemma 9.14: the Bregman-difference prefix
`∑_{n=0}^N (B_ω(xStar, x^n) - B_ω(xStar, x^(n+1)))` telescopes to its endpoint difference. -/
private lemma mirrorDescentBregmanDifference_sum_range
    (xStar : E) (N : ℕ) :
    Finset.sum (Finset.range (N + 1))
      (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) =
        B[ω] xStar (x 0) - B[ω] xStar (x (N + 1)) := by
  -- The successive Bregman drops form an exact finite telescope.
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (Finset.sum (Finset.range (N + 1))
            (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1)))) +
            (B[ω] xStar (x (N + 1)) - B[ω] xStar (x (N + 2)))
            = (B[ω] xStar (x 0) - B[ω] xStar (x (N + 1))) +
                (B[ω] xStar (x (N + 1)) - B[ω] xStar (x (N + 2))) := by
                  rw [ih]
        _ = B[ω] xStar (x 0) - B[ω] xStar (x (N + 2)) := by
              ring

/-- Helper for Lemma 9.14: summing Lemma 9.13 over `0, …, N` yields the weighted mirror-descent
gap bound with the exact correction term involving the selected subgradients. -/
private lemma mirrorDescentWeightedObjectiveGapSumLeWithNormCorrection
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt)) ≤
      B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
  have hpointwise :
      ∀ n ∈ Finset.range (N + 1),
        t n * ((f (x n)).toReal - fOpt) ≤
          B[ω] xStar (x n) - B[ω] xStar (x (n + 1)) +
            ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ) := by
    intro n hn
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mirror_descent_fundamental_inequality
        (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
        (h_traj := h_traj) hxStar n
  have hsum_le := Finset.sum_le_sum hpointwise
  have hsplit :
      Finset.sum (Finset.range (N + 1))
        (fun n ↦
          (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
            ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) =
        Finset.sum (Finset.range (N + 1))
            (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) := by
    -- Separate the Bregman telescope from the norm-correction prefix.
    rw [Finset.sum_add_distrib]
  calc
    Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt))
      ≤ Finset.sum (Finset.range (N + 1))
          (fun n ↦
            (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
              ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) := hsum_le
    _ =
        Finset.sum (Finset.range (N + 1))
            (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) := hsplit
    _ = (B[ω] xStar (x 0) - B[ω] xStar (x (N + 1))) +
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) := by
          rw [mirrorDescentBregmanDifference_sum_range (ω := ω) (x := x) xStar N]
    _ ≤ B[ω] xStar (x 0) +
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) / (2 * σ)) := by
          have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
            simpa [h_problem.optimal_set_eq] using hxStar
          have htail_nonneg :
              0 ≤ B[ω] xStar (x (N + 1)) := by
            exact bregmanDistance_nonneg_of_mem_subdifferential_domain
              hω xStar (x (N + 1)) hxStar_data.1
              (h_traj.mem_feasible_set (N + 1))
              (mirrorDescent_memSubdifferentialDomain hω h_traj (N + 1))
              (hω_diff _ (mirrorDescent_memSubdifferentialDomain hω h_traj (N + 1)))
          linarith
    _ = B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (N + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
          simp [div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 9.14: the exact norm-correction term from the summed mirror-descent
inequality is dominated by the uniform `L_f` bound from `SubgradientNormBoundOn`. -/
private lemma mirrorDescentNormCorrection_le_uniformBound
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (N : ℕ) :
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (N + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
      (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
        Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
  have hsum_le :
      Finset.sum (Finset.range (N + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (N + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) := by
    -- Bound each squared norm by the uniform subgradient-norm cap.
    refine Finset.sum_le_sum ?_
    intro n hn
    have hnorm_le :=
      mirrorDescentSelectedSubgradient_norm_le
        (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
        (x := x) (g := g) (t := t) h_problem h_bound h_traj n
    have hsq_le : ‖g n‖ ^ (2 : ℕ) ≤ h_bound.L_f ^ (2 : ℕ) := by
      have hnorm_nonneg : 0 ≤ ‖g n‖ := norm_nonneg _
      have hLf_nonneg : 0 ≤ h_bound.L_f := le_of_lt h_bound.L_f_pos
      nlinarith
    exact mul_le_mul_of_nonneg_left hsq_le (sq_nonneg (t n))
  have hcoeff_nonneg : 0 ≤ 1 / (2 * σ) := by
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    exact le_of_lt (one_div_pos.mpr htwoσ_pos)
  have hsum_factor :
      Finset.sum (Finset.range (N + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) =
        Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) *
          h_bound.L_f ^ (2 : ℕ) := by
    exact
      (Finset.sum_mul (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
        (h_bound.L_f ^ (2 : ℕ))).symm
  calc
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (N + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))
      ≤ (1 / (2 * σ)) *
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hsum_le hcoeff_nonneg
    _ = (1 / (2 * σ)) *
          (Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) *
            h_bound.L_f ^ (2 : ℕ)) := by
          rw [hsum_factor]
    _ = (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
          ring

/-- Helper for Lemma 9.14: the running-best gap is bounded by the weighted sum of the prefix
objective gaps because `best_achieved_function_value` is the minimum over the prefix. -/
private lemma bestAchievedGap_mul_prefixSum_le
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (N : ℕ) :
    (Finset.sum (Finset.range (N + 1)) (fun n ↦ t n)) *
        (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt) ≤
      Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt)) := by
  have h_stepsize_nonneg : ∀ n, 0 ≤ t n := fun n ↦ le_of_lt (h_traj.stepsize_pos n)
  calc
    (Finset.sum (Finset.range (N + 1)) (fun n ↦ t n)) *
        (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt)
      = Finset.sum (Finset.range (N + 1))
          (fun n ↦ t n * (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt)) := by
            rw [Finset.sum_mul]
    _ ≤ Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hbest_le :
              best_achieved_function_value (fun y ↦ (f y).toReal) x N ≤ (f (x n)).toReal :=
            best_achieved_function_value_le_objective_value
              (fun y ↦ (f y).toReal) x N n hn
          exact
            mul_le_mul_of_nonneg_left
              (sub_le_sub_right hbest_le fOpt)
              (h_stepsize_nonneg n)

-- Proof sketch: sum `mirror_descent_fundamental_inequality` from `k = 0` to `N`, telescope the
-- Bregman terms, and use the norm cap `‖g k‖ ≤ h_bound.L_f` from `h_bound` at each iterate.
/-- Companion to Lemma 9.14: summing the one-step mirror-descent inequality from Lemma 9.13 and
using the Chapter 8 uniform subgradient bound yields the weighted prefix estimate
`∑_{k=0}^N t_k (f(x^k).toReal - f_opt) ≤ B_ω(xStar, x⁰) + (L_f^2 / (2σ)) ∑_{k=0}^N t_k^2`
for every optimal point `xStar ∈ XStar`. -/
theorem mirror_descent_weighted_objective_gap_sum_le
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun k ↦ t k * ((f (x k)).toReal - fOpt)) ≤
      B[ω] xStar (x 0) +
        (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ)) := by
  -- Start from the exact correction term and dominate each `‖g k‖²` by the uniform bound `L_f²`.
  have hbase :=
    mirrorDescentWeightedObjectiveGapSumLeWithNormCorrection
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
      (h_traj := h_traj) hxStar N
  have hcorr_le :
      (1 / (2 * σ)) *
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
        (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) :=
    mirrorDescentNormCorrection_le_uniformBound
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (x := x) (g := g) (t := t) h_problem hω h_bound h_traj N
  exact hbase.trans <| by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hcorr_le (B[ω] xStar (x 0))

-- Proof sketch: apply `mirror_descent_weighted_objective_gap_sum_le`, use the prefix-minimality
-- of `best_achieved_function_value` to bound each objective gap below by the running-best gap, and
-- divide by the positive stepsize prefix sum supplied by `h_traj.stepsize_pos`.
/-- Lemma 9.14: under Definition 9.1 for the constrained problem `min {f(x) : x ∈ C}` and
Definition 9.2 for the mirror potential `ω`, if every subgradient of `f` on `C` has norm at most
`L_f = h_bound.L_f`, then for every optimal point `xStar ∈ XStar`, every mirror-descent
trajectory `x` with positive stepsizes `t`, and every `N`, the running-best objective gap
satisfies
`f_best^N - f_opt ≤ (B_ω(xStar, x⁰) + (h_bound.L_f^2 / (2σ)) * ∑_{k=0}^N t_k^2) / ∑_{k=0}^N t_k`. -/
theorem mirror_descent_best_value_gap_le
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      (B[ω] xStar (x 0) +
          (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
  have hprefix_pos :
      0 < Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) :=
    positiveStepsizePrefixSum_pos (t := t) h_traj.stepsize_pos N
  have hbest_weighted :
      (Finset.sum (Finset.range (N + 1)) (fun n ↦ t n)) *
          (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt) ≤
        Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt)) := by
    -- Turn the prefix minimum property of `best_achieved_function_value` into a weighted bound.
    exact bestAchievedGap_mul_prefixSum_le
      (f := f) (ω := ω) (C := C) (x := x) (g := g) (t := t) h_traj N
  have hweighted :=
    mirror_descent_weighted_objective_gap_sum_le
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
      (h_bound := h_bound) (h_traj := h_traj) hxStar N
  have hmain :
      (Finset.sum (Finset.range (N + 1)) (fun n ↦ t n)) *
          (best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt) ≤
        B[ω] xStar (x 0) +
          (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
            Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
    -- The summed weighted-gap theorem is the exact numerator bound needed here.
    exact hbest_weighted.trans hweighted
  -- Divide by the strictly positive prefix sum to isolate the running-best gap.
  rw [le_div_iff₀ hprefix_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

end
