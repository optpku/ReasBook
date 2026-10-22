/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_27
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_1
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_13
import FirstOrderMethodsOptimization_Beck_2017.Chap09.MirrorDescentStepsize

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace (toDualMap)

noncomputable section

universe u

/- `prompt_add/` is absent in this workspace, so the API review is based on the existing Chapter 8
and Chapter 9 owner files. Theorem 9.18 is `source-facing`: it states the asymptotic convergence
and the dynamic-step `O(log k / √k)` rate for a concrete mirror-descent trajectory under the
standing constrained-problem assumptions of Definition 9.1 and the Bregman-potential assumptions of
Definition 9.2. The canonical owners already present are `IsConstrainedConvexProblem`,
`IsBregmanPotentialOn`, `SubgradientNormBoundOn`, `is_mirror_descent_trajectory`,
`best_achieved_function_value`, and `B[ω]`. -/

/- The two stepsize rules used in Theorem 9.18 are a `bridge/view` layer on top of the source-
facing trajectory predicate `is_mirror_descent_trajectory`: they are explicit sequences attached to
that owner, not a second owner for mirror descent itself. The reusable owners now live in the
chapter support file `MirrorDescentStepsize`, so later Chapter 9 items can import the stepsize API
without depending on the theorem statements below. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/-- Helper for Theorem 9.18: every positive-stepsize prefix sum `∑_{n=0}^k t n` is strictly
positive. -/
private lemma positiveStepsizePrefixSum_pos
    (h_stepsize_pos : ∀ n, 0 < t n) (k : ℕ) :
    0 < Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
  -- The initial positive stepsize already appears in every prefix sum.
  have hmem : 0 ∈ Finset.range (k + 1) := by
    simp
  have hle :
      t 0 ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
    simpa using
      (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_stepsize_pos n)) hmem)
  exact lt_of_lt_of_le (h_stepsize_pos 0) hle

/-- Helper for Theorem 9.18: if `(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n) → 0` and all stepsizes are
positive, then the prefix sums `∑_{n=0}^k t_n` tend to `+∞`. -/
private lemma stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            (Finset.sum (Finset.range (k + 1)) fun n ↦ t n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
      Filter.atTop Filter.atTop := by
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  have hS_pos : ∀ k, 0 < S k := by
    intro k
    exact positiveStepsizePrefixSum_pos (t := t) h_stepsize_pos k
  have hS_mono : Monotone S := by
    -- Each new prefix adds the nonnegative summand `t (k + 1)`.
    refine monotone_nat_of_le_succ ?_
    intro k
    have hsucc : S (k + 1) = S k + t (k + 1) := by
      simp [S, Finset.sum_range_succ]
    calc
      S k ≤ S k + t (k + 1) := by
        exact le_add_of_nonneg_right (le_of_lt (h_stepsize_pos (k + 1)))
      _ = S (k + 1) := hsucc.symm
  refine Filter.tendsto_atTop.2 ?_
  intro b
  by_cases hb : b < S 0
  · exact
      (Filter.eventually_ge_atTop 0).mono fun n hn ↦
        le_trans (le_of_lt hb) (hS_mono hn)
  · have hS0_le_b : S 0 ≤ b := le_of_not_gt hb
    have hexists : ∃ N, b ≤ S N := by
      by_contra hbounded
      push Not at hbounded
      have hbound : ∀ k, S k ≤ b := by
        intro k
        exact le_of_lt (hbounded k)
      have hb_pos : 0 < b := lt_of_lt_of_le (hS_pos 0) hS0_le_b
      let c : ℝ := (t 0) ^ (2 : ℕ) / b
      have hc_pos : 0 < c := by
        dsimp [c]
        have ht_sq_pos : 0 < (t 0) ^ (2 : ℕ) := by
          simpa [pow_two] using sq_pos_of_pos (h_stepsize_pos 0)
        exact div_pos ht_sq_pos hb_pos
      have hratio_lower : ∀ k, c ≤ Q k / S k := by
        intro k
        have hQ_lower :
            (t 0) ^ (2 : ℕ) ≤ Q k := by
          have hmem : 0 ∈ Finset.range (k + 1) := by
            simp
          simpa [Q] using
            (Finset.single_le_sum (fun n _ ↦ sq_nonneg (t n)) hmem)
        have hQ_nonneg : 0 ≤ Q k := by
          simpa [Q] using Finset.sum_nonneg (fun n _ ↦ sq_nonneg (t n))
        calc
          c = (t 0) ^ (2 : ℕ) / b := by
            rfl
          _ ≤ Q k / b := by
            exact (div_le_div_iff_of_pos_right hb_pos).2 hQ_lower
          _ ≤ Q k / S k := by
            exact div_le_div_of_nonneg_left hQ_nonneg (hS_pos k) (hbound k)
      have hc_le_zero : c ≤ 0 := by
        have hratio' :
            Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
          simpa [S, Q] using h_ratio
        exact
          le_of_tendsto_of_tendsto tendsto_const_nhds hratio'
            (Filter.Eventually.of_forall hratio_lower)
      exact (not_le_of_gt hc_pos) hc_le_zero
    rcases hexists with ⟨N, hN⟩
    exact (Filter.eventually_ge_atTop N).mono fun n hn ↦ le_trans hN (hS_mono hn)

omit [CompleteSpace E] in
/-- Helper for Theorem 9.18: a Euclidean subgradient of the real-valued restriction
`x ↦ (f x).toReal` at a finite point induces a strong-dual subgradient of the original
extended-real objective. -/
private lemma toDualMap_mem_subdifferential_of_mem_euclideanSubdifferentialAt_toReal
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {y v : E} (hy : y ∈ effective_domain f)
    (hv : v ∈ euclideanSubdifferentialAt (fun z ↦ (f z).toReal) y) :
    (toDualMap ℝ E v : Module.Dual ℝ E) ∈ subdifferential f y := by
  -- Rewrite Euclidean membership into the owner subdifferential inequality on `f.toReal`.
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

omit [CompleteSpace E] in
/-- Helper for Theorem 9.18: a subgradient of the real-valued lift `x ↦ (ω x).toReal` at a
feasible point is also a subgradient of the original extended-real-valued potential `ω`. -/
private lemma memSubdifferentialOfMemSubdifferentialToReal
    (hω : IsBregmanPotentialOn ω C σ)
    {y : E} (hyC : y ∈ C) {s : Module.Dual ℝ E}
    (hs : s ∈ subdifferential (Function.toEReal (fun z ↦ (ω z).toReal)) y) :
    s ∈ subdifferential ω y := by
  -- Rewrite the lifted subgradient into a real inequality and lift it back through `ω.toReal`.
  have hy : y ∈ effective_domain ω := hω.subset_effective_domain hyC
  change s ∈ subdifferential (fun z ↦ (((ω z).toReal : ℝ) : EReal)) y at hs
  rw [mem_subdifferential, is_subgradient_at_coe_iff] at hs
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hy, ?_⟩
  intro z hz
  have hy_top : ω y ≠ ⊤ := ne_of_lt hy
  have hz_top : ω z ≠ ⊤ := ne_of_lt hz
  have hy_bot : ω y ≠ ⊥ := hω.toIsProperExtendedRealFunction.ne_bot y
  have hz_bot : ω z ≠ ⊥ := hω.toIsProperExtendedRealFunction.ne_bot z
  have hsz : (ω z).toReal ≥ (ω y).toReal + s (z - y) := hs z
  have hszE :
      (((ω y).toReal + s (z - y) : ℝ) : EReal) ≤ ((((ω z).toReal : ℝ) : EReal) : EReal) := by
    exact EReal.coe_le_coe (by simpa [ge_iff_le] using hsz)
  simpa [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hz_top hz_bot,
    EReal.coe_add, ge_iff_le] using hszE

/-- Helper for Theorem 9.18: the trajectory's real-valued mirror-map domain membership yields the
owner-domain membership `x^k ∈ dom(∂ω)`. -/
private lemma mirrorDescent_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (n : ℕ) :
    x n ∈ subdifferential_domain ω := by
  -- Extract a witness for the lifted real-valued subgradient and transport it to `ω`.
  have hx_domain :
      x n ∈ subdifferential_domain (Function.toEReal (fun y ↦ (ω y).toReal)) :=
    h_traj.mem_subdifferential_domain n
  rw [mem_subdifferential_domain] at hx_domain
  rw [mem_subdifferential_domain]
  have hx_feasible : x n ∈ C := h_traj.mem_feasible_set n
  rcases hx_domain with ⟨s, hs⟩
  exact ⟨s, memSubdifferentialOfMemSubdifferentialToReal hω hx_feasible hs⟩

/-- Helper for Theorem 9.18: every selected mirror-descent subgradient has norm at most
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

/-- Helper for Theorem 9.18: the Bregman-difference prefix
`∑_{n=0}^N (B_ω(xStar, x^n) - B_ω(xStar, x^(n+1)))` telescopes to the endpoint difference. -/
private lemma mirrorDescentBregmanDifference_sum_range
    (xStar : E) (N : ℕ) :
    Finset.sum (Finset.range (N + 1))
      (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) =
        B[ω] xStar (x 0) - B[ω] xStar (x (N + 1)) := by
  -- The prefix of successive Bregman differences is an exact finite telescope.
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

/-- Helper for Theorem 9.18: summing Lemma 9.13 without replacing `‖g_n‖` by `L_f` yields the
actual weighted mirror-descent gap estimate with the correction
`(1 / (2σ)) ∑_{n=0}^N t_n^2 ‖g_n‖^2`. -/
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
              (mirrorDescent_mem_subdifferential_domain
                (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj (N + 1))
              (hω_diff _ (mirrorDescent_mem_subdifferential_domain
                (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj (N + 1)))
          linarith
    _ = B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (N + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
          simp [div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 9.18: dividing the actual weighted gap estimate by the positive prefix
sum yields the running-best gap bound with the true norm correction. -/
private lemma mirrorDescentBestValueGapLeWithNormCorrection
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      (B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (N + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := by
  let S : ℕ → ℝ := fun j ↦ Finset.sum (Finset.range (j + 1)) (fun n ↦ t n)
  let bestGap : ℕ → ℝ :=
    fun j ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x j - fOpt
  have h_stepsize_nonneg : ∀ n, 0 ≤ t n := fun n ↦ le_of_lt (h_traj.stepsize_pos n)
  have hS_pos : 0 < S N :=
    positiveStepsizePrefixSum_pos (t := t) h_traj.stepsize_pos N
  have hS_best :
      Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * bestGap N) = S N * bestGap N := by
    symm
    dsimp [S]
    exact Finset.sum_mul (Finset.range (N + 1)) (fun n ↦ t n) (bestGap N)
  have hbest_sum_le :
      S N * bestGap N ≤
        Finset.sum (Finset.range (N + 1)) (fun n ↦ t n * ((f (x n)).toReal - fOpt)) := by
    -- Compare the running-best gap against each prefix term and then sum the inequalities.
    rw [← hS_best]
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
  have hweighted :=
    mirrorDescentWeightedObjectiveGapSumLeWithNormCorrection
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
      (h_traj := h_traj) hxStar N
  have hmain :
      S N * bestGap N ≤
        B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (N + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
    -- Lemma 9.13 summed over the prefix already has the exact correction term required here.
    exact hbest_sum_le.trans hweighted
  have hdiv :
      bestGap N ≤
        (B[ω] xStar (x 0) +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (N + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) / S N := by
    -- Divide by the strictly positive stepsize prefix sum to isolate the best-gap term.
    rw [le_div_iff₀ hS_pos]
    simpa [S, bestGap, mul_comm, mul_left_comm, mul_assoc] using hmain
  exact by
    simpa [S, bestGap] using hdiv

/-- Helper for Theorem 9.18: the exact-correction best-gap bound simplifies to the usual
uniform-`L_f` estimate once every selected mirror-descent subgradient is bounded by `h_bound.L_f`.
-/
private lemma mirrorDescentBestValueGapLe
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
            Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := by
  -- Start from the exact correction term and dominate each `‖g n‖²` by `h_bound.L_f²`.
  have hbase :=
    mirrorDescentBestValueGapLeWithNormCorrection
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
      (h_traj := h_traj) hxStar N
  have hcorr_le :
      (1 / (2 * σ)) *
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
        (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
    -- Replace each norm square by the uniform bound `h_bound.L_f²`.
    have hsum_le :
        Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
          Finset.sum (Finset.range (N + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) := by
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
  have hprefix_pos :
      0 < Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) :=
    positiveStepsizePrefixSum_pos (t := t) h_traj.stepsize_pos N
  -- Monotonicity in the numerator transfers the exact estimate to the uniform bound.
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt
      ≤ (B[ω] xStar (x 0) +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (N + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
          Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := hbase
    _ ≤ (B[ω] xStar (x 0) +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
              Finset.sum (Finset.range (N + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
          Finset.sum (Finset.range (N + 1)) (fun n ↦ t n) := by
            exact
              div_le_div_of_nonneg_right
                (by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hcorr_le (B[ω] xStar (x 0)))
                (le_of_lt hprefix_pos)

omit [CompleteSpace E] in
/-- Helper for Theorem 9.18: under the adaptive schedule, the actual correction term is bounded by
the harmonic prefix sum `∑_{n=0}^k 1 / (n + 1)`. -/
private lemma mirrorDescentAdaptiveCorrection_le_harmonicPrefix
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_stepsize : t = mirror_descent_adaptive_stepsize h_bound.L_f σ g)
    (k : ℕ) :
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
      harmonicPrefixSum k := by
  -- Normalize each adaptive summand to `1 / (n + 1)` by splitting on whether `g n = 0`.
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        (1 / (2 * σ)) * ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤ 1 / ((n : ℝ) + 1) := by
    intro n hn
    by_cases hg0 : g n = 0
    · -- In the zero branch the weighted correction vanishes.
      rw [h_stepsize, mirror_descent_adaptive_stepsize_apply_zero _ _ _ hg0]
      simp only [hg0, norm_zero, sq, mul_zero]
      positivity
    · -- In the nonzero branch the adaptive formula makes the weighted term exactly `1 / (n + 1)`.
      have hσ_ne : σ ≠ 0 := ne_of_gt hω.sigma_pos
      have hnorm_ne : ‖g n‖ ≠ 0 := by
        simpa [norm_eq_zero] using hg0
      have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
      have hσ_nonneg : 0 ≤ 2 * σ := by nlinarith [hω.sigma_pos]
      have hn_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
      rw [h_stepsize, mirror_descent_adaptive_stepsize_apply_nonzero _ _ _ hg0]
      calc
        (1 / (2 * σ)) *
            ((Real.sqrt (2 * σ) / (‖g n‖ * Real.sqrt ((n : ℝ) + 1))) ^ (2 : ℕ) *
              ‖g n‖ ^ (2 : ℕ))
          = ‖g n‖ ^ (2 : ℕ) / (‖g n‖ ^ (2 : ℕ) * ((n : ℝ) + 1)) := by
              field_simp [hσ_ne, hnorm_ne, hsqrt_ne]
              nlinarith [Real.sq_sqrt hσ_nonneg, Real.sq_sqrt hn_nonneg]
        _ ≤ 1 / ((n : ℝ) + 1) := by
              field_simp [pow_two, hnorm_ne]
              norm_num
  calc
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))
      = Finset.sum (Finset.range (k + 1))
          (fun n ↦ (1 / (2 * σ)) * ((t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) := by
            rw [Finset.mul_sum]
    _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / ((n : ℝ) + 1)) := by
          exact Finset.sum_le_sum hpointwise
    _ = harmonicPrefixSum k := by
          rw [← harmonicPrefixSum_eq_sum]

/-- Helper for Theorem 9.18: under the adaptive schedule, the stepsize prefix dominates the
scaled inverse-square-root prefix sum
`(√(2σ) / L_f) * ∑_{n=0}^k 1 / √(n + 1)`. -/
private lemma mirrorDescentAdaptivePrefix_ge_scaledInverseSqrtPrefix
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (h_stepsize : t = mirror_descent_adaptive_stepsize h_bound.L_f σ g)
    (k : ℕ) :
    (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k ≤
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
  -- Compare each adaptive stepsize with the fallback `√(2σ) / (L_f √(n + 1))`.
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        (Real.sqrt (2 * σ) / h_bound.L_f) * (1 / Real.sqrt ((n : ℝ) + 1)) ≤ t n := by
    intro n hn
    by_cases hg0 : g n = 0
    · -- The zero branch is exactly the fallback formula.
      rw [h_stepsize, mirror_descent_adaptive_stepsize_apply_zero _ _ _ hg0]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · -- The nonzero branch improves the denominator because `‖g n‖ ≤ L_f`.
      have hnorm_le :=
        mirrorDescentSelectedSubgradient_norm_le
          (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
          (x := x) (g := g) (t := t) h_problem h_bound h_traj n
      have hcoeff_nonneg : 0 ≤ Real.sqrt (2 * σ) := by positivity
      have hnorm_pos : 0 < ‖g n‖ := by
        simpa [norm_eq_zero] using hg0
      have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by positivity
      rw [h_stepsize, mirror_descent_adaptive_stepsize_apply_nonzero _ _ _ hg0]
      calc
        (Real.sqrt (2 * σ) / h_bound.L_f) * (1 / Real.sqrt ((n : ℝ) + 1))
          = Real.sqrt (2 * σ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)) := by
              field_simp [ne_of_gt h_bound.L_f_pos, ne_of_gt hsqrt_pos]
        _ ≤ Real.sqrt (2 * σ) / (‖g n‖ * Real.sqrt ((n : ℝ) + 1)) := by
              have hden_le :
                  ‖g n‖ * Real.sqrt ((n : ℝ) + 1) ≤
                    h_bound.L_f * Real.sqrt ((n : ℝ) + 1) := by
                exact mul_le_mul_of_nonneg_right hnorm_le (by positivity)
              exact div_le_div_of_nonneg_left hcoeff_nonneg (mul_pos hnorm_pos hsqrt_pos) hden_le
  calc
    (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k
      = Finset.sum (Finset.range (k + 1))
          (fun n ↦ (Real.sqrt (2 * σ) / h_bound.L_f) * (1 / Real.sqrt ((n : ℝ) + 1))) := by
            rw [inverseSqrtPrefixSum_eq_sum, Finset.mul_sum]
    _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
          exact Finset.sum_le_sum hpointwise

-- Proof sketch: apply the local running-best estimate with the bound constant
-- `h_bound.L_f`. The right-hand side becomes
-- `B_ω(xStar, x⁰) / ∑_{n ≤ k} t_n + (h_bound.L_f^2 / (2σ)) * (∑_{n ≤ k} t_n^2 / ∑_{n ≤ k} t_n)`
-- for an optimal point `xStar ∈ XStar`. Since `xStar` is fixed, the first term is negligible and
-- the hypothesis `h_ratio` forces the second term to converge to `0`, so the running-best value
-- tends to `fOpt`.
/-- Theorem 9.18 (1): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if every subgradient of `f` on `C` has norm at most `L_f = h_bound.L_f` and
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n) → 0`, then the running-best objective value attained by the
mirror-descent iterates converges to the optimal value `fOpt`. -/
theorem mirror_descent_best_value_tendsto_of_stepsize_ratio
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            (Finset.sum (Finset.range (k + 1)) fun n ↦ t n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x k)
      Filter.atTop (nhds fOpt) := by
  -- Route correction: use the stable squeeze-to-zero proof from Theorem 8.25 on the mirror-descent
  -- running-best gap, then shift back by `fOpt`.
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  let bestGap : ℕ → ℝ :=
    fun k ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x k - fOpt
  have hS_atTop :
      Filter.Tendsto S Filter.atTop Filter.atTop :=
    stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero
      (t := t) h_traj.stepsize_pos h_ratio
  have hbest_nonneg : ∀ k, 0 ≤ bestGap k := by
    intro k
    -- Every attained value stays above `fOpt`, so the running best does too.
    have hbest_lower :
        fOpt ≤ best_achieved_function_value (fun y ↦ (f y).toReal) x k := by
      unfold best_achieved_function_value
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
      have hx_image : f (x n) ∈ f '' C := by
        exact Set.mem_image_of_mem f (h_traj.mem_feasible_set n)
      have hlower : (fOpt : EReal) ≤ f (x n) :=
        h_problem.optimal_value_isGLB.left hx_image
      have hx_dom : x n ∈ effective_domain f := by
        exact
          interior_subset
            (h_problem.feasible_subset_interior_effective_domain (h_traj.mem_feasible_set n))
      have htop : f (x n) ≠ ⊤ := ne_of_lt hx_dom
      have hbot : f (x n) ≠ ⊥ := h_problem.ne_bot _
      have hreal :
          (fOpt : EReal) ≤ ((((f (x n)).toReal : ℝ) : EReal)) := by
        simpa [EReal.coe_toReal htop hbot] using hlower
      exact EReal.coe_le_coe_iff.mp hreal
    dsimp [bestGap]
    linarith
  have hfirst_tendsto :
      Filter.Tendsto
        (fun k ↦ (B[ω] xStar (x 0)) / S k)
        Filter.atTop (nhds 0) :=
    hS_atTop.const_div_atTop (B[ω] xStar (x 0))
  have hsecond_tendsto :
      Filter.Tendsto
        (fun k ↦ (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) * (Q k / S k))
        Filter.atTop (nhds 0) := by
    have hratio' : Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
      simpa [Q, S] using h_ratio
    simpa using hratio'.const_mul (h_bound.L_f ^ (2 : ℕ) / (2 * σ))
  have hupper_tendsto :
      Filter.Tendsto
        (fun k ↦
          (B[ω] xStar (x 0)) / S k +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) * (Q k / S k))
        Filter.atTop (nhds 0) := by
    simpa using hfirst_tendsto.add hsecond_tendsto
  have hupper_bound :
      ∀ k,
        bestGap k ≤
          (B[ω] xStar (x 0)) / S k +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) * (Q k / S k) := by
    intro k
    have hbase :=
      mirrorDescentBestValueGapLe
        (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff) (h_bound := h_bound)
        (h_traj := h_traj) hxStar k
    have hS_pos_k : 0 < S k :=
      positiveStepsizePrefixSum_pos (t := t) h_traj.stepsize_pos k
    calc
      bestGap k
        ≤ (B[ω] xStar (x 0) +
              (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
                Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) / S k := by
              simpa [bestGap, S, Q] using hbase
      _ = (B[ω] xStar (x 0)) / S k +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) * (Q k / S k) := by
            simp [Q]
            field_simp [S, ne_of_gt hS_pos_k]
  have hgap_tendsto_zero :
      Filter.Tendsto (fun k ↦ bestGap k) Filter.atTop (nhds 0) := by
    refine squeeze_zero hbest_nonneg hupper_bound hupper_tendsto
  simpa [bestGap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hgap_tendsto_zero.const_add fOpt

-- Proof sketch: use the local uniform-`L_f` running-best estimate and
-- substitute the predefined diminishing family
-- `mirror_descent_predefined_diminishing_stepsize h_bound.L_f σ`. This gives
-- `(t n)^2 * ‖g n‖^2 ≤ 2σ / (n + 1)` from the uniform norm bound `‖g n‖ ≤ L_f`. The numerator
-- then becomes
-- `B_ω(xStar, x⁰) + ∑_{n ≤ k} 1 / (n + 1)`, the denominator is bounded below by
-- `(√(2σ) / L_f) * ∑_{n ≤ k} 1 / √(n + 1)`, and Lemma 8.27 (1) gives the stated
-- `O(log k / √k)` bound.
/-- Theorem 9.18 (2): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if the mirror-descent stepsizes are given by the predefined diminishing family
`mirror_descent_predefined_diminishing_stepsize h_bound.L_f σ`, equivalently by the rule
`t_k = √(2σ) / (L_f √(k + 1))`, then for every optimal point `xStar ∈ XStar` and every `k ≥ 1`
the running-best objective gap satisfies the standard
`(L_f / √(2σ)) * (B_ω(xStar, x⁰) + 1 + log (k + 1)) / √(k + 1)` estimate. -/
theorem mirror_descent_best_value_gap_le_log_over_sqrt_of_predefined_diminishing_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize : t = mirror_descent_predefined_diminishing_stepsize h_bound.L_f σ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x k - fOpt ≤
      (h_bound.L_f / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := by
  -- Route correction: rewrite Lemma 9.14 into the Chapter 8 prefix-sum owners and then apply the
  -- harmonic-prefix ratio bound.
  have _hk : 1 ≤ k := hk
  let D := B[ω] xStar (x 0)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hD_nonneg : 0 ≤ D := by
      exact bregmanDistance_nonneg_of_mem_subdifferential_domain
        hω xStar (x 0) hxStar_data.1 (h_traj.mem_feasible_set 0)
        (mirrorDescent_mem_subdifferential_domain
          (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj 0)
        (hω_diff _ (mirrorDescent_mem_subdifferential_domain
          (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj 0))
  have hbase :=
    mirrorDescentBestValueGapLe
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff) (h_bound := h_bound)
      (h_traj := h_traj) hxStar k
  have hsum_eq :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) =
        (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k := by
    -- Pull the constant `√(2σ) / L_f` out of the named diminishing schedule.
    rw [h_stepsize, inverseSqrtPrefixSum_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [mirror_descent_predefined_diminishing_stepsize_apply]
    ring_nf
  have hcorr :
      (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) =
        harmonicPrefixSum k := by
    -- The closed-form diminishing schedule makes each corrected summand equal `1 / (n + 1)`.
    rw [h_stepsize, harmonicPrefixSum_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hLf_ne : h_bound.L_f ≠ 0 := ne_of_gt h_bound.L_f_pos
    have hσ_ne : σ ≠ 0 := ne_of_gt hω.sigma_pos
    have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2σ_nonneg : 0 ≤ 2 * σ := by nlinarith [hω.sigma_pos]
    have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    have hsqrt2σ_sq : Real.sqrt (2 * σ) ^ (2 : ℕ) = 2 * σ := Real.sq_sqrt h2σ_nonneg
    have hsqrtn_sq : Real.sqrt ((n : ℝ) + 1) ^ (2 : ℕ) = (n : ℝ) + 1 :=
      Real.sq_sqrt hn1_nonneg
    rw [mirror_descent_predefined_diminishing_stepsize_apply]
    calc
      (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
          (Real.sqrt (2 * σ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) ^ (2 : ℕ)
        = h_bound.L_f ^ (2 : ℕ) / (h_bound.L_f ^ (2 : ℕ) * ((n : ℝ) + 1)) := by
            field_simp [pow_two, hLf_ne, hσ_ne, hsqrt_ne]
            rw [hsqrt2σ_sq, hsqrtn_sq]
      _ = 1 / ((n : ℝ) + 1) := by
            field_simp [pow_two, hLf_ne, hn1_ne]
  have hInv_nonneg : 0 ≤ inverseSqrtPrefixSum k := by
    rw [inverseSqrtPrefixSum_eq_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hnum_le :
      D +
          (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) ≤
        D + harmonicPrefixSum k := by
    rw [hcorr]
  have hratio :
      (D +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
              Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) ≤
        (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
    rw [hsum_eq]
    have hcoeff_nonneg' : 0 ≤ Real.sqrt (2 * σ) / h_bound.L_f := by
      exact div_nonneg (by positivity) (le_of_lt h_bound.L_f_pos)
    have hden_nonneg :
        0 ≤ (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k := by
      exact mul_nonneg hcoeff_nonneg' hInv_nonneg
    have hdiv := div_le_div_of_nonneg_right hnum_le hden_nonneg
    have hLf_ne : h_bound.L_f ≠ 0 := ne_of_gt h_bound.L_f_pos
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    have hsqrt_pos : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.mpr htwoσ_pos
    have hsqrt_ne : Real.sqrt (2 * σ) ≠ 0 := ne_of_gt hsqrt_pos
    calc
      (D +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
              Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
          ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k)
        ≤ (D + harmonicPrefixSum k) /
            ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k) := hdiv
      _ = (h_bound.L_f / Real.sqrt (2 * σ)) *
            ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
          field_simp [D, hLf_ne, hsqrt_ne]
  have hprefix_ratio :=
    harmonic_prefix_ratio_le_log_bound D hD_nonneg k
  have hcoeff_nonneg : 0 ≤ h_bound.L_f / Real.sqrt (2 * σ) := by
    exact div_nonneg (le_of_lt h_bound.L_f_pos) (by positivity)
  have hscaled :
      (h_bound.L_f / Real.sqrt (2 * σ)) * ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) ≤
        (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := by
    exact mul_le_mul_of_nonneg_left hprefix_ratio hcoeff_nonneg
  exact calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x k - fOpt
      ≤ (D +
            (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
              Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
            simpa [D] using hbase
    _ ≤ (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := hratio
    _ ≤ (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := hscaled
    _ = (h_bound.L_f / Real.sqrt (2 * σ)) *
          (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
        simp [D, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

-- Proof sketch: use the local uniform-`L_f` running-best estimate again. The adaptive rule gives
-- the
-- fallback formula whenever `g n = 0`, and when `g n ≠ 0` it gives
-- `t n = √(2σ) / (‖g n‖ √(n + 1))`; the named owner
-- `mirror_descent_adaptive_stepsize h_bound.L_f σ g` packages both branches. In either case one
-- obtains the lower bound
-- `t n ≥ √(2σ) / (L_f √(n + 1))` and the estimate `(t n)^2 * ‖g n‖^2 ≤ 2σ / (n + 1)`. The same
-- harmonic-sum comparison as in part (2), together with Lemma 8.27 (1), yields the displayed
-- `O(log k / √k)` rate.
/-- Theorem 9.18 (3): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if the mirror-descent stepsizes are given by the adaptive family
`mirror_descent_adaptive_stepsize h_bound.L_f σ g`, equivalently by the rule
`t_k = √(2σ) / (‖g_k‖ √(k + 1))` when `g_k ≠ 0` and
`t_k = √(2σ) / (L_f √(k + 1))` when `g_k = 0`, then for every optimal point `xStar ∈ XStar` and
every `k ≥ 1` the running-best objective gap satisfies the same
`(L_f / √(2σ)) * (B_ω(xStar, x⁰) + 1 + log (k + 1)) / √(k + 1)` estimate. -/
theorem mirror_descent_best_value_gap_le_log_over_sqrt_of_adaptive_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize : t = mirror_descent_adaptive_stepsize h_bound.L_f σ g) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x k - fOpt ≤
      (h_bound.L_f / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := by
  -- Keep the actual `‖g_n‖` correction until after substituting the adaptive schedule.
  let D := B[ω] xStar (x 0)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hD_nonneg : 0 ≤ D := by
    simpa [D] using
      bregmanDistance_nonneg_of_mem_subdifferential_domain
        hω xStar (x 0) hxStar_data.1 (h_traj.mem_feasible_set 0)
        (mirrorDescent_mem_subdifferential_domain
        (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj 0)
        (hω_diff _ (mirrorDescent_mem_subdifferential_domain
          (f := f) (ω := ω) (C := C) (g := g) (t := t) hω h_traj 0))
  have hbase :=
    mirrorDescentBestValueGapLeWithNormCorrection
      (h_problem := h_problem) (hω := hω) (hω_diff := hω_diff)
      (h_traj := h_traj) hxStar k
  have hcorr :
      (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) ≤
        harmonicPrefixSum k :=
    mirrorDescentAdaptiveCorrection_le_harmonicPrefix
      (f := f) (ω := ω) (C := C) (hω := hω) (h_bound := h_bound) (h_stepsize := h_stepsize) k
  have hsum_lower :
      (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k ≤
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) :=
    mirrorDescentAdaptivePrefix_ge_scaledInverseSqrtPrefix
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (x := x) (g := g) (t := t) h_problem h_bound h_traj h_stepsize k
  have hInv_pos : 0 < inverseSqrtPrefixSum k := by
    exact lt_of_lt_of_le (by positivity) (sqrt_le_inverseSqrtPrefixSum k)
  have hcoeff_pos : 0 < Real.sqrt (2 * σ) / h_bound.L_f := by
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    have hsqrt_pos : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.mpr htwoσ_pos
    exact div_pos hsqrt_pos h_bound.L_f_pos
  have hnum_nonneg :
      0 ≤ D +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
    have hsum_nonneg :
        0 ≤ Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ)) := by
      exact Finset.sum_nonneg fun n hn ↦ mul_nonneg (sq_nonneg (t n)) (sq_nonneg ‖g n‖)
    have hcoeff_nonneg' : 0 ≤ 1 / (2 * σ) := by
      have htwoσ_pos : 0 < 2 * σ := by
        nlinarith [hω.sigma_pos]
      exact le_of_lt (one_div_pos.mpr htwoσ_pos)
    exact add_nonneg hD_nonneg (mul_nonneg hcoeff_nonneg' hsum_nonneg)
  have hratio :
      (D +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) ≤
        (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
    have hfirst :
        (D +
              (1 / (2 * σ)) *
                Finset.sum (Finset.range (k + 1))
                  (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) ≤
          (D +
              (1 / (2 * σ)) *
                Finset.sum (Finset.range (k + 1))
                  (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
            ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k) := by
      exact div_le_div_of_nonneg_left hnum_nonneg (mul_pos hcoeff_pos hInv_pos) hsum_lower
    have hsecond :
        (D +
              (1 / (2 * σ)) *
                Finset.sum (Finset.range (k + 1))
                  (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
            ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k) ≤
          (D + harmonicPrefixSum k) /
            ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k) := by
      have hden_nonneg :
          0 ≤ (Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k := by
        exact mul_nonneg hcoeff_pos.le hInv_pos.le
      simpa [add_assoc, add_left_comm, add_comm] using
        (div_le_div_of_nonneg_right (add_le_add_left hcorr D) hden_nonneg)
    calc
      (D +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
        ≤ (D + harmonicPrefixSum k) /
            ((Real.sqrt (2 * σ) / h_bound.L_f) * inverseSqrtPrefixSum k) := hfirst.trans hsecond
      _ = (h_bound.L_f / Real.sqrt (2 * σ)) *
            ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
          have hLf_ne : h_bound.L_f ≠ 0 := ne_of_gt h_bound.L_f_pos
          have htwoσ_pos : 0 < 2 * σ := by
            nlinarith [hω.sigma_pos]
          have hsqrt_pos : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.mpr htwoσ_pos
          have hsqrt_ne : Real.sqrt (2 * σ) ≠ 0 := ne_of_gt hsqrt_pos
          field_simp [D, hLf_ne, hsqrt_ne]
  have hprefix_ratio :=
    harmonic_prefix_ratio_le_log_bound D hD_nonneg k
  have hcoeff_nonneg : 0 ≤ h_bound.L_f / Real.sqrt (2 * σ) := by
    exact div_nonneg (le_of_lt h_bound.L_f_pos) (by positivity)
  have hscaled :
      (h_bound.L_f / Real.sqrt (2 * σ)) * ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) ≤
        (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := by
    exact mul_le_mul_of_nonneg_left hprefix_ratio hcoeff_nonneg
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x k - fOpt
      ≤ (D +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n‖ ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
            simpa [D] using hbase
    _ ≤ (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := hratio
    _ ≤ (h_bound.L_f / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := hscaled
    _ = (h_bound.L_f / Real.sqrt (2 * σ)) *
          (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
        simp [D, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end
