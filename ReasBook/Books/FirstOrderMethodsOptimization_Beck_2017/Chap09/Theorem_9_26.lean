/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_15
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_25
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_5
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt Lf σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the relevant API guidance comes from the existing
Chapter 8 and Chapter 9 owner files. Theorem 9.26 is `source-facing`: it states the fixed-horizon
`O(1 / √N)` rate for a concrete Mirror-C trajectory. The canonical owners already present are the
composite-problem package `IsCompositeMirrorDescentProblem`, the Bregman-potential package
`IsBregmanPotentialOn`, the trajectory predicate `is_mirror_c_trajectory`, the Bregman distance
`B[ω]`, the running-best value owner `best_achieved_function_value`, and the finite-horizon
constant-step family `fixed_iteration_uniform_steps`. The textbook closed form for the stepsizes is
derived from that owner, so the public API keeps the rate theorem source-facing and exposes the
owner-to-textbook identification as a companion bridge theorem rather than as a second stepsize
owner. -/

-- Proof sketch: specialize `fixed_iteration_uniform_steps_eq_const` to `ι = Fin N` and
-- `β = Lf ^ 2 / (2 * σ)`, then use `hLf` and `hσ` to rewrite the resulting constant value to the
-- textbook formula `√(2 * Theta0 * σ) / (Lf * √N)`.
/-- Specializing the Lemma 9.15 uniform step family to the Mirror-C coefficients yields the
textbook constant stepsize `√(2 * Theta0 * σ) / (L_f * √N)` on `Fin N`. -/
theorem fixed_iteration_uniform_steps_eq_mirror_c_textbook_stepsize
    (Theta0 Lf σ : ℝ) (N : ℕ) (hLf : 0 < Lf) (hσ : 0 < σ) :
    fixed_iteration_uniform_steps (Fin N) Theta0 (Lf ^ 2 / (2 * σ)) =
      fun _ : Fin N ↦ Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ)) := by
  by_cases hN : N = 0
  · -- When `N = 0`, both sides are functions on the empty type.
    subst hN
    funext i
    exact Fin.elim0 i
  · -- For a nonempty horizon, rewrite the uniform-step denominator into the textbook form.
    funext i
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
    have hN_real_pos : 0 < (N : ℝ) := by
      exact_mod_cast hN_pos
    have hinside :
        Theta0 / ((Lf ^ 2 / (2 * σ)) * (N : ℝ)) =
          (2 * Theta0 * σ) / (Lf ^ 2 * (N : ℝ)) := by
      field_simp [pow_two, hLf.ne', hσ.ne', Nat.cast_ne_zero.mpr hN]
    have hsqrt_den :
        Real.sqrt (Lf ^ 2 * (N : ℝ)) = Lf * Real.sqrt (N : ℝ) := by
      calc
        Real.sqrt (Lf ^ 2 * (N : ℝ))
          = Real.sqrt (Lf ^ 2) * Real.sqrt (N : ℝ) := by
              exact Real.sqrt_mul (sq_nonneg Lf) (N : ℝ)
        _ = Lf * Real.sqrt (N : ℝ) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_pos hLf]
    rw [fixed_iteration_uniform_steps_apply]
    simp only [Fintype.card_fin]
    rw [hinside, Real.sqrt_div']
    · simp [hsqrt_den]
    · positivity

/-- Helper for Theorem 9.26: the source-facing fixed stepsize rule agrees with the canonical
finite-horizon uniform-step owner on `Fin N`. -/
lemma mirrorCRestrictedSteps_eq_fixedIterationUniformSteps
    (Theta0 : ℝ) {N : ℕ}
    (h_stepsize :
      ∀ n : Fin N, t n = Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ)))
    (hLf : 0 < Lf) (hσ : 0 < σ) :
    (fun n : Fin N ↦ t n) =
      fixed_iteration_uniform_steps (Fin N) Theta0 (Lf ^ 2 / (2 * σ)) := by
  -- The bridge theorem identifies the textbook constant with the canonical uniform family.
  funext n
  rw [h_stepsize n]
  rw [fixed_iteration_uniform_steps_eq_mirror_c_textbook_stepsize Theta0 Lf σ N hLf hσ]

/-- Helper for Theorem 9.26: the finite correction term from Lemma 9.25 is bounded by `Theta0`
under the textbook constant stepsize rule. -/
lemma mirrorCPrefixCorrection_le_theta
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      ∀ n : Fin N, t n = Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) :
    (1 / (2 * σ)) *
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
      Theta0 := by
  -- First recover `Theta0 ≥ 0` from the nonnegativity of the Bregman term.
  have hx0_dom : x 0 ∈ effective_domain g := h_traj.mem_effective_domain 0
  have hxStar_dom : xStar ∈ effective_domain g :=
    mirrorCOptimalPoint_memEffectiveDomain
      h_problem.toIsCompositeConvexMinimizationProblem hxStar
  have hB_nonneg : 0 ≤ B[ω] xStar (x 0) := by
    exact bregmanDistance_nonneg_of_mem_subdifferential_domain
      hω xStar (x 0) hxStar_dom hx0_dom (h_traj.mem_subdifferential_domain 0)
      (hω_diff _ (h_traj.mem_subdifferential_domain 0))
  have hTheta0_nonneg : 0 ≤ Theta0 := le_trans hB_nonneg h_bregman_upper
  -- Next bound each selected subgradient norm by `Lf`.
  have hsum_le :
      Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hs_norm : ‖s n‖ ≤ Lf :=
      h_problem.subgradient_norm_le (h_traj.mem_effective_domain n) (h_traj.subgradient_mem n)
    have hs_sq : ‖s n‖ ^ (2 : ℕ) ≤ Lf ^ (2 : ℕ) := by
      nlinarith [hs_norm, norm_nonneg (s n), h_problem.Lf_pos]
    exact mul_le_mul_of_nonneg_left hs_sq (sq_nonneg (t n))
  have hσ_nonneg : 0 ≤ 1 / (2 * σ) := by
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    exact le_of_lt (one_div_pos.mpr htwoσ_pos)
  have hscaled_le :
      (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
        (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hsum_le hσ_nonneg
  have hterm :
      ∀ n : Fin N,
        (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ) = (2 * Theta0 * σ) / (N : ℝ) := by
    intro n
    rw [h_stepsize n]
    have hN_real_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := by
      positivity
    have hsqrt_arg_nonneg : 0 ≤ 2 * Theta0 * σ := by
      nlinarith [hTheta0_nonneg, hω.sigma_pos]
    let a : ℝ := Real.sqrt (2 * Theta0 * σ)
    let r : ℝ := Real.sqrt (N : ℝ)
    have ha_sq : a * a = 2 * Theta0 * σ := by
      dsimp [a]
      exact Real.mul_self_sqrt hsqrt_arg_nonneg
    have hr_sq : r * r = (N : ℝ) := by
      dsimp [r]
      exact Real.mul_self_sqrt (by positivity : 0 ≤ (N : ℝ))
    calc
      (Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) ^ (2 : ℕ) * Lf ^ (2 : ℕ)
          = a * a / (r * r) := by
              dsimp [a, r]
              rw [pow_two, pow_two]
              field_simp [pow_two, h_problem.Lf_pos.ne', hsqrtN_ne]
      _ = a * a / (N : ℝ) := by rw [hr_sq]
      _ = (2 * Theta0 * σ) / (N : ℝ) := by rw [ha_sq]
  have hscaled_eq :
      (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) =
        Theta0 := by
    have hsum_eq :
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) =
          Finset.sum Finset.univ (fun _ : Fin N ↦ (2 * Theta0 * σ) / (N : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact hterm n
    rw [hsum_eq]
    have hN_real_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    simp [Finset.sum_const]
    field_simp [hN_real_ne, hω.sigma_pos.ne']
  calc
    (1 / (2 * σ)) *
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))
      ≤ (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := hscaled_le
    _ = Theta0 := hscaled_eq

/-- Helper for Theorem 9.26: summing the constant textbook stepsize over `Fin N` produces the
expected factor `(N : ℝ) * (√(2 * Theta0 * σ) / (Lf * √N))`. -/
lemma mirrorCPrefixStepsizeSum_eq_textbookConstantMultiple
    (Theta0 : ℝ) {N : ℕ}
    (h_stepsize :
      ∀ n : Fin N, t n = Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) :
    Finset.sum Finset.univ (fun n : Fin N ↦ t n) =
      (N : ℝ) * (Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) := by
  -- Every prefix step is the same constant, so the sum is cardinality times that constant.
  let c : ℝ := Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))
  calc
    Finset.sum Finset.univ (fun n : Fin N ↦ t n)
      = Finset.sum Finset.univ (fun _ : Fin N ↦ c) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [h_stepsize n]
    _ = (N : ℝ) * c := by simp [c, nsmul_eq_mul, Fintype.card_fin]
    _ = (N : ℝ) * (Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) := rfl

omit [CompleteSpace E] in
/-- Helper for Theorem 9.26: on a constant prefix, the weighted difference between the current
and shifted penalty terms telescopes to the initial penalty minus a nonnegative terminal term. -/
lemma mirrorCPrefixShiftedPenaltyLeInitialPenalty
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {N : ℕ}
    (h_constRange : ∀ n ∈ Finset.range N, t n = t 0) :
    Finset.sum (Finset.range N)
        (fun n ↦ t n * ((g (x n)).toReal - (g (x (n + 1))).toReal)) ≤
      (t 0) * (g (x 0)).toReal := by
  -- Rewrite every prefix stepsize to the initial constant and telescope the scalar difference sum.
  have htelescopeAux :
      ∀ M : ℕ,
        Finset.sum (Finset.range M)
            (fun n ↦ (g (x n)).toReal - (g (x (n + 1))).toReal) =
          (g (x 0)).toReal - (g (x M)).toReal := by
    intro M
    induction M with
    | zero =>
        simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have htelescope :
      Finset.sum (Finset.range N)
          (fun n ↦ (g (x n)).toReal - (g (x (n + 1))).toReal) =
        (g (x 0)).toReal - (g (x N)).toReal := htelescopeAux N
  have hterminal_nonneg : 0 ≤ (g (x N)).toReal := by
    exact EReal.toReal_nonneg (h_nonneg (x N) (h_traj.mem_effective_domain N))
  have ht0_nonneg : 0 ≤ t 0 := le_of_lt (h_traj.stepsize_pos 0)
  calc
    Finset.sum (Finset.range N)
        (fun n ↦ t n * ((g (x n)).toReal - (g (x (n + 1))).toReal)) =
      Finset.sum (Finset.range N)
        (fun n ↦ (t 0) * ((g (x n)).toReal - (g (x (n + 1))).toReal)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [h_constRange n hn]
    _ =
      (t 0) *
        Finset.sum (Finset.range N)
          (fun n ↦ (g (x n)).toReal - (g (x (n + 1))).toReal) := by
            rw [← Finset.mul_sum]
    _ = (t 0) * ((g (x 0)).toReal - (g (x N)).toReal) := by rw [htelescope]
    _ ≤ (t 0) * (g (x 0)).toReal := by
          nlinarith

/-- Helper for Theorem 9.26: on a constant prefix, the weighted sum of unshifted composite
objective gaps is controlled by the shifted Mirror-C estimate from Lemma 9.25. -/
theorem mirror_c_weighted_objective_gap_sum_le_constant_range_prefix
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_constRange : ∀ n ∈ Finset.range N, t n = t 0) :
    Finset.sum (Finset.range N)
        (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
  -- Route correction: keep the difficult summation work on `Finset.range N`, where the imported
  -- shifted-prefix theorem and the constant-prefix penalty telescope line up directly.
  let baseSum :=
    Finset.sum (Finset.range N) (fun n ↦ t n * ((f (x n)).toReal - FOpt))
  let penaltySum :=
    Finset.sum (Finset.range N) (fun n ↦ t n * (g (x n)).toReal)
  let shiftedPenaltySum :=
    Finset.sum (Finset.range N) (fun n ↦ t n * (g (x (n + 1))).toReal)
  have hleft :
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) =
        baseSum + penaltySum := by
    -- Split each finite composite objective value into its `f`- and `g`-parts.
    dsimp [baseSum, penaltySum]
    calc
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) =
        Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal - FOpt) + t n * (g (x n)).toReal) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [mirrorCObjectiveValue_toReal_eq_add
              h_problem.toIsCompositeConvexMinimizationProblem h_traj n]
            ring
      _ = baseSum + penaltySum := by
            rw [Finset.sum_add_distrib]
  have hright :
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) =
        baseSum + shiftedPenaltySum := by
    -- The shifted prefix has the same base term and only moves the penalty index by one step.
    dsimp [baseSum, shiftedPenaltySum]
    calc
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) =
        Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal - FOpt) + t n * (g (x (n + 1))).toReal) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = baseSum + shiftedPenaltySum := by
            rw [Finset.sum_add_distrib]
  have hpenalty_core :
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((g (x n)).toReal - (g (x (n + 1))).toReal)) ≤
        (t 0) * (g (x 0)).toReal := by
    -- The constant-prefix penalty difference telescope is the only new finite-horizon ingredient.
    exact mirrorCPrefixShiftedPenaltyLeInitialPenalty
      (f := f) (g := g) (ω := ω) (x := x) (s := s) (t := t)
      h_nonneg h_traj h_constRange
  have hpenalty :
      penaltySum ≤ (t 0) * (g (x 0)).toReal + shiftedPenaltySum := by
    have hdiff :
        Finset.sum (Finset.range N)
            (fun n ↦ t n * ((g (x n)).toReal - (g (x (n + 1))).toReal)) =
          penaltySum - shiftedPenaltySum := by
      -- Expand the weighted penalty difference into the difference of the two prefix sums.
      dsimp [penaltySum, shiftedPenaltySum]
      calc
        Finset.sum (Finset.range N)
            (fun n ↦ t n * ((g (x n)).toReal - (g (x (n + 1))).toReal)) =
          Finset.sum (Finset.range N)
            (fun n ↦ t n * (g (x n)).toReal - t n * (g (x (n + 1))).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
        _ = penaltySum - shiftedPenaltySum := by
              rw [Finset.sum_sub_distrib]
    rw [hdiff] at hpenalty_core
    nlinarith
  have hshifted :
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
        (t 0) * (g (x 0)).toReal +
          Finset.sum (Finset.range N)
            (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) := by
    -- Compare the unshifted and shifted objective sums through the penalty telescope above.
    rw [hleft, hright]
    nlinarith
  have hpred : (N - 1) + 1 = N := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hN
  have hprefix :
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
        B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
    -- Sum the one-step shifted estimate and telescope the Bregman terms exactly as in
    -- Lemma 9.25, but only over the finite horizon `0, …, N - 1`.
    have hsum_le :
        Finset.sum (Finset.range N)
            (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
          Finset.sum (Finset.range N)
            (fun n ↦
              (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
                ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact mirrorCStepShiftedObjectiveGap_le
        (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (σ := σ)
        (x := x) (s := s) (t := t)
        h_problem.toIsCompositeConvexMinimizationProblem hω hω_diff h_traj hxStar n
    have htelescope :
        Finset.sum (Finset.range N)
            (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) =
          B[ω] xStar (x 0) - B[ω] xStar (x N) := by
      rw [← hpred]
      simpa using
        (by
          induction (N - 1) with
          | zero =>
              simp
          | succ k ih =>
              rw [Finset.sum_range_succ, ih]
              ring :
          Finset.sum (Finset.range ((N - 1) + 1))
              (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) =
            B[ω] xStar (x 0) - B[ω] xStar (x ((N - 1) + 1)))
    have hquadraticSum :
        Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) =
          (1 / (2 * σ)) *
            Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
      calc
        Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) =
          Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) * (1 / (2 * σ))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
        _ =
          (Finset.sum (Finset.range N) fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) *
            (1 / (2 * σ)) := by
              rw [Finset.sum_mul]
        _ =
          (1 / (2 * σ)) *
            Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
              ring
    have hxStar_dom : xStar ∈ effective_domain g :=
      mirrorCOptimalPoint_memEffectiveDomain
        h_problem.toIsCompositeConvexMinimizationProblem hxStar
    have hterminal_nonneg : 0 ≤ B[ω] xStar (x N) := by
      exact bregmanDistance_nonneg_of_mem_subdifferential_domain
        hω xStar (x N) hxStar_dom
        (h_traj.mem_effective_domain N)
        (h_traj.mem_subdifferential_domain N)
        (hω_diff _ (h_traj.mem_subdifferential_domain N))
    calc
      Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) ≤
        Finset.sum (Finset.range N)
          (fun n ↦
            (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
              ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := hsum_le
      _ =
        Finset.sum (Finset.range N)
            (fun n ↦ B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) +
          Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
              rw [Finset.sum_add_distrib]
      _ =
        (B[ω] xStar (x 0) - B[ω] xStar (x N)) +
          Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
              rw [htelescope]
      _ ≤
        B[ω] xStar (x 0) +
          Finset.sum (Finset.range N)
            (fun n ↦ ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) / (2 * σ)) := by
              nlinarith
      _ =
        B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
              rw [hquadraticSum]
  calc
    Finset.sum (Finset.range N)
        (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        Finset.sum (Finset.range N)
          (fun n ↦ t n * ((f (x n)).toReal + (g (x (n + 1))).toReal - FOpt)) := hshifted
    _ ≤
      (t 0) * (g (x 0)).toReal +
        (B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hprefix ((t 0) * (g (x 0)).toReal)
    _ =
      (t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
            ring

/-- Helper for Theorem 9.26: summing the one-step shifted Mirror-C inequality over a constant
prefix yields the finite-horizon weighted objective-gap estimate needed by the theorem. -/
theorem mirror_c_weighted_objective_gap_sum_le_constant_prefix
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_const : ∀ n : Fin N, t n = t 0) :
    Finset.sum Finset.univ
        (fun n : Fin N ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
      (t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
  have h_constRange : ∀ n ∈ Finset.range N, t n = t 0 := by
    -- Transport the `Fin N` constancy hypothesis to the matching `Finset.range N` statement once.
    intro n hn
    exact h_const ⟨n, by simpa using hn⟩
  have hobjective_sum :
      Finset.sum Finset.univ (fun n : Fin N ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) =
        Finset.sum (Finset.range N) (fun n ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) N)
  have hcorrection_sum :
      Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) =
        Finset.sum (Finset.range N) (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) N)
  -- The new `range` theorem contains all of the nontrivial summation work; this theorem only
  -- transports it back to the source-facing `Fin N` surface.
  rw [hobjective_sum, hcorrection_sum]
  exact
    mirror_c_weighted_objective_gap_sum_le_constant_range_prefix
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
      (x := x) (s := s) (t := t)
      h_problem hω hω_diff h_nonneg h_traj hxStar hN h_constRange

/-- Helper for Theorem 9.26: dividing the finite-horizon weighted estimate by the positive prefix
stepsize sum yields the running-best ratio bound on `best_achieved_function_value ... (N - 1)`. -/
theorem mirror_c_best_value_gap_le_constant_prefix
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_const : ∀ n : Fin N, t n = t 0) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x (N - 1) - FOpt ≤
      ((t 0) * (g (x 0)).toReal +
        B[ω] xStar (x 0) +
        (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
        Finset.sum Finset.univ (fun n : Fin N ↦ t n) := by
  let bestGap := best_achieved_function_value (fun y ↦ (f y + g y).toReal) x (N - 1) - FOpt
  let prefixSum := Finset.sum Finset.univ (fun n : Fin N ↦ t n)
  let numerator :=
    (t 0) * (g (x 0)).toReal +
      B[ω] xStar (x 0) +
      (1 / (2 * σ)) *
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))
  let n0 : Fin N := ⟨0, hN⟩
  have hprefix_ge_n0 : t n0 ≤ prefixSum := by
    -- The positive initial stepsize already appears in the finite prefix sum.
    dsimp [prefixSum]
    exact
      Finset.single_le_sum
        (f := fun n : Fin N ↦ t n) (s := Finset.univ) (a := n0)
        (fun n _ ↦ le_of_lt (h_traj.stepsize_pos n))
        (by simp : n0 ∈ Finset.univ)
  have hprefix_ge : t 0 ≤ prefixSum := by
    simpa [n0] using hprefix_ge_n0
  have hprefix_pos : 0 < prefixSum := by
    exact lt_of_lt_of_le (h_traj.stepsize_pos 0) hprefix_ge
  have hpred : (N - 1) + 1 = N := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hN
  have hpointwise :
      ∀ n : Fin N, n ∈ Finset.univ →
        t n * bestGap ≤ t n * ((f (x n) + g (x n)).toReal - FOpt) := by
    intro n hn
    have hbest_le :
        best_achieved_function_value (fun y ↦ (f y + g y).toReal) x (N - 1) ≤
          (f (x n) + g (x n)).toReal := by
      exact best_achieved_function_value_le_objective_value
        (fun y ↦ (f y + g y).toReal) x (N - 1) n
        (by
          simp [hpred])
    have hgap_le : bestGap ≤ (f (x n) + g (x n)).toReal - FOpt := by
      dsimp [bestGap]
      linarith
    exact mul_le_mul_of_nonneg_left hgap_le (le_of_lt (h_traj.stepsize_pos n))
  have hsum_best :
      Finset.sum Finset.univ (fun n : Fin N ↦ t n * bestGap) ≤
        Finset.sum Finset.univ (fun n : Fin N ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) := by
    -- Sum the pointwise running-best comparison over the whole prefix.
    exact Finset.sum_le_sum hpointwise
  have hsum_best_eq :
      Finset.sum Finset.univ (fun n : Fin N ↦ t n * bestGap) = prefixSum * bestGap := by
    dsimp [prefixSum]
    rw [Finset.sum_mul]
  have hweighted :
      Finset.sum Finset.univ
          (fun n : Fin N ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) ≤
        numerator := by
    dsimp [numerator]
    exact mirror_c_weighted_objective_gap_sum_le_constant_prefix
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
      (x := x) (s := s) (t := t) h_problem hω hω_diff h_nonneg h_traj hxStar hN h_const
  have hscaled : prefixSum * bestGap ≤ numerator := by
    -- Combine the summed pointwise bounds with the finite-prefix weighted-gap estimate.
    calc
      prefixSum * bestGap =
        Finset.sum Finset.univ (fun n : Fin N ↦ t n * bestGap) := by
          symm
          exact hsum_best_eq
      _ ≤
        Finset.sum Finset.univ
          (fun n : Fin N ↦ t n * ((f (x n) + g (x n)).toReal - FOpt)) := hsum_best
      _ ≤ numerator := hweighted
  change
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x (N - 1) - FOpt ≤
      numerator / prefixSum
  have hscaled' : bestGap * prefixSum ≤ numerator := by
    simpa [mul_comm] using hscaled
  exact
    (le_div_iff₀ hprefix_pos).2
      (by
        simpa [bestGap, prefixSum, numerator] using hscaled')

-- Proof sketch: apply the fixed-horizon estimate from Lemma 9.25 to a chosen optimal point
-- `xStar ∈ XStar`, use the pointwise Bregman upper bound `B[ω](xStar, x 0) ≤ Theta0`, the
-- initial-feasibility condition `g (x 0) = 0`, and the companion bridge theorem
-- `fixed_iteration_uniform_steps_eq_mirror_c_textbook_stepsize` to identify the source-facing
-- textbook constant rule with the canonical finite-horizon uniform family from Lemma 9.15.
-- Simplifying the resulting ratio gives the standard
-- `Lf * √(2 * Theta0) / (√σ * √N)` bound for the running best objective value.
/-- Theorem 9.26: under the standing composite mirror-descent assumptions of Definition 9.4
together with Definitions 9.5 and 9.6, if `g` is nonnegative on `dom(g)`, if some optimizer
`xStar ∈ X^*` satisfies `B[ω](xStar, x⁰) ≤ Theta0`, if `g(x⁰) = 0`, and if the first `N` Mirror-C
stepsizes are given by the textbook constant value
`√(2 * Theta0 * σ) / (Lf * √N)`, equivalently by the canonical finite-horizon uniform family from
Lemma 9.15, then after `N` iterations the best objective value attained among
`x⁰, …, x^(N-1)` satisfies the fixed-horizon
`O(1 / √N)` estimate. -/
theorem mirror_c_best_value_gap_le_one_div_sqrt_of_constant_stepsizes
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_g0 : g (x 0) = 0)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      ∀ n : Fin N, t n = Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N : ℝ))) :
    best_achieved_function_value (fun y : E ↦ (f y + g y).toReal) x (N - 1) - FOpt ≤
      Lf * Real.sqrt (2 * Theta0) / (Real.sqrt σ * Real.sqrt (N : ℝ)) := by
  let β : ℝ := Lf ^ 2 / (2 * σ)
  let prefixSum := Finset.sum Finset.univ (fun n : Fin N ↦ t n)
  let correction :=
    (1 / (2 * σ)) *
      Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))
  let numerator := (t 0) * (g (x 0)).toReal + B[ω] xStar (x 0) + correction
  let n0 : Fin N := ⟨0, hN⟩
  letI : Nonempty (Fin N) := ⟨n0⟩
  have h_const : ∀ n : Fin N, t n = t 0 := by
    -- The textbook rule is constant on the whole `Fin N` prefix.
    intro n
    rw [h_stepsize n, h_stepsize n0]
  have hbase :=
    mirror_c_best_value_gap_le_constant_prefix
      (f := f) (g := g) (ω := ω) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
      (x := x) (s := s) (t := t) h_problem hω hω_diff h_nonneg h_traj hxStar hN h_const
  have hprefix_ge_n0 : t n0 ≤ prefixSum := by
    -- The positive initial stepsize is one summand of the denominator.
    dsimp [prefixSum]
    exact
      Finset.single_le_sum
        (f := fun n : Fin N ↦ t n) (s := Finset.univ) (a := n0)
        (fun n _ ↦ le_of_lt (h_traj.stepsize_pos n))
        (by simp : n0 ∈ Finset.univ)
  have hprefix_ge : t 0 ≤ prefixSum := by
    simpa [n0] using hprefix_ge_n0
  have hprefix_pos : 0 < prefixSum := by
    exact lt_of_lt_of_le (h_traj.stepsize_pos 0) hprefix_ge
  have hTheta0_pos : 0 < Theta0 := by
    -- The positive initial stepsize forces the square-root numerator in the textbook rule
    -- to be strictly positive, hence `Theta0 > 0`.
    have hden_pos : 0 < Lf * Real.sqrt (N : ℝ) := by
      exact mul_pos h_problem.Lf_pos (by positivity)
    have hsqrt_pos : 0 < Real.sqrt (2 * Theta0 * σ) := by
      have hstep0 : 0 < t 0 := h_traj.stepsize_pos 0
      rw [h_stepsize n0] at hstep0
      have hmul := mul_lt_mul_of_pos_right hstep0 hden_pos
      simpa [hden_pos.ne'] using hmul
    have hinside_pos : 0 < 2 * Theta0 * σ := Real.sqrt_pos.mp hsqrt_pos
    nlinarith [hinside_pos, hω.sigma_pos]
  have hβ_pos : 0 < β := by
    dsimp [β]
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    have hLf_sq_pos : 0 < Lf ^ (2 : ℕ) := by
      nlinarith [h_problem.Lf_pos]
    exact div_pos hLf_sq_pos htwoσ_pos
  have hsum_le :
      Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
        Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := by
    -- Bound each selected subgradient norm by `Lf` before comparing the correction numerators.
    refine Finset.sum_le_sum ?_
    intro n hn
    have hs_norm : ‖s n‖ ≤ Lf :=
      h_problem.subgradient_norm_le (h_traj.mem_effective_domain n) (h_traj.subgradient_mem n)
    have hs_sq : ‖s n‖ ^ (2 : ℕ) ≤ Lf ^ (2 : ℕ) := by
      nlinarith [hs_norm, norm_nonneg (s n), h_problem.Lf_pos]
    exact mul_le_mul_of_nonneg_left hs_sq (sq_nonneg (t n))
  have hσ_nonneg : 0 ≤ 1 / (2 * σ) := by
    have htwoσ_pos : 0 < 2 * σ := by
      nlinarith [hω.sigma_pos]
    exact le_of_lt (one_div_pos.mpr htwoσ_pos)
  have hcorr_le_beta :
      correction ≤ β * Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ)) := by
    -- Rewrite the correction with the uniform `Lf` bound so the numerator matches the
    -- fixed-iteration objective from Lemma 9.15.
    have hscaled_le :
        correction ≤
          (1 / (2 * σ)) *
            Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := by
      dsimp [correction]
      exact mul_le_mul_of_nonneg_left hsum_le hσ_nonneg
    calc
      correction ≤
        (1 / (2 * σ)) *
          Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ) * Lf ^ (2 : ℕ)) := hscaled_le
      _ =
        (1 / (2 * σ)) *
          (Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ)) * Lf ^ (2 : ℕ)) := by
            rw [Finset.sum_mul]
      _ = β * Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ)) := by
            dsimp [β]
            ring
  have hg0_toReal : (g (x 0)).toReal = 0 := by
    simp [h_g0]
  have hhead_le : (t 0) * (g (x 0)).toReal + B[ω] xStar (x 0) ≤ Theta0 := by
    simpa [hg0_toReal] using h_bregman_upper
  have hnum_le :
      numerator ≤ Theta0 + β * Finset.sum Finset.univ (fun n : Fin N ↦ (t n) ^ (2 : ℕ)) := by
    -- The initial penalty vanishes and the remaining terms fit the fixed-iteration numerator.
    dsimp [numerator]
    exact add_le_add hhead_le hcorr_le_beta
  have hratio :
      numerator / prefixSum ≤ fixed_iteration_objective Theta0 β (fun n : Fin N ↦ t n) := by
    -- Divide by the positive denominator to turn the numerator bound into the canonical ratio
    -- objective from Lemma 9.15.
    have hdiv := div_le_div_of_nonneg_right hnum_le (le_of_lt hprefix_pos)
    simpa [prefixSum, β, fixed_iteration_objective] using hdiv
  have h_uniform_steps :
      (fun n : Fin N ↦ t n) = fixed_iteration_uniform_steps (Fin N) Theta0 β := by
    -- The source-facing textbook stepsize is exactly the canonical uniform family on `Fin N`.
    simpa [β] using
      (mirrorCRestrictedSteps_eq_fixedIterationUniformSteps
        (Lf := Lf) (σ := σ) Theta0 h_stepsize h_problem.Lf_pos hω.sigma_pos)
  have hvalue :
      fixed_iteration_objective Theta0 β (fun n : Fin N ↦ t n) =
        2 * (Real.sqrt (Theta0 * β) / Real.sqrt (N : ℝ)) := by
    -- Evaluate the fixed-iteration objective on the canonical uniform minimizer.
    rw [h_uniform_steps]
    simpa [β, Fintype.card_fin, Real.sqrt_div (by positivity : 0 ≤ (N : ℝ))] using
      (fixed_iteration_objective_uniform_step_value
        (ι := Fin N) (α := Theta0) (β := β) hTheta0_pos hβ_pos)
  have hpred : (N - 1) + 1 = N := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hN
  have htextbook :
      2 * (Real.sqrt (Theta0 * β) / Real.sqrt (N : ℝ)) =
        Lf * Real.sqrt (2 * Theta0) / (Real.sqrt σ * Real.sqrt (N : ℝ)) := by
    -- Reuse the Chapter 9 scalar simplification already proved for constant-step mirror descent.
    have hsqrt_two_theta : Real.sqrt (2 * Theta0) = Real.sqrt 2 * Real.sqrt Theta0 := by
      have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      rw [Real.sqrt_mul htwo_nonneg Theta0]
    have hbound1 :
        2 * Real.sqrt (Theta0 * β / (((N - 1) + 1 : ℕ) : ℝ)) =
          Lf * (Real.sqrt 2 * Real.sqrt Theta0) /
            Real.sqrt (σ * ((((N - 1) + 1 : ℕ) : ℝ))) := by
      simpa [β, hsqrt_two_theta] using
        (mirrorDescentUniformObjectiveValueEqTextbookBound
          Theta0 Lf σ (N - 1) hTheta0_pos h_problem.Lf_pos hω.sigma_pos)
    have hbound :
        2 * (Real.sqrt (Theta0 * β) / Real.sqrt (N : ℝ)) =
          Lf * (Real.sqrt 2 * Real.sqrt Theta0) / Real.sqrt (σ * (N : ℝ)) := by
      simpa [hpred, Real.sqrt_div (by positivity : 0 ≤ (N : ℝ))] using hbound1
    calc
      2 * (Real.sqrt (Theta0 * β) / Real.sqrt (N : ℝ)) =
        Lf * (Real.sqrt 2 * Real.sqrt Theta0) / Real.sqrt (σ * (N : ℝ)) := hbound
      _ = Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N : ℝ)) := by
            rw [← hsqrt_two_theta]
      _ = Lf * Real.sqrt (2 * Theta0) / (Real.sqrt σ * Real.sqrt (N : ℝ)) := by
            rw [Real.sqrt_mul (le_of_lt hω.sigma_pos) (N : ℝ)]
  calc
    best_achieved_function_value (fun y : E ↦ (f y + g y).toReal) x (N - 1) - FOpt
      ≤ numerator / prefixSum := by
          simpa [prefixSum, numerator, correction] using hbase
    _ ≤ fixed_iteration_objective Theta0 β (fun n : Fin N ↦ t n) := hratio
    _ = 2 * (Real.sqrt (Theta0 * β) / Real.sqrt (N : ℝ)) := hvalue
    _ = Lf * Real.sqrt (2 * Theta0) / (Real.sqrt σ * Real.sqrt (N : ℝ)) := htextbook

end
