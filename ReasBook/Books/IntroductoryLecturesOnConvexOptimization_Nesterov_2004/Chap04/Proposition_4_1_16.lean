/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

variable {X : Type u}

/- Proposition 4.1.16 lies in the finite-horizon conservative cubic-regularization backtracking
complexity domain.

Sampled owner declarations:
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Definition_4_1_16`, the canonical
  acceptance-set owner and view;
* `CubicRegularizationBacktracking.acceptingExponents`,
  `CubicRegularizationBacktracking.index`, and
  `CubicRegularizationBacktracking.nextRegularization` in `Definition_4_1_17`, the chapter owner
  API for the accepted-exponent set, its least element, and the conservative update
  `M_(k+1) = max {L₀, hat M_k / 2}`;
* `CubicRegularizationMethod.regularization_mem_Icc` in `Algorithm_4_1_5`, the nearby chapter
  pattern where regularization bounds remain theorem-level trajectory data rather than a second
  local owner.

Best owner abstraction:
* source-facing: the finite-horizon conservative complexity statement for a regularization
  schedule `M₀, …, M_(N+1)` and iterate sequence `x₀, x₁, …`;
* core/canonical: `RegularizedNewton.acceptingParameters` for automatic acceptance and
  `CubicRegularizationBacktracking.nextRegularization` for the conservative parameter update;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`, which records the
  witness-free conservative one-step update used by the finite-horizon trajectory hypotheses.

Primitive data:
* the iterate sequence `x₀, x₁, …`;
* the regularization sequence `M₀, M₁, …`;
* the initial bound `M₀ ∈ [L₀, 2L]`;
* the theorem-level conservative update law
  `IsNextRegularization ... x_k M_k L₀ M_(k+1)`.

Derived API:
* automatic acceptance above `L`, phrased directly through `acceptingParameters`;
* existence of accepted exponents at each step under the automatic-acceptance hypothesis;
* propagated interval bounds, the intrinsic endpoint-ratio control on total backtracking
  increments, and the resulting conservative bound on computed trial maps.

Source/core/bridge triage:
* source-facing: the total-backtracking and total-trial-mapping bounds in Proposition 4.1.16;
* core/canonical: `RegularizedNewton.acceptingParameters` and
  `CubicRegularizationBacktracking.nextRegularization`;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`.
-/

namespace CubicRegularizationBacktracking

open RegularizedNewton

variable {f : X → ℝ} {stepMap : ℝ → X → X} {modelValue : ℝ → X → ℝ}
variable {x : ℕ → X} {regularization : ℕ → ℝ} {L0 L : ℝ} {N : ℕ}

/-- The initial interval condition `M₀ ∈ [L₀, 2L]` together with `L₀ > 0` already forces
`L > 0`. -/
theorem L_pos_of_regularization_zero_mem_Icc
    (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
    (hL0 : 0 < L0) :
    0 < L := by
  have hM0_pos : 0 < regularization 0 :=
    lt_of_lt_of_le hL0 hregularization_zero_mem_Icc.1
  have hM0_le : regularization 0 ≤ 2 * L :=
    hregularization_zero_mem_Icc.2
  linarith

section AutomaticAcceptanceAboveL

variable
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hL0 : 0 < L0)

include hautomatic hL0

/-- If the current regularization parameter lies in `[L₀, 2L]`, then automatic acceptance above
`L` produces some accepted backtracking exponent at that step. -/
theorem acceptingExponents_nonempty_of_mem_Icc
    {k : ℕ} (hk : k ≤ N)
    (hk_regularization : regularization k ∈ Set.Icc L0 (2 * L)) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := by
  -- The interval hypothesis gives the current regularization positivity needed for rescaling.
  have hk_regularization_pos : 0 < regularization k :=
    lt_of_lt_of_le hL0 hk_regularization.1
  -- Choose a dyadic trial parameter above the automatic-acceptance threshold `L`.
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (L / regularization k) one_lt_two
  have hL_le_trial : L ≤ (2 : ℝ) ^ i * regularization k := by
    exact ((div_lt_iff₀ hk_regularization_pos).1 hi).le
  -- Any tested parameter above `L` is accepted by hypothesis.
  exact ⟨i, hautomatic k hk hL_le_trial⟩

end AutomaticAcceptanceAboveL

section FiniteHorizon

variable
  (htrajectory :
    ∀ i : Fin (N + 1),
      IsNextRegularization
        f stepMap modelValue (x i.1) (regularization i.1) L0
        (regularization (i.1 + 1)))
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
  (hL0 : 0 < L0)

include htrajectory hautomatic hregularization_zero_mem_Icc hL0

/-- Helper for Proposition 4.1.16: once the least accepted dyadic parameter is chosen at step
`k`, dividing it by `2` never exceeds the automatic-acceptance threshold `L`. -/
theorem acceptedRegularization_div_two_le_L_of_mem_Icc
    {k : ℕ} (hk : k ≤ N)
    (hk_regularization : regularization k ∈ Set.Icc L0 (2 * L))
    (hAccepts : (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty) :
    acceptedRegularization f stepMap modelValue (x k) (regularization k) hAccepts / 2 ≤ L := by
  classical
  by_cases hindex_zero :
      index f stepMap modelValue (x k) (regularization k) hAccepts = 0
  · -- If the least accepted exponent is `0`, the accepted parameter is just `M_k`.
    have hhalf_le : regularization k / 2 ≤ L := by
      nlinarith [hk_regularization.2]
    simpa [acceptedRegularization, hindex_zero] using hhalf_le
  · -- Otherwise the previous dyadic trial is rejected, so it must still lie below `L`.
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hindex_zero
    have hj_not_mem :
        j ∉ acceptingExponents f stepMap modelValue (x k) (regularization k) := by
      apply not_mem_acceptingExponents_of_lt_index
        f stepMap modelValue (x k) (regularization k) hAccepts
      simp [hj]
    have hj_lt_L : (2 : ℝ) ^ j * regularization k < L := by
      by_contra hj_ge_L
      have hj_ge_L' : L ≤ (2 : ℝ) ^ j * regularization k :=
        not_lt.mp hj_ge_L
      exact hj_not_mem (hautomatic k hk hj_ge_L')
    calc
      acceptedRegularization f stepMap modelValue (x k) (regularization k) hAccepts / 2
          = (((2 : ℝ) ^ j) * regularization k) := by
              rw [acceptedRegularization, hj, pow_succ]
              ring
      _ ≤ L := hj_lt_L.le

-- Proof sketch: start from `hregularization_zero_mem_Icc`, derive accepted exponents from
-- `hautomatic`, and use `htrajectory` together with the minimality of the least
-- accepted exponent to show `hat M_k < 2L`; then `nextRegularization` keeps the next parameter
-- inside `[L₀, L] ⊆ [L₀, 2L]`.
/-- Under automatic acceptance above `L`, every regularization parameter produced by the canonical
conservative backtracking update up to index `N + 1` stays in the admissible interval
`[L₀, 2L]`. -/
theorem regularization_mem_Icc
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ∈ Set.Icc L0 (2 * L) := by
  have hL_pos : 0 < L :=
    L_pos_of_regularization_zero_mem_Icc hregularization_zero_mem_Icc hL0
  have hL0_le_two_mul_L : L0 ≤ 2 * L :=
    le_trans hregularization_zero_mem_Icc.1 hregularization_zero_mem_Icc.2
  intro k hk
  induction' k with k ih
  · -- The zeroth parameter satisfies the interval condition by assumption.
    simpa using hregularization_zero_mem_Icc
  · -- Propagate the interval bound through the witness-free conservative update.
    have hk_le_N : k ≤ N :=
      Nat.succ_le_succ_iff.mp hk
    have hk_mem_Icc : regularization k ∈ Set.Icc L0 (2 * L) :=
      ih (le_trans hk_le_N (Nat.le_succ N))
    have hAccepts :
        (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty :=
      acceptingExponents_nonempty_of_mem_Icc
        hautomatic hL0 hk_le_N hk_mem_Icc
    have hnext_eq :
        regularization (k + 1) =
          nextRegularization f stepMap modelValue (x k) (regularization k) L0 hAccepts :=
      IsNextRegularization.eq
        (f := f) (stepMap := stepMap) (modelValue := modelValue)
        (xk := x k) (Mk := regularization k)
        (htrajectory ⟨k, Nat.lt_succ_iff.mpr hk_le_N⟩) hAccepts
    have hupper_half :
        acceptedRegularization f stepMap modelValue (x k) (regularization k) hAccepts / 2 ≤
          2 * L := by
      exact le_trans
        (acceptedRegularization_div_two_le_L_of_mem_Icc
          htrajectory hautomatic hregularization_zero_mem_Icc hL0
          hk_le_N hk_mem_Icc hAccepts)
        (by nlinarith [hL_pos])
    constructor
    · -- The update rule always keeps the next regularization estimate above `L₀`.
      rw [hnext_eq]
      exact le_nextRegularization f stepMap modelValue (x k) (regularization k) L0 hAccepts
    · -- The same update takes values in the maximum of two quantities already bounded by `2L`.
      rw [hnext_eq, nextRegularization]
      exact max_le hL0_le_two_mul_L hupper_half

/-- Every regularization parameter produced up to index `N + 1` stays bounded by `2L`. -/
theorem regularization_le_two_mul_L
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ≤ 2 * L := by
  intro k hk
  exact (regularization_mem_Icc
    htrajectory hautomatic hregularization_zero_mem_Icc hL0 k hk).2

/-- Under the automatic-acceptance hypothesis, every step `k ≤ N` admits an accepted backtracking
exponent. -/
theorem acceptingExponents_nonempty
    {k : ℕ} (hk : k ≤ N) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := by
  exact acceptingExponents_nonempty_of_mem_Icc
    hautomatic hL0 hk
    (regularization_mem_Icc
      htrajectory hautomatic hregularization_zero_mem_Icc hL0
      k (le_trans hk (Nat.le_succ N)))

/-- The total number of backtracking increments accumulated from steps `0` through `N`. -/
def totalBacktrackingIncrements
    :
    ℕ :=
  ∑ i : Fin (N + 1),
    index f stepMap modelValue (x i) (regularization i)
      (acceptingExponents_nonempty
        htrajectory hautomatic hregularization_zero_mem_Icc hL0
        (Nat.lt_succ_iff.mp i.2))

/-- The total number of evaluated trial mappings `T_M` over the first `N + 1` iterations equals
one trial per iteration plus the extra backtracking increments. -/
def totalComputedMappings
    :
    ℕ :=
  (N + 1) +
    totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0

-- Proof sketch: for each step `k`, the conservative update law gives
-- `2^(i_k - 1) M_k ≤ M_(k+1)`, so the least accepted exponent satisfies
-- `i_k ≤ 1 + log₂ (M_(k+1) / M_k)`. Summing these inequalities over `k = 0, …, N` telescopes the
-- logarithmic term to the endpoint ratio `M_(N+1) / M₀`.
/-- Helper for Proposition 4.1.16: the base-`2` logarithms of consecutive regularization ratios
collapse to the endpoint ratio. -/
theorem sum_range_logb_ratio_eq_logb_endpoint_ratio
    (hregularization_pos : ∀ k : ℕ, k ≤ N + 1 → 0 < regularization k) :
    Finset.sum (Finset.range (N + 1))
      (fun k ↦ Real.logb 2 (regularization (k + 1) / regularization k)) =
        Real.logb 2 (regularization (N + 1) / regularization 0) := by
  -- Rewrite each ratio logarithm as a difference of endpoint logarithms.
  calc
    Finset.sum (Finset.range (N + 1))
        (fun k ↦ Real.logb 2 (regularization (k + 1) / regularization k)) =
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.logb 2 (regularization (k + 1)) -
              Real.logb 2 (regularization k)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simpa using
                (Real.logb_div (b := 2)
                  (hregularization_pos (k + 1)
                    (Nat.succ_le_succ <| Nat.le_of_lt_succ <| Finset.mem_range.mp hk)).ne'
                  (hregularization_pos k
                    (Nat.le_trans (Nat.le_of_lt_succ <| Finset.mem_range.mp hk) <|
                      Nat.le_succ N)).ne')
    _ = Real.logb 2 (regularization (N + 1)) - Real.logb 2 (regularization 0) := by
          have htel :
              Finset.sum (Finset.range (N + 1))
                (fun k ↦ Real.logb 2 (regularization k) -
                  Real.logb 2 (regularization (k + 1))) =
                Real.logb 2 (regularization 0) -
                  Real.logb 2 (regularization (N + 1)) := by
            simpa using Finset.sum_range_sub' (fun k ↦ Real.logb 2 (regularization k)) (N + 1)
          -- Negating the forward telescoping identity flips every logarithmic difference.
          have htel_neg :
              Finset.sum (Finset.range (N + 1))
                (fun k ↦ -(Real.logb 2 (regularization k) -
                  Real.logb 2 (regularization (k + 1)))) =
                -(Real.logb 2 (regularization 0) -
                  Real.logb 2 (regularization (N + 1))) := by
            simpa [Finset.sum_neg_distrib] using congrArg (fun t : ℝ ↦ -t) htel
          simpa [neg_sub] using htel_neg
    _ = Real.logb 2 (regularization (N + 1) / regularization 0) := by
          symm
          simpa using
            (Real.logb_div (b := 2)
              (hregularization_pos (N + 1) (Nat.le_refl _)).ne'
              (hregularization_pos 0 (Nat.zero_le _)).ne')

/-- Helper for Proposition 4.1.16: each least accepted dyadic exponent is bounded by one plus the
base-`2` logarithm of the next/current regularization ratio. -/
theorem index_le_one_add_logb_ratio_of_mem_Icc
    {k : ℕ} (hk : k ≤ N)
    (hk_regularization : regularization k ∈ Set.Icc L0 (2 * L))
    (hAccepts : (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty) :
    (index f stepMap modelValue (x k) (regularization k) hAccepts : ℝ) ≤
      1 + Real.logb 2 (regularization (k + 1) / regularization k) := by
  have hk_regularization_pos : 0 < regularization k :=
    lt_of_lt_of_le hL0 hk_regularization.1
  have hnext_eq :
      regularization (k + 1) =
        nextRegularization f stepMap modelValue (x k) (regularization k) L0 hAccepts :=
    IsNextRegularization.eq
      (f := f) (stepMap := stepMap) (modelValue := modelValue)
      (xk := x k) (Mk := regularization k)
      (htrajectory ⟨k, Nat.lt_succ_iff.mpr hk⟩) hAccepts
  have hnext_ge_L0 : L0 ≤ regularization (k + 1) := by
    rw [hnext_eq]
    exact le_nextRegularization f stepMap modelValue (x k) (regularization k) L0 hAccepts
  have hnext_pos : 0 < regularization (k + 1) :=
    lt_of_lt_of_le hL0 hnext_ge_L0
  have haccepted_le_two_next :
      acceptedRegularization f stepMap modelValue (x k) (regularization k) hAccepts ≤
        2 * regularization (k + 1) := by
    have hhalf_le :
        acceptedRegularization f stepMap modelValue (x k) (regularization k) hAccepts / 2 ≤
          regularization (k + 1) := by
      rw [hnext_eq, nextRegularization]
      exact le_max_right _ _
    nlinarith
  have hpow_le :
      (2 : ℝ) ^ index f stepMap modelValue (x k) (regularization k) hAccepts ≤
        2 * (regularization (k + 1) / regularization k) := by
    have hpow_mul :
        (2 : ℝ) ^ index f stepMap modelValue (x k) (regularization k) hAccepts *
            regularization k ≤
          2 * regularization (k + 1) := by
      simpa [acceptedRegularization, mul_comm, mul_left_comm, mul_assoc] using
        haccepted_le_two_next
    -- Divide by the positive current regularization to expose the endpoint ratio.
    have hdiv :
        (2 : ℝ) ^ index f stepMap modelValue (x k) (regularization k) hAccepts ≤
          (2 * regularization (k + 1)) / regularization k :=
      (le_div_iff₀ hk_regularization_pos).2 hpow_mul
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hlog_le :
      (index f stepMap modelValue (x k) (regularization k) hAccepts : ℝ) ≤
        Real.logb 2 (2 * (regularization (k + 1) / regularization k)) := by
    have hpow_rpow :
        (2 : ℝ) ^
            ((index f stepMap modelValue (x k) (regularization k) hAccepts : ℕ) : ℝ) ≤
          2 * (regularization (k + 1) / regularization k) := by
      simpa [Real.rpow_natCast] using hpow_le
    exact
      (Real.le_logb_iff_rpow_le (b := 2)
        (x := (index f stepMap modelValue (x k) (regularization k) hAccepts : ℝ))
        (y := 2 * (regularization (k + 1) / regularization k))
        one_lt_two
        (mul_pos zero_lt_two (div_pos hnext_pos hk_regularization_pos))).2
        hpow_rpow
  -- Normalize the logarithm of the product `2 * (M_(k+1) / M_k)`.
  calc
    (index f stepMap modelValue (x k) (regularization k) hAccepts : ℝ) ≤
        Real.logb 2 (2 * (regularization (k + 1) / regularization k)) := hlog_le
    _ = 1 + Real.logb 2 (regularization (k + 1) / regularization k) := by
          rw [Real.logb_mul (b := 2) (by norm_num)
            (div_pos hnext_pos hk_regularization_pos).ne', Real.logb_self_eq_one one_lt_two]

/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus the base-`2` logarithm of the endpoint regularization ratio. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 (regularization (N + 1) / regularization 0) := by
  have hregularization_pos : ∀ k : ℕ, k ≤ N + 1 → 0 < regularization k := by
    intro k hk
    exact lt_of_lt_of_le hL0
      (regularization_mem_Icc
        htrajectory hautomatic hregularization_zero_mem_Icc hL0 k hk).1
  -- First bound the `Fin`-indexed sum pointwise, then rewrite only the logarithmic part to a
  -- `range` sum for telescoping.
  rw [totalBacktrackingIncrements, Nat.cast_sum]
  calc
    (∑ i : Fin (N + 1),
        (index f stepMap modelValue (x i) (regularization i)
          (acceptingExponents_nonempty
            htrajectory hautomatic hregularization_zero_mem_Icc hL0
            (Nat.le_of_lt_succ i.2)) : ℝ)) ≤
        ∑ i : Fin (N + 1),
          (1 + Real.logb 2 (regularization (i.1 + 1) / regularization i.1)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hk_le_N : i.1 ≤ N :=
            Nat.le_of_lt_succ i.2
          exact index_le_one_add_logb_ratio_of_mem_Icc
            htrajectory hautomatic hregularization_zero_mem_Icc hL0
            hk_le_N
            (regularization_mem_Icc
              htrajectory hautomatic hregularization_zero_mem_Icc hL0
              i.1 (le_trans hk_le_N (Nat.le_succ N)))
            (acceptingExponents_nonempty
              htrajectory hautomatic hregularization_zero_mem_Icc hL0 hk_le_N)
    _ = (∑ _ : Fin (N + 1), (1 : ℝ)) +
          ∑ i : Fin (N + 1),
            Real.logb 2 (regularization (i.1 + 1) / regularization i.1) := by
          rw [Finset.sum_add_distrib]
    _ = (N + 1 : ℝ) +
          ∑ i : Fin (N + 1),
            Real.logb 2 (regularization (i.1 + 1) / regularization i.1) := by
          rw [Fin.sum_univ_eq_sum_range (fun _ ↦ (1 : ℝ)) (N + 1)]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp
    _ = (N + 1 : ℝ) +
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ Real.logb 2 (regularization (k + 1) / regularization k)) := by
          rw [Fin.sum_univ_eq_sum_range
            (fun k ↦ Real.logb 2 (regularization (k + 1) / regularization k))
            (N + 1)]
    _ = (N + 1 : ℝ) + Real.logb 2 (regularization (N + 1) / regularization 0) := by
          rw [sum_range_logb_ratio_eq_logb_endpoint_ratio
            htrajectory hautomatic hregularization_zero_mem_Icc hL0 hregularization_pos]

-- Proof sketch: combine
-- `totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio` with the propagated interval
-- bounds `regularization 0 ≥ L₀` and `regularization (N + 1) ≤ 2L`.
/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus `log₂ (2L / L₀)`. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := by
  have hL_pos : 0 < L :=
    L_pos_of_regularization_zero_mem_Icc hregularization_zero_mem_Icc hL0
  have hregularization_zero_pos : 0 < regularization 0 :=
    lt_of_lt_of_le hL0 hregularization_zero_mem_Icc.1
  have hendpoint_ratio_le :
      regularization (N + 1) / regularization 0 ≤ (2 * L) / L0 := by
    have hstep1 :
        regularization (N + 1) / regularization 0 ≤ regularization (N + 1) / L0 := by
      exact div_le_div_of_nonneg_left
        (le_of_lt <| lt_of_lt_of_le hL0 <|
          (regularization_mem_Icc
            htrajectory hautomatic hregularization_zero_mem_Icc hL0 (N + 1) (Nat.le_refl _)).1)
        hL0
        hregularization_zero_mem_Icc.1
    have hstep2 :
        regularization (N + 1) / L0 ≤ (2 * L) / L0 := by
      exact div_le_div_of_nonneg_right
        (regularization_le_two_mul_L
          htrajectory hautomatic hregularization_zero_mem_Icc hL0 (N + 1) (Nat.le_refl _))
        hL0.le
    exact le_trans hstep1 hstep2
  have hendpoint_ratio_pos : 0 < regularization (N + 1) / regularization 0 := by
    exact div_pos
      (lt_of_lt_of_le hL0
        (regularization_mem_Icc
          htrajectory hautomatic hregularization_zero_mem_Icc hL0 (N + 1) (Nat.le_refl _)).1)
      hregularization_zero_pos
  calc
    (totalBacktrackingIncrements
        htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
        (N + 1 : ℝ) + Real.logb 2 (regularization (N + 1) / regularization 0) :=
      totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio
        htrajectory hautomatic hregularization_zero_mem_Icc hL0
    _ ≤ (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left
              (Real.logb_le_logb_of_le (b := 2) one_lt_two
                hendpoint_ratio_pos hendpoint_ratio_le)
              (N + 1 : ℝ)

-- Proof sketch: by definition,
-- `totalComputedMappings = (N + 1) + totalBacktrackingIncrements`. Apply
-- `totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio` and rearrange the constants.
/-- Proposition 4.1.16: for the conservative backtracking rule, if the acceptance inequality holds
for every tested parameter `M ≥ L` and the initial regularization satisfies `M₀ ∈ [L₀, 2L]`,
then the total number of computed trial mappings `T_M` through iteration `N` is at most
`2 (N + 1) + log₂ (2L / L₀)`. -/
theorem totalComputedMappings_le_conservative_backtracking_cost_bound
    :
    (totalComputedMappings
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (2 : ℝ) * (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := by
  -- Expand the total-count definition and then insert the backtracking bound.
  calc
    (totalComputedMappings
        htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) =
        (N + 1 : ℝ) +
          (totalBacktrackingIncrements
            htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) := by
          simp [totalComputedMappings]
    _ ≤ (N + 1 : ℝ) +
          ((N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0)) := by
          gcongr
          exact totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio
            htrajectory hautomatic hregularization_zero_mem_Icc hL0
    _ = (2 : ℝ) * (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := by
          ring

end FiniteHorizon

end CubicRegularizationBacktracking
