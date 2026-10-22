/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_51
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/- Layering for Exercise 17.6.4:
- primitive/source-facing data: the explicit singleton-mass function for the candidate invariant
  measure of Fig. 17.2;
- core/canonical owner: `Kernel.Invariant` for stationarity of that measure;
- source-facing chain-level clauses: the three recurrence/transience branches are proved locally
  from the Chapter 17 owners `Theorem_17_37`, `Theorem_17_51`, and the explicit matrix algebra
  below;
- bridge/view for the exceptional boundary `r = 0`: the sharper owner-level state
  classification is recorded locally through `IsPositiveRecurrentState` and `IsTransientState`. -/

/-- Transition matrix for Exercise 17.6.4: the nearest-neighbor transition matrix encoded by
Fig. 17.2, with
deterministic jump `0 → 1` and, for `n + 1`, left jump probability `1 - r` and right jump
probability `r`. -/
def figure17_2TransitionMatrix (r : Set.Icc (0 : ℝ≥0∞) 1) : ℕ → ℕ → ℝ≥0∞
  | 0, 1 => 1
  | 0, _ => 0
  | n + 1, m =>
      if m = n then 1 - (r : ℝ≥0∞) else if m = n + 2 then (r : ℝ≥0∞) else 0

/-- The singleton-mass function of the weighted counting measure used in the invariant-measure
calculation for the reflected nearest-neighbor chain of Fig. 17.2. It gives mass `1 - r` to `0`
and mass `(r / (1 - r))^n` to `n + 1`. -/
def figure17_2InvariantMass (r : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 1 - r
  | n + 1 => (r / (1 - r)) ^ n

/-- The weighted counting measure on `ℕ` with singleton masses given by
`figure17_2InvariantMass r`. -/
def figure17_2InvariantMeasure (r : ℝ≥0∞) : Measure ℕ :=
  Measure.count.withDensity (figure17_2InvariantMass r)

/-- Helper for Exercise 17.6.4: in `ℝ≥0∞`, subtracting `1 / 2` from `1` leaves `1 / 2`. -/
theorem figure17_2_one_sub_half : 1 - (1 / 2 : ℝ≥0∞) = 1 / 2 := by
  have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
    norm_num
  have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    calc
      (1 / 2 : ℝ≥0∞) + 1 / 2
          = ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := by
              rw [hhalf_eq]
      _ = ENNReal.ofReal (1 : ℝ) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num
      _ = 1 := by norm_num
  -- Proof comment: rewrite `1` as `1 / 2 + 1 / 2` and cancel one copy of `1 / 2`.
  exact
    ENNReal.eq_sub_of_add_eq (a := (1 / 2 : ℝ≥0∞)) (c := (1 / 2 : ℝ≥0∞)) (b := 1)
      (by simp) hhalf |>.symm

-- Proof sketch: on the discrete state space `ℕ`, `Measure.count.withDensity` evaluates on a
-- singleton `{n}` as the density value at `n`.
/-- The weighted counting measure `figure17_2InvariantMeasure r` has singleton mass
`figure17_2InvariantMass r n` at `{n}`. -/
theorem figure17_2InvariantMeasure_apply_singleton (r : ℝ≥0∞) (n : ℕ) :
    figure17_2InvariantMeasure r {n} = figure17_2InvariantMass r n := by
  -- Proof comment: `Measure.count.withDensity` integrates the singleton indicator against the
  -- counting measure, so only the density value at `n` survives.
  rw [figure17_2InvariantMeasure, withDensity_apply _ (measurableSet_singleton n),
    ← lintegral_indicator (measurableSet_singleton n), lintegral_count]
  simp

/-- Helper for Exercise 17.6.4: the total mass of `figure17_2InvariantMeasure r` is the boundary
mass at `0` plus the geometric tail from the states `n + 1`. -/
theorem figure17_2InvariantMeasure_univ_eq_series (r : ℝ≥0∞) :
    figure17_2InvariantMeasure r Set.univ =
      figure17_2InvariantMass r 0 + ∑' n : ℕ, figure17_2InvariantMass r (n + 1) := by
  -- Proof comment: evaluate the weighted counting measure on `Set.univ`, rewrite the count
  -- integral as a series, and then split off the `n = 0` term.
  calc
    figure17_2InvariantMeasure r Set.univ
      = ∫⁻ y, figure17_2InvariantMass r y ∂Measure.count := by
          rw [figure17_2InvariantMeasure, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ]
    _ = ∑' y : ℕ, figure17_2InvariantMass r y := by
          rw [lintegral_count]
    _ = figure17_2InvariantMass r 0 + ∑' n : ℕ, figure17_2InvariantMass r (n + 1) := by
          rw [tsum_eq_zero_add' ENNReal.summable]

/-- Helper for Exercise 17.6.4: in the left-drift regime `r < 1 / 2`, the geometric ratio
`r / (1 - r)` is strictly smaller than `1`. -/
theorem figure17_2InvariantRatio_lt_one_of_lt_half
    {r : ℝ≥0∞} (hrhalf : r < 1 / 2) :
    r / (1 - r) < 1 := by
  have hr1 : r < 1 := lt_trans hrhalf (by norm_num)
  have hden_ne_zero : 1 - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
  have hden_ne_top : 1 - r ≠ ⊤ := by
    exact ne_of_lt (lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp)))
  have hhalf_le : (1 / 2 : ℝ≥0∞) ≤ 1 - r := by
    calc
      (1 / 2 : ℝ≥0∞) = 1 - (1 / 2 : ℝ≥0∞) := figure17_2_one_sub_half.symm
      _ ≤ 1 - r := by
            exact tsub_le_tsub_left (le_of_lt hrhalf) 1
  have hlt : r < 1 - r := lt_of_lt_of_le hrhalf hhalf_le
  -- Proof comment: once `r < 1 - r`, the quotient inequality is the direct `div_lt_iff` rewrite.
  rw [ENNReal.div_lt_iff (Or.inl hden_ne_zero) (Or.inl hden_ne_top)]
  simpa using hlt

/-- Helper for Exercise 17.6.4: once `r` is no longer smaller than `1 / 2`, the geometric ratio
`r / (1 - r)` is at least `1`. -/
theorem figure17_2InvariantRatio_ge_one_of_not_lt_half
    {r : ℝ≥0∞} (hrhalf : ¬ r < 1 / 2) :
    1 ≤ r / (1 - r) := by
  by_cases hr1 : r < 1
  · have hhalf_le : (1 / 2 : ℝ≥0∞) ≤ r := le_of_not_gt hrhalf
    have hden_pos : 0 < 1 - r := tsub_pos_of_lt hr1
    have hden_ne_zero : 1 - r ≠ 0 := ne_of_gt hden_pos
    have hden_ne_top : 1 - r ≠ ⊤ := by
      exact ne_of_lt (lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp)))
    have hden_le_half : 1 - r ≤ 1 / 2 := by
      calc
        1 - r ≤ 1 - (1 / 2 : ℝ≥0∞) := by
            exact tsub_le_tsub_left hhalf_le 1
        _ = 1 / 2 := figure17_2_one_sub_half
    have hden_le_r : 1 - r ≤ r := le_trans hden_le_half hhalf_le
    -- Proof comment: `1 ≤ r / (1 - r)` is the quotient form of `1 - r ≤ r`.
    exact
      (ENNReal.le_div_iff_mul_le (Or.inl hden_ne_zero) (Or.inl hden_ne_top)).2 <| by
        simpa using hden_le_r
  · have hr_le : 1 ≤ r := le_of_not_gt hr1
    have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2) (le_of_not_gt hrhalf)
    have hden_zero : 1 - r = 0 := tsub_eq_zero_of_le hr_le
    -- Proof comment: if `r ≥ 1`, the denominator vanishes and the quotient is `⊤`.
    have hdiv_top : r / 0 = ⊤ := ENNReal.div_zero hr_pos.ne'
    simpa [hden_zero, hdiv_top]

-- Proof sketch: sum the singleton masses of `figure17_2InvariantMeasure r`. For `r < 1`, the tail
-- is a geometric series with ratio `r / (1 - r)`, so finiteness is equivalent to that ratio being
-- strictly smaller than `1`, i.e. to `r < 1 / 2`. For `r ≥ 1`, the denominator `1 - r` vanishes,
-- so the tail masses blow up and the total mass is automatically infinite.
/-- The weighted counting measure `figure17_2InvariantMeasure r` has finite total mass exactly in
the left-drift regime `r < 1 / 2`. -/
theorem figure17_2InvariantMeasure_univ_lt_top_iff (r : ℝ≥0∞) :
    figure17_2InvariantMeasure r Set.univ < ∞ ↔ r < 1 / 2 := by
  let q : ℝ≥0∞ := r / (1 - r)
  have htail :
      (∑' n : ℕ, figure17_2InvariantMass r (n + 1)) = ∑' n : ℕ, q ^ n := by
    simp [figure17_2InvariantMass, q]
  constructor
  · intro hμ
    by_contra hrhalf
    have hq_ge : 1 ≤ q := figure17_2InvariantRatio_ge_one_of_not_lt_half hrhalf
    have hpow_ge : ∀ n : ℕ, (1 : ℝ≥0∞) ≤ q ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (1 : ℝ≥0∞) = 1 * 1 := by simp
            _ ≤ q ^ n * q := mul_le_mul' ih hq_ge
            _ = q ^ (n + 1) := by rw [pow_succ]
    have htsum_ge : (∑' n : ℕ, (1 : ℝ≥0∞)) ≤ ∑' n : ℕ, q ^ n :=
      ENNReal.tsum_le_tsum hpow_ge
    have hconst_top : (∑' n : ℕ, (1 : ℝ≥0∞)) = ∞ := by
      simpa using ENNReal.tsum_const_eq_top_of_ne_zero (by simp : (1 : ℝ≥0∞) ≠ 0)
    have htail_top : (∑' n : ℕ, q ^ n) = ∞ := by
      rw [hconst_top] at htsum_ge
      exact top_unique htsum_ge
    have hnot_lt_top : ¬ figure17_2InvariantMeasure r Set.univ < ∞ := by
      rw [figure17_2InvariantMeasure_univ_eq_series, htail, htail_top]
      simp
    exact hnot_lt_top hμ
  · intro hrhalf
    have hq_lt : q < 1 := figure17_2InvariantRatio_lt_one_of_lt_half hrhalf
    have htail_lt : (∑' n : ℕ, q ^ n) < ∞ := (tsum_geometric_lt_top).2 hq_lt
    have hmass0_lt : figure17_2InvariantMass r 0 < ∞ := by
      calc
        figure17_2InvariantMass r 0 = 1 - r := by rfl
        _ ≤ 1 := tsub_le_self
        _ < ∞ := by simp
    -- Proof comment: the boundary mass is finite and the remaining tail is a convergent
    -- geometric series.
    rw [figure17_2InvariantMeasure_univ_eq_series, htail]
    exact ENNReal.add_lt_top.2 ⟨hmass0_lt, htail_lt⟩

/-- Helper for Exercise 17.6.4: the only incoming edge to state `0` in Fig. 17.2 is the left jump
from state `1`. -/
theorem figure17_2TransitionMatrix_apply_zero
    (r : Set.Icc (0 : ℝ≥0∞) 1) (y : ℕ) :
    figure17_2TransitionMatrix r y 0 =
      if y = 1 then 1 - (r : ℝ≥0∞) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` jumps deterministically to `1`, so it sends no mass to `0`.
      simp [figure17_2TransitionMatrix]
  | succ n =>
      cases n with
      | zero =>
          -- Proof comment: state `1` is the unique predecessor of `0`.
          simp [figure17_2TransitionMatrix]
      | succ k =>
          -- Proof comment: no state `k + 2 ≥ 2` reaches `0` in one step.
          simp [figure17_2TransitionMatrix]

/-- Helper for Exercise 17.6.4: the only incoming edges to state `1` in Fig. 17.2 are the
deterministic jump from `0` and the left jump from `2`. -/
theorem figure17_2TransitionMatrix_apply_one
    (r : Set.Icc (0 : ℝ≥0∞) 1) (y : ℕ) :
    figure17_2TransitionMatrix r y 1 =
      if y = 0 then 1 else if y = 2 then 1 - (r : ℝ≥0∞) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` reaches `1` with probability `1`.
      simp [figure17_2TransitionMatrix]
  | succ n =>
      cases n with
      | zero =>
          -- Proof comment: state `1` has no self-loop.
          simp [figure17_2TransitionMatrix]
      | succ k =>
          cases k with
          | zero =>
              -- Proof comment: state `2` reaches `1` by its left jump.
              simp [figure17_2TransitionMatrix]
          | succ l =>
              -- Proof comment: all states `≥ 3` miss `1` in one step.
              simp [figure17_2TransitionMatrix]

/-- Helper for Exercise 17.6.4: the only incoming edges to state `n + 2` in Fig. 17.2 are the
right jump from `n + 1` and the left jump from `n + 3`. -/
theorem figure17_2TransitionMatrix_apply_succ_succ
    (r : Set.Icc (0 : ℝ≥0∞) 1) (y n : ℕ) :
    figure17_2TransitionMatrix r y (n + 2) =
      if y = n + 1 then (r : ℝ≥0∞) else if y = n + 3 then 1 - (r : ℝ≥0∞) else 0 := by
  cases y with
  | zero =>
      -- Proof comment: state `0` can only jump to `1`, so it never reaches `n + 2 ≥ 2`.
      simp [figure17_2TransitionMatrix]
  | succ m =>
      by_cases hm : m = n
      · -- Proof comment: `m = n` means `y = n + 1`, so only the right-jump term survives.
        subst hm
        simp [figure17_2TransitionMatrix]
      · by_cases hm' : m = n + 2
        · -- Proof comment: `m = n + 2` means `y = n + 3`, so only the left-jump term survives.
          subst hm'
          simp [figure17_2TransitionMatrix]
        · -- Proof comment: all other predecessors miss `n + 2` in one step.
          rw [figure17_2TransitionMatrix]
          by_cases hnm : n = m
          · exact (hm hnm.symm).elim
          · by_cases hnm2 : n + 2 = m
            · exact (hm' hnm2.symm).elim
            · have hmn : m ≠ n := fun h => hnm h.symm
              have hmn2 : m ≠ n + 2 := fun h => hnm2 h.symm
              simp [hnm, hnm2, hmn, hmn2]

/-- Helper for Exercise 17.6.4: the boundary masses satisfy the singleton balance at state `0`. -/
theorem figure17_2InvariantMass_balance_zero (r : Set.Icc (0 : ℝ≥0∞) 1) :
    figure17_2InvariantMass r 1 * (1 - (r : ℝ≥0∞)) =
      figure17_2InvariantMass r 0 := by
  -- Proof comment: the singleton mass at `1` is `1`, so multiplying by `1 - r` reproduces
  -- the boundary mass at `0`.
  simp [figure17_2InvariantMass]

/-- Helper for Exercise 17.6.4: for `r < 1`, the singleton masses satisfy the balance at
state `1`. -/
theorem figure17_2InvariantMass_balance_one
    (r : Set.Icc (0 : ℝ≥0∞) 1) (hr1 : (r : ℝ≥0∞) < 1) :
    figure17_2InvariantMass r 0 +
        figure17_2InvariantMass r 2 * (1 - (r : ℝ≥0∞)) =
      figure17_2InvariantMass r 1 := by
  let q : ℝ≥0∞ := (r : ℝ≥0∞) / (1 - (r : ℝ≥0∞))
  have hden0 : 1 - (r : ℝ≥0∞) ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
  have hqmul : q * (1 - (r : ℝ≥0∞)) = (r : ℝ≥0∞) := by
    -- Proof comment: multiplying the geometric ratio by the left-jump weight recovers `r`.
    dsimp [q]
    rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hden0 (by simp [hden0]), mul_one]
  calc
    figure17_2InvariantMass r 0 + figure17_2InvariantMass r 2 * (1 - (r : ℝ≥0∞))
      = (1 - (r : ℝ≥0∞)) + q * (1 - (r : ℝ≥0∞)) := by
          simp [figure17_2InvariantMass, q]
    _ = (1 - (r : ℝ≥0∞)) + (r : ℝ≥0∞) := by rw [hqmul]
    _ = 1 := by simpa using tsub_add_cancel_of_le r.2.2
    _ = figure17_2InvariantMass r 1 := by simp [figure17_2InvariantMass]

/-- Helper for Exercise 17.6.4: for `r < 1`, the singleton masses satisfy the interior
two-neighbor balance equations. -/
theorem figure17_2InvariantMass_balance_succ_succ
    (r : Set.Icc (0 : ℝ≥0∞) 1) (hr1 : (r : ℝ≥0∞) < 1) (n : ℕ) :
    figure17_2InvariantMass r (n + 1) * (r : ℝ≥0∞) +
        figure17_2InvariantMass r (n + 3) * (1 - (r : ℝ≥0∞)) =
      figure17_2InvariantMass r (n + 2) := by
  let q : ℝ≥0∞ := (r : ℝ≥0∞) / (1 - (r : ℝ≥0∞))
  have hden0 : 1 - (r : ℝ≥0∞) ≠ 0 := ne_of_gt (tsub_pos_of_lt hr1)
  have hqmul : q * (1 - (r : ℝ≥0∞)) = (r : ℝ≥0∞) := by
    -- Proof comment: the ratio `q` was chosen so that `q * (1 - r) = r`.
    dsimp [q]
    rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hden0 (by simp [hden0]), mul_one]
  have hqsum : (r : ℝ≥0∞) + q * (r : ℝ≥0∞) = q := by
    calc
      (r : ℝ≥0∞) + q * (r : ℝ≥0∞)
        = q * (1 - (r : ℝ≥0∞)) + q * (r : ℝ≥0∞) := by rw [hqmul]
      _ = q * ((1 - (r : ℝ≥0∞)) + (r : ℝ≥0∞)) := by rw [mul_add]
      _ = q := by rw [tsub_add_cancel_of_le r.2.2, mul_one]
  -- Proof comment: factor out the common power `q ^ n` and use the defining identity for `q`.
  calc
    figure17_2InvariantMass r (n + 1) * (r : ℝ≥0∞) +
        figure17_2InvariantMass r (n + 3) * (1 - (r : ℝ≥0∞))
      = q ^ n * (r : ℝ≥0∞) + q ^ (n + 2) * (1 - (r : ℝ≥0∞)) := by
          simp [figure17_2InvariantMass, q]
    _ = q ^ n * (r : ℝ≥0∞) + q ^ (n + 1) * (q * (1 - (r : ℝ≥0∞))) := by
          simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
    _ = q ^ n * (r : ℝ≥0∞) + q ^ (n + 1) * (r : ℝ≥0∞) := by
          rw [hqmul]
    _ = q ^ n * (r : ℝ≥0∞) + q ^ n * (q * (r : ℝ≥0∞)) := by
          rw [pow_succ']
          ac_rfl
    _ = q ^ n * ((r : ℝ≥0∞) + q * (r : ℝ≥0∞)) := by
          rw [← mul_add]
    _ = q ^ (n + 1) := by
          rw [hqsum, pow_succ']
          ac_rfl
    _ = figure17_2InvariantMass r (n + 2) := by
          simp [figure17_2InvariantMass, q]

/-- Helper for Exercise 17.6.4: on the countable discrete state space `ℕ`, invariance of the
Fig. 17.2 kernel is equivalent to the singleton balance equations. -/
theorem figure17_2KernelInvariant_iff_singleton
    (r : Set.Icc (0 : ℝ≥0∞) 1) (μ : Measure ℕ) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r)) μ ↔
      ∀ x : ℕ,
        ∑' y : ℕ, μ ({y} : Set ℕ) * figure17_2TransitionMatrix r y x =
          μ ({x} : Set ℕ) := by
  constructor
  · intro hμ x
    -- Proof comment: evaluate the invariant-measure identity on the singleton `{x}`.
    have hx := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) hμ.def
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx
  · intro hμ
    rw [Kernel.Invariant]
    refine Measure.ext_of_singleton fun x ↦ ?_
    -- Proof comment: singleton balance determines the full measure on the discrete state space.
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hμ x

-- Proof sketch: evaluate the stationarity equation on singletons. The boundary balance
-- `μ {0} = μ {1} * (1 - r)` and the interior balance
-- `μ {n + 1} * (1 - r) = μ {n} * r` are exactly the recursion satisfied by
-- `figure17_2InvariantMass r`. The boundary value `r = 1` is excluded because the chain then
-- drifts deterministically to `+∞`, while this mass profile does not satisfy the singleton
-- balance equation at `1`.
/-- Invariant-measure clause for Exercise 17.6.4 (1): for `r ∈ [0, 1)` the weighted counting
measure with singleton masses
`μ {0} = 1 - r` and `μ {n + 1} = (r / (1 - r))^n` is invariant for the Fig. 17.2 transition
kernel. -/
theorem figure17_2InvariantMeasure_isInvariant
    (r : Set.Icc (0 : ℝ≥0∞) 1) (hr1 : (r : ℝ≥0∞) < 1) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2InvariantMeasure r) := by
  rw [figure17_2KernelInvariant_iff_singleton]
  intro x
  cases x with
  | zero =>
      -- Proof comment: only the left jump from state `1` contributes to the incoming mass at `0`.
      calc
        ∑' y : ℕ,
            figure17_2InvariantMeasure r ({y} : Set ℕ) * figure17_2TransitionMatrix r y 0
          = ∑' y : ℕ, figure17_2InvariantMass r y * figure17_2TransitionMatrix r y 0 := by
              congr with y
              rw [figure17_2InvariantMeasure_apply_singleton]
        _ = ∑' y : ℕ,
              figure17_2InvariantMass r y *
                (if y = 1 then 1 - (r : ℝ≥0∞) else 0) := by
              congr with y
              rw [figure17_2TransitionMatrix_apply_zero]
        _ = figure17_2InvariantMass r 1 * (1 - (r : ℝ≥0∞)) := by
              rw [ENNReal.tsum_eq_add_tsum_ite 1]
              have htail :
                  (∑' x : ℕ,
                    if x = 1 then 0
                    else figure17_2InvariantMass r x *
                      if x = 1 then 1 - (r : ℝ≥0∞) else 0) = 0 := by
                refine ENNReal.tsum_eq_zero.2 ?_
                intro x
                by_cases hx : x = 1
                · simp [hx]
                · simp [hx]
              simp only [if_pos rfl]
              have hcollapse :=
                congrArg
                  (fun t : ℝ≥0∞ ↦ figure17_2InvariantMass r 1 * (1 - (r : ℝ≥0∞)) + t)
                  htail
              simpa using hcollapse
        _ = figure17_2InvariantMass r 0 := figure17_2InvariantMass_balance_zero r
        _ = figure17_2InvariantMeasure r ({0} : Set ℕ) := by
              rw [figure17_2InvariantMeasure_apply_singleton]
  | succ x =>
      cases x with
      | zero =>
          -- Proof comment: the incoming mass at `1` splits into the deterministic jump from `0`
          -- and the left jump from `2`.
          calc
            ∑' y : ℕ,
                figure17_2InvariantMeasure r ({y} : Set ℕ) * figure17_2TransitionMatrix r y 1
              = ∑' y : ℕ, figure17_2InvariantMass r y * figure17_2TransitionMatrix r y 1 := by
                  congr with y
                  rw [figure17_2InvariantMeasure_apply_singleton]
            _ = ∑' y : ℕ,
                  figure17_2InvariantMass r y *
                    (if y = 0 then 1 else if y = 2 then 1 - (r : ℝ≥0∞) else 0) := by
                  congr with y
                  rw [figure17_2TransitionMatrix_apply_one]
            _ = figure17_2InvariantMass r 0 +
                  figure17_2InvariantMass r 2 * (1 - (r : ℝ≥0∞)) := by
                  rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 2]
                  have htail :
                      (∑' x : ℕ,
                        if x = 2 then 0
                        else
                          if x = 0 then 0
                          else
                            figure17_2InvariantMass r x *
                              if x = 0 then 1 else if x = 2 then 1 - (r : ℝ≥0∞) else 0) = 0 := by
                    refine ENNReal.tsum_eq_zero.2 ?_
                    intro x
                    by_cases hx2 : x = 2
                    · simp [hx2]
                    · by_cases hx0 : x = 0
                      · simp [hx2, hx0]
                      · simp [hx2, hx0]
                  simp
                  have hcollapse :=
                    congrArg
                      (fun t : ℝ≥0∞ ↦
                        figure17_2InvariantMass r 0 +
                          (figure17_2InvariantMass r 2 * (1 - (r : ℝ≥0∞)) + t))
                      htail
                  simpa [add_assoc] using hcollapse
            _ = figure17_2InvariantMass r 1 := figure17_2InvariantMass_balance_one r hr1
            _ = figure17_2InvariantMeasure r ({1} : Set ℕ) := by
                  rw [figure17_2InvariantMeasure_apply_singleton]
      | succ n =>
          -- Proof comment: for interior states `n + 2`, only the right jump from `n + 1` and the
          -- left jump from `n + 3` contribute to the balance.
          calc
            ∑' y : ℕ,
                figure17_2InvariantMeasure r ({y} : Set ℕ) *
                  figure17_2TransitionMatrix r y (n + 2)
              = ∑' y : ℕ,
                  figure17_2InvariantMass r y * figure17_2TransitionMatrix r y (n + 2) := by
                  congr with y
                  rw [figure17_2InvariantMeasure_apply_singleton]
            _ = ∑' y : ℕ,
                  figure17_2InvariantMass r y *
                    (if y = n + 1 then (r : ℝ≥0∞)
                      else if y = n + 3 then 1 - (r : ℝ≥0∞) else 0) := by
                  congr with y
                  rw [figure17_2TransitionMatrix_apply_succ_succ]
            _ = figure17_2InvariantMass r (n + 1) * (r : ℝ≥0∞) +
                  figure17_2InvariantMass r (n + 3) * (1 - (r : ℝ≥0∞)) := by
                  rw [ENNReal.tsum_eq_add_tsum_ite (n + 1), ENNReal.tsum_eq_add_tsum_ite (n + 3)]
                  have htail :
                      (∑' x : ℕ,
                        if x = n + 3 then 0
                        else
                          if x = n + 1 then 0
                          else
                            figure17_2InvariantMass r x *
                              if x = n + 1 then (r : ℝ≥0∞)
                              else if x = n + 3 then 1 - (r : ℝ≥0∞) else 0) = 0 := by
                    refine ENNReal.tsum_eq_zero.2 ?_
                    intro x
                    by_cases hx3 : x = n + 3
                    · simp [hx3]
                    · by_cases hx1 : x = n + 1
                      · simp [hx3, hx1]
                      · simp [hx3, hx1]
                  simp
                  have hcollapse :=
                    congrArg
                      (fun t : ℝ≥0∞ ↦
                        figure17_2InvariantMass r (n + 1) * (r : ℝ≥0∞) +
                          (figure17_2InvariantMass r (n + 3) * (1 - (r : ℝ≥0∞)) + t))
                      htail
                  simpa [add_assoc] using hcollapse
            _ = figure17_2InvariantMass r (n + 2) :=
                figure17_2InvariantMass_balance_succ_succ r hr1 n
            _ = figure17_2InvariantMeasure r ({n + 2} : Set ℕ) := by
                  rw [figure17_2InvariantMeasure_apply_singleton]

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {r : Set.Icc (0 : ℝ≥0∞) 1} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]

/-- Helper for Exercise 17.6.4: a positive `n`-step singleton mass followed by a positive
one-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
theorem figure17_2_discreteKernel_singleton_pos_succ
    {x y z : ℕ} {n : ℕ}
    (hxy : 0 <
      ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({y} : Set ℕ))
    (hyz : 0 <
      (discreteMatrixKernel (figure17_2TransitionMatrix r) y) ({z} : Set ℕ)) :
    0 <
      ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (n + 1)) x) ({z} : Set ℕ) := by
  let κ : Kernel ℕ ℕ := discreteMatrixKernel (figure17_2TransitionMatrix r)
  have hmeas : Measurable fun w : ℕ ↦ κ w ({z} : Set ℕ) :=
    Kernel.measurable_coe κ (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ) := by
    change (κ y) ({z} : Set ℕ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the positive intermediate state `y` belongs to the integrand support, so the
  -- successor-step lintegral is strictly positive.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Exercise 17.6.4: following `n` successive right jumps from `x` has strictly
positive `n`-step mass whenever `r > 0`. -/
theorem figure17_2_rightPathStepMass_pos
    (hr0 : 0 < (r : ℝ≥0∞)) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({x + n} : Set ℕ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x)
              ({x + n} : Set ℕ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + n))
              ({x + (n + 1)} : Set ℕ) := by
        rw [discreteMatrixKernel_apply_singleton]
        by_cases hxn : x + n = 0
        · have hx0 : x = 0 := by omega
          have hn0 : n = 0 := by omega
          subst hx0
          subst hn0
          simp [figure17_2TransitionMatrix]
        · rcases Nat.exists_eq_succ_of_ne_zero hxn with ⟨m, hm⟩
          rw [hm]
          have hstep : x + (n + 1) = m + 2 := by omega
          simpa [figure17_2TransitionMatrix, hstep] using hr0
      exact figure17_2_discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Exercise 17.6.4: following `n` successive left jumps from `x + n` back to `x`
has strictly positive mass whenever `r < 1`. -/
theorem figure17_2_leftPathStepMass_pos
    (hr1 : (r : ℝ≥0∞) < 1) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) (x + n)) ({x} : Set ℕ) := by
  have hleft : 0 < 1 - (r : ℝ≥0∞) := tsub_pos_of_lt hr1
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) ((x + 1) + n))
              ({x + 1} : Set ℕ) := by
        simpa [Nat.add_assoc] using ih (x + 1)
      have hlast :
          0 <
            (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + 1)) ({x} : Set ℕ) := by
        rw [discreteMatrixKernel_apply_singleton]
        simpa [figure17_2TransitionMatrix] using hleft
      -- Proof comment: follow the already-positive path from `x + (n + 1)` down to `x + 1`,
      -- then take one final left jump to `x`.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        figure17_2_discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Exercise 17.6.4: any strictly positive finite-step singleton mass already forces
strictly positive ever-hit probability. -/
theorem figure17_2_everHitsProbability_pos_of_posStepMass
    {x y n : ℕ} (hn : 0 < n)
    (hstep :
      0 < ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x) ({y} : Set ℕ)) :
    0 < (F[P, X]) x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hslice :
      0 < (P x : Measure Ω) {ω | X n ω = y} := by
    have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
    rw [hReal.transition_eq x n]
    simpa using hstep
  have hsubset :
      {ω | X n ω = y} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
    intro ω hω
    exact ⟨n, hn, hω⟩
  have hhit_enn :
      0 < (P x : Measure Ω) {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
    -- Proof comment: the concrete time-`n` slice sits inside the positive-time ever-hit event.
    exact lt_of_lt_of_le hslice (measure_mono hsubset)
  -- Proof comment: the ever-hit probability is the real mass of that positive event.
  rw [everHitsProbability_def, Measure.real_def]
  exact ENNReal.toReal_pos hhit_enn.ne' (measure_ne_top (P x : Measure Ω) _)

/-- Helper for Exercise 17.6.4: when `0 < r < 1`, the Fig. 17.2 chain communicates between any
two states by following a monotone path. -/
theorem figure17_2_isIrreducible
    (hr0 : 0 < (r : ℝ≥0∞)) (hr1 : (r : ℝ≥0∞) < 1) :
    IsIrreducibleMarkovChain P X := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have hforward :
        0 <
          ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) x) ({x + 1} : Set ℕ) := by
      -- Proof comment: every state has a one-step right move with positive mass when `r > 0`.
      simpa using figure17_2_rightPathStepMass_pos (r := r) hr0 x 1
    have hback :
        0 <
          (discreteMatrixKernel (figure17_2TransitionMatrix r) (x + 1)) ({x} : Set ℕ) := by
      -- Proof comment: from `x + 1` there is a one-step left move back to `x` whenever `r < 1`.
      simpa [pow_one, Nat.add_comm] using figure17_2_leftPathStepMass_pos (r := r) hr1 x 1
    have hstep :
        0 <
          ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 2) x) ({x} : Set ℕ) := by
      -- Proof comment: concatenate the positive right move with the positive left move.
      simpa [pow_one] using
        figure17_2_discreteKernel_singleton_pos_succ
          (r := r) (n := 1) (x := x) (y := x + 1) (z := x) hforward hback
    exact
      figure17_2_everHitsProbability_pos_of_posStepMass
        (r := r) (P := P) (X := X) (by simp) hstep
  · by_cases hxy_lt : x < y
    · have hstep :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (y - x)) x)
              ({y} : Set ℕ) := by
        -- Proof comment: the monotone right path of length `y - x` reaches `y` with positive
        -- mass.
        simpa [Nat.add_sub_of_le hxy_lt.le] using
          figure17_2_rightPathStepMass_pos (r := r) hr0 x (y - x)
      exact
        figure17_2_everHitsProbability_pos_of_posStepMass
          (r := r) (P := P) (X := X) (Nat.sub_pos_of_lt hxy_lt) hstep
    · have hyx_lt : y < x := lt_of_le_of_ne (Nat.le_of_not_gt hxy_lt) (Ne.symm hxy)
      have hstep :
          0 <
            ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (x - y)) x) ({y} : Set ℕ) := by
        -- Proof comment: if `y < x`, follow the monotone left-moving path from `x` down to `y`.
        simpa [Nat.add_sub_of_le hyx_lt.le] using
          figure17_2_leftPathStepMass_pos (r := r) hr1 y (x - y)
      exact
        figure17_2_everHitsProbability_pos_of_posStepMass
          (r := r) (P := P) (X := X) (Nat.sub_pos_of_lt hyx_lt) hstep

/-- Helper for Exercise 17.6.4: the geometric invariant-mass series is nonzero in the
left-drift regime. -/
theorem figure17_2InvariantMass_tsum_ne_zero_of_lt_half
    (hrhalf : (r : ℝ≥0∞) < 1 / 2) :
    (∑' n : ℕ, figure17_2InvariantMass r n) ≠ 0 := by
  have hr1 : (r : ℝ≥0∞) < 1 := lt_trans hrhalf (by norm_num)
  have hmass0_pos : 0 < figure17_2InvariantMass r 0 := by
    simpa [figure17_2InvariantMass] using tsub_pos_of_lt hr1
  have hmass0_le :
      figure17_2InvariantMass r 0 ≤ ∑' n : ℕ, figure17_2InvariantMass r n := ENNReal.le_tsum 0
  -- Proof comment: the boundary term `n = 0` is already strictly positive, so the full series
  -- cannot vanish.
  exact ne_of_gt (lt_of_lt_of_le hmass0_pos hmass0_le)

/-- Helper for Exercise 17.6.4: the geometric invariant-mass series is finite in the left-drift
regime. -/
theorem figure17_2InvariantMass_tsum_ne_top_of_lt_half
    (hrhalf : (r : ℝ≥0∞) < 1 / 2) :
    (∑' n : ℕ, figure17_2InvariantMass r n) ≠ ⊤ := by
  let q : ℝ≥0∞ := (r : ℝ≥0∞) / (1 - (r : ℝ≥0∞))
  have hq_lt_one : q < 1 := figure17_2InvariantRatio_lt_one_of_lt_half hrhalf
  have htail_ne_top : (∑' n : ℕ, q ^ n) ≠ ⊤ := ((tsum_geometric_lt_top).2 hq_lt_one).ne
  have htail :
      (∑' b : ℕ, figure17_2InvariantMass r (b + 1)) = ∑' n : ℕ, q ^ n := by
    simp [figure17_2InvariantMass, q]
  -- Proof comment: split off the boundary mass `1 - r`; the remaining tail is geometric.
  rw [tsum_eq_zero_add' ENNReal.summable, htail]
  exact ENNReal.add_ne_top.2 ⟨by simp [figure17_2InvariantMass], htail_ne_top⟩

/-- Helper for Exercise 17.6.4: the normalized geometric mass profile is a probability mass
function when `r < 1 / 2`. -/
def figure17_2InvariantPMF (r : Set.Icc (0 : ℝ≥0∞) 1) (hrhalf : (r : ℝ≥0∞) < 1 / 2) : PMF ℕ :=
  PMF.normalize (figure17_2InvariantMass r)
    (figure17_2InvariantMass_tsum_ne_zero_of_lt_half (r := r) hrhalf)
    (figure17_2InvariantMass_tsum_ne_top_of_lt_half (r := r) hrhalf)

/-- Helper for Exercise 17.6.4: the normalized geometric invariant distribution in the
left-drift regime. -/
def figure17_2InvariantDistribution
    (r : Set.Icc (0 : ℝ≥0∞) 1) (hrhalf : (r : ℝ≥0∞) < 1 / 2) : ProbabilityMeasure ℕ :=
  ⟨(figure17_2InvariantPMF r hrhalf).toMeasure, inferInstance⟩

/-- Helper for Exercise 17.6.4: the normalized invariant distribution has singleton masses given
by the geometric profile times the normalization constant. -/
theorem figure17_2InvariantDistribution_apply_singleton
    (hrhalf : (r : ℝ≥0∞) < 1 / 2) (n : ℕ) :
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) ({n} : Set ℕ) =
      figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ := by
  -- Proof comment: the invariant distribution is the measure of the normalized PMF, so singleton
  -- masses are exactly the normalized weights.
  change (figure17_2InvariantPMF r hrhalf).toMeasure ({n} : Set ℕ) =
    figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  simp [figure17_2InvariantPMF, PMF.normalize_apply]

/-- Helper for Exercise 17.6.4: the normalized invariant distribution is a scalar multiple of the
raw invariant measure. -/
theorem figure17_2InvariantDistribution_eq_smul_rawMeasure
    (hrhalf : (r : ℝ≥0∞) < 1 / 2) :
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) =
      (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ • figure17_2InvariantMeasure r := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  -- Proof comment: both measures have the same singleton masses, namely the raw masses scaled by
  -- the normalization constant.
  calc
    (figure17_2InvariantDistribution r hrhalf : Measure ℕ) ({n} : Set ℕ)
      = figure17_2InvariantMass r n * (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ := by
          rw [figure17_2InvariantDistribution_apply_singleton (r := r) hrhalf n]
    _ =
        ((∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ •
          figure17_2InvariantMeasure r) ({n} : Set ℕ) := by
            rw [Measure.smul_apply, figure17_2InvariantMeasure_apply_singleton]
            simp [smul_eq_mul, mul_comm]

/-- Helper for Exercise 17.6.4: the normalized geometric invariant distribution is invariant in
the left-drift regime. -/
theorem figure17_2InvariantDistribution_isInvariant
    (hrhalf : (r : ℝ≥0∞) < 1 / 2) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2InvariantDistribution r hrhalf : Measure ℕ) := by
  have hr1 : (r : ℝ≥0∞) < 1 := lt_trans hrhalf (by norm_num)
  have hraw :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) 1)
        (figure17_2InvariantMeasure r) := by
    -- Proof comment: the raw weighted counting measure is already invariant for the one-step
    -- kernel, viewed through the discrete semigroup at time `1`.
    simpa [pow_one] using figure17_2InvariantMeasure_isInvariant (r := r) hr1
  have hscaled :
      Kernel.Invariant ((fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) 1)
        ((∑' k : ℕ, figure17_2InvariantMass r k)⁻¹ • figure17_2InvariantMeasure r) :=
    kernelInvariant_smul
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (a := (∑' k : ℕ, figure17_2InvariantMass r k)⁻¹) hraw
  -- Proof comment: the normalized distribution is exactly this scalar multiple of the raw
  -- invariant measure.
  simpa [pow_one, figure17_2InvariantDistribution_eq_smul_rawMeasure (r := r) hrhalf] using
    hscaled

/-- Helper for Exercise 17.6.4: in the irreducible regime `0 < r < 1`, recurrence of state `0`
propagates to every state. -/
theorem figure17_2_allStatesRecurrent_of_zero_recurrent
    (hr0 : 0 < (r : ℝ≥0∞)) (hr1 : (r : ℝ≥0∞) < 1)
    (hzero : IsRecurrentState P X 0) :
    ∀ x : ℕ, IsRecurrentState P X x := by
  have hirr : IsIrreducibleMarkovChain P X :=
    figure17_2_isIrreducible (r := r) (P := P) (X := X) hr0 hr1
  intro x
  -- Proof comment: Theorem 17.35 transports recurrence along the strictly positive
  -- communication probabilities supplied by irreducibility.
  exact
    isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) hzero (hirr 0 x)

/-- Positive-recurrence clause for Exercise 17.6.4 (1): if `0 < r < 1 / 2`, then the Fig. 17.2
chain is positive recurrent. -/
theorem figure17_2_allStatesPositiveRecurrent_of_lt_half
    (hr0 : 0 < (r : ℝ≥0∞)) (hrhalf : (r : ℝ≥0∞) < 1 / 2) :
    IsPositiveRecurrentMarkovChain P X := by
  have hr1 : (r : ℝ≥0∞) < 1 := lt_trans hrhalf (by norm_num)
  have hirr : IsIrreducibleMarkovChain P X :=
    figure17_2_isIrreducible (r := r) (P := P) (X := X) hr0 hr1
  have hπinv :
      Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
        (figure17_2InvariantDistribution r hrhalf : Measure ℕ) :=
    figure17_2InvariantDistribution_isInvariant (r := r) hrhalf
  have hπmem :
      figure17_2InvariantDistribution r hrhalf ∈
        invariantDistributions (discreteMatrixKernel (figure17_2TransitionMatrix r)) :=
    (mem_invariantDistributions_iff
      (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2InvariantDistribution r hrhalf)).2 hπinv
  -- Proof comment: Theorem 17.51 turns the explicit invariant distribution into positive
  -- recurrence of the whole irreducible chain.
  exact
    (isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
      (p := figure17_2TransitionMatrix r) (P := P) (X := X) hirr).2
      (Set.nonempty_iff_ne_empty.1 ⟨figure17_2InvariantDistribution r hrhalf, hπmem⟩)

/-- Helper for Exercise 17.6.4: at `r = 1 / 2`, the singleton balance at `0` reduces to the
unique incoming neighbor `1`. -/
theorem figure17_2_invariantBalance_zero_half
    (hr : (r : ℝ≥0∞) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) :
    (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ℝ≥0∞) =
      (π : Measure ℕ) ({0} : Set ℕ) := by
  have hbal :=
    (figure17_2KernelInvariant_iff_singleton (r := r) (μ := (π : Measure ℕ))).1 hπ
  -- Proof comment: rewrite the singleton balance at `0` so only the left jump from `1`
  -- contributes.
  calc
    (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ℝ≥0∞)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = 1 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite 1]
            have htail :
                (∑' x : ℕ,
                  if x = 1 then 0
                  else
                    (π : Measure ℕ) ({x} : Set ℕ) * (if x = 1 then (1 / 2 : ℝ≥0∞) else 0)) =
                  0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx : x = 1
              · simp [hx]
              · simp [hx]
            simp only [if_pos rfl]
            have hcollapse :=
              congrArg
                (fun t : ℝ≥0∞ ↦ (π : Measure ℕ) ({1} : Set ℕ) * (1 / 2 : ℝ≥0∞) + t)
                htail
            simpa using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y 0 := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_zero]
          simp [hr]
    _ = (π : Measure ℕ) ({0} : Set ℕ) := hbal 0

/-- Helper for Exercise 17.6.4: at `r = 1 / 2`, the singleton balance at `1` reduces to the two
incoming neighbors `0` and `2`. -/
theorem figure17_2_invariantBalance_one_half
    (hr : (r : ℝ≥0∞) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) :
    (π : Measure ℕ) ({0} : Set ℕ) +
        (π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ℝ≥0∞) =
      (π : Measure ℕ) ({1} : Set ℕ) := by
  have hbal :=
    (figure17_2KernelInvariant_iff_singleton (r := r) (μ := (π : Measure ℕ))).1 hπ
  -- Proof comment: rewrite the singleton balance at `1` so only the deterministic jump from `0`
  -- and the left jump from `2` remain.
  calc
    (π : Measure ℕ) ({0} : Set ℕ) +
        (π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ℝ≥0∞)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = 0 then 1 else if y = 2 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 2]
            have htail :
                (∑' x : ℕ,
                  if x = 2 then 0
                  else
                    if x = 0 then 0
                    else
                      (π : Measure ℕ) ({x} : Set ℕ) *
                        (if x = 0 then (1 : ℝ≥0∞) else if x = 2 then 1 / 2 else 0)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx2 : x = 2
              · simp [hx2]
              · by_cases hx0 : x = 0
                · simp [hx2, hx0]
                · simp [hx2, hx0]
            simp
            have hcollapse :=
              congrArg
                (fun t : ℝ≥0∞ ↦
                  (π : Measure ℕ) ({0} : Set ℕ) +
                    ((π : Measure ℕ) ({2} : Set ℕ) * (1 / 2 : ℝ≥0∞) + t))
                htail
            simpa [add_assoc] using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y 1 := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_one]
          simp [hr]
    _ = (π : Measure ℕ) ({1} : Set ℕ) := hbal 1

/-- Helper for Exercise 17.6.4: at `r = 1 / 2`, the singleton balance at `m + 2` reduces to the
two incoming neighbors `m + 1` and `m + 3`. -/
theorem figure17_2_invariantBalance_succ_half
    (hr : (r : ℝ≥0∞) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) (m : ℕ) :
    (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ℝ≥0∞) +
        (π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ℝ≥0∞) =
      (π : Measure ℕ) ({m + 2} : Set ℕ) := by
  have hbal :=
    (figure17_2KernelInvariant_iff_singleton (r := r) (μ := (π : Measure ℕ))).1 hπ
  -- Proof comment: rewrite the singleton balance at `m + 2` so only its two nearest neighbors
  -- contribute.
  calc
    (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ℝ≥0∞) +
        (π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ℝ≥0∞)
      = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) *
          (if y = m + 1 then 1 / 2 else if y = m + 3 then 1 / 2 else 0) := by
            rw [ENNReal.tsum_eq_add_tsum_ite (m + 1), ENNReal.tsum_eq_add_tsum_ite (m + 3)]
            have htail :
                (∑' x : ℕ,
                  if x = m + 3 then 0
                  else
                    if x = m + 1 then 0
                    else
                      (π : Measure ℕ) ({x} : Set ℕ) *
                        (if x = m + 1 then (1 / 2 : ℝ≥0∞)
                          else if x = m + 3 then 1 / 2 else 0)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro x
              by_cases hx3 : x = m + 3
              · simp [hx3]
              · by_cases hx1 : x = m + 1
                · simp [hx3, hx1]
                · simp [hx3, hx1]
            simp
            have hcollapse :=
              congrArg
                (fun t : ℝ≥0∞ ↦
                  (π : Measure ℕ) ({m + 1} : Set ℕ) * (1 / 2 : ℝ≥0∞) +
                    ((π : Measure ℕ) ({m + 3} : Set ℕ) * (1 / 2 : ℝ≥0∞) + t))
                htail
            simpa [add_assoc] using hcollapse.symm
    _ = ∑' y : ℕ, (π : Measure ℕ) ({y} : Set ℕ) * figure17_2TransitionMatrix r y (m + 2) := by
          congr with y
          rw [figure17_2TransitionMatrix_apply_succ_succ]
          simp [hr]
    _ = (π : Measure ℕ) ({m + 2} : Set ℕ) := hbal (m + 2)

/-- Helper for Exercise 17.6.4: at `r = 1 / 2`, every invariant probability measure has zero
singleton mass at every state. -/
theorem figure17_2_invariantDistribution_singleton_eq_zero_of_eq_half
    (hr : (r : ℝ≥0∞) = 1 / 2) (π : ProbabilityMeasure ℕ)
    (hπ : Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (π : Measure ℕ)) (n : ℕ) :
    (π : Measure ℕ) ({n} : Set ℕ) = 0 := by
  let mass : ℕ → ℝ≥0∞ := fun k ↦ (π : Measure ℕ) ({k} : Set ℕ)
  have hmass_ne_top : ∀ k : ℕ, mass k ≠ ⊤ := by
    intro k
    exact measure_ne_top (π : Measure ℕ) ({k} : Set ℕ)
  have hzero :
      mass 1 * (1 / 2 : ℝ≥0∞) = mass 0 :=
    figure17_2_invariantBalance_zero_half (r := r) hr π hπ
  have hone :
      mass 0 + mass 2 * (1 / 2 : ℝ≥0∞) = mass 1 :=
    figure17_2_invariantBalance_one_half (r := r) hr π hπ
  have hzero_real :
      (mass 1).toReal * (1 / 2 : ℝ) = (mass 0).toReal := by
    simpa [ENNReal.toReal_mul, hmass_ne_top 1] using congrArg ENNReal.toReal hzero
  have hone_real :
      (mass 0).toReal + (mass 2).toReal * (1 / 2 : ℝ) = (mass 1).toReal := by
    have hmul2 : mass 2 * (1 / 2 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (hmass_ne_top 2) (by simp)
    have hone_toReal := congrArg ENNReal.toReal hone
    rw [ENNReal.toReal_add (hmass_ne_top 0) hmul2, ENNReal.toReal_mul] at hone_toReal
    simpa [hmass_ne_top 0, hmass_ne_top 2] using hone_toReal
  have htwo_real : (mass 2).toReal = (mass 1).toReal := by
    linarith
  have hconst_pair :
      ∀ m : ℕ, (mass (m + 1)).toReal = (mass 1).toReal ∧
        (mass (m + 2)).toReal = (mass 1).toReal := by
    intro m
    induction m with
    | zero =>
        exact ⟨rfl, htwo_real⟩
    | succ m ih =>
        rcases ih with ⟨hm1, hm2⟩
        have hsucc :
            mass (m + 1) * (1 / 2 : ℝ≥0∞) + mass (m + 3) * (1 / 2 : ℝ≥0∞) =
              mass (m + 2) :=
          figure17_2_invariantBalance_succ_half (r := r) hr π hπ m
        have hsucc_real :
            (mass (m + 1)).toReal * (1 / 2 : ℝ) +
                (mass (m + 3)).toReal * (1 / 2 : ℝ) =
              (mass (m + 2)).toReal := by
          have hmul13 : mass (m + 1) * (1 / 2 : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top (hmass_ne_top (m + 1)) (by simp)
          have hmul33 : mass (m + 3) * (1 / 2 : ℝ≥0∞) ≠ ⊤ :=
            ENNReal.mul_ne_top (hmass_ne_top (m + 3)) (by simp)
          have hsucc_toReal := congrArg ENNReal.toReal hsucc
          rw [ENNReal.toReal_add hmul13 hmul33, ENNReal.toReal_mul, ENNReal.toReal_mul] at hsucc_toReal
          simpa [hmass_ne_top (m + 1), hmass_ne_top (m + 3), hmass_ne_top (m + 2)] using
            hsucc_toReal
        have hm3 : (mass (m + 3)).toReal = (mass 1).toReal := by
          linarith
        simpa [Nat.add_assoc] using And.intro hm2 hm3
  have hconst :
      ∀ k : ℕ, 0 < k → mass k = mass 1 := by
    intro k hk
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨m, rfl⟩
    have hm : (mass (m + 1)).toReal = (mass 1).toReal := (hconst_pair m).1
    exact (ENNReal.toReal_eq_toReal_iff' (hmass_ne_top (m + 1)) (hmass_ne_top 1)).mp hm
  have hmass_one_zero : mass 1 = 0 := by
    by_contra hmass_one_zero
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hmass_one_zero (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    have hsum :
        ∑ x ∈ Finset.Icc 1 N, mass x = N * mass 1 := by
      calc
        ∑ x ∈ Finset.Icc 1 N, mass x = ∑ x ∈ Finset.Icc 1 N, mass 1 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact hconst x (Finset.mem_Icc.mp hx).1
        _ = N * mass 1 := by
          simp [Nat.card_Icc]
    have hle :
        ∑ x ∈ Finset.Icc 1 N, mass x ≤ 1 := by
      calc
        ∑ x ∈ Finset.Icc 1 N, mass x = (π : Measure ℕ) (Finset.Icc 1 N : Set ℕ) := by
          simpa [mass] using
            (sum_measure_singleton (μ := (π : Measure ℕ)) (s := Finset.Icc 1 N)).symm
        _ ≤ (π : Measure ℕ) Set.univ := by
              exact measure_mono (by intro x hx; simp)
        _ = 1 := by simp
    have hNle : N * mass 1 ≤ 1 := by
      simpa [hsum] using hle
    exact (not_lt_of_ge hNle) hN
  -- Proof comment: the critical balance recursion forces every positive-index singleton mass to
  -- equal `mass 1`; finiteness of the total probability mass then forces that common value to be
  -- zero, and finally the boundary mass vanishes as well.
  rcases n with _ | n
  · have hmass_zero_real : (mass 0).toReal = 0 := by
      simpa [hmass_one_zero] using hzero_real.symm
    rcases (ENNReal.toReal_eq_zero_iff (mass 0)).1 hmass_zero_real with hzero0 | htop0
    · exact hzero0
    · exact False.elim (hmass_ne_top 0 htop0)
  · simpa [mass, hmass_one_zero] using hconst (n + 1) (Nat.succ_pos _)

/-- Helper for Exercise 17.6.4: at `r = 1 / 2`, no state can be positive recurrent. -/
theorem figure17_2_not_positiveRecurrentState_of_eq_half
    (hr : (r : ℝ≥0∞) = 1 / 2) (x : ℕ) :
    ¬ IsPositiveRecurrentState P X x := by
  intro hx
  obtain ⟨π, hπinv, hπx⟩ :=
    existsInvariantDistributionAtPositiveRecurrentState
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) x hx
  have hπinv_one :
      Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
        (π : Measure ℕ) := by
    simpa [pow_one] using hπinv
  have hzero :
      (π : Measure ℕ) ({x} : Set ℕ) = 0 :=
    figure17_2_invariantDistribution_singleton_eq_zero_of_eq_half
      (r := r) hr π hπinv_one x
  -- Proof comment: a positive recurrent state would furnish an invariant distribution with
  -- positive mass at its singleton, contradicting the critical singleton-vanishing theorem.
  exact hπx.ne' hzero

/-- Helper for Exercise 17.6.4: the one-step state event has exactly the corresponding
transition-matrix mass. -/
theorem figure17_2_timeOne_stateEvent
    (x y : ℕ) :
    (P x : Measure Ω) {ω | X 1 ω = y} = figure17_2TransitionMatrix r x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hTransition :
      ((P x : Measure Ω).map (X 1)) ({y} : Set ℕ) =
        ((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) x) ({y} : Set ℕ) :=
    congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ)) (hReal.transition_eq x 1)
  have hKernel :
      discreteMatrixKernel (figure17_2TransitionMatrix r) x ({y} : Set ℕ) =
        figure17_2TransitionMatrix r x y := by
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    simpa using
      (Measure.sum_smul_dirac_singleton
        (f := fun z : ℕ ↦ figure17_2TransitionMatrix r x z) (a := y))
  rw [pow_one, hKernel] at hTransition
  -- Proof comment: the transition law at time `1` is exactly the one-step kernel.
  simpa [Measure.map_apply, hReal.measurable_process 1] using hTransition

/-- Helper for Exercise 17.6.4: a state-membership event at time `j ≤ n` is measurable in the
generated filtration at time `n`. -/
theorem figure17_2_measurableSet_mem_of_le_generatedFiltration
    {j n : ℕ} (hjn : j ≤ n) (A : Set ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | X j ω ∈ A} := by
  have hXj_meas : Measurable[generatedFiltrationSpace X n] (X j) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
  -- Proof comment: every subset of the discrete state space `ℕ` is measurable.
  simpa [Set.preimage, Set.mem_setOf_eq] using hXj_meas MeasurableSet.of_discrete

/-- Helper for Exercise 17.6.4: finite-horizon no-hit events are measurable. -/
theorem figure17_2_measurableSet_noHitHorizon
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (x n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X x n M) := by
  classical
  have hEq :
      noHitHorizonLocal X x n M =
        ⋂ m ∈ (Finset.Icc 1 M : Finset ℕ), {ω | X (n + m) ω ≠ x} := by
    ext ω
    simp [noHitHorizonLocal, Finset.mem_Icc]
  rw [hEq]
  refine MeasurableSet.biInter (Set.to_countable _) ?_
  intro m hm
  -- Proof comment: each forbidden singleton slice is measurable, hence so is its complement.
  exact (hX_meas (n + m)) (measurableSet_singleton x).compl

/-- Helper for Exercise 17.6.4: every generated history filtration of the realization is
contained in the ambient measurable space. -/
private theorem figure17_2_generatedFiltrationSpace_le_ambient
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (n : ℕ) :
    generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: every coordinate sigma-algebra used to build the history filtration is already
  -- ambient because each deterministic-time slice of the realization is measurable.
  refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
  exact (hX_meas j).comap_le

/-- Helper for Exercise 17.6.4: the generated history filtration grows monotonically with the
time index. -/
private theorem figure17_2_generatedFiltrationSpace_monoNat
    (s t : ℕ) (hst : s ≤ t) :
    generatedFiltrationSpace X s ≤ generatedFiltrationSpace X t := by
  -- Proof comment: enlarging the terminal time only enlarges the supremum of available history
  -- coordinates.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hst) le_rfl

/-- Helper for Exercise 17.6.4: `futurePrefixEventLocal X n f` is the exact path-cylinder event
that prescribes the deterministic-time segment `X n, X (n + 1), ..., X (n + M)`. -/
private def futurePrefixEventLocal (Y : ℕ → Ω → ℕ) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → ℕ) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Exercise 17.6.4: finite future-prefix events are measurable in the ambient
sigma-algebra. -/
private theorem figure17_2_measurableSet_futurePrefixEvent
    (hX_meas : ∀ n : ℕ, Measurable (X n)) {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet (futurePrefixEventLocal X n f) := by
  have hEq :
      futurePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  -- Proof comment: an exact finite path cylinder is the intersection of finitely many singleton
  -- coordinate slices.
  refine MeasurableSet.iInter fun i ↦ ?_
  exact hX_meas (n + (i : ℕ)) (measurableSet_singleton (f i))

/-- Helper for Exercise 17.6.4: a one-term future prefix is exactly the corresponding state
event. -/
private theorem figure17_2_futurePrefixEvent_zero_eq_stateEvent
    (n : ℕ) (f : Fin 1 → ℕ) :
    futurePrefixEventLocal X n f = {ω | X n ω = f 0} := by
  -- Proof comment: at horizon `0`, the unique `Fin 1` coordinate is just the current state.
  ext ω
  simp [futurePrefixEventLocal]

/-- Helper for Exercise 17.6.4: a finite future-prefix event is measurable with respect to the
generated filtration at its terminal time. -/
private theorem figure17_2_measurableSet_futurePrefixEvent_generated
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (futurePrefixEventLocal X n f) := by
  have hEq :
      futurePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [futurePrefixEventLocal]
  rw [hEq]
  -- Proof comment: every constrained coordinate occurs no later than `n + M`, so each singleton
  -- slice is already measurable in the terminal history filtration.
  refine MeasurableSet.iInter fun i ↦ ?_
  exact figure17_2_measurableSet_mem_of_le_generatedFiltration
    (X := X) (j := n + (i : ℕ)) (n := n + M)
    (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) ({f i} : Set ℕ)

/-- Helper for Exercise 17.6.4: a longer future-prefix event splits into its shorter prefix and
its terminal state event. -/
private theorem figure17_2_futurePrefixEvent_succ_eq
    {M n : ℕ} (f : Fin (M + 2) → ℕ) :
    futurePrefixEventLocal X n f =
      futurePrefixEventLocal X n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | X (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  -- Proof comment: split the exact path condition into the first `M + 1` coordinates and the
  -- terminal coordinate.
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [futurePrefixEventLocal] using hω i.castSucc
    · simpa [futurePrefixEventLocal] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [futurePrefixEventLocal] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [futurePrefixEventLocal] using hωPrefix j

/-- Helper for Exercise 17.6.4: a finite future-prefix event determines its terminal state. -/
private theorem figure17_2_futurePrefixEvent_terminal_subset
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    futurePrefixEventLocal X n f ⊆ {ω | X (n + M) ω = f (Fin.last M)} := by
  -- Proof comment: the terminal deterministic time is one of the prescribed coordinates.
  intro ω hω
  simpa [futurePrefixEventLocal] using hω (Fin.last M)

/-- Helper for Exercise 17.6.4: if a history event already fixes the state at time `n`, then
intersecting it with a later singleton event factors through the corresponding transition mass. -/
private theorem figure17_2_measure_inter_prefix_stepEvent_eq_mulLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)).toReal *
        (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set ℕ)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (measurableSet_singleton z)
  have hA_measAmbient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
      figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) (X n ω))
          ({z} : Set ℕ)).toReal := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set ℕ)) (measurableSet_singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov conditional expectation over `A`, then freeze the future
  -- law at `y` because `A` already pins the time-`n` state.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp
              (figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n)
              hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A,
          (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) (X n ω))
            ({z} : Set ℕ)).toReal ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A,
          (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
            ({z} : Set ℕ)).toReal ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
            have hω : X n ω = y := hA_sub hω
            rw [hω]
    _ =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
          ({z} : Set ℕ)).toReal * μ.real A := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Exercise 17.6.4: the deterministic-time prefix factorization is cleaner in raw
`Measure` (`ℝ≥0∞`) form. -/
private theorem figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)) *
        (P x : Measure Ω) A := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  let _ :
      IsMarkovKernel (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) :=
    hReal.semigroup.isMarkovKernel m
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
          ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A :=
    figure17_2_measure_inter_prefix_stepEvent_eq_mulLocal
      (r := r) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ := measure_ne_top _ _
  have hkernel_ne_top :
      (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
        ({z} : Set ℕ)) ≠ ⊤ := measure_ne_top _ _
  have hA_ne_top : (P x : Measure Ω) A ≠ ⊤ := measure_ne_top _ _
  -- Proof comment: convert the already-proved real-valued identity back to ENNReal masses.
  calc
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
        ENNReal.ofReal ((P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ =
        ENNReal.ofReal
          ((((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
            ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A) := by
              rw [hstep]
    _ =
        (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y) ({z} : Set ℕ)) *
          (P x : Measure Ω) A := by
            rw [ENNReal.ofReal_mul]
            · rw [ENNReal.ofReal_toReal hkernel_ne_top]
              change
                (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
                  ({z} : Set ℕ)) * ENNReal.ofReal (((P x : Measure Ω) A).toReal) =
                  (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) y)
                    ({z} : Set ℕ)) * (P x : Measure Ω) A
              rw [ENNReal.ofReal_toReal hA_ne_top]
            · positivity

/-- Helper for Exercise 17.6.4: once a history event pins down the current state, intersecting it
with a finite exact future path factors through the future path law from that state. -/
private theorem figure17_2_measure_inter_prefix_futurePrefixEvent_eq_mulLocal
    (hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X)
    {x y : ℕ} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → ℕ) :
    (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
      (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
  induction M generalizing n A y with
  | zero =>
      have hright_eval :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
            if f 0 = y then 1 else 0 := by
        rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set ℕ) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton (f 0))]
        rw [hReal.initial_eq y]
        by_cases hf0 : f 0 = y <;> simp [hf0]
      by_cases hf0 : f 0 = y
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = A := by
          ext ω
          constructor
          · intro hω
            exact hω.1
          · intro hω
            refine ⟨hω, ?_⟩
            rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := n) f]
            simpa [hf0] using hA_sub hω
        -- Proof comment: at horizon `0`, the exact future path only asks for the current state.
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = (P x : Measure Ω) A := by
            rw [hleft_eq]
          _ = 1 * (P x : Measure Ω) A := by rw [one_mul]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_pos hf0]
      · have hleft_eq : A ∩ futurePrefixEventLocal X n f = ∅ := by
          ext ω
          constructor
          · rintro ⟨hωA, hωf⟩
            rw [figure17_2_futurePrefixEvent_zero_eq_stateEvent (X := X) (n := n) f] at hωf
            exact hf0 (hωf.symm.trans (hA_sub hωA))
          · intro hω
            exact False.elim (by simpa using hω)
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) = 0 := by
            simp [hleft_eq]
          _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_neg hf0]
            simp
  | succ M ih =>
      let g : Fin (M + 1) → ℕ := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ futurePrefixEventLocal X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        have hmono : generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) :=
          figure17_2_generatedFiltrationSpace_monoNat (X := X) n (n + M) (Nat.le_add_right n M)
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter
          (figure17_2_measurableSet_futurePrefixEvent_generated (X := X) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact figure17_2_futurePrefixEvent_terminal_subset (X := X) (n := n) g hω.2
      have hleft_step :
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := by
        calc
          (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
              (P x : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, figure17_2_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P x : Measure Ω) B := by
                  simpa [B] using
                    figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (r := r) (P := P) (X := X)
                      (x := x) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := B) (n := n + M) (m := 1) hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (futurePrefixEventLocal X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (futurePrefixEventLocal X 0 g) :=
          figure17_2_measurableSet_futurePrefixEvent_generated (X := X) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub :
          futurePrefixEventLocal X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            futurePrefixEventLocal X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          figure17_2_futurePrefixEvent_terminal_subset (X := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
        calc
          (P y : Measure Ω) (futurePrefixEventLocal X 0 f) =
              (P y : Measure Ω)
                (futurePrefixEventLocal X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, figure17_2_futurePrefixEvent_succ_eq, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
                ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P y : Measure Ω) (futurePrefixEventLocal X 0 g) := by
                  simpa using
                    figure17_2_measure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (r := r) (P := P) (X := X)
                      (x := y) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := futurePrefixEventLocal X 0 g) (n := M) (m := 1) hg_meas hg_sub
      -- Proof comment: split off the terminal coordinate and reuse the induction hypothesis on
      -- the shorter prefix.
      calc
        (P x : Measure Ω) (A ∩ futurePrefixEventLocal X n f) =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := hleft_step
        _ =
            (((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              ((P y : Measure Ω) (futurePrefixEventLocal X 0 g) * (P x : Measure Ω) A) := by
                have hBfactor :
                    (P x : Measure Ω) B =
                      (P y : Measure Ω) (futurePrefixEventLocal X 0 g) * (P x : Measure Ω) A := by
                        simpa [B] using ih hA_meas hA_sub g
                rw [hBfactor]
        _ =
            ((((discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) (g (Fin.last M)))
              ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (futurePrefixEventLocal X 0 g)) *
              (P x : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P y : Measure Ω) (futurePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
              rw [hright_step]

/-- Helper for Exercise 17.6.4: on a slice where the first step is fixed to `z + 1`, the
remaining no-hit event against `0` factors through the restarted chain from `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_noHitHorizonZero_eq_mulLocal
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start M : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω) (A ∩ noHitHorizonLocal X 0 1 M) =
      (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (P start : Measure Ω) A := by
  classical
  let μstart : Measure Ω := P start
  let μz : Measure Ω := P (z + 1)
  let T : Type := {f : Fin (M + 1) → ℕ //
    f 0 = z + 1 ∧ ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0}
  let hReal : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun k hk ↦ ?_
      exact (hReal.measurable_process k).comap_le
    exact hFiltration_le (s := A) hA_meas
  have hleft_union :
      A ∩ noHitHorizonLocal X 0 1 M = ⋃ f : T, A ∩ futurePrefixEventLocal X 1 f.1 := by
    ext ω
    constructor
    · rintro ⟨hωA, hωNoHit⟩
      let f : Fin (M + 1) → ℕ := fun i ↦ X (1 + (i : ℕ)) ω
      have hf0 : f 0 = z + 1 := by
        simpa [f] using hA_sub hωA
      have hfNoHit : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        exact hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf0, hfNoHit⟩, ?_⟩
      refine ⟨hωA, ?_⟩
      intro i
      rfl
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      refine ⟨hωf.1, ?_⟩
      intro m hm hmM hmEq
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (1 + m) ω = f.1 i := by
        simpa [futurePrefixEventLocal, i] using hωf.2 i
      exact (f.2.2 i hm) (hpath ▸ hmEq)
  have hright_union :
      {ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M = ⋃ f : T, futurePrefixEventLocal X 0 f.1 := by
    ext ω
    constructor
    · rintro ⟨hω0, hωNoHit⟩
      let f : Fin (M + 1) → ℕ := fun i ↦ X (i : ℕ) ω
      have hf0 : f 0 = z + 1 := by
        simpa [f] using hω0
      have hfNoHit : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf0, hfNoHit⟩, ?_⟩
      intro i
      simp [f, zero_add]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      refine ⟨?_, ?_⟩
      · simpa [f.2.1] using hωf 0
      · intro m hm hmM hmEq
        let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
        have hpath : X (0 + m) ω = f.1 i := by
          simpa [futurePrefixEventLocal, i, zero_add] using hωf i
        exact (f.2.2 i hm) (by simpa [zero_add] using hpath ▸ hmEq)
  have hpairwise_left :
      Pairwise (fun f g : T ↦ Disjoint (A ∩ futurePrefixEventLocal X 1 f.1)
        (A ∩ futurePrefixEventLocal X 1 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf.2 i).symm.trans (hωg.2 i)
    exact hfg (Subtype.ext hEq)
  have hpairwise_right :
      Pairwise (fun f g : T ↦ Disjoint (futurePrefixEventLocal X 0 f.1)
        (futurePrefixEventLocal X 0 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf i).symm.trans (hωg i)
    exact hfg (Subtype.ext hEq)
  have hleft_sum :
      μstart (A ∩ noHitHorizonLocal X 0 1 M) =
        ∑' f : T, μstart (A ∩ futurePrefixEventLocal X 1 f.1) := by
    rw [hleft_union, measure_iUnion hpairwise_left]
    intro f
    exact hA_ambient.inter
      (figure17_2_measurableSet_futurePrefixEvent (X := X) hReal.measurable_process
        (n := 1) f.1)
  have hright_sum :
      μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) =
        ∑' f : T, μz (futurePrefixEventLocal X 0 f.1) := by
    rw [hright_union, measure_iUnion hpairwise_right]
    intro f
    exact figure17_2_measurableSet_futurePrefixEvent (X := X) hReal.measurable_process
      (n := 0) f.1
  have hslices :
      ∀ f : T,
        μstart (A ∩ futurePrefixEventLocal X 1 f.1) =
          μz (futurePrefixEventLocal X 0 f.1) * μstart A := by
    intro f
    have hA_sub_f : A ⊆ {ω | X 1 ω = f.1 0} := by
      intro ω hω
      rw [f.2.1]
      exact hA_sub hω
    -- Proof comment: once the time-`1` state is fixed to `z + 1`, each exact future path is
    -- governed by the restarted chain started from `z + 1`.
    simpa [μstart, μz, f.2.1] using
      (figure17_2_measure_inter_prefix_futurePrefixEvent_eq_mulLocal
        (r := r) (P := P) (X := X) hReal (x := start) (y := f.1 0)
        (A := A) (n := 1) (f := f.1) hA_meas hA_sub_f)
  have hstate_meas : MeasurableSet {ω | X 0 ω = z + 1} :=
    hReal.measurable_process 0 (measurableSet_singleton (z + 1))
  have hnohit_meas : MeasurableSet (noHitHorizonLocal X 0 0 M) :=
    figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process 0 0 M
  have hstate_prob_one : μz {ω | X 0 ω = z + 1} = 1 := by
    have hpreimage : {ω | X 0 ω = z + 1} = X 0 ⁻¹' ({z + 1} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton (z + 1))]
    rw [hReal.initial_eq (z + 1)]
    simp
  have hstate_compl_zero : μz ({ω | X 0 ω = z + 1}ᶜ) = 0 := by
    exact (prob_compl_eq_zero_iff hstate_meas).2 hstate_prob_one
  have hright_full :
      μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) =
        μz (noHitHorizonLocal X 0 0 M) := by
    have hstate_ae : ∀ᵐ ω ∂ μz, ω ∈ {ω | X 0 ω = z + 1} := by
      rw [ae_iff]
      exact hstate_compl_zero
    simpa [Set.inter_comm] using
      (Measure.measure_inter_eq_of_ae (μ := μz) (s := noHitHorizonLocal X 0 0 M)
        (t := {ω | X 0 ω = z + 1}) hstate_ae)
  -- Proof comment: partition the target-zero no-hit event by the whole finite future path, factor
  -- each cylinder through the restarted chain at `z + 1`, and then drop the deterministic
  -- time-`0` state constraint under `P (z + 1)`.
  calc
    μstart (A ∩ noHitHorizonLocal X 0 1 M) =
        ∑' f : T, μstart (A ∩ futurePrefixEventLocal X 1 f.1) := hleft_sum
    _ = ∑' f : T, μz (futurePrefixEventLocal X 0 f.1) * μstart A := by
          refine tsum_congr fun f ↦ hslices f
    _ = (∑' f : T, μz (futurePrefixEventLocal X 0 f.1)) * μstart A := by
          rw [ENNReal.tsum_mul_right]
    _ = μz ({ω | X 0 ω = z + 1} ∩ noHitHorizonLocal X 0 0 M) * μstart A := by
          rw [← hright_sum]
    _ = μz (noHitHorizonLocal X 0 0 M) * μstart A := by
          rw [hright_full]

/-- Helper for Exercise 17.6.4: `tailNoHitLocal X y n` is the event that after time `n` the path
never visits `y` again. -/
private def tailNoHitLocal (Y : ℕ → Ω → ℕ) (y : ℕ) (n : ℕ) : Set Ω :=
  ⋂ M : ℕ, noHitHorizonLocal Y y n M

/-- Helper for Exercise 17.6.4: tail no-hit events are measurable. -/
private theorem figure17_2_measurableSet_tailNoHitLocal
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (y n : ℕ) :
    MeasurableSet (tailNoHitLocal X y n) := by
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  -- Proof comment: the tail event is the countable intersection of the measurable finite-horizon
  -- no-hit events.
  refine MeasurableSet.iInter fun M ↦ ?_
  exact figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process y n M

/-- Helper for Exercise 17.6.4: the tail no-hit event is exactly the complement of the shifted
future-hit event. -/
private theorem figure17_2_tailNoHitLocal_compl_eq_futureHit
    (y n : ℕ) :
    (tailNoHitLocal X y n)ᶜ = {ω | ∃ m : ℕ, 0 < m ∧ X (n + m) ω = y} := by
  -- Proof comment: failing the tail no-hit condition means that some positive-time index after
  -- `n` hits `y`, and conversely such a hit violates one horizon in the intersection.
  ext ω
  constructor
  · intro hω
    by_contra hhit
    apply hω
    refine Set.mem_iInter.2 ?_
    intro M
    intro m hm hmM
    exact fun hmEq ↦ hhit ⟨m, hm, hmEq⟩
  · rintro ⟨m, hm, hmEq⟩ hω
    exact (Set.mem_iInter.1 hω m) m hm le_rfl hmEq

/-- Helper for Exercise 17.6.4: on a slice where the time-`1` state is fixed to `z + 1`, the
tail event of never hitting `0` again factors through the restarted chain from `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_tailNoHitZero_eq_mulLocal
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω) (A ∩ tailNoHitLocal X 0 1) =
      (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * (P start : Measure Ω) A := by
  let μstart : Measure Ω := P start
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› :=
      figure17_2_generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process 1
    exact hFiltration_le (s := A) hA_meas
  have htail_eq :
      A ∩ tailNoHitLocal X 0 1 = ⋂ M : ℕ, A ∩ noHitHorizonLocal X 0 1 M := by
    -- Proof comment: intersecting `A` with the tail event is the same as intersecting `A` with
    -- every finite no-hit horizon simultaneously.
    ext ω
    constructor
    · rintro ⟨hωA, hωtail⟩
      refine Set.mem_iInter.2 ?_
      intro M
      exact ⟨hωA, Set.mem_iInter.1 hωtail M⟩
    · intro hω
      refine ⟨(Set.mem_iInter.1 hω 0).1, Set.mem_iInter.2 ?_⟩
      intro M
      exact (Set.mem_iInter.1 hω M).2
  have hleft_antitone :
      Antitone (fun M : ℕ ↦ A ∩ noHitHorizonLocal X 0 1 M) := by
    -- Proof comment: increasing the horizon strengthens the no-hit requirement.
    intro M N hMN
    intro ω hω
    refine ⟨hω.1, ?_⟩
    intro m hm hmN
    exact hω.2 m hm (hmN.trans hMN)
  have hright_antitone :
      Antitone (fun M : ℕ ↦ noHitHorizonLocal X 0 0 M) := by
    -- Proof comment: the restarted no-hit events decrease in the same way.
    intro M N hMN
    intro ω hω
    intro m hm hmN
    exact hω m hm (hmN.trans hMN)
  have hleft_null :
      ∀ M : ℕ, NullMeasurableSet (A ∩ noHitHorizonLocal X 0 1 M) μstart := by
    intro M
    exact
      MeasurableSet.nullMeasurableSet <|
        hA_ambient.inter
          (figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process 0 1 M)
  have hright_null :
      ∀ M : ℕ, NullMeasurableSet (noHitHorizonLocal X 0 0 M) (P (z + 1) : Measure Ω) := by
    intro M
    exact
      MeasurableSet.nullMeasurableSet <|
        figure17_2_measurableSet_noHitHorizon (X := X) hReal.measurable_process 0 0 M
  have hleft_tendsto :
      Filter.Tendsto (fun M ↦ μstart (A ∩ noHitHorizonLocal X 0 1 M)) Filter.atTop
        (nhds (μstart (A ∩ tailNoHitLocal X 0 1))) := by
    -- Proof comment: continuity from above identifies the tail event with the limit of the
    -- decreasing finite-horizon slices.
    have hbase :=
      tendsto_measure_iInter_atTop (μ := μstart)
        (s := fun M : ℕ ↦ A ∩ noHitHorizonLocal X 0 1 M)
        hleft_null
        hleft_antitone
        ⟨0, measure_ne_top _ _⟩
    simpa [htail_eq] using hbase
  have hright_tendsto :
      Filter.Tendsto (fun M ↦ (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)) Filter.atTop
        (nhds ((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0))) := by
    -- Proof comment: the restarted chain sees the same decreasing approximation of its tail
    -- no-hit event.
    have hbase :=
      tendsto_measure_iInter_atTop (μ := (P (z + 1) : Measure Ω))
        (s := fun M : ℕ ↦ noHitHorizonLocal X 0 0 M)
        hright_null
        hright_antitone
        ⟨0, measure_ne_top _ _⟩
    simpa [tailNoHitLocal] using hbase
  have hfinite_real_eq :
      (fun M ↦ (μstart (A ∩ noHitHorizonLocal X 0 1 M)).toReal) =
        fun M ↦ ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal * (μstart A).toReal := by
    funext M
    have hEqM :
        μstart (A ∩ noHitHorizonLocal X 0 1 M) =
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * μstart A :=
      figure17_2_measure_inter_prefix_noHitHorizonZero_eq_mulLocal
        (r := r) (P := P) (X := X) (z := z) (start := start) (M := M)
        (A := A) hA_meas hA_sub
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hEqM
  have hleft_real_tendsto :
      Filter.Tendsto (fun M ↦ (μstart (A ∩ noHitHorizonLocal X 0 1 M)).toReal) Filter.atTop
        (nhds ((μstart (A ∩ tailNoHitLocal X 0 1)).toReal)) := by
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hleft_tendsto
  have hright_real_base :
      Filter.Tendsto
        (fun M ↦ ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal)
        Filter.atTop
        (nhds (((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal)) := by
    exact
      (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hright_tendsto
  have hright_real_tendsto :
      Filter.Tendsto
        (fun M ↦
          ((P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M)).toReal * (μstart A).toReal)
        Filter.atTop
        (nhds (((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal * (μstart A).toReal)) := by
    exact hright_real_base.mul_const ((μstart A).toReal)
  rw [hfinite_real_eq] at hleft_real_tendsto
  have hreal_eq :
      (μstart (A ∩ tailNoHitLocal X 0 1)).toReal =
        ((P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0)).toReal * (μstart A).toReal :=
    tendsto_nhds_unique hleft_real_tendsto hright_real_tendsto
  have hleft_ne_top : μstart (A ∩ tailNoHitLocal X 0 1) ≠ ⊤ := measure_ne_top _ _
  have hright_ne_top :
      (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * μstart A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  -- Proof comment: the tail factorization is the limit of the finite-horizon factorization along
  -- the decreasing no-hit approximation.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using hreal_eq

/-- Helper for Exercise 17.6.4: after fixing the time-`1` state to `z + 1`, the probability of
eventually hitting `0` factors by the hit probability from the restarted chain at `z + 1`. -/
private theorem figure17_2_measure_inter_prefix_futureHitZero_eq_mul
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    {z start : ℕ} {A : Set Ω}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X 1] A)
    (hA_sub : A ⊆ {ω | X 1 ω = z + 1}) :
    (P start : Measure Ω).real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}) =
      (F[P, X]) (z + 1) 0 * (P start : Measure Ω).real A := by
  let μstart : Measure Ω := P start
  have htail_meas : MeasurableSet (tailNoHitLocal X 0 1) :=
    figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1
  have htail_factor :
      μstart.real (A ∩ tailNoHitLocal X 0 1) =
        (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) * μstart.real A := by
    have htail_eq :
        μstart (A ∩ tailNoHitLocal X 0 1) =
          (P (z + 1) : Measure Ω) (tailNoHitLocal X 0 0) * μstart A :=
      figure17_2_measure_inter_prefix_tailNoHitZero_eq_mulLocal
        (r := r) (P := P) (X := X) (z := z) (start := start) (A := A) hA_meas hA_sub
    simpa [Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal htail_eq
  have hsplit :
      μstart.real (A ∩ tailNoHitLocal X 0 1) +
        μstart.real (A ∩ {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}) =
          μstart.real A := by
    have hbase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μstart) (s := A) htail_meas.nullMeasurableSet
    simpa [Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1] using hbase
  have htail_zero :
      (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) = 1 - (F[P, X]) (z + 1) 0 := by
    have htail_meas_zero : MeasurableSet (tailNoHitLocal X 0 0) :=
      figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 0
    calc
      (P (z + 1) : Measure Ω).real (tailNoHitLocal X 0 0) =
          (P (z + 1) : Measure Ω).real ((tailNoHitLocal X 0 0)ᶜ)ᶜ := by simp
      _ = 1 - (P (z + 1) : Measure Ω).real ((tailNoHitLocal X 0 0)ᶜ) := by
            simpa using
              (MeasureTheory.probReal_compl_eq_one_sub (μ := (P (z + 1) : Measure Ω))
                (s := (tailNoHitLocal X 0 0)ᶜ) htail_meas_zero.compl)
      _ = 1 - (F[P, X]) (z + 1) 0 := by
            rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 0]
            simp [everHitsProbability_def, Nat.zero_add]
  -- Proof comment: split the time-`1` slice into the tail-no-hit part and its complementary
  -- future-hit part, then solve the resulting scalar identity.
  rw [htail_factor, htail_zero] at hsplit
  nlinarith

/-- Helper for Exercise 17.6.4: finite no-hit horizons split according to the positive state
visited at time `1`. -/
theorem figure17_2_noHitHorizon_step_decomposition
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (start M : ℕ) :
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      ∑' z : ℕ,
        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
          (figure17_2TransitionMatrix r start (z + 1)) := by
  let A : ℕ → Set Ω := fun z ↦ {ω | X 1 ω = z + 1}
  have hsplit :
      noHitHorizonLocal X 0 0 (M + 1) =
        ⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M := by
    ext ω
    constructor
    · intro hω
      have hstep_ne_zero : X 1 ω ≠ 0 := by
        exact hω 1 (by simp) (by omega)
      rcases Nat.exists_eq_succ_of_ne_zero hstep_ne_zero with ⟨z, hz⟩
      refine Set.mem_iUnion.2 ⟨z, ?_⟩
      refine ⟨by simpa [A, hz], ?_⟩
      intro m hm hmM
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hω (m + 1) (by omega) (by omega)
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hωz⟩
      rcases hωz with ⟨hz, htail⟩
      intro m hm hmM
      cases m with
      | zero =>
          omega
      | succ m =>
          cases m with
          | zero =>
              have hstep_ne_zero : X 1 ω ≠ 0 := by
                rw [hz]
                omega
              simpa using hstep_ne_zero
          | succ k =>
              have htail' : X (1 + (k + 1)) ω ≠ 0 := htail (k + 1) (by simp) (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one] using
                htail'
  have hpairwise :
      Pairwise (fun z w : ℕ ↦ Disjoint (A z ∩ noHitHorizonLocal X 0 1 M)
        (A w ∩ noHitHorizonLocal X 0 1 M)) := by
    intro z w hzw
    refine Set.disjoint_left.2 ?_
    intro ω hωz hωw
    have : z + 1 = w + 1 := hωz.1.symm.trans hωw.1
    exact hzw (Nat.succ.inj this)
  have hmeas :
      ∀ z : ℕ, MeasurableSet (A z ∩ noHitHorizonLocal X 0 1 M) := by
    intro z
    exact ((inferInstance : IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process 1
        (measurableSet_singleton (z + 1))).inter
      (figure17_2_measurableSet_noHitHorizon (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
        0 1 M)
  have hslices :
      ∀ z : ℕ,
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) =
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
    intro z
    have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] (A z) := by
      simpa [A] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({z + 1} : Set ℕ)
    have hA_sub : A z ⊆ {ω | X 1 ω = z + 1} := by
      intro ω hω
      exact hω
    -- Proof comment: after conditioning on the first step `X 1 = z + 1`, the remainder is
    -- exactly the restarted no-hit law from `z + 1`.
    exact figure17_2_measure_inter_prefix_noHitHorizonZero_eq_mulLocal
      (r := r) (P := P) (X := X) (z := z) (start := start) (M := M)
      (A := A z) hA_meas hA_sub
  calc
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        (P start : Measure Ω) (⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [hsplit]
    _ = ∑' z : ℕ, (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [measure_iUnion hpairwise]
          exact hmeas
    _ = ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
              refine tsum_congr fun z ↦ hslices z
    _ = ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (figure17_2TransitionMatrix r start (z + 1)) := by
              refine tsum_congr fun z ↦ ?_
              rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) start (z + 1)]

/-- Helper for Exercise 17.6.4: starting from `0`, finite no-hit horizons are the shifted
finite no-hit horizons from `1`. -/
theorem figure17_2_noHitHorizon_zero_eq_from_one
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (M : ℕ) :
    (P 0 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) := by
  calc
    (P 0 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r 0 (z + 1) := by
              exact figure17_2_noHitHorizon_step_decomposition (r := r) (P := P) (X := X) 0 M
    _ = (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) * 1 := by
          rw [ENNReal.tsum_eq_add_tsum_ite 0]
          have htail :
              (∑' x : ℕ,
                if x = 0 then 0
                else
                  (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    figure17_2TransitionMatrix r 0 (x + 1)) = 0 := by
            refine ENNReal.tsum_eq_zero.2 ?_
            intro x
            by_cases hx : x = 0
            · simp [hx]
            · simp [hx, figure17_2TransitionMatrix]
          have hcollapse :=
            congrArg
              (fun t : ENNReal ↦
                (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) * 1 + t)
              htail
          simpa [figure17_2TransitionMatrix] using hcollapse
    _ = (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 M) := by simp

/-- Helper for Exercise 17.6.4: from state `1`, finite no-hit horizons advance only through the
right jump to `2`. -/
theorem figure17_2_noHitHorizon_step_one
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (M : ℕ) :
    (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
  calc
    (P 1 : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r 1 (z + 1) := by
              exact figure17_2_noHitHorizon_step_decomposition (r := r) (P := P) (X := X) 1 M
    _ = (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
          rw [ENNReal.tsum_eq_add_tsum_ite 1]
          have htail :
              (∑' x : ℕ,
                if x = 1 then 0
                else
                  (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    figure17_2TransitionMatrix r 1 (x + 1)) = 0 := by
            refine ENNReal.tsum_eq_zero.2 ?_
            intro x
            by_cases hx : x = 1
            · simp [hx]
            · simp [hx, figure17_2TransitionMatrix]
          have hcollapse :=
            congrArg
              (fun t : ENNReal ↦
                (P 2 : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) + t)
              htail
          simpa [figure17_2TransitionMatrix] using hcollapse

/-- Helper for Exercise 17.6.4: from state `n + 2`, finite no-hit horizons split into the left
move to `n + 1` and the right move to `n + 3`. -/
theorem figure17_2_noHitHorizon_step_succ
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (n M : ℕ) :
    (P (n + 2) : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
        (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
  calc
    (P (n + 2) : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            figure17_2TransitionMatrix r (n + 2) (z + 1) := by
              exact
                figure17_2_noHitHorizon_step_decomposition
                  (r := r) (P := P) (X := X) (n + 2) M
    _ = (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
          ((P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) +
            ∑' z : ℕ,
              if z = n then 0
              else if z = n + 2 then 0
              else
                (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                  figure17_2TransitionMatrix r (n + 2) (z + 1)) := by
            rw [ENNReal.tsum_eq_add_tsum_ite n]
            have htail :
                (∑' x : ℕ,
                  if x = n then 0
                  else
                    (P (x + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      figure17_2TransitionMatrix r (n + 2) (x + 1)) =
                  (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) +
                    ∑' z : ℕ,
                      if z = n then 0
                      else if z = n + 2 then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1) := by
              rw [ENNReal.tsum_eq_add_tsum_ite (n + 2)]
              have htail' :
                  (∑' z : ℕ,
                    if z = n + 2 then 0
                    else
                      (if z = n then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1))) =
                    ∑' z : ℕ,
                      if z = n then 0
                      else if z = n + 2 then 0
                      else
                        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                          figure17_2TransitionMatrix r (n + 2) (z + 1) := by
                refine tsum_congr fun z ↦ ?_
                by_cases hz1 : z = n
                · simp [hz1]
                · by_cases hz2 : z = n + 2
                  · simp [hz1, hz2]
                  · simp [hz1, hz2]
              have hcollapse :=
                congrArg
                  (fun t : ENNReal ↦
                    (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) + t)
                  htail'
              simpa [figure17_2TransitionMatrix] using hcollapse
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                    (1 - (r : ENNReal)) + t)
                htail
            simpa [figure17_2TransitionMatrix, add_assoc] using hcollapse
    _ = (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
          (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) := by
            have htail :
                (∑' z : ℕ,
                  if z = n then 0
                  else if z = n + 2 then 0
                  else
                    (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      figure17_2TransitionMatrix r (n + 2) (z + 1)) = 0 := by
              refine ENNReal.tsum_eq_zero.2 ?_
              intro z
              by_cases hz1 : z = n
              · simp [hz1]
              · by_cases hz2 : z = n + 2
                · simp [hz1, hz2]
                · simp [hz1, hz2, figure17_2TransitionMatrix]
            have hcollapse :=
              congrArg
                (fun t : ENNReal ↦
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) +
                    ((P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
                      (r : ENNReal) + t))
                htail
            simpa [add_assoc] using hcollapse

/-- Helper for Exercise 17.6.4: the positive-time return probability at `0` equals the hit
probability of `0` when the chain is started from `1`. -/
theorem figure17_2_returnProbability_zero_eq_hitProbability_one_zero
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X] :
    (F[P, X]) 0 0 = (F[P, X]) 1 0 := by
  let μ0 : Measure Ω := P 0
  let μ1 : Measure Ω := P 1
  let hitWithin : ℕ → Set Ω := fun M ↦ {ω | ∃ n ∈ Set.Icc 1 M, X n ω = 0}
  let hitEvent : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0}
  have hhitWithin_eq_compl :
      ∀ M : ℕ, hitWithin M = (noHitHorizonLocal X 0 0 M)ᶜ := by
    intro M
    ext ω
    constructor
    · intro hω hnohit
      rcases hω with ⟨n, hn, hnx⟩
      exact (hnohit n hn.1 hn.2 (by simpa [zero_add] using hnx)).elim
    · intro hω
      by_contra hhit
      exact hω <| by
        intro n hn1 hnM hnEq
        exact hhit ⟨n, ⟨hn1, hnM⟩, by simpa [zero_add] using hnEq⟩
  have hfinite_eq :
      ∀ M : ℕ, μ0.real (hitWithin (M + 1)) = μ1.real (hitWithin M) := by
    intro M
    have hμ0 :
        μ0.real (hitWithin (M + 1)) = 1 - μ0.real (noHitHorizonLocal X 0 0 (M + 1)) := by
      rw [hhitWithin_eq_compl (M + 1), probReal_compl_eq_one_sub (μ := μ0)]
      exact figure17_2_measurableSet_noHitHorizon (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
        0 0 (M + 1)
    have hμ1 :
        μ1.real (hitWithin M) = 1 - μ1.real (noHitHorizonLocal X 0 0 M) := by
      rw [hhitWithin_eq_compl M, probReal_compl_eq_one_sub (μ := μ1)]
      exact figure17_2_measurableSet_noHitHorizon (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
        0 0 M
    -- Proof comment: the deterministic first step `0 → 1` identifies the bounded hit event from
    -- `0` within `M + 1` steps with the bounded hit event from `1` within `M` steps.
    rw [hμ0, hμ1]
    congr 1
    simpa [Measure.real_def] using
      congrArg ENNReal.toReal
        (figure17_2_noHitHorizon_zero_eq_from_one (r := r) (P := P) (X := X) M)
  have hhitEvent_union :
      hitEvent = ⋃ M : ℕ, hitWithin (M + 1) := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨by simpa using hn, Nat.le_succ n⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hhitWithin_union :
      hitEvent = ⋃ M : ℕ, hitWithin M := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨hn, le_rfl⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hmono0 : Directed (· ⊆ ·) fun M : ℕ ↦ hitWithin (M + 1) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (Nat.succ_le_succ (le_max_left i j))⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (Nat.succ_le_succ (le_max_right i j))⟩, hnx⟩
  have hmono1 : Directed (· ⊆ ·) hitWithin := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_left i j)⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_right i j)⟩, hnx⟩
  have hμ0_union :
      μ0 (⋃ M : ℕ, hitWithin (M + 1)) = ⨆ M : ℕ, μ0 (hitWithin (M + 1)) := hmono0.measure_iUnion
  have hμ1_union :
      μ1 (⋃ M : ℕ, hitWithin M) = ⨆ M : ℕ, μ1 (hitWithin M) := hmono1.measure_iUnion
  have hsups_eq :
      ⨆ M : ℕ, μ0 (hitWithin (M + 1)) = ⨆ M : ℕ, μ1 (hitWithin M) := by
    apply le_antisymm
    · refine iSup_le fun M ↦ ?_
      have hEq : μ0 (hitWithin (M + 1)) = μ1 (hitWithin M) := by
        exact
          (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top μ0 (hitWithin (M + 1)))
            (measure_ne_top μ1 (hitWithin M))).mp (by
              simpa [Measure.real_def] using hfinite_eq M)
      rw [hEq]
      exact le_iSup (fun N : ℕ ↦ μ1 (hitWithin N)) M
    · refine iSup_le fun M ↦ ?_
      have hEq : μ0 (hitWithin (M + 1)) = μ1 (hitWithin M) := by
        exact
          (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top μ0 (hitWithin (M + 1)))
            (measure_ne_top μ1 (hitWithin M))).mp (by
              simpa [Measure.real_def] using hfinite_eq M)
      rw [← hEq]
      exact le_iSup (fun N : ℕ ↦ μ0 (hitWithin (N + 1))) M
  -- Proof comment: both eventual positive-time hit events are directed unions of bounded
  -- horizons, so the finite-horizon equality passes to the full ever-hit probabilities.
  calc
    (F[P, X]) 0 0 = μ0.real hitEvent := by
      simpa [μ0, hitEvent] using (everHitsProbability_def P X 0 0)
    _ = μ0.real (⋃ M : ℕ, hitWithin (M + 1)) := by
          rw [hhitEvent_union]
    _ = (⨆ M : ℕ, μ0 (hitWithin (M + 1))).toReal := by
          rw [Measure.real_def, hμ0_union]
    _ = (⨆ M : ℕ, μ1 (hitWithin M)).toReal := by
          rw [hsups_eq]
    _ = μ1.real (⋃ M : ℕ, hitWithin M) := by
          rw [Measure.real_def, hμ1_union]
    _ = μ1.real hitEvent := by
          rw [hhitWithin_union]
    _ = (F[P, X]) 1 0 := by
      simpa [μ1, hitEvent] using (everHitsProbability_def P X 1 0).symm

/-- Helper for Exercise 17.6.4: the eventual hit probability of `0` from state `1` splits over
the two possible first-step outcomes. -/
private theorem figure17_2_hitProbability_zero_step_one
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X] :
    (F[P, X]) 1 0 = (1 - (r : ℝ≥0∞)).toReal + (r : ℝ≥0∞).toReal * (F[P, X]) 2 0 := by
  let μ1 : Measure Ω := P 1
  let hitEvent : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0}
  let futureHit : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
  let B0 : Set Ω := {ω | X 1 ω = 0}
  let B2 : Set Ω := {ω | X 1 ω = 2}
  let Bad : Set Ω := {ω | X 1 ω ≠ 0 ∧ X 1 ω ≠ 2}
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hB0_meas : MeasurableSet B0 := by
    change MeasurableSet (X 1 ⁻¹' ({0} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton 0)
  have hB2_meas : MeasurableSet B2 := by
    change MeasurableSet (X 1 ⁻¹' ({2} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton 2)
  have hB0_mass :
      μ1.real B0 = (1 - (r : ℝ≥0∞)).toReal := by
    simpa [μ1, B0, Measure.real_def] using
      congrArg ENNReal.toReal (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 0)
  have hB2_mass :
      μ1.real B2 = (r : ℝ≥0∞).toReal := by
    simpa [μ1, B2, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 2)
  have hgood_prob : μ1 (B0 ∪ B2) = 1 := by
    calc
      μ1 (B0 ∪ B2) = μ1 B0 + μ1 B2 := by
        rw [measure_union]
        · refine Set.disjoint_left.2 ?_
          intro ω hω0 hω2
          have : (0 : ℕ) = 2 := hω0.symm.trans hω2
          omega
        · exact hB2_meas
      _ = (1 - (r : ℝ≥0∞)) + (r : ℝ≥0∞) := by
            rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 0,
              figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) 1 2]
            simp [figure17_2TransitionMatrix]
      _ = 1 := by
            exact tsub_add_cancel_of_le r.2.2
  have hBad_zero : μ1 Bad = 0 := by
    have hEq : Bad = (B0 ∪ B2)ᶜ := by
      ext ω
      simp [Bad, B0, B2]
    rw [hEq]
    exact (prob_compl_eq_zero_iff (hB0_meas.union hB2_meas)).2 hgood_prob
  have hfuture_meas : MeasurableSet futureHit := by
    rw [show futureHit = (tailNoHitLocal X 0 1)ᶜ by
      rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1]]
    exact (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1).compl
  have hhitEvent_meas : MeasurableSet hitEvent := by
    rw [show hitEvent = (tailNoHitLocal X 0 0)ᶜ by
      rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 0]
      simp [hitEvent, Nat.zero_add]]
    exact (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 0).compl
  have hBad_meas : MeasurableSet Bad := by
    have hEq : Bad = (B0 ∪ B2)ᶜ := by
      ext ω
      simp [Bad, B0, B2]
    rw [hEq]
    exact (hB0_meas.union hB2_meas).compl
  have hBad_hit_zero : μ1 (Bad ∩ hitEvent) = 0 := by
    refine measure_mono_null ?_ hBad_zero
    intro ω hω
    exact hω.1
  have hdecomp :
      hitEvent = (B0 ∪ (B2 ∩ futureHit)) ∪ (Bad ∩ hitEvent) := by
    -- Proof comment: the first step from state `1` can only be `0`, `2`, or a null bad branch.
    ext ω
    constructor
    · rintro hω
      by_cases h0 : X 1 ω = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h2 : X 1 ω = 2
        · refine Or.inl (Or.inr ⟨h2, ?_⟩)
          rcases hω with ⟨m, hm, hmEq⟩
          rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
          cases k with
          | zero =>
              exact False.elim (h0 (by simpa using hmEq))
          | succ l =>
              exact ⟨l + 1, by simpa using Nat.succ_pos l,
                by simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  using hmEq⟩
        · exact Or.inr ⟨⟨h0, h2⟩, hω⟩
    · intro hω
      rcases hω with hω | hω
      · rcases hω with hω | hω
        · exact ⟨1, Nat.succ_pos _, hω⟩
        · rcases hω with ⟨hω2, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
      · exact hω.2
  have hB0_disj_B2future : Disjoint B0 (B2 ∩ futureHit) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω0 hω2
    have : (0 : ℕ) = 2 := hω0.symm.trans hω2.1
    omega
  have hmain_disj_bad : Disjoint (B0 ∪ (B2 ∩ futureHit)) (Bad ∩ hitEvent) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωmain hωbad
    rcases hωmain with hω0 | hω2
    · exact hωbad.1.1 hω0
    · exact hωbad.1.2 hω2.1
  have hfuture_factor :
      μ1.real (B2 ∩ futureHit) = (F[P, X]) 2 0 * μ1.real B2 := by
    have hB2_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] B2 := by
      simpa [B2] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({2} : Set ℕ)
    have hB2_sub : B2 ⊆ {ω | X 1 ω = 1 + 1} := by
      intro ω hω
      simpa using hω
    simpa [μ1, B2, futureHit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := 1) (start := 1) (A := B2) hB2_meas_generated hB2_sub
  have hμ_eq :
      μ1 hitEvent = μ1 B0 + μ1 (B2 ∩ futureHit) := by
    calc
      μ1 hitEvent = μ1 ((B0 ∪ (B2 ∩ futureHit)) ∪ (Bad ∩ hitEvent)) := by
        conv_lhs => rw [hdecomp]
      _ = μ1 (B0 ∪ (B2 ∩ futureHit)) + μ1 (Bad ∩ hitEvent) := by
            rw [measure_union hmain_disj_bad]
            exact hBad_meas.inter hhitEvent_meas
      _ = μ1 (B0 ∪ (B2 ∩ futureHit)) := by rw [hBad_hit_zero, add_zero]
      _ = μ1 B0 + μ1 (B2 ∩ futureHit) := by
            rw [measure_union hB0_disj_B2future]
            exact hB2_meas.inter hfuture_meas
  have hμ_real :
      μ1.real hitEvent = μ1.real B0 + μ1.real (B2 ∩ futureHit) := by
    simpa [Measure.real_def, ENNReal.toReal_add, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hμ_eq
  -- Proof comment: decompose the hit event by the first step, discard the null bad branch, and
  -- factor the surviving `1 → 2` branch through the restarted hit probability from `2`.
  calc
    (F[P, X]) 1 0 = μ1.real hitEvent := by
      simpa [μ1, hitEvent] using (show (F[P, X]) 1 0 =
        (P 1 : Measure Ω).real {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0} by
          rw [everHitsProbability_def])
    _ = μ1.real B0 + μ1.real (B2 ∩ futureHit) := hμ_real
    _ = (1 - (r : ℝ≥0∞)).toReal + (r : ℝ≥0∞).toReal * (F[P, X]) 2 0 := by
          rw [hB0_mass, hfuture_factor, hB2_mass, mul_comm]

/-- Helper for Exercise 17.6.4: from state `n + 2`, the eventual hit probability of `0` splits
over the left and right nearest-neighbor moves. -/
private theorem figure17_2_hitProbability_zero_step_succ
    (r : Set.Icc (0 : ℝ≥0∞) 1)
    [IsMarkovProcessRealization
      (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X]
    (n : ℕ) :
    (F[P, X]) (n + 2) 0 =
      (1 - (r : ℝ≥0∞)).toReal * (F[P, X]) (n + 1) 0 +
        (r : ℝ≥0∞).toReal * (F[P, X]) (n + 3) 0 := by
  let μ : Measure Ω := P (n + 2)
  let hitEvent : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0}
  let futureHit : Set Ω := {ω | ∃ m : ℕ, 0 < m ∧ X (1 + m) ω = 0}
  let Bleft : Set Ω := {ω | X 1 ω = n + 1}
  let Bright : Set Ω := {ω | X 1 ω = n + 3}
  let Bad : Set Ω := {ω | X 1 ω ≠ n + 1 ∧ X 1 ω ≠ n + 3}
  let hReal :
      IsMarkovProcessRealization
        (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
  have hBleft_meas : MeasurableSet Bleft := by
    change MeasurableSet (X 1 ⁻¹' ({n + 1} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton (n + 1))
  have hBright_meas : MeasurableSet Bright := by
    change MeasurableSet (X 1 ⁻¹' ({n + 3} : Set ℕ))
    exact hReal.measurable_process 1 (measurableSet_singleton (n + 3))
  have hgood_prob : μ (Bleft ∪ Bright) = 1 := by
    calc
      μ (Bleft ∪ Bright) = μ Bleft + μ Bright := by
        rw [measure_union]
        · refine Set.disjoint_left.2 ?_
          intro ω hωl hωr
          have : n + 1 = n + 3 := hωl.symm.trans hωr
          omega
        · exact hBright_meas
      _ = figure17_2TransitionMatrix r (n + 2) (n + 1) +
            figure17_2TransitionMatrix r (n + 2) (n + 3) := by
            rw [figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 1),
              figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 3)]
      _ = 1 := by
            simpa [figure17_2TransitionMatrix, add_comm] using
              (tsub_add_cancel_of_le r.2.2 : (1 - (r : ℝ≥0∞)) + (r : ℝ≥0∞) = 1)
  have hBad_zero : μ Bad = 0 := by
    have hEq : Bad = (Bleft ∪ Bright)ᶜ := by
      ext ω
      simp [Bad, Bleft, Bright]
    rw [hEq]
    exact (prob_compl_eq_zero_iff (hBleft_meas.union hBright_meas)).2 hgood_prob
  have hfuture_meas : MeasurableSet futureHit := by
    rw [show futureHit = (tailNoHitLocal X 0 1)ᶜ by
      rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 1]]
    exact (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 1).compl
  have hhitEvent_meas : MeasurableSet hitEvent := by
    rw [show hitEvent = (tailNoHitLocal X 0 0)ᶜ by
      rw [figure17_2_tailNoHitLocal_compl_eq_futureHit (X := X) 0 0]
      simp [hitEvent, Nat.zero_add]]
    exact (figure17_2_measurableSet_tailNoHitLocal (r := r) (P := P) (X := X) 0 0).compl
  have hBad_meas : MeasurableSet Bad := by
    have hEq : Bad = (Bleft ∪ Bright)ᶜ := by
      ext ω
      simp [Bad, Bleft, Bright]
    rw [hEq]
    exact (hBleft_meas.union hBright_meas).compl
  have hBad_hit_zero : μ (Bad ∩ hitEvent) = 0 := by
    refine measure_mono_null ?_ hBad_zero
    intro ω hω
    exact hω.1
  have hdecomp :
      hitEvent = ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) ∪ (Bad ∩ hitEvent) := by
    -- Proof comment: from state `n + 2`, the first step can only move left, right, or into a
    -- null bad branch.
    ext ω
    constructor
    · rintro hω
      by_cases hl : X 1 ω = n + 1
      · refine Or.inl (Or.inl ⟨hl, ?_⟩)
        rcases hω with ⟨m, hm, hmEq⟩
        rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
        cases k with
        | zero =>
            have hzero : X 1 ω = 0 := by simpa using hmEq
            have : n + 1 = 0 := hl.symm.trans hzero
            omega
        | succ l =>
            exact ⟨l + 1, by simpa using Nat.succ_pos l,
              by simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using hmEq⟩
      · by_cases hr : X 1 ω = n + 3
        · refine Or.inl (Or.inr ⟨hr, ?_⟩)
          rcases hω with ⟨m, hm, hmEq⟩
          rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
          cases k with
          | zero =>
              have hzero : X 1 ω = 0 := by simpa using hmEq
              have : n + 3 = 0 := hr.symm.trans hzero
              omega
          | succ l =>
              exact ⟨l + 1, by simpa using Nat.succ_pos l,
                by simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  using hmEq⟩
        · exact Or.inr ⟨⟨hl, hr⟩, hω⟩
    · intro hω
      rcases hω with hω | hω
      · rcases hω with hω | hω
        · rcases hω with ⟨_, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
        · rcases hω with ⟨_, hfuture⟩
          rcases hfuture with ⟨m, hm, hmEq⟩
          exact ⟨1 + m, by simpa [Nat.add_comm] using Nat.succ_pos m,
            by simpa [Nat.add_assoc] using hmEq⟩
      · exact hω.2
  have hleft_disj_bright : Disjoint (Bleft ∩ futureHit) (Bright ∩ futureHit) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωl hωr
    have : n + 1 = n + 3 := hωl.1.symm.trans hωr.1
    omega
  have hmain_disj_bad :
      Disjoint ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) (Bad ∩ hitEvent) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωmain hωbad
    rcases hωmain with hωl | hωr
    · exact hωbad.1.1 hωl.1
    · exact hωbad.1.2 hωr.1
  have hleft_factor :
      μ.real (Bleft ∩ futureHit) = (F[P, X]) (n + 1) 0 * μ.real Bleft := by
    have hBleft_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] Bleft := by
      simpa [Bleft] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({n + 1} : Set ℕ)
    have hBleft_sub : Bleft ⊆ {ω | X 1 ω = n + 1} := by
      intro ω hω
      exact hω
    simpa [μ, Bleft, futureHit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := n) (start := n + 2) (A := Bleft)
        hBleft_meas_generated hBleft_sub
  have hright_factor :
      μ.real (Bright ∩ futureHit) = (F[P, X]) (n + 3) 0 * μ.real Bright := by
    have hBright_meas_generated :
        MeasurableSet[generatedFiltrationSpace X 1] Bright := by
      simpa [Bright] using
        figure17_2_measurableSet_mem_of_le_generatedFiltration
          (X := X) (j := 1) (n := 1) le_rfl ({n + 3} : Set ℕ)
    have hBright_sub : Bright ⊆ {ω | X 1 ω = n + 2 + 1} := by
      intro ω hω
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hω
    simpa [μ, Bright, futureHit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      figure17_2_measure_inter_prefix_futureHitZero_eq_mul
        (r := r) (P := P) (X := X) (z := n + 2) (start := n + 2) (A := Bright)
        hBright_meas_generated hBright_sub
  have hμ_eq :
      μ hitEvent = μ (Bleft ∩ futureHit) + μ (Bright ∩ futureHit) := by
    calc
      μ hitEvent = μ (((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) ∪ (Bad ∩ hitEvent)) := by
        conv_lhs => rw [hdecomp]
      _ = μ ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) + μ (Bad ∩ hitEvent) := by
            rw [measure_union hmain_disj_bad]
            exact hBad_meas.inter hhitEvent_meas
      _ = μ ((Bleft ∩ futureHit) ∪ (Bright ∩ futureHit)) := by rw [hBad_hit_zero, add_zero]
      _ = μ (Bleft ∩ futureHit) + μ (Bright ∩ futureHit) := by
            rw [measure_union hleft_disj_bright]
            exact hBright_meas.inter hfuture_meas
  have hμ_real :
      μ.real hitEvent = μ.real (Bleft ∩ futureHit) + μ.real (Bright ∩ futureHit) := by
    simpa [Measure.real_def, ENNReal.toReal_add, measure_ne_top _ _, measure_ne_top _ _] using
      congrArg ENNReal.toReal hμ_eq
  have hBleft_mass :
      μ.real Bleft = (1 - (r : ℝ≥0∞)).toReal := by
    simpa [μ, Bleft, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal
        (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 1))
  have hBright_mass :
      μ.real Bright = (r : ℝ≥0∞).toReal := by
    simpa [μ, Bright, Measure.real_def, figure17_2TransitionMatrix] using
      congrArg ENNReal.toReal
        (figure17_2_timeOne_stateEvent (r := r) (P := P) (X := X) (n + 2) (n + 3))
  -- Proof comment: decompose the hit event by the two nearest-neighbor first steps, discard the
  -- null bad branch, and factor the two surviving branches through the restarted chain.
  calc
    (F[P, X]) (n + 2) 0 = μ.real hitEvent := by
      simpa [μ, hitEvent] using (show (F[P, X]) (n + 2) 0 =
        (P (n + 2) : Measure Ω).real {ω | ∃ m : ℕ, 0 < m ∧ X m ω = 0} by
          rw [everHitsProbability_def])
    _ = μ.real (Bleft ∩ futureHit) + μ.real (Bright ∩ futureHit) := hμ_real
    _ = (1 - (r : ℝ≥0∞)).toReal * (F[P, X]) (n + 1) 0 +
          (r : ℝ≥0∞).toReal * (F[P, X]) (n + 3) 0 := by
            rw [hleft_factor, hright_factor, hBleft_mass, hBright_mass]
            ring

/-- Helper for Exercise 17.6.4: in the irreducible regime `0 < r < 1`, transience of the anchor
state `0` propagates to every state. -/
theorem figure17_2_allStatesTransient_of_zero_transient
    (hr0 : 0 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1)
    (hzero : IsTransientState P X 0) :
    ∀ x : ℕ, IsTransientState P X x := by
  have hirr : IsIrreducibleMarkovChain P X :=
    figure17_2_isIrreducible (r := r) (P := P) (X := X) hr0 hr1
  rcases irreducibleMarkovChain_recurrent_or_transient
      (p := figure17_2TransitionMatrix r) (P := P) (X := X) hirr with hrec | htrans
  · have hnot_zero_transient : ¬ IsTransientState P X 0 := by
      rw [IsTransientState, hrec 0]
      simp
    exact False.elim (hnot_zero_transient hzero)
  · intro x
    exact htrans x

/-- Helper for Exercise 17.6.4: in the right-drift regime, finite no-hit probabilities dominate
the harmonic profile `1 - q^k` with `q = (1 - r) / r`. -/
theorem figure17_2_noHitHorizon_real_lowerBound_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1) :
    ∀ k M : ℕ,
      1 - (((1 - ((r : ENNReal).toReal)) / ((r : ENNReal).toReal)) : ℝ) ^ k ≤
        (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M) := by
  let ρ : ℝ := (r : ENNReal).toReal
  let q : ℝ := (1 - ρ) / ρ
  have hr_top : (r : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt r.2.2 (by simp))
  have hρ_gt_half : (1 / 2 : ℝ) < ρ := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal (by simp) hr_top).2 hrhalf
  have hρ_pos : 0 < ρ := by
    linarith
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal hr_top ENNReal.one_ne_top).2 hr1
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hone_sub_nonneg : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ_lt_one.le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hone_sub_nonneg hρ_nonneg
  have hq_lt_one : q < 1 := by
    have hnum_lt : 1 - ρ < ρ := by
      linarith
    dsimp [q]
    have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
    field_simp [hρ_ne]
    linarith
  have hqmul : q * ρ = 1 - ρ := by
    dsimp [q]
    field_simp [hρ_pos.ne]
  have hstep_one :
      ρ * (1 - q ^ 2) = 1 - q := by
    have hqq : ρ * q ^ 2 = q * (1 - ρ) := by
      calc
        ρ * q ^ 2 = (q * ρ) * q := by ring
        _ = (1 - ρ) * q := by rw [hqmul]
        _ = q * (1 - ρ) := by ring
    calc
      ρ * (1 - q ^ 2) = ρ - ρ * q ^ 2 := by ring
      _ = ρ - q * (1 - ρ) := by rw [hqq]
      _ = ρ - q + q * ρ := by ring
      _ = 1 - q := by linarith [hqmul]
  have hstep_succ :
      ∀ n : ℕ,
        (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ = 1 - q ^ (n + 2) := by
    intro n
    have hcoeff :
        (1 - ρ) + ρ * q ^ 2 = q := by
      calc
        (1 - ρ) + ρ * q ^ 2 = q * ρ + ρ * q ^ 2 := by rw [hqmul]
        _ = q * (ρ + ρ * q) := by ring
        _ = q * 1 := by
              have hone : ρ + ρ * q = 1 := by
                linarith [hqmul]
              rw [hone]
        _ = q := by ring
    have hpow :
        q ^ (n + 3) = q ^ (n + 1) * q ^ 2 := by
      rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
    calc
      (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ
          = (1 - ρ) + ρ - ((1 - ρ) * q ^ (n + 1) + ρ * q ^ (n + 3)) := by ring
      _ = 1 - ((1 - ρ) * q ^ (n + 1) + ρ * q ^ (n + 3)) := by linarith
      _ = 1 - (q ^ (n + 1) * ((1 - ρ) + ρ * q ^ 2)) := by
            rw [hpow]
            ring
      _ = 1 - (q ^ (n + 1) * q) := by rw [hcoeff]
      _ = 1 - q ^ (n + 2) := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_add]
            ring
  intro k M
  change 1 - q ^ k ≤ (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M)
  induction M generalizing k with
  | zero =>
      have hbase : (P k : Measure Ω).real (noHitHorizonLocal X 0 0 0) = 1 := by
        have hset : noHitHorizonLocal X 0 0 0 = Set.univ := by
          ext ω
          constructor
          · intro _
            simp
          · intro _
            intro m hm1 hm0 hmEq
            omega
        simp [Measure.real_def, hset]
      rw [hbase]
      exact sub_le_self _ (pow_nonneg hq_nonneg k)
  | succ M ih =>
      cases k with
      | zero =>
          -- Proof comment: the state `0` case only needs the trivial nonnegativity lower bound
          -- because `1 - q^0 = 0`.
          simpa [q] using
            (measureReal_nonneg (μ := (P 0 : Measure Ω))
              (s := noHitHorizonLocal X 0 0 (M + 1)))
      | succ k =>
          cases k with
          | zero =>
              have hstep :
                  (P 1 : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) =
                    (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                simpa [ρ, Measure.real_def, ENNReal.toReal_mul, hr_top, measure_ne_top _ _] using
                  congrArg ENNReal.toReal
                    (figure17_2_noHitHorizon_step_one (r := r) (P := P) (X := X) M)
              have hmul :
                  ρ * (1 - q ^ 2) ≤
                    (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                simpa [mul_comm] using mul_le_mul_of_nonneg_right (ih 2) hρ_nonneg
              calc
                1 - q ^ (0 + 1) = ρ * (1 - q ^ 2) := by simpa using hstep_one.symm
                _ ≤ (P 2 : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := hmul
                _ = (P 1 : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) := hstep.symm
          | succ n =>
              have hleft_ne_top :
                  (P (n + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (1 - (r : ENNReal)) ≠ ⊤ :=
                ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [hr_top])
              have hright_ne_top :
                  (P (n + 3) : Measure Ω) (noHitHorizonLocal X 0 0 M) * (r : ENNReal) ≠ ⊤ :=
                ENNReal.mul_ne_top (measure_ne_top _ _) hr_top
              have hstep :
                  (P (n + 2) : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) =
                    (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) +
                      (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                have hstep' := congrArg ENNReal.toReal
                  (figure17_2_noHitHorizon_step_succ (r := r) (P := P) (X := X) n M)
                rw [ENNReal.toReal_add hleft_ne_top hright_ne_top, ENNReal.toReal_mul,
                  ENNReal.toReal_mul] at hstep'
                rw [ENNReal.toReal_sub_of_le r.2.2 (by simp)] at hstep'
                simpa [ρ, Measure.real_def, measure_ne_top _ _] using hstep'
              have hmul1 :
                  (1 - q ^ (n + 1)) * (1 - ρ) ≤
                    (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) := by
                exact mul_le_mul_of_nonneg_right (ih (n + 1)) hone_sub_nonneg
              have hmul2 :
                  (1 - q ^ (n + 3)) * ρ ≤
                    (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ := by
                exact mul_le_mul_of_nonneg_right (ih (n + 3)) hρ_nonneg
              calc
                1 - q ^ (n + 2) =
                    (1 - q ^ (n + 1)) * (1 - ρ) + (1 - q ^ (n + 3)) * ρ := by
                      symm
                      exact hstep_succ n
                _ ≤ (P (n + 1) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * (1 - ρ) +
                      (P (n + 3) : Measure Ω).real (noHitHorizonLocal X 0 0 M) * ρ :=
                      add_le_add hmul1 hmul2
                _ = (P (n + 2) : Measure Ω).real (noHitHorizonLocal X 0 0 (M + 1)) :=
                    hstep.symm

/-- Helper for Exercise 17.6.4: in the right-drift regime `1 / 2 < r < 1`, the anchor state `0`
is transient. -/
theorem figure17_2_zero_transient_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) (hr1 : (r : ENNReal) < 1) :
    IsTransientState P X 0 := by
  let ρ : ℝ := (r : ENNReal).toReal
  let q : ℝ := (1 - ρ) / ρ
  let μ1 : Measure Ω := P 1
  let hitWithin : ℕ → Set Ω := fun M ↦ {ω | ∃ n ∈ Set.Icc 1 M, X n ω = 0}
  have hr_top : (r : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt r.2.2 (by simp))
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal hr_top ENNReal.one_ne_top).2 hr1
  have hρ_gt_half : (1 / 2 : ℝ) < ρ := by
    simpa [ρ] using (ENNReal.toReal_lt_toReal (by simp) hr_top).2 hrhalf
  have hρ_pos : 0 < ρ := by
    linarith
  have hq_lt_one : q < 1 := by
    have hnum_lt : 1 - ρ < ρ := by
      linarith
    dsimp [q]
    have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
    field_simp [hρ_ne]
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (sub_nonneg.mpr hρ_lt_one.le) hρ_pos.le
  have hnohit_lower :
      ∀ k M : ℕ, 1 - q ^ k ≤ (P k : Measure Ω).real (noHitHorizonLocal X 0 0 M) :=
    figure17_2_noHitHorizon_real_lowerBound_of_half_lt
      (r := r) (P := P) (X := X) hrhalf hr1
  have hhitWithin_bound : ∀ M : ℕ, μ1.real (hitWithin M) ≤ q := by
    intro M
    have hprob :
        μ1.real (hitWithin M) = 1 - μ1.real (noHitHorizonLocal X 0 0 M) := by
      have hEq : hitWithin M = (noHitHorizonLocal X 0 0 M)ᶜ := by
        ext ω
        constructor
        · intro hω hnohit
          rcases hω with ⟨n, hn, hnx⟩
          exact (hnohit n hn.1 hn.2 (by simpa [zero_add] using hnx)).elim
        · intro hω
          by_contra hhit
          exact hω <| by
            intro n hn1 hnM hnEq
            exact hhit ⟨n, ⟨hn1, hnM⟩, by simpa [zero_add] using hnEq⟩
      rw [hEq, probReal_compl_eq_one_sub (μ := μ1)]
      exact
        figure17_2_measurableSet_noHitHorizon (X := X)
          ((inferInstance : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X).measurable_process)
          0 0 M
    have hlower : 1 - q ≤ μ1.real (noHitHorizonLocal X 0 0 M) := by
      simpa [q] using hnohit_lower 1 M
    rw [hprob]
    nlinarith
  have hUnion : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} = ⋃ M : ℕ, hitWithin M := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, ⟨by simpa using hn, le_rfl⟩, hnx⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      rcases hM with ⟨n, hn, hnx⟩
      exact ⟨n, hn.1, hnx⟩
  have hmono : Directed (· ⊆ ·) hitWithin := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_left _ _)⟩, hnx⟩
    · intro ω hω
      rcases hω with ⟨n, hn, hnx⟩
      exact ⟨n, ⟨hn.1, le_trans hn.2 (le_max_right _ _)⟩, hnx⟩
  have hμ1 :
      μ1 (⋃ M : ℕ, hitWithin M) = ⨆ M : ℕ, μ1 (hitWithin M) := hmono.measure_iUnion
  have hiSup_ne_top : (⨆ M : ℕ, μ1 (hitWithin M)) ≠ ⊤ := by
    apply ne_of_lt
    calc
      ⨆ M : ℕ, μ1 (hitWithin M) = μ1 (⋃ M : ℕ, hitWithin M) := hμ1.symm
      _ ≤ μ1 Set.univ := measure_mono (by intro ω hω; simp)
      _ = 1 := by simp [μ1]
      _ < ⊤ := by simp
  have hsup_le :
      ⨆ M : ℕ, μ1 (hitWithin M) ≤ ENNReal.ofReal q := by
    refine iSup_le fun M ↦ ?_
    have hboundReal :
        (μ1 (hitWithin M)).toReal ≤ (ENNReal.ofReal q).toReal := by
      simpa [Measure.real_def, ENNReal.toReal_ofReal hq_nonneg] using hhitWithin_bound M
    exact
      (ENNReal.toReal_le_toReal (measure_ne_top μ1 _) ENNReal.ofReal_ne_top).1 hboundReal
  have hhit_one_zero_le_q : (F[P, X]) 1 0 ≤ q := by
    rw [everHitsProbability_def, hUnion, Measure.real_def, hμ1]
    simpa [ENNReal.toReal_ofReal hq_nonneg] using
      (ENNReal.toReal_le_toReal hiSup_ne_top ENNReal.ofReal_ne_top).2 hsup_le
  have hhit_one_zero_lt_one : (F[P, X]) 1 0 < 1 := lt_of_le_of_lt hhit_one_zero_le_q hq_lt_one
  have hreturn_lt_one : (F[P, X]) 0 0 < 1 := by
    rw [figure17_2_returnProbability_zero_eq_hitProbability_one_zero (r := r)]
    exact hhit_one_zero_lt_one
  -- Proof comment: the right-drift lower bound leaves uniformly positive mass on the no-hit tail,
  -- so the return probability of `0` is strictly smaller than `1`.
  simpa [IsTransientState] using hreturn_lt_one

/-- Helper for Exercise 17.6.4: at `r = 1`, the chain moves deterministically one step to the
right. -/
theorem figure17_2_oneStepLaw_eq_dirac_of_eq_one
    (hr : (r : ENNReal) = 1) (x : ℕ) :
    discreteMatrixKernel (figure17_2TransitionMatrix r) x = Measure.dirac (x + 1) := by
  -- Proof comment: the row of the transition matrix has a single nonzero entry at `x + 1`.
  rw [Measure.ext_iff_singleton]
  intro y
  rw [discreteMatrixKernel_apply_singleton]
  cases x with
  | zero =>
      by_cases hy : y = 1
      · subst hy
        simp [figure17_2TransitionMatrix, hr]
      · simp [figure17_2TransitionMatrix, hr, hy]
  | succ n =>
      by_cases hy : y = n + 2
      · subst hy
        simp [figure17_2TransitionMatrix, hr]
      · simp [figure17_2TransitionMatrix, hr, hy]

/-- Helper for Exercise 17.6.4: at `r = 1`, every deterministic-time law is a Dirac mass on the
state reached by repeatedly moving one step to the right. -/
theorem figure17_2_powLaw_eq_dirac_of_eq_one
    (hr : (r : ENNReal) = 1) (x n : ℕ) :
    (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) x = Measure.dirac (x + n) := by
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step law is the identity kernel, hence the Dirac mass at `x`.
      rw [pow_zero]
      rw [Measure.ext_iff_singleton]
      intro y
      simpa using
        congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ)) (Kernel.id_apply x)
  | succ n ih =>
      -- Proof comment: one more kernel step from the inductive Dirac state uses the already
      -- identified deterministic one-step law.
      rw [Measure.ext_iff_singleton]
      intro y
      rw [Kernel.pow_succ_apply_eq_lintegral _ n x (measurableSet_singleton y)]
      rw [ih]
      simpa [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y),
        Nat.add_assoc] using
        congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ))
          (figure17_2_oneStepLaw_eq_dirac_of_eq_one (r := r) hr (x + n))

/-- Helper for Exercise 17.6.4: at `r = 1`, every state is transient because the chain never
returns after moving strictly to the right. -/
theorem figure17_2_allStatesTransient_of_eq_one
    (hr : (r : ENNReal) = 1) :
    ∀ x : ℕ, IsTransientState P X x := by
  intro x
  rw [IsTransientState, everHitsProbability_def]
  have hUnion :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | X n.succ ω = x} := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2 ⟨m, by simpa using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact ⟨n.succ, Nat.succ_pos _, by simpa using hn⟩
  have hslice_zero : ∀ n : ℕ, (P x : Measure Ω) {ω | X n.succ ω = x} = 0 := by
    intro n
    let hReal :
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
    have hpreimage : {ω | X n.succ ω = x} = X n.succ ⁻¹' ({x} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n.succ) (measurableSet_singleton x)]
    rw [hReal.transition_eq x n.succ]
    rw [figure17_2_powLaw_eq_dirac_of_eq_one (r := r) hr x n.succ]
    simp
  have hhit_zero :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 0 := by
    rw [hUnion]
    refine measure_iUnion_null ?_
    intro n
    exact hslice_zero n
  -- Proof comment: every positive-time return slice has zero mass, so the ever-return event has
  -- probability `0`, which is certainly `< 1`.
  simp [Measure.real_def, hhit_zero]

/-- Exercise 17.6.4: at the critical value `r = 1 / 2`, the anchor state `0` is recurrent. -/
theorem figure17_2_zeroRecurrent_of_eq_half
    (hr : (r : ℝ≥0∞) = 1 / 2) :
    IsRecurrentState P X 0 := by
  -- Route correction: the target-zero tail factorization is now in place. The remaining step is
  -- to close the half-critical recurrence by proving the first-step hit recursions above and then
  -- using boundedness of the resulting affine sequence to force the common difference to vanish.
  let a : ℕ → ℝ := fun k ↦ (F[P, X]) k 0
  have hnonneg : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    dsimp [a]
    rw [everHitsProbability_def]
    exact measureReal_nonneg
  have hone : ∀ k : ℕ, a k ≤ 1 := by
    intro k
    dsimp [a]
    rw [everHitsProbability_def]
    exact measureReal_le_one
  have hstepOne :
      a 1 = 1 / 2 + (1 / 2 : ℝ) * a 2 := by
    have hraw := figure17_2_hitProbability_zero_step_one (r := r) (P := P) (X := X)
    rw [hr] at hraw
    norm_num [figure17_2_one_sub_half] at hraw
    simpa [a] using hraw
  have hstepSucc :
      ∀ n : ℕ, 2 * a (n + 2) = a (n + 1) + a (n + 3) := by
    intro n
    have hraw := figure17_2_hitProbability_zero_step_succ (r := r) (P := P) (X := X) n
    rw [hr] at hraw
    norm_num [figure17_2_one_sub_half] at hraw
    nlinarith [hraw]
  let d : ℝ := a 2 - a 1
  have hdiff : ∀ n : ℕ, a (n + 2) - a (n + 1) = d := by
    intro n
    induction n with
    | zero =>
        simp [d]
    | succ n ih =>
        have hstep := hstepSucc n
        have : a (n + 3) - a (n + 2) = a (n + 2) - a (n + 1) := by
          nlinarith
        exact this.trans ih
  have hlinear : ∀ n : ℕ, a (n + 1) = a 1 + (n : ℝ) * d := by
    intro n
    induction n with
    | zero =>
        simp [d]
    | succ n ih =>
        have hdiffn : a (n + 2) - a (n + 1) = d := hdiff n
        calc
          a (n + 2) = a (n + 1) + d := by
            nlinarith
          _ = (a 1 + (n : ℝ) * d) + d := by rw [ih]
          _ = a 1 + ((n + 1 : ℕ) : ℝ) * d := by
            rw [Nat.cast_add]
            ring
  have hd_eq_zero : d = 0 := by
    by_contra hd_ne
    rcases lt_or_gt_of_ne hd_ne with hd_neg | hd_pos
    · have hpos : 0 < -d := by
        linarith
      obtain ⟨N, hN⟩ : ∃ N : ℕ, a 1 / (-d) < N := exists_nat_gt (a 1 / (-d))
      have hN' : a 1 < (N : ℝ) * (-d) := by
        rwa [div_lt_iff₀ hpos] at hN
      have hlt : a 1 + (N : ℝ) * d < 0 := by
        nlinarith [hN']
      have hlt' : a (N + 1) < 0 := by
        rw [hlinear N]
        exact hlt
      exact (not_lt_of_ge (hnonneg (N + 1))) hlt'
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 - a 1) / d < N := exists_nat_gt ((1 - a 1) / d)
      have hN' : 1 - a 1 < (N : ℝ) * d := by
        rwa [div_lt_iff₀ hd_pos] at hN
      have hgt : 1 < a 1 + (N : ℝ) * d := by
        nlinarith [hN']
      have hgt' : 1 < a (N + 1) := by
        rw [hlinear N]
        exact hgt
      exact (not_lt_of_ge (hone (N + 1))) hgt'
  have ha2_eq : a 2 = a 1 := by
    have : a 2 - a 1 = 0 := by
      simpa [d] using hd_eq_zero
    nlinarith
  have ha1_eq_one : a 1 = 1 := by
    rw [ha2_eq] at hstepOne
    nlinarith
  -- Proof comment: the return probability at `0` equals the hit probability of `0` from `1`, so
  -- the critical anchor closes once the harmonic recurrence forces `a 1 = 1`.
  rw [IsRecurrentState]
  simpa [a] using
    (figure17_2_returnProbability_zero_eq_hitProbability_one_zero (r := r) (P := P) (X := X)).trans
      ha1_eq_one

/-- Null-recurrence clause for Exercise 17.6.4 (2): if `r = 1 / 2`, then the Fig. 17.2 chain is
null recurrent. -/
theorem figure17_2_allStatesNullRecurrent_of_eq_half
    (hr : (r : ℝ≥0∞) = 1 / 2) :
    IsNullRecurrentMarkovChain P X := by
  have hr0 : 0 < (r : ℝ≥0∞) := by
    rw [hr]
    norm_num
  have hr1 : (r : ℝ≥0∞) < 1 := by
    rw [hr]
    norm_num
  have hzero : IsRecurrentState P X 0 :=
    figure17_2_zeroRecurrent_of_eq_half (r := r) (P := P) (X := X) hr
  intro x
  -- Proof comment: once the anchor state `0` is recurrent, irreducibility propagates
  -- recurrence to every state, and the critical singleton-vanishing theorem rules out positive
  -- recurrence everywhere.
  refine
    ⟨figure17_2_allStatesRecurrent_of_zero_recurrent
        (r := r) (P := P) (X := X) hr0 hr1 hzero x,
      figure17_2_not_positiveRecurrentState_of_eq_half (r := r) (P := P) (X := X) hr x⟩

/-- Helper for Exercise 17.6.4: the invariant measure of the degenerate boundary two-cycle
`0 ↔ 1` assigns mass `1 / 2` to each of the states `0` and `1`. -/
def figure17_2ZeroBoundaryCycleMeasure : Measure ℕ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- Helper for Exercise 17.6.4: the two-cycle measure on `{0, 1}` is a probability measure. -/
theorem figure17_2ZeroBoundaryCycleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure figure17_2ZeroBoundaryCycleMeasure := by
  -- Proof comment: both Dirac masses charge the whole space by `1`, so the two weights
  -- `1 / 2 + 1 / 2` normalize the total mass to `1`.
  have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    nth_rewrite 1 [← figure17_2_one_sub_half]
    exact tsub_add_cancel_of_le (show (1 / 2 : ℝ≥0∞) ≤ 1 by norm_num)
  refine ⟨?_⟩
  calc
    figure17_2ZeroBoundaryCycleMeasure Set.univ = (1 / 2 : ℝ≥0∞) + 1 / 2 := by
      simp [figure17_2ZeroBoundaryCycleMeasure]
    _ = 1 := hhalf

/-- Helper for Exercise 17.6.4: the probability distribution of the degenerate two-cycle
`0 ↔ 1`. -/
def figure17_2ZeroBoundaryCycleDistribution : ProbabilityMeasure ℕ :=
  ⟨figure17_2ZeroBoundaryCycleMeasure, figure17_2ZeroBoundaryCycleMeasure_isProbabilityMeasure⟩

/-- Helper for Exercise 17.6.4: the two-cycle distribution gives mass `1 / 2` to `{0}`. -/
theorem figure17_2ZeroBoundaryCycleDistribution_apply_zero :
    (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({0} : Set ℕ) = 1 / 2 := by
  -- Proof comment: only the Dirac mass at `0` contributes to the singleton `{0}`.
  change figure17_2ZeroBoundaryCycleMeasure ({0} : Set ℕ) = 1 / 2
  simp [figure17_2ZeroBoundaryCycleMeasure]

/-- Helper for Exercise 17.6.4: the two-cycle distribution gives mass `1 / 2` to `{1}`. -/
theorem figure17_2ZeroBoundaryCycleDistribution_apply_one :
    (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({1} : Set ℕ) = 1 / 2 := by
  -- Proof comment: only the Dirac mass at `1` contributes to the singleton `{1}`.
  change figure17_2ZeroBoundaryCycleMeasure ({1} : Set ℕ) = 1 / 2
  simp [figure17_2ZeroBoundaryCycleMeasure]

/-- Helper for Exercise 17.6.4: the two-cycle distribution vanishes on every singleton
`{n + 2}`. -/
theorem figure17_2ZeroBoundaryCycleDistribution_apply_succ_succ (n : ℕ) :
    (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({n + 2} : Set ℕ) = 0 := by
  -- Proof comment: both Dirac masses are supported on `{0, 1}`, so every singleton `{n + 2}`
  -- has zero mass.
  change figure17_2ZeroBoundaryCycleMeasure ({n + 2} : Set ℕ) = 0
  simp [figure17_2ZeroBoundaryCycleMeasure]

/-- Helper for Exercise 17.6.4: in the boundary case `r = 0`, the one-step dynamics are the
deterministic map `0 ↦ 1`, `n + 1 ↦ n`. -/
def figure17_2ZeroBoundaryNext : ℕ → ℕ
  | 0 => 1
  | n + 1 => n

/-- Helper for Exercise 17.6.4: when `r = 0`, the Fig. 17.2 kernel is the deterministic kernel
of the map `figure17_2ZeroBoundaryNext`. -/
theorem figure17_2ZeroBoundaryKernel_eq_deterministic
    (hr : (r : ℝ≥0∞) = 0) :
    discreteMatrixKernel (figure17_2TransitionMatrix r) =
      Kernel.deterministic figure17_2ZeroBoundaryNext
        (measurable_of_countable figure17_2ZeroBoundaryNext) := by
  -- Proof comment: on the discrete state space `ℕ`, each row has exactly one nonzero entry when
  -- `r = 0`, so the kernel agrees with the deterministic update `figure17_2ZeroBoundaryNext`.
  ext x s hs
  have hrow :
      discreteMatrixKernel (figure17_2TransitionMatrix r) x =
        (Kernel.deterministic figure17_2ZeroBoundaryNext
          (measurable_of_countable figure17_2ZeroBoundaryNext)) x := by
        refine Measure.ext_of_singleton ?_
        intro y
        rw [discreteMatrixKernel_apply_singleton, Kernel.deterministic_apply]
        cases x with
        | zero =>
            by_cases hy : y = 1
            · subst hy
              simp [figure17_2TransitionMatrix, hr, figure17_2ZeroBoundaryNext]
            · simp [figure17_2TransitionMatrix, hr, figure17_2ZeroBoundaryNext, hy]
        | succ n =>
            by_cases hy : y = n
            · subst hy
              simp [figure17_2TransitionMatrix, hr, figure17_2ZeroBoundaryNext]
            · simp [figure17_2TransitionMatrix, hr, figure17_2ZeroBoundaryNext, hy]
  simpa [hrow]

/-- Helper for Exercise 17.6.4: under `r = 0`, the `m`-step kernel is deterministic with value
`Nat.iterate figure17_2ZeroBoundaryNext m`. -/
theorem figure17_2ZeroBoundaryKernel_pow
    (hr : (r : ℝ≥0∞) = 0) :
    ∀ m : ℕ,
      discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m =
        Kernel.deterministic (Nat.iterate figure17_2ZeroBoundaryNext m)
          ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate m)
  := by
  intro m
  induction m with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity kernel, i.e. the deterministic
      -- kernel of `Nat.iterate _ 0 = id`.
      rw [pow_zero]
      change Kernel.id = Kernel.deterministic (Nat.iterate figure17_2ZeroBoundaryNext 0)
        ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate 0)
      rw [Kernel.id]
      rfl
  | succ m ih =>
      -- Proof comment: rewrite the `(m + 1)`-step kernel as one more composition of the
      -- deterministic one-step map with the deterministic `m`-step iterate.
      calc
        discreteMatrixKernel (figure17_2TransitionMatrix r) ^ (m + 1)
          = (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ 1) ∘ₖ
              (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) := by
                rw [show m + 1 = 1 + m by omega, Kernel.pow_add]
        _ =
            (Kernel.deterministic figure17_2ZeroBoundaryNext
              (measurable_of_countable figure17_2ZeroBoundaryNext)) ∘ₖ
              (discreteMatrixKernel (figure17_2TransitionMatrix r) ^ m) := by
                  rw [pow_one, figure17_2ZeroBoundaryKernel_eq_deterministic (r := r) hr]
        _ =
            (Kernel.deterministic figure17_2ZeroBoundaryNext
              (measurable_of_countable figure17_2ZeroBoundaryNext)) ∘ₖ
              Kernel.deterministic (Nat.iterate figure17_2ZeroBoundaryNext m)
                ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate m) := by
                  rw [ih]
        _ =
            Kernel.deterministic
              (figure17_2ZeroBoundaryNext ∘ Nat.iterate figure17_2ZeroBoundaryNext m)
              ((measurable_of_countable figure17_2ZeroBoundaryNext).comp
                ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate m)) := by
                  rw [Kernel.deterministic_comp_deterministic]
        _ =
            Kernel.deterministic (Nat.iterate figure17_2ZeroBoundaryNext (m + 1))
              ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate (m + 1)) := by
                  apply Kernel.deterministic_congr
                  funext x
                  simp [Function.iterate_succ_apply']

/-- Helper for Exercise 17.6.4: applying `figure17_2ZeroBoundaryNext` to a state already bounded
by `b ≥ 1` keeps the state within the same bound. -/
theorem figure17_2ZeroBoundaryNext_le_of_le
    {x b : ℕ} (hb : 1 ≤ b) (hx : x ≤ b) :
    figure17_2ZeroBoundaryNext x ≤ b := by
  -- Proof comment: `0` jumps to `1 ≤ b`, and every positive state steps down by one.
  cases x with
  | zero =>
      simpa [figure17_2ZeroBoundaryNext] using hb
  | succ n =>
      exact le_trans (Nat.le_succ n) hx

/-- Helper for Exercise 17.6.4: once a state is at most `b` with `b ≥ 1`, every further
zero-boundary iterate remains at most `b`. -/
theorem figure17_2ZeroBoundaryIterate_le_of_le
    {x b : ℕ} (hb : 1 ≤ b) (hx : x ≤ b) :
    ∀ m : ℕ, Nat.iterate figure17_2ZeroBoundaryNext m x ≤ b := by
  intro m
  induction m with
  | zero =>
      simpa using hx
  | succ m ih =>
      -- Proof comment: one more iterate stays below the same bound because the deterministic
      -- update preserves every interval `[0, b]` with `b ≥ 1`.
      simpa [Function.iterate_succ_apply'] using
        figure17_2ZeroBoundaryNext_le_of_le (hb := hb) (hx := ih)

/-- Helper for Exercise 17.6.4: after any positive number of zero-boundary steps, the state
started from `n + 2` lies at most at `n + 1`. -/
theorem figure17_2ZeroBoundaryIterate_le_pred (n m : ℕ) :
    Nat.iterate figure17_2ZeroBoundaryNext (m + 1) (n + 2) ≤ n + 1 := by
  have hb : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  -- Proof comment: the first step sends `n + 2` to `n + 1`, and every later iterate stays
  -- within the same upper bound.
  simpa [Function.iterate_succ_apply, figure17_2ZeroBoundaryNext] using
    (figure17_2ZeroBoundaryIterate_le_of_le (x := n + 1) (b := n + 1) hb le_rfl m)

/-- Helper for Exercise 17.6.4: the two-cycle distribution is invariant for the Fig. 17.2 kernel
when `r = 0`. -/
theorem figure17_2ZeroBoundaryCycleDistribution_isInvariant
    (hr : (r : ℝ≥0∞) = 0) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) := by
  rw [figure17_2KernelInvariant_iff_singleton]
  intro x
  cases x with
  | zero =>
      -- Proof comment: only state `1` can send mass into `0`, and the two-cycle gives equal
      -- masses to `{0}` and `{1}`.
      calc
        ∑' y : ℕ,
            (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
              figure17_2TransitionMatrix r y 0
          = ∑' y : ℕ,
              (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
                (if y = 1 then 1 else 0) := by
                  congr with y
                  rw [figure17_2TransitionMatrix_apply_zero]
                  simp [hr]
        _ = (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({1} : Set ℕ) := by
              rw [tsum_eq_single 1]
              · simp
              · intro b hb
                simp [hb]
        _ = (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({0} : Set ℕ) := by
              rw [figure17_2ZeroBoundaryCycleDistribution_apply_one,
                figure17_2ZeroBoundaryCycleDistribution_apply_zero]
  | succ n =>
      cases n with
      | zero =>
          -- Proof comment: the only incoming mass to `1` comes from `0` and `2`, but the
          -- two-cycle measure vanishes at `2`.
          calc
            ∑' y : ℕ,
                (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
                  figure17_2TransitionMatrix r y 1
              = ∑' y : ℕ,
                  (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
                    (if y = 0 then 1 else if y = 2 then 1 else 0) := by
                      congr with y
                      rw [figure17_2TransitionMatrix_apply_one]
                      simp [hr]
            _ =
                (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({0} : Set ℕ) +
                  (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({2} : Set ℕ) := by
                    rw [ENNReal.tsum_eq_add_tsum_ite 0]
                    rw [tsum_eq_single 2]
                    · simp
                    · intro b hb
                      by_cases hb0 : b = 0
                      · simp [hb0]
                      · simp [hb, hb0]
            _ = (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({0} : Set ℕ) := by
                  rw [figure17_2ZeroBoundaryCycleDistribution_apply_succ_succ 0]
                  simp
            _ = (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({1} : Set ℕ) := by
                  rw [figure17_2ZeroBoundaryCycleDistribution_apply_zero,
                    figure17_2ZeroBoundaryCycleDistribution_apply_one]
      | succ n =>
          -- Proof comment: for every state `n + 2 ≥ 2`, the only possible incoming predecessor
          -- at `r = 0` is `n + 3`, and the two-cycle measure gives that singleton mass `0`.
          calc
            ∑' y : ℕ,
                (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
                  figure17_2TransitionMatrix r y (n + 2)
              = ∑' y : ℕ,
                  (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({y} : Set ℕ) *
                    (if y = n + 3 then 1 else 0) := by
                      congr with y
                      by_cases hy1 : y = n + 1
                      · by_cases hy3 : y = n + 3
                        · omega
                        · rw [figure17_2TransitionMatrix_apply_succ_succ]
                          simp [hr, hy1, hy3]
                      · by_cases hy3 : y = n + 3
                        · rw [figure17_2TransitionMatrix_apply_succ_succ]
                          simp [hr, hy1, hy3]
                        · rw [figure17_2TransitionMatrix_apply_succ_succ]
                          simp [hr, hy1, hy3]
            _ = (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({n + 3} : Set ℕ) := by
                  rw [tsum_eq_single (n + 3)]
                  · simp
                  · intro b hb
                    simp [hb]
            _ = 0 := figure17_2ZeroBoundaryCycleDistribution_apply_succ_succ (n + 1)
            _ =
                (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({n + 2} : Set ℕ) := by
                  symm
                  exact figure17_2ZeroBoundaryCycleDistribution_apply_succ_succ n

/-- In the degenerate boundary case `r = 0`, the state `0` belongs to the deterministic two-cycle
`0 ↔ 1`, so it is positive recurrent. -/
theorem figure17_2_zero_positiveRecurrent_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) :
    IsPositiveRecurrentState P X 0 := by
  have hπinvPow :
      Kernel.Invariant
        ((fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) 1)
        (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) := by
    simpa [pow_one] using
      figure17_2ZeroBoundaryCycleDistribution_isInvariant (r := r) hr
  have hmass :
      0 < (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({0} : Set ℕ) := by
    rw [figure17_2ZeroBoundaryCycleDistribution_apply_zero]
    norm_num
  -- Proof comment: the invariant two-cycle distribution charges `{0}` positively, so Theorem
  -- 17.51's companion API upgrades state `0` to positive recurrence.
  exact
    isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) hπinvPow hmass

/-- In the degenerate boundary case `r = 0`, the state `1` belongs to the deterministic two-cycle
`0 ↔ 1`, so it is positive recurrent. -/
theorem figure17_2_one_positiveRecurrent_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) :
    IsPositiveRecurrentState P X 1 := by
  have hπinvPow :
      Kernel.Invariant
        ((fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) 1)
        (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) := by
    simpa [pow_one] using
      figure17_2ZeroBoundaryCycleDistribution_isInvariant (r := r) hr
  have hmass :
      0 < (figure17_2ZeroBoundaryCycleDistribution : Measure ℕ) ({1} : Set ℕ) := by
    rw [figure17_2ZeroBoundaryCycleDistribution_apply_one]
    norm_num
  -- Proof comment: the same invariant two-cycle distribution charges `{1}` positively, so the
  -- companion Kac inequality yields positive recurrence of state `1`.
  exact
    isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n)
      (P := P) (X := X) hπinvPow hmass

/-- In the degenerate boundary case `r = 0`, every state `n + 2` drifts deterministically toward
the two-cycle `0 ↔ 1`, so it is transient. -/
theorem figure17_2_states_ge_two_transient_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) (n : ℕ) :
    IsTransientState P X (n + 2) := by
  rw [IsTransientState, everHitsProbability_def]
  have hUnion :
      {ω | ∃ m : ℕ, 0 < m ∧ X m ω = n + 2} = ⋃ m : ℕ, {ω | X m.succ ω = n + 2} := by
    ext ω
    constructor
    · rintro ⟨m, hm, hmx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
      exact Set.mem_iUnion.2 ⟨k, by simpa using hmx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      exact ⟨m.succ, Nat.succ_pos _, by simpa using hm⟩
  have hslice_zero : ∀ m : ℕ, (P (n + 2) : Measure Ω) {ω | X m.succ ω = n + 2} = 0 := by
    intro m
    let hReal :
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ k) P X := inferInstance
    have hpreimage : {ω | X m.succ ω = n + 2} = X m.succ ⁻¹' ({n + 2} : Set ℕ) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process m.succ) (measurableSet_singleton (n + 2))]
    rw [hReal.transition_eq (n + 2) m.succ]
    rw [figure17_2ZeroBoundaryKernel_pow (r := r) hr (m + 1)]
    rw [Kernel.deterministic_apply'
      ((measurable_of_countable figure17_2ZeroBoundaryNext).iterate (m + 1))
      (n + 2) (measurableSet_singleton (n + 2))]
    rw [Function.iterate_succ_apply']
    have hle :
        Nat.iterate figure17_2ZeroBoundaryNext (m + 1) (n + 2) ≤ n + 1 :=
      figure17_2ZeroBoundaryIterate_le_pred n m
    have hne :
        Nat.iterate figure17_2ZeroBoundaryNext (m + 1) (n + 2) ≠ n + 2 := by
      omega
    have hne' :
        figure17_2ZeroBoundaryNext
            (Nat.iterate figure17_2ZeroBoundaryNext m (n + 2)) ≠ n + 2 := by
          simpa [Function.iterate_succ_apply'] using hne
    simp [hne']
  have hreturn_zero :
      (P (n + 2) : Measure Ω) {ω | ∃ m : ℕ, 0 < m ∧ X m ω = n + 2} = 0 := by
    rw [hUnion]
    refine measure_iUnion_null ?_
    intro m
    exact hslice_zero m
  -- Proof comment: every positive-time return slice has zero mass, so the total return
  -- probability is `0`, which is strictly smaller than `1`.
  simp [Measure.real_def, hreturn_zero]

/-- Transience clause for Exercise 17.6.4 (3): if `1 / 2 < r`, then the Fig. 17.2 chain is
transient. -/
theorem figure17_2_allStatesTransient_of_half_lt
    (hrhalf : 1 / 2 < (r : ℝ≥0∞)) :
    ∀ x : ℕ, IsTransientState P X x := by
  by_cases hr_eq_one : (r : ℝ≥0∞) = 1
  · -- Proof comment: at `r = 1`, the chain is the deterministic right shift, so every state is
    -- transient without any irreducibility argument.
    exact figure17_2_allStatesTransient_of_eq_one (r := r) (P := P) (X := X) hr_eq_one
  · have hr0 : 0 < (r : ℝ≥0∞) := lt_trans (by norm_num) hrhalf
    have hr1 : (r : ℝ≥0∞) < 1 := lt_of_le_of_ne r.2.2 hr_eq_one
    have hzero : IsTransientState P X 0 :=
      figure17_2_zero_transient_of_half_lt (r := r) (P := P) (X := X) hrhalf hr1
    -- Proof comment: once state `0` is transient, irreducibility propagates that transience to
    -- every state via the Chapter 17 owner theorem.
    exact
      figure17_2_allStatesTransient_of_zero_transient
        (r := r) (P := P) (X := X) hr0 hr1 hzero

/-- Source-wording clause for Exercise 17.6.4 (4): for `r ∈ {0} ∪ (1 / 2, 1]` the chain is
transient. In the chapter owner API we record this source-facing clause as non-recurrence of the
chain, while the sharper owner-level classification of the exceptional boundary case `r = 0` is
split out into companion theorems above. -/
theorem figure17_2_not_recurrent_of_eq_zero_or_half_lt
    (hr : (r : ℝ≥0∞) = 0 ∨ 1 / 2 < (r : ℝ≥0∞)) :
    ¬ IsRecurrentMarkovChain P X := by
  intro hrec
  rcases hr with hr0 | hrhalf
  · have htrans : IsTransientState P X 2 := by
      simpa using figure17_2_states_ge_two_transient_of_eq_zero
        (r := r) (P := P) (X := X) hr0 0
    rw [IsTransientState, hrec 2] at htrans
    simp at htrans
  · have htrans : IsTransientState P X 0 :=
      figure17_2_allStatesTransient_of_half_lt (r := r) (P := P) (X := X) hrhalf 0
    rw [IsTransientState, hrec 0] at htrans
    simp at htrans

end

end ProbabilityTheory
