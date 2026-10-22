/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_52
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

private def resetWalkTransientExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: `1 / (n + 2)^2` lies in `[0, 1]` for every `n`, so subtracting it from `1`
-- again gives a value in `[0, 1]`.
private theorem resetWalkTransientExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkTransientExampleSequenceReal := by
  intro n
  have hq_nonneg : 0 ≤ 1 / (n + 2 : ℝ) ^ (2 : ℕ) := by
    positivity
  have hq_mul :
      (1 / (n + 2 : ℝ) ^ (2 : ℕ)) * (n + 2 : ℝ) ^ (2 : ℕ) = 1 := by
    field_simp
  have hden_ge_one : 1 ≤ (n + 2 : ℝ) ^ (2 : ℕ) := by
    have hn : (1 : ℝ) ≤ n + 2 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    nlinarith
  have hq_le_one : 1 / (n + 2 : ℝ) ^ (2 : ℕ) ≤ 1 := by
    nlinarith
  -- Proof comment: the square defect lies in `[0, 1]`, so subtracting it from `1` preserves the
  -- probability interval.
  constructor
  · simpa [resetWalkTransientExampleSequenceReal] using sub_nonneg.mpr hq_le_one
  · simpa [resetWalkTransientExampleSequenceReal] using sub_le_self (1 : ℝ) hq_nonneg

/-- A transient example sequence for the reset walk, with square-summable defects `1 - p_n`. -/
def resetWalkTransientExampleSequence : ResetWalkParameters :=
  ⟨resetWalkTransientExampleSequenceReal,
    resetWalkTransientExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkNullRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ)

-- Proof sketch: since `n + 2 ≥ 2`, the harmonic term `1 / (n + 2)` lies in `[0, 1 / 2]`,
-- hence `1 - 1 / (n + 2)` lies in `[1 / 2, 1]`.
private theorem resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkNullRecurrentExampleSequenceReal := by
  intro n
  have hq_nonneg : 0 ≤ 1 / (n + 2 : ℝ) := by
    positivity
  have hq_mul : (1 / (n + 2 : ℝ)) * (n + 2 : ℝ) = 1 := by
    field_simp
  have hden_ge_one : 1 ≤ (n + 2 : ℝ) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hq_le_one : 1 / (n + 2 : ℝ) ≤ 1 := by
    nlinarith
  -- Proof comment: the harmonic defect lies in `[0, 1]`, so the complementary jump
  -- probability still lies in `[0, 1]`.
  constructor
  · simpa [resetWalkNullRecurrentExampleSequenceReal] using sub_nonneg.mpr hq_le_one
  · simpa [resetWalkNullRecurrentExampleSequenceReal] using sub_le_self (1 : ℝ) hq_nonneg

/-- A null recurrent example sequence for the reset walk, with harmonic defects `1 - p_n`. -/
def resetWalkNullRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkNullRecurrentExampleSequenceReal,
    resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkPositiveRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun _ ↦ 1 / 2

-- Proof sketch: the constant value `1 / 2` lies in `[0, 1]`.
private theorem resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkPositiveRecurrentExampleSequenceReal := by
  intro n
  -- Proof comment: the constant value `1 / 2` is already inside the probability interval.
  constructor <;> norm_num [resetWalkPositiveRecurrentExampleSequenceReal]

/-- A positive recurrent geometric example sequence for the reset walk. -/
def resetWalkPositiveRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkPositiveRecurrentExampleSequenceReal,
    resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkDyadicSpikeSequenceReal : ℕ → ℝ :=
  fun n ↦
    if 2 ^ Nat.log2 n = n then
      1 / 3
    else
      1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: both branches lie in `[0, 1]`: the spike branch is the constant `1 / 3`, and
-- the background branch is the transient example sequence.
private theorem resetWalkDyadicSpikeSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkDyadicSpikeSequenceReal := by
  intro n
  by_cases hpow : 2 ^ Nat.log2 n = n
  · -- Proof comment: on the spike branch the value is the fixed probability `1 / 3`.
    constructor <;> norm_num [resetWalkDyadicSpikeSequenceReal, hpow]
  · -- Proof comment: off the dyadic spikes we fall back to the transient background sequence.
    simpa [resetWalkDyadicSpikeSequenceReal, resetWalkTransientExampleSequenceReal, hpow] using
      resetWalkTransientExampleSequenceReal_isProbabilitySequence n

/-- A dyadic-spike sequence for the reset walk: at powers of two the upward-jump probability is
`1 / 3`, while away from powers of two the defects are square-summable. -/
def resetWalkDyadicSpikeSequence : ResetWalkParameters :=
  ⟨resetWalkDyadicSpikeSequenceReal, resetWalkDyadicSpikeSequenceReal_isProbabilitySequence⟩

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}

section ResetWalkRealization

variable {p : ResetWalkParameters}
variable [IsMarkovProcessRealization (fun n ↦ resetWalkKernel p ^ n) P X]

/- Exercise 17.6.5 (1): this recurrence criterion is already the source-facing reset-walk theorem
from Example 17.52. -/
recall resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub

-- Proof sketch: use the tail-sum formula `𝔼[τ] = ∑_{n ≥ 0} ℙ(τ > n)` for the first return time to
-- `0`; for the reset walk, the survival probability `ℙ_0(τ_0^1 > n)` is exactly the prefix
-- product `∏_{k < n} p_k`.
/-- Part (2) of Exercise 17.6.5: the expected first return time to `0` in the reset walk is the series
`M = ∑_{n=0}^\infty ∏_{k=0}^{n-1} p_k`, represented here by `resetWalkMassSeries p`. -/
theorem expectedFirstReturnTime_resetWalk_zero_eq_massSeries :
    expectedFirstReturnTime P X 0 = resetWalkMassSeries p := by
  -- Proof comment: identify the expected first return time with the tail-probability series and
  -- then rewrite each tail term by the explicit reset-walk prefix-product formula.
  rw [expectedFirstReturnTime_eq_tsum_tailProbabilities
    (κ := fun n ↦ resetWalkKernel p ^ n) (P := P) (X := X) 0]
  rw [resetWalkMassSeries_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  simpa using resetWalkFirstReturnTail_zero_eq_prefixProduct
    (p := p) (P := P) (X := X) n

/- Exercise 17.6.5 (3): this positive-recurrence criterion is already the source-facing
reset-walk theorem from Example 17.52. -/
recall resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top

/-- Helper for Exercise 17.6.5: if both the upward and reset probabilities are strictly positive,
then the realized reset walk communicates between every two states. -/
lemma resetWalk_isIrreducible_of_pos_and_reset_pos
    (hp : ∀ n : ℕ, 0 < p n) (hreset : ∀ n : ℕ, 0 < 1 - p n) :
    IsIrreducibleMarkovChain P X := by
  let hReal : IsMarkovProcessRealization (fun n ↦ resetWalkKernel p ^ n) P X := inferInstance
  refine
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ resetWalkKernel p ^ n) P X).2 ?_
  intro x y hxy
  by_cases hy0 : y = 0
  · subst hy0
    have hstep :
        0 < ((resetWalkKernel p ^ 1) x) ({0} : Set ℕ) := by
      rw [pow_one, resetWalkKernel, discreteMatrixKernel_apply_singleton]
      rw [resetWalkTransitionMatrix_apply_zero]
      exact ENNReal.ofReal_pos.mpr (hreset x)
    -- Proof comment: if the target is `0`, the positive reset mass gives a one-step path.
    exact greenFunctionFrom_one_pos_of_posStepMass P X (by simp) hstep
  · have hstepToZero :
        0 < ((resetWalkKernel p ^ 1) x) ({0} : Set ℕ) := by
      rw [pow_one, resetWalkKernel, discreteMatrixKernel_apply_singleton]
      rw [resetWalkTransitionMatrix_apply_zero]
      exact ENNReal.ofReal_pos.mpr (hreset x)
    have hstepFromZero :
        0 < ((resetWalkKernel p ^ y) 0) ({y} : Set ℕ) := by
      rw [resetWalkKernelPow_apply_zero_singleton]
      rw [resetWalkPrefixProductENNReal_eq_ofReal]
      exact ENNReal.ofReal_pos.mpr (resetWalkPrefixProduct_pos p hp y)
    have hcomp :
        0 < (((resetWalkKernel p ^ y) ∘ₖ (resetWalkKernel p ^ 1)) x) ({y} : Set ℕ) :=
      compSingletonMass_pos_of_posSingletonMass hstepToZero hstepFromZero
    have hstep :
        0 < ((resetWalkKernel p ^ y.succ) x) ({y} : Set ℕ) := by
      simpa [Nat.succ_eq_add_one, Nat.add_comm, hReal.semigroup.comp_eq 1 y] using hcomp
    -- Proof comment: otherwise, reset once to `0` and then follow the positive monotone path
    -- from `0` to `y`.
    exact
      greenFunctionFrom_one_pos_of_posStepMass
        (κ := fun n ↦ resetWalkKernel p ^ n) P X (Nat.succ_pos y) hstep

/-- Helper for Exercise 17.6.5: once state `0` fails to be positive recurrent, every state fails
to be positive recurrent as well because each state resets to `0` in one positive step. -/
lemma resetWalk_notPositiveRecurrentState_of_notPositiveRecurrent_zero
    (hreset : ∀ n : ℕ, 0 < 1 - p n) (hzero : ¬ IsPositiveRecurrentState P X 0) :
    ∀ x : ℕ, ¬ IsPositiveRecurrentState P X x := by
  let hReal : IsMarkovProcessRealization (fun n ↦ resetWalkKernel p ^ n) P X := inferInstance
  intro x hx
  by_cases hx0 : x = 0
  · exact hzero (by simpa [hx0] using hx)
  · have hstep :
        0 < ((resetWalkKernel p ^ 1) x) ({0} : Set ℕ) := by
      rw [pow_one, resetWalkKernel, discreteMatrixKernel_apply_singleton]
      rw [resetWalkTransitionMatrix_apply_zero]
      exact ENNReal.ofReal_pos.mpr (hreset x)
    have hgreen : 0 < (G[P, X; 1]) x 0 :=
      greenFunctionFrom_one_pos_of_posStepMass P X (by simp) hstep
    have hhit : 0 < (F[P, X]) x 0 :=
      (greenFunctionFrom_one_pos_iff_everHitsProbability_pos
        P X (fun n ↦ hReal.measurable_process n) x 0).1 hgreen
    have hzero_pos : IsPositiveRecurrentState P X 0 :=
      isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
        (κ := fun n ↦ resetWalkKernel p ^ n) (P := P) (X := X) hx hhit
    exact hzero hzero_pos

end ResetWalkRealization

/-- Helper for Exercise 17.6.5: the null-recurrent example has the exact prefix-product formula
`∏_{k < n} (1 - 1 / (k + 2)) = 1 / (n + 1)`. -/
lemma resetWalkNullExample_prefixProduct
    (n : ℕ) :
    resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence n = 1 / (n + 1 : ℝ) := by
  induction n with
  | zero =>
      -- Proof comment: the empty prefix product is `1`, matching `1 / (0 + 1)`.
      simp [resetWalkPrefixProduct_zero]
  | succ n ih =>
      -- Proof comment: unfold one more factor and simplify the harmonic telescoping identity.
      calc
        resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence (n + 1)
          = resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence n *
              resetWalkNullRecurrentExampleSequence n := by
                rw [resetWalkPrefixProduct_succ]
        _ = (1 / (n + 1 : ℝ)) * (1 - 1 / (n + 2 : ℝ)) := by
              have hseq :
                  resetWalkNullRecurrentExampleSequence n = 1 - 1 / (n + 2 : ℝ) := by
                rfl
              rw [ih, hseq]
        _ = 1 / (n + 2 : ℝ) := by
              field_simp
              ring
        _ = 1 / (↑(n + 1) + 1 : ℝ) := by
              have hcast : (n + 2 : ℝ) = ↑(n + 1) + 1 := by
                rw [Nat.cast_add]
                ring
              rw [hcast]

/-- Helper for Exercise 17.6.5: summability of the real prefix-product sequence is equivalent to
finiteness of the `ℝ≥0∞` mass series `resetWalkMassSeries p`. -/
lemma resetWalkMassSeries_lt_top_of_summable_prefixProduct
    (p : ResetWalkParameters) (h : Summable (resetWalkPrefixProduct p)) :
    resetWalkMassSeries p < ∞ := by
  have hsummableNN :
      Summable (fun n : ℕ ↦
        (show NNReal from
          ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩)) :=
    NNReal.summable_coe.1 h
  have hEq :
      (fun n : ℕ ↦ resetWalkPrefixProductENNReal p n) =
        fun n : ℕ ↦
          ((show NNReal from
            ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩) : ℝ≥0∞) := by
    funext n
    rfl
  have hne : resetWalkMassSeries p ≠ ∞ := by
    rw [resetWalkMassSeries_eq_tsum, hEq, ENNReal.tsum_coe_ne_top_iff_summable]
    exact hsummableNN
  exact lt_of_le_of_ne le_top hne

section TransientExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n) P X]

-- Proof sketch: for `resetWalkTransientExampleSequence`, the defect series
-- `∑ 1 / (n + 2)^2` is summable, so part (1) gives nonrecurrence; irreducibility of the reset
-- walk then identifies the regime as one where every state is transient, hence Definition 17.30
-- applies vacuously.
/-- Part (4) of Exercise 17.6.5: part (iii)(a). The sequence
`p_n = 1 - 1 / (n + 2)^2` gives a transient reset walk. -/
theorem resetWalkTransientExample_isTransientMarkovChain :
    IsTransientMarkovChain (resetWalkTransitionMatrix resetWalkTransientExampleSequence) P X :=
  by
    have hp : ∀ n : ℕ, 0 < resetWalkTransientExampleSequence n := by
      intro n
      have hq_nonneg : 0 ≤ 1 / (n + 2 : ℝ) ^ (2 : ℕ) := by
        positivity
      have hq_mul :
          (1 / (n + 2 : ℝ) ^ (2 : ℕ)) * (n + 2 : ℝ) ^ (2 : ℕ) = 1 := by
        field_simp
      have hden_gt_one : 1 < (n + 2 : ℝ) ^ (2 : ℕ) := by
        have hn : (1 : ℝ) < n + 2 := by
          have hn0 : (0 : ℝ) ≤ n := by positivity
          linarith
        nlinarith
      have hq_lt_one : 1 / (n + 2 : ℝ) ^ (2 : ℕ) < 1 := by
        nlinarith
      -- Proof comment: the square defect is strictly smaller than `1`, so the upward
      -- probability is strictly positive.
      simpa [resetWalkTransientExampleSequence, resetWalkTransientExampleSequenceReal] using
        sub_pos.2 hq_lt_one
    have hreset : ∀ n : ℕ, 0 < 1 - resetWalkTransientExampleSequence n := by
      intro n
      -- Proof comment: the reset probability is exactly the positive square defect.
      have hdefect : 0 < 1 / (n + 2 : ℝ) ^ (2 : ℕ) := by
        positivity
      simpa [resetWalkTransientExampleSequence, resetWalkTransientExampleSequenceReal] using hdefect
    have hdefect_summable : Summable (fun n : ℕ ↦ 1 - resetWalkTransientExampleSequence n) := by
      refine ((Real.summable_one_div_nat_add_rpow 2 2).2 (by norm_num)).congr ?_
      intro n
      simp [resetWalkTransientExampleSequence, resetWalkTransientExampleSequenceReal]
    have hnot_recurrent : ¬ IsRecurrentMarkovChain P X := by
      intro hrec
      exact
        ((resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub
          (p := resetWalkTransientExampleSequence) (P := P) (X := X) hp).1 hrec)
          hdefect_summable
    have hirr : IsIrreducibleMarkovChain P X :=
      resetWalk_isIrreducible_of_pos_and_reset_pos
        (p := resetWalkTransientExampleSequence) (P := P) (X := X) hp hreset
    have hnot_recurrent_zero : ¬ IsRecurrentState P X 0 := by
      intro hrec0
      have hrec : IsRecurrentMarkovChain P X := by
        intro y
        by_cases hy : y = 0
        · simpa [hy] using hrec0
        · exact
            isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
              (κ := fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n)
              (P := P) (X := X) hrec0 (hirr 0 y)
      exact hnot_recurrent hrec
    have htransient : ∀ x : ℕ, IsTransientState P X x := by
      intro x
      have hx_not_recurrent : ¬ IsRecurrentState P X x := by
        intro hxrec
        have hrec0 :
            IsRecurrentState P X 0 :=
          isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
            (κ := fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n)
            (P := P) (X := X) hxrec (hirr x 0)
        exact hnot_recurrent_zero hrec0
      have hxx_le_one : (F[P, X]) x x ≤ 1 := by
        rw [everHitsProbability_def]
        exact measureReal_le_one
      -- Proof comment: once recurrence of `x` is ruled out, the return probability must be
      -- strictly smaller than `1`, which is exactly transience.
      rw [IsTransientState]
      by_contra hnot
      have hxx_eq_one : (F[P, X]) x x = 1 := le_antisymm hxx_le_one (le_of_not_gt hnot)
      exact hx_not_recurrent (by simpa [IsRecurrentState] using hxx_eq_one)
    exact
      letI :
          IsMarkovProcessRealization
            (fun n ↦
              discreteMatrixKernel (resetWalkTransitionMatrix resetWalkTransientExampleSequence) ^ n)
            P X := by
              simpa [resetWalkKernel] using
                (inferInstance :
                  IsMarkovProcessRealization
                    (fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n) P X)
      isTransientMarkovChain_of_forall_isTransientState
        (resetWalkTransitionMatrix resetWalkTransientExampleSequence) P X htransient

end TransientExample

section NullRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkNullRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for `p_n = 1 - 1 / (n + 2)`, the defect series is harmonic and hence divergent,
-- while the prefix products are comparable to `1 / (n + 1)`, so the return-time series is
-- infinite. Parts (1) and (3) therefore give recurrence but not positive recurrence.
/-- Part (5) of Exercise 17.6.5: part (iii)(b). The sequence
`p_n = 1 - 1 / (n + 2)` gives a null recurrent reset walk. -/
theorem resetWalkNullRecurrentExample_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := by
  have hp : ∀ n : ℕ, 0 < resetWalkNullRecurrentExampleSequence n := by
    intro n
    have hq_nonneg : 0 ≤ 1 / (n + 2 : ℝ) := by
      positivity
    have hq_mul : (1 / (n + 2 : ℝ)) * (n + 2 : ℝ) = 1 := by
      field_simp
    have hden_gt_one : 1 < (n + 2 : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    have hq_lt_one : 1 / (n + 2 : ℝ) < 1 := by
      nlinarith
    -- Proof comment: the harmonic defect is strictly smaller than `1`, so the upward
    -- probability stays strictly positive.
    simpa [resetWalkNullRecurrentExampleSequence, resetWalkNullRecurrentExampleSequenceReal] using
      sub_pos.2 hq_lt_one
  have hreset : ∀ n : ℕ, 0 < 1 - resetWalkNullRecurrentExampleSequence n := by
    intro n
    -- Proof comment: the reset probability is the positive harmonic defect `1 / (n + 2)`.
    have hdefect : 0 < 1 / (n + 2 : ℝ) := by
      positivity
    simpa [resetWalkNullRecurrentExampleSequence, resetWalkNullRecurrentExampleSequenceReal] using
      hdefect
  have hnotSummable :
      ¬ Summable (fun n : ℕ ↦ 1 - resetWalkNullRecurrentExampleSequence n) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm,
      resetWalkNullRecurrentExampleSequence, resetWalkNullRecurrentExampleSequenceReal] using
      mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 2).1)
        Real.not_summable_one_div_natCast
  have hrec :
      IsRecurrentMarkovChain P X :=
    (resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub
      (p := resetWalkNullRecurrentExampleSequence) (P := P) (X := X) hp).2 hnotSummable
  have hnot_pos_zero : ¬ IsPositiveRecurrentState P X 0 := by
    intro hpos0
    have hmass_lt_top :
        resetWalkMassSeries resetWalkNullRecurrentExampleSequence < ∞ := by
      -- Proof comment: positive recurrence of `0` would force the mass series to be finite via
      -- the explicit return-time formula.
      simpa [IsPositiveRecurrentState, expectedFirstReturnTime_resetWalk_zero_eq_massSeries
        (p := resetWalkNullRecurrentExampleSequence) (P := P) (X := X)] using hpos0
    have hsummableNN :
        Summable (fun n : ℕ ↦
          (show NNReal from
            ⟨resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence n,
              resetWalkPrefixProduct_nonneg resetWalkNullRecurrentExampleSequence n⟩)) := by
      have hEq :
          (fun n : ℕ ↦ resetWalkPrefixProductENNReal resetWalkNullRecurrentExampleSequence n) =
            fun n : ℕ ↦
              ((show NNReal from
                ⟨resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence n,
                  resetWalkPrefixProduct_nonneg resetWalkNullRecurrentExampleSequence n⟩) : ℝ≥0∞) := by
        funext n
        rfl
      have hne : resetWalkMassSeries resetWalkNullRecurrentExampleSequence ≠ ∞ :=
        ne_of_lt hmass_lt_top
      rw [resetWalkMassSeries_eq_tsum, hEq, ENNReal.tsum_coe_ne_top_iff_summable] at hne
      exact hne
    have hsummable :
        Summable (resetWalkPrefixProduct resetWalkNullRecurrentExampleSequence) :=
      NNReal.summable_coe.2 hsummableNN
    have hshift :
        Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
      refine hsummable.congr ?_
      intro n
      simpa using resetWalkNullExample_prefixProduct n
    have hharmonic :
        ¬ Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).1)
          Real.not_summable_one_div_natCast
    exact hharmonic hshift
  have hnot_pos :
      ∀ x : ℕ, ¬ IsPositiveRecurrentState P X x :=
    resetWalk_notPositiveRecurrentState_of_notPositiveRecurrent_zero
      (p := resetWalkNullRecurrentExampleSequence) (P := P) (X := X) hreset hnot_pos_zero
  intro x
  -- Proof comment: part (1) gives recurrence at every state, while the harmonic return-time
  -- series rules out positive recurrence and the reset step transports that failure to all states.
  exact ⟨hrec x, hnot_pos x⟩

end NullRecurrentExample

section PositiveRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkPositiveRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for the constant choice `p_n = 1 / 2`, the prefix products form a geometric
-- sequence, so `M` is finite; part (3) then yields positive recurrence.
/-- Part (6) of Exercise 17.6.5: part (iii)(c). The constant sequence `p_n = 1 / 2` gives a positive
recurrent reset walk. -/
theorem resetWalkPositiveRecurrentExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := by
  have hp : ∀ n : ℕ, 0 < resetWalkPositiveRecurrentExampleSequence n := by
    intro n
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    simpa [resetWalkPositiveRecurrentExampleSequence,
      resetWalkPositiveRecurrentExampleSequenceReal] using hhalf
  have hprefix_eq :
      ∀ n : ℕ,
        resetWalkPrefixProduct resetWalkPositiveRecurrentExampleSequence n = (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        -- Proof comment: the empty product matches the zeroth geometric term.
        simp [resetWalkPrefixProduct_zero]
    | succ n ih =>
        -- Proof comment: every extra factor is again `1 / 2`, so the prefix product follows the
        -- geometric recursion exactly.
        calc
          resetWalkPrefixProduct resetWalkPositiveRecurrentExampleSequence (n + 1)
            = resetWalkPrefixProduct resetWalkPositiveRecurrentExampleSequence n *
                resetWalkPositiveRecurrentExampleSequence n := by
                  rw [resetWalkPrefixProduct_succ]
          _ = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) := by
                have hseq : resetWalkPositiveRecurrentExampleSequence n = (1 / 2 : ℝ) := by
                  rfl
                rw [ih, hseq]
          _ = (1 / 2 : ℝ) ^ (n + 1) := by
                rw [pow_succ]
  have hsummable :
      Summable (resetWalkPrefixProduct resetWalkPositiveRecurrentExampleSequence) := by
    refine (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).congr ?_
    intro n
    symm
    exact hprefix_eq n
  have hmass_lt_top :
      resetWalkMassSeries resetWalkPositiveRecurrentExampleSequence < ∞ :=
    resetWalkMassSeries_lt_top_of_summable_prefixProduct
      resetWalkPositiveRecurrentExampleSequence hsummable
  -- Proof comment: the constant sequence produces a geometric prefix-product series, so the mass
  -- series is finite and the reset-walk criterion yields positive recurrence.
  exact
    (resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top
      (p := resetWalkPositiveRecurrentExampleSequence) (P := P) (X := X) hp).2 hmass_lt_top

end PositiveRecurrentExample

/-- Helper for Exercise 17.6.5: every dyadic spike occurs at the left endpoint `2 ^ m` of its
dyadic block. -/
lemma resetWalkDyadicSpike_eq_oneThird_at_powTwo
    (m : ℕ) :
    resetWalkDyadicSpikeSequence (2 ^ m) = (1 / 3 : ℝ) := by
  -- Route correction: instead of reasoning about the whole prefix at once, first normalize the
  -- dyadic spike value at the left endpoint of each block.
  have hlog : Nat.log2 (2 ^ m) = m := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num : 1 < 2)]
  -- Proof comment: powers of two satisfy the spike branch of the defining `if`.
  simp [resetWalkDyadicSpikeSequence, resetWalkDyadicSpikeSequenceReal, hlog]

/-- Helper for Exercise 17.6.5: strict interior points of a dyadic block follow the square-defect
background branch of `resetWalkDyadicSpikeSequence`. -/
lemma resetWalkDyadicSpike_eq_background_of_between_powTwo
    {m k : ℕ} (hleft : 2 ^ m < k) (hright : k < 2 ^ (m + 1)) :
    resetWalkDyadicSpikeSequence k = 1 - 1 / (k + 2 : ℝ) ^ (2 : ℕ) := by
  -- Proof comment: on the strict interior of the block, `k` cannot itself be a power of two.
  have hlog : Nat.log2 k = m := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_eq_of_pow_le_of_lt_pow hleft.le hright
  have hnotSpike : 2 ^ Nat.log2 k ≠ k := by
    rw [hlog]
    exact ne_of_lt hleft
  simp [resetWalkDyadicSpikeSequence, resetWalkDyadicSpikeSequenceReal, hnotSpike]

/-- Helper for Exercise 17.6.5: each dyadic block contributes at most one factor `1 / 3` to the
prefix product, because every other factor in the block is at most `1`. -/
lemma resetWalkDyadicSpike_blockProduct_le_oneThird
    (m : ℕ) :
    ∏ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k ≤ (1 / 3 : ℝ) := by
  have hlt : 2 ^ m < 2 ^ (m + 1) := by
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
  have htail_nonneg :
      ∀ k ∈ Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)), 0 ≤ resetWalkDyadicSpikeSequence k := by
    intro k hk
    exact (resetWalkDyadicSpikeSequence.property k).1
  have htail_le_one :
      ∀ k ∈ Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k ≤ 1 := by
    intro k hk
    exact (resetWalkDyadicSpikeSequence.property k).2
  have htail_prod_le :
      ∏ k ∈ Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k ≤ 1 := by
    exact Finset.prod_le_one htail_nonneg htail_le_one
  -- Proof comment: split off the unique spike at the left endpoint and bound the rest of the
  -- block by `1`.
  calc
    ∏ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k
      = resetWalkDyadicSpikeSequence (2 ^ m) *
          ∏ k ∈ Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k := by
            rw [Finset.prod_eq_prod_Ico_succ_bot hlt]
    _ ≤ (1 / 3 : ℝ) * 1 := by
          rw [resetWalkDyadicSpike_eq_oneThird_at_powTwo]
          exact mul_le_mul_of_nonneg_left htail_prod_le (by norm_num)
    _ = (1 / 3 : ℝ) := by ring

/-- Helper for Exercise 17.6.5: each square background defect is bounded by the corresponding
telescoping harmonic increment. -/
lemma squareDefect_le_harmonicDiff
    (k : ℕ) :
    1 / (k + 2 : ℝ) ^ (2 : ℕ) ≤ 1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ) := by
  have hk : (k + 1 : ℝ) ≤ k + 2 := by
    nlinarith
  have hmul_le : ((k + 1 : ℝ) * (k + 2 : ℝ)) ≤ (k + 2 : ℝ) ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ (k + 2 : ℝ) := by
      positivity
    simpa [pow_two] using mul_le_mul_of_nonneg_right hk hnonneg
  have hpos : 0 < ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
    positivity
  have hcompare :
      1 / (k + 2 : ℝ) ^ (2 : ℕ) ≤ 1 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
    exact one_div_le_one_div_of_le hpos hmul_le
  -- Proof comment: after comparing denominators, the remaining expression telescopes exactly.
  calc
    1 / (k + 2 : ℝ) ^ (2 : ℕ) ≤ 1 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := hcompare
    _ = 1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ) := by
          field_simp
          ring

/-- Helper for Exercise 17.6.5: the square background defects on any finite interval are bounded
by a telescoping harmonic difference. -/
lemma squareDefect_sum_Ico_le_telescoping
    (a b : ℕ) (hab : a ≤ b) :
    Finset.sum (Finset.Ico a b) (fun k ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) ≤
      1 / (a + 1 : ℝ) - 1 / (b + 1 : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero =>
      -- Proof comment: the interval `Ico a a` is empty.
      simp
  | succ n ih =>
      have hsplit :
          Finset.sum (Finset.Ico a (a + (n + 1))) (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) =
            Finset.sum (Finset.Ico a (a + n)) (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) +
              1 / (a + n + 2 : ℝ) ^ (2 : ℕ) := by
        simpa [Nat.add_assoc] using
          (Finset.sum_Ico_succ_top
            (a := a) (b := a + n) (f := fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ))
            (Nat.le_add_right a n))
      have hih :
          Finset.sum (Finset.Ico a (a + n)) (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) ≤
            1 / (a + 1 : ℝ) - 1 / (a + n + 1 : ℝ) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          ih (Nat.le_add_right a n)
      have hstep :
          1 / (a + n + 2 : ℝ) ^ (2 : ℕ) ≤
            1 / (a + n + 1 : ℝ) - 1 / (a + n + 2 : ℝ) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          squareDefect_le_harmonicDiff (a + n)
      -- Proof comment: peel off the top summand and compare it with one more harmonic step.
      rw [hsplit]
      have hmain :
          Finset.sum (Finset.Ico a (a + n)) (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) +
              1 / (a + n + 2 : ℝ) ^ (2 : ℕ) ≤
            1 / (a + 1 : ℝ) - 1 / (a + n + 2 : ℝ) := by
        calc
        Finset.sum (Finset.Ico a (a + n)) (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) +
            1 / (a + n + 2 : ℝ) ^ (2 : ℕ)
          ≤ (1 / (a + 1 : ℝ) - 1 / (a + n + 1 : ℝ)) +
              (1 / (a + n + 1 : ℝ) - 1 / (a + n + 2 : ℝ)) := by
                exact add_le_add hih
                  hstep
        _ = 1 / (a + 1 : ℝ) - 1 / (a + n + 2 : ℝ) := by ring
      refine le_trans hmain ?_
      exact le_of_eq (by
        norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm])

/-- Helper for Exercise 17.6.5: the defect accumulated on one dyadic block is the spike defect
`2 / 3` plus a telescoping background contribution. -/
lemma resetWalkDyadicSpike_blockDefect_le
    (m : ℕ) :
    Finset.sum (Finset.Ico (2 ^ m) (2 ^ (m + 1)))
        (fun k ↦ 1 - resetWalkDyadicSpikeSequence k) ≤
      (2 / 3 : ℝ) + (1 / (2 ^ m + 1 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ)) := by
  have hlt : 2 ^ m < 2 ^ (m + 1) := by
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
  have htail_eq :
      Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
          (fun k : ℕ ↦ 1 - resetWalkDyadicSpikeSequence k) =
        Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
          (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_left : 2 ^ m < k := (Finset.mem_Ico.mp hk).1
    have hk_right : k < 2 ^ (m + 1) := (Finset.mem_Ico.mp hk).2
    rw [resetWalkDyadicSpike_eq_background_of_between_powTwo hk_left hk_right]
    ring
  have htail_sq :
      Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
          (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) ≤
        1 / ((2 ^ m + 1) + 1 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      squareDefect_sum_Ico_le_telescoping (2 ^ m + 1) (2 ^ (m + 1)) (Nat.succ_le_of_lt hlt)
  have hhead :
      1 / (2 ^ m + 2 : ℝ) ≤ 1 / (2 ^ m + 1 : ℝ) := by
    have hpos : 0 < (2 ^ m + 1 : ℝ) := by
      positivity
    have hle : (2 ^ m + 1 : ℝ) ≤ 2 ^ m + 2 := by
      nlinarith
    exact one_div_le_one_div_of_le hpos hle
  -- Proof comment: split off the spike at `2 ^ m`, rewrite the tail by the background formula,
  -- and finish with the telescoping estimate.
  have htail_sq' :
      Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
          (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) ≤
        1 / (2 ^ m + 2 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ) := by
    convert htail_sq using 1 <;> ring_nf
  calc
    Finset.sum (Finset.Ico (2 ^ m) (2 ^ (m + 1))) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k)
      = (1 - resetWalkDyadicSpikeSequence (2 ^ m)) +
          Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
            (fun k : ℕ ↦ 1 - resetWalkDyadicSpikeSequence k) := by
              simpa using
                (Finset.sum_eq_sum_Ico_succ_bot
                  (a := 2 ^ m) (b := 2 ^ (m + 1))
                  (f := fun k : ℕ ↦ 1 - resetWalkDyadicSpikeSequence k) hlt)
    _ = (2 / 3 : ℝ) +
          Finset.sum (Finset.Ico (2 ^ m + 1) (2 ^ (m + 1)))
            (fun k : ℕ ↦ 1 / (k + 2 : ℝ) ^ (2 : ℕ)) := by
              rw [htail_eq, resetWalkDyadicSpike_eq_oneThird_at_powTwo]
              ring
    _ ≤ (2 / 3 : ℝ) + (1 / (2 ^ m + 2 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right htail_sq' (2 / 3 : ℝ)
    _ ≤ (2 / 3 : ℝ) + (1 / (2 ^ m + 1 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ)) := by
          nlinarith

/-- Helper for Exercise 17.6.5: the cumulative defect up to time `2 ^ m` is controlled by
`1 + (2 / 3) m` together with a telescoping remainder. -/
lemma resetWalkDyadicSpike_defectSum_pow_two_le
    (m : ℕ) :
    Finset.sum (Finset.range (2 ^ m)) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k) ≤
      1 + (2 / 3 : ℝ) * m - 1 / (2 ^ m + 1 : ℝ) := by
  induction m with
  | zero =>
      -- Proof comment: up to time `1`, only the background defect at `0` appears.
      norm_num [resetWalkDyadicSpikeSequence, resetWalkDyadicSpikeSequenceReal]
  | succ m ih =>
      have hlt : 2 ^ m < 2 ^ (m + 1) := by
        exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
      -- Proof comment: split the range at `2 ^ m`, apply the inductive bound to the old prefix,
      -- and use the dyadic block estimate on the new block.
      calc
        ∑ k ∈ Finset.range (2 ^ (m + 1)), (1 - resetWalkDyadicSpikeSequence k)
          = ∑ k ∈ Finset.range (2 ^ m), (1 - resetWalkDyadicSpikeSequence k) +
              ∑ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (1 - resetWalkDyadicSpikeSequence k) := by
                symm
                exact Finset.sum_range_add_sum_Ico (fun k ↦ 1 - resetWalkDyadicSpikeSequence k)
                  (Nat.le_of_lt hlt)
        _ ≤ (1 + (2 / 3 : ℝ) * m - 1 / (2 ^ m + 1 : ℝ)) +
              ((2 / 3 : ℝ) + (1 / (2 ^ m + 1 : ℝ) - 1 / (2 ^ (m + 1) + 1 : ℝ))) := by
                exact add_le_add ih (resetWalkDyadicSpike_blockDefect_le m)
        _ = 1 + (2 / 3 : ℝ) * ((m : ℝ) + 1) - 1 / (2 ^ (m + 1) + 1 : ℝ) := by
              ring
        _ = 1 + (2 / 3 : ℝ) * (((m + 1 : ℕ) : ℝ)) - 1 / (2 ^ (m + 1) + 1 : ℝ) := by
              have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by
                rw [Nat.cast_add]
                norm_num
              rw [hcast]

/-- Helper for Exercise 17.6.5: by time `2^m`, the dyadic-spike prefix product has accumulated
`m` factors equal to `1 / 3`, while every other factor is at most `1`. -/
lemma resetWalkDyadicSpike_prefixProduct_pow_two_le
    (m : ℕ) :
    resetWalkPrefixProduct resetWalkDyadicSpikeSequence (2 ^ m) ≤ (1 / 3 : ℝ) ^ m :=
  by
    induction m with
    | zero =>
        -- Proof comment: before time `1`, the prefix product is just the single factor at `0`,
        -- which is a probability and hence at most `1`.
        rw [show (2 : ℕ) ^ 0 = 1 by norm_num]
        rw [resetWalkPrefixProduct_succ, resetWalkPrefixProduct_zero]
        simpa using (resetWalkDyadicSpikeSequence.property 0).2
    | succ m ih =>
        have hlt : 2 ^ m < 2 ^ (m + 1) := by
          exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
        have hsplit :
            resetWalkPrefixProduct resetWalkDyadicSpikeSequence (2 ^ (m + 1)) =
              resetWalkPrefixProduct resetWalkDyadicSpikeSequence (2 ^ m) *
                ∏ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k := by
          -- Proof comment: the new dyadic prefix is the old prefix times the product over the
          -- next dyadic block.
          unfold resetWalkPrefixProduct
          symm
          exact Finset.prod_range_mul_prod_Ico resetWalkDyadicSpikeSequence (Nat.le_of_lt hlt)
        have hblock_nonneg :
            0 ≤ ∏ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k := by
          exact Finset.prod_nonneg fun k hk ↦ (resetWalkDyadicSpikeSequence.property k).1
        calc
          resetWalkPrefixProduct resetWalkDyadicSpikeSequence (2 ^ (m + 1))
            = resetWalkPrefixProduct resetWalkDyadicSpikeSequence (2 ^ m) *
                ∏ k ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), resetWalkDyadicSpikeSequence k := hsplit
          _ ≤ (1 / 3 : ℝ) ^ m * (1 / 3 : ℝ) := by
                exact mul_le_mul ih (resetWalkDyadicSpike_blockProduct_le_oneThird m)
                  hblock_nonneg (pow_nonneg (by norm_num) _)
          _ = (1 / 3 : ℝ) ^ (m + 1) := by
                rw [pow_succ]

/-- Exercise 17.6.5: at time `2^m`, the exponential comparison term is bounded below
by the contribution of the `m` dyadic spikes together with a uniformly bounded background defect
sum. -/
lemma resetWalkDyadicSpike_expTerm_pow_two_ge
    (m : ℕ) :
    Real.exp
        (-Finset.sum (Finset.range (2 ^ m)) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k)) ≥
      Real.exp (-(1 + (2 / 3 : ℝ) * m)) :=
  by
    have hsum_le :
        Finset.sum (Finset.range (2 ^ m)) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k) ≤
          1 + (2 / 3 : ℝ) * m := by
      have hstrong := resetWalkDyadicSpike_defectSum_pow_two_le m
      have htail_nonneg : 0 ≤ 1 / (2 ^ m + 1 : ℝ) := by
        positivity
      -- Proof comment: the stronger cumulative defect bound differs only by a nonnegative tail.
      nlinarith
    have hneg :
        -(1 + (2 / 3 : ℝ) * m) ≤
          -Finset.sum (Finset.range (2 ^ m)) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k) := by
      nlinarith
    -- Proof comment: monotonicity of `Real.exp` turns the upper bound on the defect sum into the
    -- desired lower bound on the exponential comparison term.
    have hexp :
        Real.exp (-(1 + (2 / 3 : ℝ) * m)) ≤
          Real.exp (-Finset.sum (Finset.range (2 ^ m))
            (fun k ↦ 1 - resetWalkDyadicSpikeSequence k)) :=
      Real.exp_le_exp.mpr hneg
    simpa [ge_iff_le] using hexp

section DyadicSpikeExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkDyadicSpikeSequence ^ n) P X]

-- Proof sketch: each dyadic spike contributes a factor `1 / 3` to the prefix product, so along
-- the interval `[2^m, 2^(m + 1))` the product is bounded by a multiple of `3^{-m}`; this makes
-- the mass series `M` summable, and part (3) yields positive recurrence.
/-- Part (7) of Exercise 17.6.5: part (iii)(d). The dyadic-spike sequence gives a positive recurrent reset
walk. -/
theorem resetWalkDyadicSpikeExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := by
  let f : ℕ → ℝ := resetWalkPrefixProduct resetWalkDyadicSpikeSequence
  have hp : ∀ n : ℕ, 0 < resetWalkDyadicSpikeSequence n := by
    intro n
    by_cases hpow : 2 ^ Nat.log2 n = n
    · simpa [resetWalkDyadicSpikeSequence, resetWalkDyadicSpikeSequenceReal, hpow] using
        (show (0 : ℝ) < 1 / 3 by norm_num)
    · have hq_mul :
          (1 / (n + 2 : ℝ) ^ (2 : ℕ)) * (n + 2 : ℝ) ^ (2 : ℕ) = 1 := by
        field_simp
      have hden_gt_one : 1 < (n + 2 : ℝ) ^ (2 : ℕ) := by
        have hn : (1 : ℝ) < n + 2 := by
          have hn0 : (0 : ℝ) ≤ n := by positivity
          linarith
        nlinarith
      have hq_lt_one : 1 / (n + 2 : ℝ) ^ (2 : ℕ) < 1 := by
        nlinarith
      simpa [resetWalkDyadicSpikeSequence, resetWalkDyadicSpikeSequenceReal, hpow] using
        sub_pos.2 hq_lt_one
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := fun n ↦
    resetWalkPrefixProduct_nonneg resetWalkDyadicSpikeSequence n
  have hf_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    induction hmn with
    | refl =>
        exact le_rfl
    | @step n hmn ih =>
        calc
          f (n + 1) = f n * resetWalkDyadicSpikeSequence n := by
              simpa [f] using resetWalkPrefixProduct_succ resetWalkDyadicSpikeSequence n
          _ ≤ f n := by
              have hfn_nonneg : 0 ≤ f n := hf_nonneg n
              have hstep_le : resetWalkDyadicSpikeSequence n ≤ 1 :=
                (resetWalkDyadicSpikeSequence.property n).2
              nlinarith
          _ ≤ f m := ih
  have hcond_le :
      ∀ m : ℕ, (2 : ℝ) ^ m * f (2 ^ m) ≤ (2 / 3 : ℝ) ^ m := by
    intro m
    calc
      (2 : ℝ) ^ m * f (2 ^ m)
        ≤ (2 : ℝ) ^ m * (1 / 3 : ℝ) ^ m := by
            exact mul_le_mul_of_nonneg_left
              (resetWalkDyadicSpike_prefixProduct_pow_two_le m) (by positivity)
      _ = (2 / 3 : ℝ) ^ m := by
            rw [← mul_pow]
            norm_num
  have hcond_summable :
      Summable (fun m : ℕ ↦ (2 : ℝ) ^ m * f (2 ^ m)) := by
    exact
      Summable.of_nonneg_of_le
        (fun m ↦ mul_nonneg (pow_nonneg (by positivity) _) (hf_nonneg _))
        hcond_le
        (summable_geometric_of_lt_one (by positivity : 0 ≤ (2 / 3 : ℝ))
          (by norm_num : (2 / 3 : ℝ) < 1))
  have hsummable : Summable f :=
    (summable_condensed_iff_of_nonneg hf_nonneg hf_mono).1 hcond_summable
  have hmass_lt_top :
      resetWalkMassSeries resetWalkDyadicSpikeSequence < ∞ :=
    resetWalkMassSeries_lt_top_of_summable_prefixProduct
      resetWalkDyadicSpikeSequence hsummable
  -- Proof comment: Cauchy condensation reduces summability of the dyadic-spike prefix products to
  -- the geometric bound on the dyadic subsequence `2^m * f (2^m)`.
  exact
    (resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top
      (p := resetWalkDyadicSpikeSequence) (P := P) (X := X) hp).2 hmass_lt_top

end DyadicSpikeExample

-- Proof sketch: up to time `n`, the dyadic spikes contribute about `(2 / 3) log₂ n` to the defect
-- sum, while the square-summable background contributes only a bounded amount. Hence the
-- exponential comparison terms are comparable to `n^{-2 / (3 * log 2)}`, whose exponent is
-- strictly smaller than `1`, so the series is not summable.
/-- Part (8) of Exercise 17.6.5: part (iii)(d). For the dyadic-spike sequence, the exponential comparison
series `∑ exp ( - ∑_{k < n} (1 - p_k))` is still divergent. -/
theorem resetWalkDyadicSpikeExample_expSeries_not_summable :
    ¬ Summable
      (fun n ↦
        Real.exp
          (-Finset.sum (Finset.range n) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k))) := by
  let f : ℕ → ℝ := fun n ↦
    Real.exp (-Finset.sum (Finset.range n) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k))
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hf_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    induction hmn with
    | refl =>
        exact le_rfl
    | @step n hmn ih =>
        calc
          f (n + 1) = f n * Real.exp (-(1 - resetWalkDyadicSpikeSequence n)) := by
              dsimp [f]
              rw [Finset.sum_range_succ, neg_add, Real.exp_add]
          _ ≤ f n := by
              have hfn_nonneg : 0 ≤ f n := hf_nonneg n
              have hdef_nonneg : 0 ≤ 1 - resetWalkDyadicSpikeSequence n :=
                sub_nonneg.mpr (resetWalkDyadicSpikeSequence.property n).2
              have hfactor_le : Real.exp (-(1 - resetWalkDyadicSpikeSequence n)) ≤ 1 := by
                exact Real.exp_le_one_iff.mpr (by nlinarith)
              nlinarith
          _ ≤ f m := ih
  let base : ℝ := (2 : ℝ) * Real.exp (-(2 / 3 : ℝ))
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    have happrox : (2 / 3 : ℝ) < 0.6931471803 := by
      norm_num
    exact lt_trans happrox Real.log_two_gt_d9
  have hexp_lt_two : Real.exp (2 / 3 : ℝ) < 2 := by
    calc
      Real.exp (2 / 3 : ℝ) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
      _ = 2 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hbase_gt_one : 1 < base := by
    have hpos : 0 < Real.exp (2 / 3 : ℝ) := Real.exp_pos _
    rw [show base = 2 / Real.exp (2 / 3 : ℝ) by
      unfold base
      rw [Real.exp_neg]
      ring]
    exact (lt_div_iff₀ hpos).2 (by simpa using hexp_lt_two)
  have hcond_ge :
      ∀ m : ℕ, Real.exp (-1) * base ^ m ≤ (2 : ℝ) ^ m * f (2 ^ m) := by
    intro m
    have hlower := resetWalkDyadicSpike_expTerm_pow_two_ge m
    calc
      Real.exp (-1) * base ^ m
        = (2 : ℝ) ^ m * Real.exp (-(1 + (2 / 3 : ℝ) * m)) := by
            rw [show (-(1 + (2 / 3 : ℝ) * m)) = (-1 : ℝ) + m * (-(2 / 3 : ℝ)) by ring]
            rw [Real.exp_add, Real.exp_nat_mul, mul_pow]
            ring
      _ ≤ (2 : ℝ) ^ m * f (2 ^ m) := by
            exact mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcond_not_summable :
      ¬ Summable (fun m : ℕ ↦ (2 : ℝ) ^ m * f (2 ^ m)) := by
    intro hcond
    have hgeom :
        Summable (fun m : ℕ ↦ Real.exp (-1) * base ^ m) := by
      exact
        Summable.of_nonneg_of_le
          (fun m ↦ mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
          hcond_ge hcond
    have hratio : Summable (fun m : ℕ ↦ base ^ m) := by
      exact (summable_mul_left_iff (by positivity : Real.exp (-1) ≠ 0)).1 hgeom
    have hnorm_lt : ‖base‖ < 1 := summable_geometric_iff_norm_lt_one.mp hratio
    have hnorm_ge : 1 ≤ ‖base‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact le_of_lt hbase_gt_one
      · positivity
    exact not_lt_of_ge hnorm_ge hnorm_lt
  intro hf
  exact hcond_not_summable ((summable_condensed_iff_of_nonneg hf_nonneg hf_mono).2 hf)

end ProbabilityTheory
