/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_38

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The Bernoulli sequence space `{0,1}^ℕ`, modeled as `ℕ → Bool`. -/
abbrev BernoulliSequence := ℕ → Bool

/-- The fair Bernoulli product measure on `BernoulliSequence`. -/
noncomputable def fairBernoulliMeasure : Measure BernoulliSequence :=
  Measure.infinitePi fun _ : ℕ ↦ (PMF.uniformOfFintype Bool).toMeasure

/-- The textbook round payoff attached to one coin toss: `false` is the loss `-1`, `true` is the
win `1`. -/
def petersburgRoundPayoff : Bool → ℝ
  | false => -1
  | true => 1

@[simp] theorem petersburgRoundPayoff_false : petersburgRoundPayoff false = -1 := rfl
@[simp] theorem petersburgRoundPayoff_true : petersburgRoundPayoff true = 1 := rfl

/-- The textbook doubling stake: before round `n + 1`, the gambler stakes `2^n` exactly when the
first `n` rounds have all been losses, and otherwise stakes `0`. -/
def petersburgStake (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  if ∀ k < n, ω k = false then (2 : ℝ) ^ n else 0

/-- The cumulative Petersburg gain `S_n = ∑_{k < n} H_k D_k`. -/
def petersburgPartialSum (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  ∑ k ∈ Finset.range n, petersburgStake k ω * petersburgRoundPayoff (ω k)

/-- Helper for Example 9.40: after `n` rounds, the Petersburg gain is `1 - 2^n` exactly on the
all-loss prefix event and equals `1` once a win has occurred. -/
theorem petersburgPartialSum_eq_if_allPrefixLosses (n : ℕ) (ω : BernoulliSequence) :
    petersburgPartialSum n ω =
      if ∀ k < n, ω k = false then 1 - (2 : ℝ) ^ n else 1 := by
  induction n with
  | zero =>
      -- The empty sum matches the empty-prefix branch `1 - 2^0 = 0`.
      simp [petersburgPartialSum]
  | succ n ih =>
      -- Freeze the first `n` rounds as the main branching invariant, then inspect round `n`.
      have hsplit :
          petersburgPartialSum (n + 1) ω =
            petersburgPartialSum n ω + petersburgStake n ω * petersburgRoundPayoff (ω n) := by
        -- Separate the final summand from the earlier cumulative gain.
        rw [petersburgPartialSum, Finset.sum_range_succ, petersburgPartialSum]
      by_cases hprefix : ∀ k < n, ω k = false
      · have hstake : petersburgStake n ω = (2 : ℝ) ^ n := by
          rw [petersburgStake, if_pos hprefix]
        rw [hsplit, ih, if_pos hprefix]
        cases hωn : ω n with
        | false =>
            have hall : ∀ k < n + 1, ω k = false := by
              -- One more loss extends the all-loss prefix by one step.
              intro k hk
              by_cases hkn : k = n
              · simpa [hkn] using hωn
              · exact hprefix k (by omega)
            rw [if_pos hall]
            -- Another loss subtracts the current doubled stake.
            simp [hstake, pow_succ]
            ring
        | true =>
            have hnotall : ¬ ∀ k < n + 1, ω k = false := by
              -- A win at time `n` breaks the longer all-loss prefix exactly at that index.
              intro hall
              have hnfalse : ω n = false := hall n (by omega)
              simp [hωn] at hnfalse
            rw [if_neg hnotall]
            -- The first win at time `n` recovers the net profit `1`.
            simp [hstake]
      · have hstake : petersburgStake n ω = 0 := by
          rw [petersburgStake, if_neg hprefix]
        have hnotall : ¬ ∀ k < n + 1, ω k = false := by
          -- If an earlier prefix already contains a win, the longer prefix cannot be all losses.
          intro hall
          exact hprefix (fun k hk ↦ hall k (by omega))
        rw [hsplit, ih, if_neg hprefix, if_neg hnotall]
        -- After the first win, all later stakes vanish, so the partial sum stays at `1`.
        simp [hstake]

/-- The `{-1,1}`-valued Petersburg round-payoff process on the fair Bernoulli sequence space,
obtained by evaluating the Chapter 4 payoff map `petersburgRoundPayoff` along the coordinate
process. -/
def petersburgRoundPayoffProcess : ℕ → BernoulliSequence → ℝ :=
  fun n ω ↦ petersburgRoundPayoff (ω n)

/-- The Petersburg round-payoff process is strongly measurable at every time. -/
theorem petersburgRoundPayoffProcess_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (petersburgRoundPayoffProcess n) := by
  -- The payoff coordinate is the measurable finite-valued payoff map composed with evaluation.
  simpa [petersburgRoundPayoffProcess] using
    ((measurable_of_finite petersburgRoundPayoff).comp (measurable_pi_apply n)).stronglyMeasurable

local notation "X" => partialSum petersburgRoundPayoffProcess

private theorem petersburgCumulativePayoffProcess_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (X n) :=
  (partialSum_measurable petersburgRoundPayoffProcess
    (fun n ↦ (petersburgRoundPayoffProcess_stronglyMeasurable n).measurable) n).stronglyMeasurable

/-- The natural filtration generated by the cumulative Petersburg payoff process. -/
def petersburgPayoffFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace BernoulliSequence) :=
  Filtration.natural X petersburgCumulativePayoffProcess_stronglyMeasurable

/-- Helper for Example 9.40: the Petersburg payoff coordinates are independent under the fair
Bernoulli product measure. -/
private theorem petersburgRoundPayoffProcess_iIndep :
    iIndepFun petersburgRoundPayoffProcess fairBernoulliMeasure := by
  -- Compose the independent coordinate projections on the Bernoulli product space with the fixed
  -- payoff map `false ↦ -1`, `true ↦ 1`.
  have h :
      iIndepFun (fun i (ω : BernoulliSequence) ↦ petersburgRoundPayoff (ω i))
        fairBernoulliMeasure := by
    simpa [fairBernoulliMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ ↦ (PMF.uniformOfFintype Bool).toMeasure)
        (fun _ ↦ measurable_of_finite petersburgRoundPayoff))
  simpa [petersburgRoundPayoffProcess] using h

/-- Helper for Example 9.40: each Petersburg payoff coordinate is integrable. -/
private theorem integrable_petersburgRoundPayoffProcess (n : ℕ) :
    Integrable (petersburgRoundPayoffProcess n) fairBernoulliMeasure := by
  -- Pull back the integrable two-point payoff map along the `n`th coordinate evaluation.
  simpa [fairBernoulliMeasure, petersburgRoundPayoffProcess] using
    ((measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ (PMF.uniformOfFintype Bool).toMeasure) n).integrable_comp_of_integrable
        (g := petersburgRoundPayoff) (Integrable.of_finite))

/-- Helper for Example 9.40: each Petersburg payoff coordinate has expectation `0`. -/
private theorem integral_petersburgRoundPayoffProcess_eq_zero (n : ℕ) :
    ∫ ω, petersburgRoundPayoffProcess n ω ∂ fairBernoulliMeasure = 0 := by
  have hmap :
      Measure.map (fun ω : BernoulliSequence ↦ ω n) fairBernoulliMeasure =
        (PMF.uniformOfFintype Bool).toMeasure := by
    simpa [fairBernoulliMeasure] using
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ (PMF.uniformOfFintype Bool).toMeasure) n).map_eq
  -- Push the integral forward to the one-coordinate Bernoulli law.
  calc
    ∫ ω, petersburgRoundPayoffProcess n ω ∂ fairBernoulliMeasure
        =
          ∫ ω, petersburgRoundPayoff ((fun ω : BernoulliSequence ↦ ω n) ω)
            ∂ fairBernoulliMeasure := by
            rfl
    _ = ∫ b : Bool, petersburgRoundPayoff b ∂Measure.map (fun ω : BernoulliSequence ↦ ω n)
          fairBernoulliMeasure := by
            symm
            exact MeasureTheory.integral_map (μ := fairBernoulliMeasure)
              (φ := fun ω : BernoulliSequence ↦ ω n) (measurable_pi_apply n).aemeasurable
              (measurable_of_finite petersburgRoundPayoff).aestronglyMeasurable
    _ = ∫ b : Bool, petersburgRoundPayoff b ∂((PMF.uniformOfFintype Bool).toMeasure) := by
          rw [hmap]
    _ = 0 := by
          rw [PMF.integral_eq_sum]
          norm_num [petersburgRoundPayoff, PMF.uniformOfFintype_apply]

/-- Helper for Example 9.40: consecutive cumulative Petersburg payoffs differ by the current
round payoff. -/
private theorem petersburgCumulativePayoff_succ_sub (n : ℕ) (ω : BernoulliSequence) :
    X (n + 1) ω - X n ω = petersburgRoundPayoffProcess n ω := by
  -- The difference of successive partial sums is the singleton `Ico` block at the new time.
  simpa using partialSum_sub_eq_sum_Ico petersburgRoundPayoffProcess (Nat.le_succ n) ω

/-- Helper for Example 9.40: the shifted filtration that reveals precisely the payoff increments
available before each cumulative sum `X n`. -/
private def petersburgIncrementFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace BernoulliSequence) where
  seq
    | 0 => ⊥
    | n + 1 =>
        Filtration.natural petersburgRoundPayoffProcess
          petersburgRoundPayoffProcess_stronglyMeasurable n
  mono' := by
    intro i j hij
    cases j with
    | zero =>
        have hi : i = 0 := Nat.eq_zero_of_le_zero hij
        subst hi
        exact le_rfl
    | succ j =>
        cases i with
        | zero =>
            exact bot_le
        | succ i =>
            exact (Filtration.natural petersburgRoundPayoffProcess
              petersburgRoundPayoffProcess_stronglyMeasurable).mono
              (Nat.succ_le_succ_iff.mp hij)
  le' := by
    intro n
    cases n with
    | zero =>
        exact bot_le
    | succ n =>
        exact (Filtration.natural petersburgRoundPayoffProcess
          petersburgRoundPayoffProcess_stronglyMeasurable).le n

/-- The textbook doubling strategy `H`, with constant initial stake `H_0 = 1` and, for
time `n + 1`, stake `petersburgStake n` from Chapter 4. -/
def petersburgDoublingStrategy : ℕ → BernoulliSequence → ℝ
  | 0, _ => 1
  | n + 1, ω => petersburgStake n ω

/-- The cumulative Petersburg round-payoff process is a martingale for its natural filtration. -/
theorem petersburgCumulativePayoffProcess_martingale :
    Martingale X petersburgPayoffFiltration fairBernoulliMeasure := by
  haveI : IsProbabilityMeasure fairBernoulliMeasure :=
    petersburgRoundPayoffProcess_iIndep.isProbabilityMeasure
  let Xshift : ℕ → BernoulliSequence → ℝ := fun n ω ↦ X (n + 1) ω
  let ℱinc : Filtration ℕ (inferInstance : MeasurableSpace BernoulliSequence) :=
    Filtration.natural petersburgRoundPayoffProcess petersburgRoundPayoffProcess_stronglyMeasurable
  have hShift :
      Martingale Xshift ℱinc fairBernoulliMeasure := by
    simpa [Xshift, ℱinc, shiftedPartialSumProcess] using
      cumulativeSumProcess_martingale_of_mean_zero
        (Y := petersburgRoundPayoffProcess)
        (μ := fairBernoulliMeasure)
        (hY_meas := fun n ↦ (petersburgRoundPayoffProcess_stronglyMeasurable n).measurable)
        integrable_petersburgRoundPayoffProcess
        integral_petersburgRoundPayoffProcess_eq_zero
        petersburgRoundPayoffProcess_iIndep
  have hPreAdapt : StronglyAdapted petersburgIncrementFiltration X := by
    intro n
    cases n with
    | zero =>
        simpa [petersburgIncrementFiltration] using
          (stronglyMeasurable_const : StronglyMeasurable[⊥]
            (fun _ : BernoulliSequence ↦ (0 : ℝ)))
    | succ n =>
        simpa [petersburgIncrementFiltration, Xshift] using hShift.stronglyAdapted n
  have hPreInt : ∀ n, Integrable (X n) fairBernoulliMeasure := by
    intro n
    cases n with
    | zero =>
        change Integrable (fun _ : BernoulliSequence ↦ (0 : ℝ)) fairBernoulliMeasure
        exact
          (integrable_const (0 : ℝ) : Integrable (fun _ : BernoulliSequence ↦ (0 : ℝ))
            fairBernoulliMeasure)
    | succ n =>
        simpa [Xshift] using hShift.integrable n
  have hPre :
      Martingale X petersburgIncrementFiltration fairBernoulliMeasure := by
    refine martingale_nat hPreAdapt hPreInt ?_
    intro n
    cases n with
    | zero =>
        have hmean0 : ∫ ω, X 1 ω ∂ fairBernoulliMeasure = 0 := by
          simpa [partialSum_apply] using integral_petersburgRoundPayoffProcess_eq_zero 0
        have hbot0 :
            fairBernoulliMeasure[X 1 | petersburgIncrementFiltration 0] =ᵐ[fairBernoulliMeasure]
              fun _ ↦ ∫ ω, X 1 ω ∂ fairBernoulliMeasure := by
          -- Conditioning the first payoff on the trivial sigma-algebra returns its mean.
          change fairBernoulliMeasure[X 1 | ⊥] =ᵐ[fairBernoulliMeasure]
            fun _ ↦ ∫ ω, X 1 ω ∂ fairBernoulliMeasure
          exact Filter.EventuallyEq.of_eq
            (MeasureTheory.condExp_bot (μ := fairBernoulliMeasure) (f := X 1))
        have hconst0 :
            (fun _ : BernoulliSequence ↦ ∫ ω, X 1 ω ∂ fairBernoulliMeasure) =
              (0 : BernoulliSequence → ℝ) := by
          funext ω
          exact hmean0
        have hbot :
            fairBernoulliMeasure[X 1 | petersburgIncrementFiltration 0] =ᵐ[fairBernoulliMeasure]
              (0 : BernoulliSequence → ℝ) :=
          hbot0.trans (Filter.EventuallyEq.of_eq hconst0)
        simpa [partialSum_apply] using hbot.symm
    | succ n =>
        have hsucc :
            fairBernoulliMeasure[Xshift (n + 1) | ℱinc n] =ᵐ[fairBernoulliMeasure] Xshift n := by
          simpa [Xshift, ℱinc] using hShift.condExp_ae_eq (Nat.le_succ n)
        change X (n + 1) =ᵐ[fairBernoulliMeasure]
          fairBernoulliMeasure[X (n + 2) | petersburgIncrementFiltration (n + 1)]
        simpa [petersburgIncrementFiltration, ℱinc] using hsucc.symm
  have hNatLe : petersburgPayoffFiltration ≤ petersburgIncrementFiltration := by
    let hXm : ∀ i, Measurable (X i) := fun i ↦
      (petersburgCumulativePayoffProcess_stronglyMeasurable i).measurable
    have hgen : generatedFiltration X hXm ≤ petersburgIncrementFiltration :=
      (adapted_iff_generatedFiltration_le hXm).mp hPreAdapt.adapted
    simpa [petersburgPayoffFiltration, generatedFiltration_eq_natural X
      petersburgCumulativePayoffProcess_stronglyMeasurable] using hgen
  have hNatAdapted : Adapted petersburgPayoffFiltration X := by
    simpa [petersburgPayoffFiltration] using
      (Filtration.stronglyAdapted_natural
        petersburgCumulativePayoffProcess_stronglyMeasurable).adapted
  exact martingale_of_le_filtration hNatLe hPre
    hNatAdapted

-- Proof sketch: the increment `X (k + 1) - X k` is exactly the round payoff
-- `petersburgRoundPayoffProcess k`, while `H (k + 1)` is `petersburgStake k`; unfolding both
-- finite sums gives the Chapter 4 definition of `petersburgPartialSum`.
/-- The discrete stochastic integral for the Petersburg doubling strategy recovers the Chapter 4
gain process `petersburgPartialSum`. -/
theorem stochasticIntegral_petersburgDoublingStrategy_eq_partialSum (n : ℕ)
    (ω : BernoulliSequence) :
    stochasticIntegral petersburgDoublingStrategy X n ω = petersburgPartialSum n ω := by
  induction n with
  | zero =>
      -- Both processes start from the empty sum.
      simp [ProbabilityTheory.stochasticIntegral_apply, petersburgPartialSum]
  | succ n ih =>
      -- Append the new stochastic-integral summand and identify it with the new game payoff.
      calc
        stochasticIntegral petersburgDoublingStrategy X (n + 1) ω
            = stochasticIntegral petersburgDoublingStrategy X n ω
                + petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω) := by
                  simp [ProbabilityTheory.stochasticIntegral_apply, Finset.sum_range_succ]
        _ = petersburgPartialSum n ω
              + petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω) := by
                  rw [ih]
        _ = petersburgPartialSum n ω
              + petersburgStake n ω * petersburgRoundPayoff (ω n) := by
                  simp [petersburgDoublingStrategy, petersburgCumulativePayoff_succ_sub,
                    petersburgRoundPayoffProcess]
        _ = petersburgPartialSum (n + 1) ω := by
                  simp [petersburgPartialSum, Finset.sum_range_succ]

/-- Helper for Example 9.40: the Petersburg gain process changes by the current stake times the
current cumulative-payoff increment. -/
private theorem petersburgPartialSum_succ_sub (n : ℕ) (ω : BernoulliSequence) :
    petersburgPartialSum (n + 1) ω - petersburgPartialSum n ω =
      petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω) := by
  -- Expand the new gain summand and rewrite the cumulative-payoff increment pathwise.
  calc
    petersburgPartialSum (n + 1) ω - petersburgPartialSum n ω
        = petersburgStake n ω * petersburgRoundPayoff (ω n) := by
            rw [petersburgPartialSum, Finset.sum_range_succ, petersburgPartialSum]
            ring
    _ = petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω) := by
            simp [petersburgDoublingStrategy, petersburgCumulativePayoff_succ_sub,
              petersburgRoundPayoffProcess]

/-- Helper for Example 9.40: after `n` rounds, the cumulative payoff `X n` cannot be smaller than
`-n`. -/
private theorem cumulativePayoff_ge_negNat (n : ℕ) (ω : BernoulliSequence) :
    -(n : ℝ) ≤ X n ω := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      cases hωn : ω n with
      | false =>
          have hstep : X (n + 1) ω = X n ω - 1 := by
            linarith [petersburgCumulativePayoff_succ_sub n ω,
              show petersburgRoundPayoffProcess n ω = (-1 : ℝ) by
                simp [petersburgRoundPayoffProcess, hωn]]
          calc
            -((n + 1 : ℕ) : ℝ) = -(n : ℝ) - 1 := by
                norm_num [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            _ ≤ X n ω - 1 := sub_le_sub_right ih 1
            _ = X (n + 1) ω := by rw [hstep]
      | true =>
          have hstep : X (n + 1) ω = X n ω + 1 := by
            linarith [petersburgCumulativePayoff_succ_sub n ω,
              show petersburgRoundPayoffProcess n ω = (1 : ℝ) by
                simp [petersburgRoundPayoffProcess, hωn]]
          calc
            -((n + 1 : ℕ) : ℝ) ≤ -(n : ℝ) + 1 := by
                norm_num [Nat.cast_add]
            _ ≤ X n ω + 1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ih 1
            _ = X (n + 1) ω := by rw [hstep]

/-- Helper for Example 9.40: an initial block of `n` losses is equivalent to the cumulative
payoff after `n` rounds being `-n`. -/
private theorem allPrefixLosses_iff_cumulativePayoff_eq_negNat (n : ℕ) (ω : BernoulliSequence) :
    (∀ k < n, ω k = false) ↔ X n ω = -(n : ℝ) := by
  induction n with
  | zero =>
      -- The empty prefix is vacuously all losses, and the empty payoff sum is `0`.
      simp [partialSum]
  | succ n ih =>
      constructor
      · intro hall
        have hprefix : ∀ k < n, ω k = false := by
          intro k hk
          exact hall k (Nat.lt_trans hk (Nat.lt_succ_self n))
        have hωn : ω n = false := hall n (Nat.lt_succ_self n)
        have hXn : X n ω = -(n : ℝ) := ih.mp hprefix
        -- Append one more loss to the prefix-sum identity.
        have hstep :
            X (n + 1) ω - X n ω = -1 := by
          simpa [petersburgRoundPayoffProcess, hωn] using petersburgCumulativePayoff_succ_sub n ω
        have hnext : X (n + 1) ω = -((n + 1 : ℕ) : ℝ) := by
          calc
            X (n + 1) ω = X n ω - 1 := by linarith [hstep]
            _ = -(n : ℝ) - 1 := by rw [hXn]
            _ = -((n + 1 : ℕ) : ℝ) := by
                norm_num [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        simpa using hnext
      · intro hsum
        cases hωn : ω n with
        | false =>
            have hstep :
                X (n + 1) ω - X n ω = -1 := by
              simpa [petersburgRoundPayoffProcess, hωn] using
                petersburgCumulativePayoff_succ_sub n ω
            have hXn : X n ω = -(n : ℝ) := by
              calc
                X n ω = X (n + 1) ω + 1 := by linarith [hstep]
                _ = -((n + 1 : ℕ) : ℝ) + 1 := by rw [hsum]
                _ = -(n : ℝ) := by
                    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
            have hprefix : ∀ k < n, ω k = false := ih.mpr hXn
            intro k hk
            by_cases hkn : k = n
            · simpa [hkn] using hωn
            · exact hprefix k (by omega)
        | true =>
            have hstep :
                X (n + 1) ω - X n ω = 1 := by
              simpa [petersburgRoundPayoffProcess, hωn] using
                petersburgCumulativePayoff_succ_sub n ω
            have hlow : -(n : ℝ) ≤ X n ω := cumulativePayoff_ge_negNat n ω
            have : False := by
              have hXn : X n ω = -((n + 2 : ℕ) : ℝ) := by
                calc
                  X n ω = X (n + 1) ω - 1 := by linarith [hstep]
                  _ = -((n + 1 : ℕ) : ℝ) - 1 := by rw [hsum]
                  _ = -((n + 2 : ℕ) : ℝ) := by
                      norm_num [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              have hlt : X n ω < -(n : ℝ) := by
                rw [hXn]
                norm_num [Nat.cast_add]
              exact (not_lt_of_ge hlow hlt).elim
            exact this.elim

/-- Helper for Example 9.40: the next doubling stake depends only on whether the current
cumulative payoff equals `-n`. -/
private theorem petersburgDoublingStrategy_succ_eq_if_cumulativePayoff_eq_negNat (n : ℕ) :
    petersburgDoublingStrategy (n + 1) =
      fun ω ↦ if X n ω = -(n : ℝ) then (2 : ℝ) ^ n else 0 := by
  funext ω
  by_cases hprefix : ∀ k < n, ω k = false
  · have hsum : X n ω = -(n : ℝ) :=
      (allPrefixLosses_iff_cumulativePayoff_eq_negNat n ω).mp hprefix
    rw [petersburgDoublingStrategy, petersburgStake, if_pos hprefix, if_pos hsum]
  · have hsum : X n ω ≠ -(n : ℝ) := by
      intro hsum
      exact hprefix ((allPrefixLosses_iff_cumulativePayoff_eq_negNat n ω).mpr hsum)
    rw [petersburgDoublingStrategy, petersburgStake, if_neg hprefix, if_neg hsum]

-- Proof sketch: the initial value is the constant function `1`, and for time `n + 1` the stake
-- depends only on whether the first `n` Bernoulli coordinates are all losses, hence is measurable
-- with respect to the time-`n` sigma-algebra generated by the cumulative payoff process
-- `X 0, ..., X n`.
/-- The Petersburg doubling strategy is predictable for the natural filtration of the cumulative
payoff process. -/
theorem petersburgDoublingStrategy_isPredictable :
    IsPredictable petersburgPayoffFiltration petersburgDoublingStrategy := by
  -- Route correction: rewrite the next stake as a piecewise-constant function of `X n` instead
  -- of rebuilding the all-loss event by hand from finitely many coordinate constraints.
  classical
  have hXadapt : StronglyAdapted petersburgPayoffFiltration X := by
    simpa [petersburgPayoffFiltration] using
      (Filtration.stronglyAdapted_natural petersburgCumulativePayoffProcess_stronglyMeasurable)
  rw [isPredictable_iff_measurable_add_one]
  constructor
  · -- The initial stake is the constant process `1`.
    simpa only [petersburgDoublingStrategy] using
      (measurable_const : Measurable[petersburgPayoffFiltration 0]
        (fun _ : BernoulliSequence ↦ (1 : ℝ)))
  · intro n
    have hlevel : MeasurableSet[petersburgPayoffFiltration n] {ω | X n ω = -(n : ℝ)} := by
      change MeasurableSet[petersburgPayoffFiltration n] (X n ⁻¹' ({-(n : ℝ)} : Set ℝ))
      exact (hXadapt n).measurable (measurableSet_singleton (-(n : ℝ)))
    -- The rewritten stake is piecewise constant on a measurable level set of `X n`.
    simpa [petersburgDoublingStrategy_succ_eq_if_cumulativePayoff_eq_negNat, Set.piecewise] using
      (measurable_const.piecewise hlevel measurable_const :
        Measurable[petersburgPayoffFiltration n]
          ({ω | X n ω = -(n : ℝ)}.piecewise
            (fun _ : BernoulliSequence ↦ (2 : ℝ) ^ n)
            (fun _ : BernoulliSequence ↦ (0 : ℝ))))

-- Proof sketch: at each fixed time `n`, the stake is either `0`, `1`, or `2^(n - 1)` depending
-- on the initial-loss event, so one can bound `|H n|` uniformly by the corresponding power of `2`.
/-- The Petersburg doubling strategy is locally bounded in the sense required by the stochastic
integral criterion. -/
theorem petersburgDoublingStrategy_locallyBounded :
    IsLocallyBoundedProcess petersburgDoublingStrategy := by
  intro n
  cases n with
  | zero =>
      -- The initial stake is the constant `1`.
      refine ⟨1, by norm_num, ?_⟩
      intro ω
      simp [petersburgDoublingStrategy]
  | succ n =>
      -- At time `n + 1`, the stake is either `0` or exactly `(2 : ℝ)^n`.
      refine ⟨(2 : ℝ) ^ n, by positivity, ?_⟩
      intro ω
      by_cases hprefix : ∀ k < n, ω k = false
      · have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
        rw [petersburgDoublingStrategy, petersburgStake, if_pos hprefix]
        rw [abs_of_nonneg hpow]
      · simp [petersburgDoublingStrategy, petersburgStake, hprefix]

-- Proof sketch: the cumulative payoff process `X` is a martingale, the doubling strategy `H` is
-- predictable and locally bounded, and the discrete stochastic-integral stability argument shows
-- that the gain process `S_n = ∑_{i=1}^n H_i D_i` is again a martingale.
/-- Helper for Example 9.40: the Petersburg gain process is adapted because it coincides with the
stochastic integral of the predictable doubling strategy against the adapted cumulative payoff
process `X`. -/
private theorem petersburgPartialSum_stronglyAdapted :
    StronglyAdapted petersburgPayoffFiltration petersburgPartialSum := by
  have hXadapt : StronglyAdapted petersburgPayoffFiltration X :=
    petersburgCumulativePayoffProcess_martingale.stronglyAdapted
  have hSIadapt :
      Adapted petersburgPayoffFiltration (stochasticIntegral petersburgDoublingStrategy X) :=
    stochasticIntegral_adapted petersburgDoublingStrategy_isPredictable hXadapt.adapted
  have hEq :
      stochasticIntegral petersburgDoublingStrategy X = petersburgPartialSum := by
    funext n ω
    exact stochasticIntegral_petersburgDoublingStrategy_eq_partialSum n ω
  simpa [hEq] using hSIadapt.stronglyAdapted

/-- Helper for Example 9.40: each fixed-time Petersburg gain is integrable under the fair
Bernoulli product measure. -/
private theorem integrable_petersburgPartialSum (n : ℕ) :
    Integrable (petersburgPartialSum n) fairBernoulliMeasure := by
  haveI : IsProbabilityMeasure fairBernoulliMeasure :=
    petersburgRoundPayoffProcess_iIndep.isProbabilityMeasure
  have hXmart : Martingale X petersburgPayoffFiltration fairBernoulliMeasure :=
    petersburgCumulativePayoffProcess_martingale
  induction n with
  | zero =>
      change Integrable (fun _ : BernoulliSequence ↦ (0 : ℝ)) fairBernoulliMeasure
      exact
        (integrable_const (0 : ℝ) : Integrable (fun _ : BernoulliSequence ↦ (0 : ℝ))
          fairBernoulliMeasure)
  | succ n ih =>
      obtain ⟨C, hC_nonneg, hC⟩ := petersburgDoublingStrategy_locallyBounded (n + 1)
      have hHmeas :
          Measurable (petersburgDoublingStrategy (n + 1)) :=
        (petersburgDoublingStrategy_isPredictable.measurable_add_one n).mono
          (petersburgPayoffFiltration.le n) (by rfl)
      have hIncrInt :
          Integrable (fun ω ↦ X (n + 1) ω - X n ω) fairBernoulliMeasure :=
        (hXmart.integrable (n + 1)).sub (hXmart.integrable n)
      have hStepInt :
          Integrable
            (fun ω ↦ petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω))
            fairBernoulliMeasure := by
        exact hIncrInt.bdd_mul (c := C) (hHmeas.stronglyMeasurable.aestronglyMeasurable)
          (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
      have hStepEq :
          petersburgPartialSum (n + 1) =
            fun ω ↦ petersburgPartialSum n ω +
              petersburgDoublingStrategy (n + 1) ω * (X (n + 1) ω - X n ω) := by
        funext ω
        linarith [petersburgPartialSum_succ_sub n ω]
      rw [hStepEq]
      exact ih.add hStepInt

/-- Helper for Example 9.40: the one-step increment of the cumulative payoff martingale `X` has
zero conditional expectation with respect to the natural filtration at the previous time. -/
private theorem petersburgCumulativePayoff_condExp_sub_eq_zero (n : ℕ) :
    fairBernoulliMeasure[fun ω ↦ X (n + 1) ω - X n ω | petersburgPayoffFiltration n] =ᵐ[
      fairBernoulliMeasure] 0 := by
  have hXmart : Martingale X petersburgPayoffFiltration fairBernoulliMeasure :=
    petersburgCumulativePayoffProcess_martingale
  have hself :
      fairBernoulliMeasure[X n | petersburgPayoffFiltration n] =ᵐ[fairBernoulliMeasure] X n :=
    hXmart.condExp_ae_eq le_rfl
  calc
    fairBernoulliMeasure[fun ω ↦ X (n + 1) ω - X n ω | petersburgPayoffFiltration n] =ᵐ[
        fairBernoulliMeasure]
      fairBernoulliMeasure[X (n + 1) | petersburgPayoffFiltration n] -
        fairBernoulliMeasure[X n | petersburgPayoffFiltration n] := by
          exact MeasureTheory.condExp_sub
            (hXmart.integrable (n + 1)) (hXmart.integrable n) (m := petersburgPayoffFiltration n)
    _ =ᵐ[fairBernoulliMeasure] X n - fairBernoulliMeasure[X n | petersburgPayoffFiltration n] := by
          exact (hXmart.condExp_ae_eq (Nat.le_succ n)).sub Filter.EventuallyEq.rfl
    _ =ᵐ[fairBernoulliMeasure] 0 := by
          filter_upwards [hself] with ω hω
          simp [hω]

/-- Helper for Example 9.40: the one-step increment of the Petersburg gain process has zero
conditional expectation with respect to the previous payoff filtration. -/
private theorem petersburgPartialSum_condExp_sub_eq_zero (n : ℕ) :
    fairBernoulliMeasure[fun ω ↦ petersburgPartialSum (n + 1) ω - petersburgPartialSum n ω |
      petersburgPayoffFiltration n] =ᵐ[fairBernoulliMeasure] 0 := by
  let ΔX : BernoulliSequence → ℝ := fun ω ↦ X (n + 1) ω - X n ω
  obtain ⟨C, hC_nonneg, hC⟩ := petersburgDoublingStrategy_locallyBounded (n + 1)
  have hHmeas :
      StronglyMeasurable[petersburgPayoffFiltration n] (petersburgDoublingStrategy (n + 1)) :=
    (petersburgDoublingStrategy_isPredictable.measurable_add_one n).stronglyMeasurable
  have hHmeas' :
      Measurable (petersburgDoublingStrategy (n + 1)) :=
    hHmeas.measurable.mono (petersburgPayoffFiltration.le n) (by rfl)
  have hIncrInt : Integrable ΔX fairBernoulliMeasure :=
    (petersburgCumulativePayoffProcess_martingale.integrable (n + 1)).sub
      (petersburgCumulativePayoffProcess_martingale.integrable n)
  have hStepInt :
      Integrable (fun ω ↦ ΔX ω * petersburgDoublingStrategy (n + 1) ω) fairBernoulliMeasure := by
    simpa [mul_comm] using
      hIncrInt.bdd_mul (c := C) (hHmeas'.stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
  calc
    fairBernoulliMeasure[fun ω ↦ petersburgPartialSum (n + 1) ω - petersburgPartialSum n ω |
        petersburgPayoffFiltration n] =ᵐ[fairBernoulliMeasure]
      fairBernoulliMeasure[fun ω ↦ ΔX ω * petersburgDoublingStrategy (n + 1) ω |
        petersburgPayoffFiltration n] := by
          exact MeasureTheory.condExp_congr_ae <|
            Filter.Eventually.of_forall fun ω ↦ by
              simpa [ΔX, mul_comm] using petersburgPartialSum_succ_sub n ω
    _ =ᵐ[fairBernoulliMeasure]
        fairBernoulliMeasure[ΔX | petersburgPayoffFiltration n] *
          petersburgDoublingStrategy (n + 1) := by
            exact MeasureTheory.condExp_mul_of_stronglyMeasurable_right hHmeas hStepInt hIncrInt
    _ =ᵐ[fairBernoulliMeasure] 0 := by
          filter_upwards [petersburgCumulativePayoff_condExp_sub_eq_zero n] with ω hω
          change fairBernoulliMeasure[ΔX | petersburgPayoffFiltration n] ω *
              petersburgDoublingStrategy (n + 1) ω = 0
          rw [hω]
          exact zero_mul (petersburgDoublingStrategy (n + 1) ω)

/-- Example 9.40: in the Petersburg game, the gain process `S_n = ∑_{i=1}^n H_i D_i` produced by
the doubling strategy is the Chapter 4 process `petersburgPartialSum`, hence is a martingale for
the natural filtration of the cumulative payoff process. -/
theorem petersburg_game_gain_process_martingale :
    Martingale petersburgPartialSum petersburgPayoffFiltration fairBernoulliMeasure := by
  haveI : IsProbabilityMeasure fairBernoulliMeasure :=
    petersburgRoundPayoffProcess_iIndep.isProbabilityMeasure
  -- The gain process is adapted, integrable, and has centered one-step conditional increments.
  exact martingale_of_condExp_sub_eq_zero_nat
    petersburgPartialSum_stronglyAdapted
    integrable_petersburgPartialSum
    petersburgPartialSum_condExp_sub_eq_zero

/-- Helper for Example 9.40: the complementary product `∏_{i < n} (1 - D_i)` is `2^n` exactly on
paths with `n` initial losses, and vanishes as soon as one win occurs before time `n`. -/
private theorem petersburgComplementProd_eq_if_allPrefixLosses (n : ℕ) (ω : BernoulliSequence) :
    ∏ i ∈ Finset.range n, (1 - petersburgRoundPayoffProcess i ω) =
      if ∀ k < n, ω k = false then (2 : ℝ) ^ n else 0 := by
  induction n with
  | zero =>
      -- The empty product matches the empty all-loss branch.
      simp
  | succ n ih =>
      -- Split off the new factor and branch on whether the first `n` rounds were all losses.
      rw [Finset.prod_range_succ]
      by_cases hprefix : ∀ k < n, ω k = false
      · rw [ih, if_pos hprefix]
        cases hωn : ω n with
        | false =>
            have hall : ∀ k < n + 1, ω k = false := by
              -- One more loss extends the all-loss prefix to length `n + 1`.
              intro k hk
              by_cases hkn : k = n
              · simpa [hkn] using hωn
              · exact hprefix k (by omega)
            rw [if_pos hall]
            -- The new complementary factor is `2` on a loss.
            simp [petersburgRoundPayoffProcess, hωn, pow_succ]
            ring
        | true =>
            have hnotall : ¬ ∀ k < n + 1, ω k = false := by
              -- A win makes the new complementary factor vanish.
              intro hall
              have hnfalse : ω n = false := hall n (Nat.lt_succ_self n)
              simp [hωn] at hnfalse
            rw [if_neg hnotall]
            simp [petersburgRoundPayoffProcess, hωn]
      · have hnotall : ¬ ∀ k < n + 1, ω k = false := by
          -- Once a previous win occurred, no longer prefix is all losses.
          intro hall
          exact hprefix (fun k hk ↦ hall k (by omega))
        rw [ih, if_neg hprefix, if_neg hnotall]
        simp

-- Proof sketch: expand the Petersburg gain pathwise along the first winning round; on each path,
-- the complement `1 - S_n` telescopes to the product of the independent factors
-- `1 - D_1, ..., 1 - D_n`.
/-- The complementary process `1 - S_n` of the Petersburg gain is the product of the factors
`1 - D_i`. -/
theorem one_sub_petersburgGainProcess_eq_prod (n : ℕ) (ω : BernoulliSequence) :
    1 - petersburgPartialSum n ω =
      ∏ i ∈ Finset.range n, (1 - petersburgRoundPayoffProcess i ω) := by
  -- Normalize both sides to the same prefix-loss branching formula.
  rw [petersburgPartialSum_eq_if_allPrefixLosses, petersburgComplementProd_eq_if_allPrefixLosses]
  by_cases hprefix : ∀ k < n, ω k = false
  · rw [if_pos hprefix, if_pos hprefix]
    ring
  · rw [if_neg hprefix, if_neg hprefix]
    ring
