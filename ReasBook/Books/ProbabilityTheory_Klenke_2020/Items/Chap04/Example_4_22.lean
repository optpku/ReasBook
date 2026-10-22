/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Exercise_1_4_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_64
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open Classical

universe u

private theorem petersburgHalfPos : 0 < (1 / 2 : ℝ) := by
  norm_num

private theorem petersburgHalfLeOne : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

/-- Helper for Example 4.22: the Bernoulli parameter `(1 / 2 : NNReal)` is bounded by `1`. -/
private theorem petersburgHalfNNRealLeOne : (1 / 2 : NNReal) ≤ 1 := by
  norm_num

/-- Helper for Example 4.22: the fair Bernoulli product measure has total mass `1`. -/
private theorem fairBernoulliMeasure_univ :
    fairBernoulliMeasure Set.univ = 1 := by
  sorry

/-- Helper for Example 4.22: every event under `fairBernoulliMeasure` has finite mass. -/
private theorem fairBernoulliMeasure_ne_top (s : Set BernoulliSequence) :
    fairBernoulliMeasure s ≠ ⊤ := by
  have huniv : fairBernoulliMeasure Set.univ ≠ ⊤ := by
    rw [fairBernoulliMeasure_univ]
    simp
  refine ne_top_of_le_ne_top huniv ?_
  exact measure_mono (Set.subset_univ s)

/-- Helper for Example 4.22: the file-local waiting time to the first `true` in a Boolean row,
counted as the number of initial `false` entries and equal to `⊤` on the all-false row. -/
private noncomputable def rowFirstSuccessWaitingTime {Ω : Type u} (X : ℕ → ℕ → Ω → Bool) :
    ℕ → Ω → ℕ∞ :=
  fun m ω ↦
    if h : ∃ n : ℕ, X m n ω = true then (Nat.find h : ℕ∞) else ⊤

/-- Helper for Example 4.22: the file-local waiting time is `⊤` exactly when the row never hits
`true`. -/
private theorem rowFirstSuccessWaitingTime_eq_top_iff {Ω : Type u} (X : ℕ → ℕ → Ω → Bool)
    {m : ℕ} {ω : Ω} :
    rowFirstSuccessWaitingTime X m ω = ⊤ ↔ ¬ ∃ n : ℕ, X m n ω = true := by
  classical
  by_cases h : ∃ n : ℕ, X m n ω = true
  · simp [rowFirstSuccessWaitingTime, h]
  · simp [rowFirstSuccessWaitingTime, h]

/-- Helper for Example 4.22: the file-local waiting time equals `n` exactly when the first `n`
entries are `false` and the `n`th entry is `true`. -/
private theorem rowFirstSuccessWaitingTime_eq_coe_iff {Ω : Type u} (X : ℕ → ℕ → Ω → Bool)
    {m n : ℕ} {ω : Ω} :
    rowFirstSuccessWaitingTime X m ω = (n : ℕ∞) ↔
      X m n ω = true ∧ ∀ k < n, X m k ω = false := by
  classical
  by_cases h : ∃ k : ℕ, X m k ω = true
  · simp [rowFirstSuccessWaitingTime, h, Nat.find_eq_iff]
  · have hn : X m n ω ≠ true := fun hn ↦ h ⟨n, hn⟩
    simp [rowFirstSuccessWaitingTime, h, hn]

/-- The first winning round on the canonical fair coin-flip space `Bool^ℕ`, counted as the number
of initial losses before the first win; it is `⊤` on the all-losses path. Here `false` denotes a
loss and `true` a win. -/
noncomputable def petersburgFirstWinWaitingTime : BernoulliSequence → ℕ∞ :=
  rowFirstSuccessWaitingTime (fun _ n ω ↦ ω n) 0

@[simp] theorem petersburgFirstWinWaitingTime_eq_top_iff {ω : BernoulliSequence} :
    petersburgFirstWinWaitingTime ω = ⊤ ↔ ∀ n, ω n = false := by
  simp [petersburgFirstWinWaitingTime, rowFirstSuccessWaitingTime_eq_top_iff]

@[simp] theorem petersburgFirstWinWaitingTime_eq_coe_iff {ω : BernoulliSequence} {n : ℕ} :
    petersburgFirstWinWaitingTime ω = (n : ℕ∞) ↔
      ω n = true ∧ ∀ k < n, ω k = false := by
  simp [petersburgFirstWinWaitingTime, rowFirstSuccessWaitingTime_eq_coe_iff]

/-- The textbook round payoff attached to a coin flip: `false` is the loss `-1`, `true` is the
win `1`. -/
def petersburgRoundPayoff : Bool → ℝ
  | false => -1
  | true => 1

@[simp] theorem petersburgRoundPayoff_false : petersburgRoundPayoff false = -1 := rfl
@[simp] theorem petersburgRoundPayoff_true : petersburgRoundPayoff true = 1 := rfl

/-- The adapted stake `H_n`: before round `n + 1`, the gambler stakes `2^n` exactly when the
first `n` rounds have all been losses, and otherwise stops playing. -/
def petersburgStake (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  if ∀ k < n, ω k = false then (2 : ℝ) ^ n else 0

/-- Companion waiting-time payoff formula: if the first win occurs after `m` initial losses, then
after `n + 1` rounds the cumulative Petersburg gain is `1 - 2^(n + 1)` while no win has yet
occurred (`n < m`) and `1` afterwards. -/
def petersburgProfit (n m : ℕ) : ℝ :=
  if n < m then 1 - (2 : ℝ) ^ (n + 1) else 1

@[simp] theorem petersburgProfit_eq_lossValue_iff {n m : ℕ} :
    petersburgProfit n m = 1 - (2 : ℝ) ^ (n + 1) ↔ n < m := by
  by_cases h : n < m
  · simp [petersburgProfit, h]
  · have hpow_pos : 0 < (2 : ℝ) ^ (n + 1) := by
      positivity
    constructor
    · intro hEq
      simp [petersburgProfit, h] at hEq
      linarith
    · intro hlt
      exact (h hlt).elim

@[simp] theorem petersburgProfit_eq_one_iff {n m : ℕ} :
    petersburgProfit n m = 1 ↔ m ≤ n := by
  by_cases h : n < m
  · simp [petersburgProfit, h, Nat.not_le.mpr h]
  · simp [petersburgProfit, h, Nat.not_lt.mp h]

/-- For each finite first winning round, the waiting-time payoff formula eventually stabilizes at
the gain `1`. -/
theorem petersburgProfit_tendsto_one (m : ℕ) :
    Tendsto (fun n ↦ petersburgProfit n m) atTop (nhds (1 : ℝ)) := by
  have h_eventually : (fun _ : ℕ ↦ (1 : ℝ)) =ᶠ[atTop] fun n ↦ petersburgProfit n m := by
    exact Filter.eventually_atTop.2 ⟨m, fun n hn ↦ by simp [petersburgProfit, Nat.not_lt.mpr hn]⟩
  exact Tendsto.congr' h_eventually tendsto_const_nhds

/-- The cumulative Petersburg gain `S_n` after the first `n` rounds on the fair coin-flip space,
using the textbook payoff convention `false ↦ -1`, `true ↦ 1`. -/
def petersburgPartialSum (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  Finset.sum (Finset.range n) fun k ↦
    petersburgStake k ω * petersburgRoundPayoff (ω k)

/-- The extended-real pointwise limit `S`: it equals `1` on paths with a win and `-∞` on the
all-losses path. -/
noncomputable def petersburgLimit (ω : BernoulliSequence) : EReal :=
  by
    classical
    exact if ∀ n, ω n = false then ⊥ else 1

/-- Helper for Example 4.22: the fair-product event that the first `n` coordinates are all losses.
-/
def petersburgPrefixLosses (n : ℕ) : Set BernoulliSequence :=
  {ω | ∀ k < n, ω k = false}

/-- Helper for Example 4.22: the prefix-loss events shrink as the prefix length grows. -/
theorem petersburgPrefixLosses_antitone : Antitone petersburgPrefixLosses := by
  -- Forgetting the final loss condition leaves an earlier prefix-loss event.
  intro m n hmn ω hω k hk
  exact hω k (lt_of_lt_of_le hk hmn)

/-- Helper for Example 4.22: the prefix-loss event is measurable because it is a finite
intersection of coordinate singleton events. -/
theorem measurableSet_petersburgPrefixLosses (n : ℕ) :
    MeasurableSet (petersburgPrefixLosses n) := by
  -- Rewrite the event as a finite intersection indexed by `Finset.range n`.
  have hset :
      petersburgPrefixLosses n =
        ⋂ k ∈ Finset.range n, Function.eval k ⁻¹' ({false} : Set Bool) := by
    ext ω
    simp [petersburgPrefixLosses]
  rw [hset]
  exact (Finset.range n).measurableSet_biInter fun k _ ↦
    (measurable_pi_apply k) (measurableSet_singleton false)

/-- Helper for Example 4.22: the probability of `n` initial losses under the fair Bernoulli
product measure is `(1 / 2)^n`. -/
theorem petersburgPrefixLosses_measure (n : ℕ) :
    fairBernoulliMeasure (petersburgPrefixLosses n) = (1 / 2 : ENNReal) ^ n := by
  sorry

/-- Helper for Example 4.22: the length-`n + 1` cylinder with `n` losses followed by the first
win. -/
private def petersburgFirstSuccessPattern (n : ℕ) : Fin (n + 1) → Bool :=
  fun i ↦ if i = Fin.last n then true else false

/-- Helper for Example 4.22: the finite waiting-time fiber is exactly the cylinder with `n`
initial losses and a win at time `n`. -/
private theorem petersburgFirstWinWaitingTime_preimage_singleton_coe (n : ℕ) :
    {ω : BernoulliSequence | petersburgFirstWinWaitingTime ω = (n : ℕ∞)} =
      {ω : BernoulliSequence | ∀ i : Fin (n + 1), ω i = petersburgFirstSuccessPattern n i} := by
  -- Rewrite the waiting-time fiber into the first-success cylinder conditions.
  ext ω
  constructor
  · intro hω i
    change petersburgFirstWinWaitingTime ω = (n : ℕ∞) at hω
    rw [petersburgFirstWinWaitingTime_eq_coe_iff] at hω
    refine Fin.lastCases ?_ ?_ i
    · simp [petersburgFirstSuccessPattern, hω.1]
    · intro j
      simp [petersburgFirstSuccessPattern, Fin.castSucc_ne_last, hω.2 j j.is_lt]
  · intro hω
    -- Read the success coordinate and all previous losses back from the cylinder equation.
    change petersburgFirstWinWaitingTime ω = (n : ℕ∞)
    rw [petersburgFirstWinWaitingTime_eq_coe_iff]
    constructor
    · simpa [petersburgFirstSuccessPattern] using hω (Fin.last n)
    · intro k hk
      let j : Fin n := ⟨k, hk⟩
      have hj : petersburgFirstSuccessPattern n j.castSucc = false := by
        simp [petersburgFirstSuccessPattern, Fin.castSucc_ne_last]
      have hωj := hω j.castSucc
      rwa [hj] at hωj

/-- Helper for Example 4.22: belonging to every finite prefix-loss event means that every round is
a loss. -/
private theorem mem_iInter_petersburgPrefixLosses_iff {ω : BernoulliSequence} :
    ω ∈ ⋂ n, petersburgPrefixLosses n ↔ ∀ n, ω n = false := by
  constructor
  · intro hω n
    -- Read the `n`th loss from the `(n + 1)`-prefix all-loss event.
    have hprefix : ω ∈ petersburgPrefixLosses (n + 1) := Set.mem_iInter.mp hω (n + 1)
    exact hprefix n (by omega)
  · intro hω
    -- Repackage the pointwise all-loss statement back into every finite prefix event.
    refine Set.mem_iInter.mpr ?_
    intro n
    show ω ∈ petersburgPrefixLosses n
    intro k hk
    exact hω k

/-- Helper for Example 4.22: a longer prefix consists of the earlier all-loss prefix together with
the final loss at the new index. -/
private theorem mem_petersburgPrefixLosses_succ_iff {ω : BernoulliSequence} {n : ℕ} :
    ω ∈ petersburgPrefixLosses (n + 1) ↔ ω ∈ petersburgPrefixLosses n ∧ ω n = false := by
  constructor
  · intro hω
    -- Split the length-`n + 1` all-loss condition into the first `n` rounds and the last round.
    refine ⟨?_, hω n (by omega)⟩
    intro k hk
    exact hω k (by omega)
  · rintro ⟨hprefix, hn⟩
    -- Reassemble the longer all-loss prefix by separating whether the index is `n`.
    intro k hk
    by_cases hkn : k = n
    · simpa [hkn] using hn
    · exact hprefix k (by omega)

/-- Helper for Example 4.22: the `⊤` fiber is the intersection of the all-loss prefix events. -/
private theorem petersburgFirstWinWaitingTime_preimage_top :
    {ω : BernoulliSequence | petersburgFirstWinWaitingTime ω = ⊤} =
      ⋂ n, petersburgPrefixLosses n := by
  -- Route correction: freeze the all-loss branch as a standalone `Set.mem_iInter` equivalence
  -- before comparing it with the waiting-time `⊤` fiber.
  ext ω
  -- Both sides now express the same pointwise all-loss condition.
  change (petersburgFirstWinWaitingTime ω = ⊤) ↔ ω ∈ ⋂ n, petersburgPrefixLosses n
  rw [petersburgFirstWinWaitingTime_eq_top_iff, mem_iInter_petersburgPrefixLosses_iff]

/-- Helper for Example 4.22: the all-loss branch has probability zero under the fair Bernoulli
product measure. -/
theorem petersburgFirstWinWaitingTime_eq_top_measure_zero :
    fairBernoulliMeasure {ω | petersburgFirstWinWaitingTime ω = ⊤} = 0 := by
  have hfinite : ∃ n, fairBernoulliMeasure (petersburgPrefixLosses n) ≠ ⊤ := by
    -- The stage `n = 0` event is the whole space and has finite mass.
    refine ⟨0, ?_⟩
    rw [petersburgPrefixLosses_measure]
    norm_num
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : NNReal) ^ n) atTop (nhds (0 : NNReal)) := by
    -- The fair-coin prefix-loss masses decay geometrically to zero.
    simpa using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : NNReal)) (by norm_num))
  have hprefix_tendsto :
      Tendsto (fun n : ℕ ↦ fairBernoulliMeasure (petersburgPrefixLosses n)) atTop
        (nhds (0 : ENNReal)) := by
    have hpow_enn :
        Tendsto (fun n : ℕ ↦ ((1 / 2 : NNReal) ^ n : ENNReal)) atTop (nhds (0 : ENNReal)) := by
      exact (ENNReal.continuous_coe.tendsto 0).comp hpow
    exact by
      simpa [petersburgPrefixLosses_measure] using hpow_enn
  have hinter_tendsto :
      Tendsto (fun n : ℕ ↦ fairBernoulliMeasure (petersburgPrefixLosses n)) atTop
        (nhds (fairBernoulliMeasure (⋂ n, petersburgPrefixLosses n))) :=
    tendsto_measure_iInter_atTop
      (μ := fairBernoulliMeasure)
      (s := petersburgPrefixLosses)
      (fun n ↦ (measurableSet_petersburgPrefixLosses n).nullMeasurableSet)
      petersburgPrefixLosses_antitone
      hfinite
  have hinter : fairBernoulliMeasure (⋂ n, petersburgPrefixLosses n) = 0 :=
    tendsto_nhds_unique hinter_tendsto hprefix_tendsto
  -- Rewrite the exceptional branch as the decreasing intersection of all-loss prefix events.
  rw [petersburgFirstWinWaitingTime_preimage_top, hinter]

/-- Helper for Example 4.22: the waiting time has the pathwise two-valued partial-sum formula from
the textbook Petersburg game. -/
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

/-- Helper for Example 4.22: the waiting time hits the finite value `n` with probability
`(1 / 2)^(n + 1)`. -/
theorem petersburgFirstWinWaitingTime_eq_coe_measure (n : ℕ) :
    fairBernoulliMeasure {ω | petersburgFirstWinWaitingTime ω = (n : ℕ∞)} =
      (1 / 2 : ENNReal) ^ (n + 1) := by
  sorry

/-- On a path whose first win occurs after `m` initial losses, the partial sums agree with the
companion waiting-time payoff formula. -/
theorem petersburgPartialSum_succ_eq_profit_of_waitingTime {ω : BernoulliSequence} {n m : ℕ}
    (hω : petersburgFirstWinWaitingTime ω = (m : ℕ∞)) :
    petersburgPartialSum (n + 1) ω = petersburgProfit n m := by
  rw [petersburgPartialSum_eq_if_allPrefixLosses]
  rw [petersburgFirstWinWaitingTime_eq_coe_iff] at hω
  by_cases hnm : n < m
  · have hall : ∀ k < n + 1, ω k = false := by
      -- Before the first win, every earlier round is still a loss.
      intro k hk
      exact hω.2 k (by omega)
    rw [if_pos hall, petersburgProfit, if_pos hnm]
  · have hmle : m ≤ n := Nat.not_lt.mp hnm
    have hnotall : ¬ ∀ k < n + 1, ω k = false := by
      -- Once the first win is within the first `n + 1` rounds, the long all-loss branch fails.
      intro hall
      have hmfalse : ω m = false := hall m (Nat.lt_succ_of_le hmle)
      simp [hω.1] at hmfalse
    rw [if_neg hnotall, petersburgProfit, if_neg hnm]

/-- Helper for Example 4.22: the fair geometric law on `ℕ` assigns mass `(1 / 2)^(n + 1)` to the
singleton `{n}`. -/
private theorem geometricHalfMeasure_apply_singleton (n : ℕ) :
    geometricMeasure petersburgHalfPos petersburgHalfLeOne ({n} : Set ℕ) =
      (1 / 2 : ENNReal) ^ (n + 1) := by
  calc
    geometricMeasure petersburgHalfPos petersburgHalfLeOne ({n} : Set ℕ)
        = geometricPMF petersburgHalfPos petersburgHalfLeOne n := by
            rw [geometricMeasure]
            exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)
    _ = ENNReal.ofReal (geometricPMFReal (1 / 2 : ℝ) n) := by
          rfl
    _ = (1 / 2 : ENNReal) ^ (n + 1) := by
          -- Rewrite the real closed form into the same geometric power on `ENNReal`.
          rw [geometricPMFReal]
          norm_num
          simpa using (pow_succ (2⁻¹ : ENNReal) n).symm

/-- The canonical first-win waiting time on the fair Bernoulli product space has the geometric law
with parameter `1 / 2`, pushed forward along `ℕ ↪ ℕ∞`. -/
theorem hasLaw_petersburgFirstWinWaitingTime :
    HasLaw petersburgFirstWinWaitingTime
      (Measure.map (fun n : ℕ ↦ (n : ℕ∞))
        (geometricMeasure petersburgHalfPos petersburgHalfLeOne))
      fairBernoulliMeasure := by
  have hmeas : Measurable petersburgFirstWinWaitingTime := by
    rw [ENat.measurable_iff]
    intro n
    change MeasurableSet {ω : BernoulliSequence | petersburgFirstWinWaitingTime ω = (n : ℕ∞)}
    rw [petersburgFirstWinWaitingTime_preimage_singleton_coe]
    have hset :
        {ω : BernoulliSequence | ∀ i : Fin (n + 1), ω i = petersburgFirstSuccessPattern n i} =
          ⋂ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            (fun ω : BernoulliSequence ↦ ω i) ⁻¹'
              ({petersburgFirstSuccessPattern n i} : Set Bool) := by
      ext ω
      simp
    rw [hset]
    exact (Finset.univ : Finset (Fin (n + 1))).measurableSet_biInter fun i _ ↦
      (measurable_pi_apply (i : ℕ)) (measurableSet_singleton _)
  refine ⟨hmeas.aemeasurable, ?_⟩
  refine Measure.ext_of_singleton ?_
  intro a
  cases a using ENat.recTopCoe with
  | top =>
      -- The top mass is exactly the null all-loss branch on the Bernoulli side and empty on the
      -- pushed-forward geometric side.
      rw [Measure.map_apply hmeas (measurableSet_singleton (⊤ : ℕ∞))]
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (⊤ : ℕ∞))]
      change fairBernoulliMeasure {ω : BernoulliSequence | petersburgFirstWinWaitingTime ω = ⊤} =
        geometricMeasure petersburgHalfPos petersburgHalfLeOne
          ((fun n : ℕ ↦ (n : ℕ∞)) ⁻¹' ({⊤} : Set ℕ∞))
      rw [petersburgFirstWinWaitingTime_eq_top_measure_zero]
      rw [show ((fun n : ℕ ↦ (n : ℕ∞)) ⁻¹' ({⊤} : Set ℕ∞)) = (∅ : Set ℕ) by
            ext n
            simp]
      simp
  | coe n =>
      -- Every finite singleton mass agrees with the geometric waiting-time formula.
      rw [Measure.map_apply hmeas (measurableSet_singleton (n : ℕ∞))]
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (n : ℕ∞))]
      change fairBernoulliMeasure {ω : BernoulliSequence |
          petersburgFirstWinWaitingTime ω = (n : ℕ∞)} =
        geometricMeasure petersburgHalfPos petersburgHalfLeOne
          ((fun k : ℕ ↦ (k : ℕ∞)) ⁻¹' ({(n : ℕ∞)} : Set ℕ∞))
      rw [petersburgFirstWinWaitingTime_eq_coe_measure]
      rw [show ((fun k : ℕ ↦ (k : ℕ∞)) ⁻¹' ({(n : ℕ∞)} : Set ℕ∞)) = ({n} : Set ℕ) by
            ext k
            simp]
      exact (geometricHalfMeasure_apply_singleton n).symm

/-- Helper for Example 4.22: along the all-loss branch, the explicit values `1 - 2^n` tend to
`-∞` in `EReal`. -/
private theorem petersburgAllLosses_tendstoBot :
    Tendsto (fun n : ℕ ↦ (((1 - (2 : ℝ) ^ n : ℝ)) : EReal)) atTop (nhds (⊥ : EReal)) := by
  have hreal : Tendsto (fun n : ℕ ↦ (1 - (2 : ℝ) ^ n : ℝ)) atTop atBot := by
    -- Route correction: prove the real sequence tends to `-∞` first, then coerce to `EReal`
    -- once via `EReal.tendsto_coe_nhds_bot_iff`.
    refine tendsto_atBot.2 ?_
    intro b
    have hpow : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hpow_eventually : ∀ᶠ n in atTop, 1 - b ≤ (2 : ℝ) ^ n := by
      exact (tendsto_atTop.1 hpow) (1 - b)
    filter_upwards [hpow_eventually] with n hn
    linarith
  simpa using (EReal.tendsto_coe_nhds_bot_iff.2 hreal)

/-- Helper for Example 4.22: the `EReal`-valued partial sum is measurable because the real-valued
process already has a stable two-valued prefix-loss normal form. -/
private theorem measurable_petersburgPartialSumEReal (n : ℕ) :
    Measurable (fun ω : BernoulliSequence ↦ (petersburgPartialSum n ω : EReal)) := by
  classical
  -- Rewrite the process into its prefix-loss piecewise-constant form before proving measurability.
  have hEqReal :
      (fun ω : BernoulliSequence ↦ petersburgPartialSum n ω) =
        (petersburgPrefixLosses n).piecewise
          (fun _ : BernoulliSequence ↦ 1 - (2 : ℝ) ^ n)
          (fun _ ↦ (1 : ℝ)) := by
    funext ω
    rw [petersburgPartialSum_eq_if_allPrefixLosses]
    simp [Set.piecewise, petersburgPrefixLosses]
  have hMeasReal : Measurable (fun ω : BernoulliSequence ↦ petersburgPartialSum n ω) := by
    rw [hEqReal]
    exact Measurable.piecewise (measurableSet_petersburgPrefixLosses n) measurable_const
      measurable_const
  exact measurable_coe_real_ereal.comp hMeasReal

/-- Helper for Example 4.22: each real-valued Petersburg partial sum is integrable because it is
piecewise constant on a probability space. -/
private theorem integrable_petersburgPartialSum (n : ℕ) :
    Integrable (fun ω : BernoulliSequence ↦ petersburgPartialSum n ω) fairBernoulliMeasure := by
  classical
  -- Freeze the two-valued normal form and apply the standard integrability theorem for a
  -- measurable piecewise combination of constants.
  have hEq :
      (fun ω : BernoulliSequence ↦ petersburgPartialSum n ω) =
        (petersburgPrefixLosses n).piecewise
          (fun _ : BernoulliSequence ↦ 1 - (2 : ℝ) ^ n)
          (fun _ ↦ (1 : ℝ)) := by
    funext ω
    rw [petersburgPartialSum_eq_if_allPrefixLosses]
    simp [Set.piecewise, petersburgPrefixLosses]
  have hleft :
      IntegrableOn (fun _ : BernoulliSequence ↦ 1 - (2 : ℝ) ^ n)
        (petersburgPrefixLosses n) fairBernoulliMeasure :=
    integrableOn_const (fairBernoulliMeasure_ne_top _) (by simp)
  have hright :
      IntegrableOn (fun _ : BernoulliSequence ↦ (1 : ℝ))
        (petersburgPrefixLosses n)ᶜ fairBernoulliMeasure :=
    integrableOn_const (fairBernoulliMeasure_ne_top _) (by simp)
  rw [hEq]
  exact Integrable.piecewise (measurableSet_petersburgPrefixLosses n) hleft hright

/-- Helper for Example 4.22: the textbook two-valued branch formula has expectation `0`. -/
private theorem integral_petersburgTwoValuedBranch_eq_zero (n : ℕ) :
    ∫ ω, (if ω ∈ petersburgPrefixLosses n then 1 - (2 : ℝ) ^ n else 1)
        ∂ fairBernoulliMeasure = 0 := by
  classical
  let A : Set BernoulliSequence := petersburgPrefixLosses n
  have hA : MeasurableSet A := measurableSet_petersburgPrefixLosses n
  have hA_fin : fairBernoulliMeasure A ≠ ⊤ := by
    simpa [A] using fairBernoulliMeasure_ne_top A
  have hAc_fin : fairBernoulliMeasure Aᶜ ≠ ⊤ := fairBernoulliMeasure_ne_top Aᶜ
  have hA_int :
      IntegrableOn (fun _ : BernoulliSequence ↦ 1 - (2 : ℝ) ^ n) A fairBernoulliMeasure :=
    integrableOn_const hA_fin (by simp)
  have hAc_int :
      IntegrableOn (fun _ : BernoulliSequence ↦ (1 : ℝ)) Aᶜ fairBernoulliMeasure :=
    integrableOn_const hAc_fin (by simp)
  -- Rewrite the branch function as a piecewise constant so each part integrates explicitly.
  have hEq :
      (fun ω : BernoulliSequence ↦ if ω ∈ A then 1 - (2 : ℝ) ^ n else 1) =
        A.piecewise (fun _ : BernoulliSequence ↦ 1 - (2 : ℝ) ^ n) (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp [Set.piecewise]
  rw [hEq]
  rw [integral_piecewise hA hA_int hAc_int]
  rw [setIntegral_const, setIntegral_const]
  have hAreal : fairBernoulliMeasure.real A = ((2 : ℝ) ^ n)⁻¹ := by
    simpa [A, Measure.real_def] using
      congrArg ENNReal.toReal (petersburgPrefixLosses_measure n)
  have hAcompl : fairBernoulliMeasure.real Aᶜ = 1 - ((2 : ℝ) ^ n)⁻¹ := by
    rw [Measure.real_def, measure_compl hA hA_fin, fairBernoulliMeasure_univ]
    rw [ENNReal.toReal_sub_of_le ?_ (by simp)]
    · simpa [hAreal]
    · change fairBernoulliMeasure (petersburgPrefixLosses n) ≤ 1
      rw [petersburgPrefixLosses_measure]
      exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [hAreal, hAcompl, smul_eq_mul, smul_eq_mul]
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by
    positivity
  field_simp [hpow_ne]
  ring

/-- Helper for Example 4.22: a real integrable function becomes textbook-`erealIntegrable` after
the canonical coercion `ℝ → EReal`. -/
private theorem erealIntegrable_realCoe {g : BernoulliSequence → ℝ}
    (hg_meas : Measurable g)
    (hg : Integrable g fairBernoulliMeasure) :
    erealIntegrable (fun ω ↦ (g ω : EReal)) fairBernoulliMeasure := by
  refine ⟨measurable_coe_real_ereal.comp hg_meas, ?_⟩
  -- The `EReal` absolute value of a finite real is exactly `ENNReal.ofReal |g|`.
  rw [hasFiniteIntegral_def]
  simpa [EReal.abs_def, Real.norm_eq_abs] using
    (hasFiniteIntegral_iff_ofReal
      (μ := fairBernoulliMeasure)
      (f := fun ω ↦ |g ω|)
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)).mp hg.norm.hasFiniteIntegral

/-- Helper for Example 4.22: the chapter-level `erealIntegral` of a real-valued integrable
function agrees with the ordinary real integral after coercion. -/
private theorem erealIntegral_realCoe_eq_integral {g : BernoulliSequence → ℝ}
    (hg : Integrable g fairBernoulliMeasure)
    (hdef : erealIntegralDefined (fun ω ↦ (g ω : EReal)) fairBernoulliMeasure) :
    erealIntegral (fun ω ↦ (g ω : EReal)) fairBernoulliMeasure hdef =
      ((∫ ω, g ω ∂ fairBernoulliMeasure : ℝ) : EReal) := by
  have hpos_ne_top : (∫⁻ ω, ENNReal.ofReal (g ω) ∂ fairBernoulliMeasure) ≠ ⊤ :=
    hg.lintegral_lt_top.ne
  have hneg_ne_top : (∫⁻ ω, ENNReal.ofReal (-g ω) ∂ fairBernoulliMeasure) ≠ ⊤ :=
    hg.neg.lintegral_lt_top.ne
  have hpos_eq :
      ∫⁻ ω, ((g ω : EReal).toENNReal) ∂ fairBernoulliMeasure =
        ∫⁻ ω, ENNReal.ofReal (g ω) ∂ fairBernoulliMeasure := by
    refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
    intro ω
    simp
  have hneg_eq :
      ∫⁻ ω, ((-(g ω : EReal)).toENNReal) ∂ fairBernoulliMeasure =
        ∫⁻ ω, ENNReal.ofReal (-g ω) ∂ fairBernoulliMeasure := by
    refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
    intro ω
    simp
  rw [erealIntegral_spec, hpos_eq, hneg_eq]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
  rfl

/-- The Petersburg partial sums converge pointwise in `EReal` to the extended-real limit `S`,
including the null all-losses branch where `S = -∞`. -/
theorem petersburgPartialSum_tendsto_limit (ω : BernoulliSequence) :
    Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω)) := by
  -- Route correction: split by the waiting time itself. The `⊤` branch uses the dedicated
  -- `EReal`-to-`⊥` lemma, while the finite branch becomes eventually constant `1`.
  cases hω : petersburgFirstWinWaitingTime ω using ENat.recTopCoe with
  | top =>
      have hall : ∀ n, ω n = false := by
        simpa [hω] using (petersburgFirstWinWaitingTime_eq_top_iff (ω := ω))
      have hseq :
          (fun n : ℕ ↦ (petersburgPartialSum n ω : EReal)) =
            fun n ↦ (((1 - (2 : ℝ) ^ n : ℝ)) : EReal) := by
        funext n
        rw [petersburgPartialSum_eq_if_allPrefixLosses]
        simp [hall]
      rw [show petersburgLimit ω = (⊥ : EReal) by simp [petersburgLimit, hall]]
      rw [hseq]
      exact petersburgAllLosses_tendstoBot
  | coe m =>
      have hwait : petersburgFirstWinWaitingTime ω = (m : ℕ∞) := hω
      rw [petersburgFirstWinWaitingTime_eq_coe_iff] at hω
      have hnotall : ¬ ∀ n, ω n = false := by
        intro hall
        simpa [hall m] using hω.1
      have h_eventually :
          (fun _ : ℕ ↦ (1 : EReal)) =ᶠ[atTop] fun n ↦ (petersburgPartialSum n ω : EReal) := by
        refine Filter.eventually_atTop.2 ⟨m + 1, ?_⟩
        intro n hn
        rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
        -- After the first win, every later partial sum stays equal to the terminal gain `1`.
        have hsum :
            petersburgPartialSum (m + 1 + k) ω = petersburgProfit (m + k) m := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (petersburgPartialSum_succ_eq_profit_of_waitingTime (ω := ω) (n := m + k) hwait)
        simp [hsum, petersburgProfit, Nat.not_lt.mpr (Nat.le_add_right m k)]
      simpa [petersburgLimit, hnotall] using
        (Tendsto.congr' h_eventually tendsto_const_nhds)

/-- The all-losses path has probability zero, so the extended-real limit is almost surely `1`. -/
theorem petersburgLimit_ae_eq_one :
    petersburgLimit =ᵐ[fairBernoulliMeasure] fun _ ↦ (1 : EReal) := by
  rw [Filter.EventuallyEq, ae_iff]
  have hset :
      {ω : BernoulliSequence | ¬ petersburgLimit ω = (1 : EReal)} =
        {ω : BernoulliSequence | petersburgFirstWinWaitingTime ω = ⊤} := by
    ext ω
    change (¬ petersburgLimit ω = (1 : EReal)) ↔ petersburgFirstWinWaitingTime ω = ⊤
    rw [petersburgFirstWinWaitingTime_eq_top_iff]
    by_cases hω : ∀ n, ω n = false
    · have hbot : ¬ ((⊥ : EReal) = 1) := EReal.bot_ne_coe 1
      simpa [petersburgLimit, hω] using hbot
    · simp [petersburgLimit, hω]
  -- Outside the all-loss branch, the limit variable is literally the constant `1`.
  rw [hset, petersburgFirstWinWaitingTime_eq_top_measure_zero]

/-- Every finite-stage Petersburg gain has expectation `0` under the fair Bernoulli product
measure. -/
theorem integral_petersburgPartialSum_eq_zero (n : ℕ) :
    ∫ ω, petersburgPartialSum n ω ∂ fairBernoulliMeasure = 0 := by
  -- Freeze the partial sum at its prefix-loss two-valued normal form before integrating.
  have hEq :
      (fun ω : BernoulliSequence ↦ petersburgPartialSum n ω) =
        fun ω ↦ if ω ∈ petersburgPrefixLosses n then 1 - (2 : ℝ) ^ n else 1 := by
    funext ω
    rw [petersburgPartialSum_eq_if_allPrefixLosses]
    simp [petersburgPrefixLosses]
  rw [hEq]
  exact integral_petersburgTwoValuedBranch_eq_zero n

/-- The Petersburg partial sums converge almost surely to the extended-real limit `S`. -/
theorem petersburgPartialSum_ae_tendsto_limit :
    ∀ᵐ ω ∂ fairBernoulliMeasure,
      Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω)) :=
  Filter.Eventually.of_forall petersburgPartialSum_tendsto_limit

/-- The Petersburg partial sums admit no integrable minorant under the fair Bernoulli product
measure. -/
theorem petersburgPartialSum_no_integrable_minorant :
    ¬ ∃ g : BernoulliSequence → ℝ,
      Integrable g fairBernoulliMeasure ∧
        ∀ n, g ≤ᵐ[fairBernoulliMeasure] petersburgPartialSum n := by
  rintro ⟨g, hg, hminor⟩
  let gm : BernoulliSequence → ℝ := hg.1.mk g
  let gE : BernoulliSequence → EReal := fun ω ↦ (gm ω : EReal)
  let fSeq : ℕ → BernoulliSequence → EReal := fun n ω ↦ (petersburgPartialSum n ω : EReal)
  have hgm_meas : Measurable gm := hg.1.measurable_mk
  have hgm_ae : g =ᵐ[fairBernoulliMeasure] gm := hg.1.ae_eq_mk
  have hgm_int : Integrable gm fairBernoulliMeasure := hg.congr hgm_ae
  have hgE : erealIntegrable gE fairBernoulliMeasure := erealIntegrable_realCoe hgm_meas hgm_int
  have hfSeq_meas : ∀ n, Measurable (fSeq n) := by
    intro n
    exact measurable_petersburgPartialSumEReal n
  have hminor_m : ∀ n, gm ≤ᵐ[fairBernoulliMeasure] petersburgPartialSum n := by
    intro n
    filter_upwards [hminor n, hgm_ae] with ω hω hgmω
    rwa [← hgmω]
  have h_lowerE : ∀ n, gE ≤ᵐ[fairBernoulliMeasure] fSeq n := by
    intro n
    -- Coerce the real-valued lower bounds into the `EReal` order once and for all.
    exact (hminor_m n).mono fun ω hω ↦ by
      change (gm ω : EReal) ≤ (petersburgPartialSum n ω : EReal)
      exact_mod_cast hω
  have h_lower_liminf :
      gE ≤ᵐ[fairBernoulliMeasure] fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop := by
    have h_all : ∀ᵐ ω ∂ fairBernoulliMeasure, ∀ n, gE ω ≤ fSeq n ω := by
      rw [ae_all_iff]
      exact h_lowerE
    -- Pointwise domination of every term implies domination of the tail liminf.
    refine h_all.mono ?_
    intro ω hω
    exact le_trans (le_iInf hω) Filter.iInf_le_liminf
  have hlimf_defined :
      erealIntegralDefined (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop) fairBernoulliMeasure :=
    erealIntegralDefined_of_ae_le hgE (Measurable.liminf hfSeq_meas) h_lower_liminf
  have hfatou :=
    erealIntegral_liminf_le_liminf_erealIntegral fairBernoulliMeasure hgE hfSeq_meas h_lowerE
  have hlimf_ae :
      (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop) =ᵐ[fairBernoulliMeasure] petersburgLimit := by
    exact Filter.EventuallyEq.of_eq
      (funext fun ω ↦ (petersburgPartialSum_tendsto_limit ω).liminf_eq)
  have hleft_eq_one :
      erealIntegral (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop)
        fairBernoulliMeasure hlimf_defined = 1 := by
    -- Rewrite the liminf integrand to the a.s.-constant limit `1` and compute its integral.
    rw [erealIntegral_spec]
    have hpos_ae :
        (fun ω ↦ (liminf (fun n ↦ fSeq n ω) atTop).toENNReal) =ᵐ[fairBernoulliMeasure]
          fun _ ↦ (1 : ENNReal) := by
      filter_upwards
        [(hlimf_ae.fun_comp fun x ↦ x.toENNReal).trans
          (petersburgLimit_ae_eq_one.fun_comp fun x ↦ x.toENNReal)] with ω hω
      have hω' : (liminf (fun n ↦ fSeq n ω) atTop).toENNReal = EReal.toENNReal (1 : EReal) := by
        simpa [Function.comp] using hω
      have hone : EReal.toENNReal (1 : EReal) = (1 : ENNReal) := by
        simpa using (EReal.real_coe_toENNReal (1 : ℝ))
      exact hω'.trans hone
    have hneg_ae :
        (fun ω ↦ (-(liminf (fun n ↦ fSeq n ω) atTop)).toENNReal) =ᵐ[fairBernoulliMeasure]
          fun _ ↦ (0 : ENNReal) := by
      filter_upwards
        [(hlimf_ae.fun_comp fun x ↦ (-x).toENNReal).trans
          (petersburgLimit_ae_eq_one.fun_comp fun x ↦ (-x).toENNReal)] with ω hω
      have hω' : (-liminf (fun n ↦ fSeq n ω) atTop).toENNReal =
          EReal.toENNReal (-((1 : EReal))) := by
        simpa [Function.comp] using hω
      have hzero : EReal.toENNReal (-((1 : EReal))) = (0 : ENNReal) := by
        simpa using (EReal.real_coe_toENNReal (-1 : ℝ))
      exact hω'.trans hzero
    rw [lintegral_congr_ae hpos_ae, lintegral_congr_ae hneg_ae]
    simpa [fairBernoulliMeasure_univ]
  have hright_term_zero :
      ∀ n,
        erealIntegral (fSeq n) fairBernoulliMeasure
            (erealIntegralDefined_of_ae_le hgE (hfSeq_meas n) (h_lowerE n)) = 0 := by
    intro n
    -- Each finite-stage `EReal` integral is the ordinary real integral of the same process.
    rw [erealIntegral_realCoe_eq_integral (g := fun ω ↦ petersburgPartialSum n ω)
      (hg := integrable_petersburgPartialSum n)
      (hdef := erealIntegralDefined_of_ae_le hgE (hfSeq_meas n) (h_lowerE n))]
    exact_mod_cast integral_petersburgPartialSum_eq_zero n
  have hright_eq_zero :
      liminf
          (fun n ↦ erealIntegral (fSeq n) fairBernoulliMeasure
            (erealIntegralDefined_of_ae_le hgE (hfSeq_meas n) (h_lowerE n)))
          atTop = 0 := by
    -- The right-hand side is the liminf of the constant-zero sequence.
    have hconst :
        (fun n ↦ erealIntegral (fSeq n) fairBernoulliMeasure
          (erealIntegralDefined_of_ae_le hgE (hfSeq_meas n) (h_lowerE n))) =
            fun _ : ℕ ↦ (0 : EReal) := by
      funext n
      exact hright_term_zero n
    rw [hconst, Filter.liminf_const]
  have hcontr : (1 : EReal) ≤ 0 := by
    calc
      (1 : EReal)
          = erealIntegral (fun ω ↦ liminf (fun n ↦ fSeq n ω) atTop) fairBernoulliMeasure
              hlimf_defined := hleft_eq_one.symm
      _ ≤ liminf
            (fun n ↦ erealIntegral (fSeq n) fairBernoulliMeasure
              (erealIntegralDefined_of_ae_le hgE (hfSeq_meas n) (h_lowerE n)))
            atTop := by
              simpa [fSeq, gE] using hfatou
      _ = 0 := hright_eq_zero
  have hnot : ¬ ((1 : EReal) ≤ 0) := by
    norm_num
  exact hnot hcontr

-- Proof sketch: the fair Petersburg doubling strategy lives on the canonical fair coin-flip space
-- `Bool^ℕ`; the adapted stakes `H_n` generate partial sums `S_n` with expectation `0`, the
-- pathwise limit is the extended-real random variable `S` that equals `-∞` on the null
-- all-losses branch and `1` otherwise, and the sequence has no integrable minorant.
/-- Example 4.22: on the canonical fair coin-flip space `Bool^ℕ`, with textbook round payoff
`false ↦ -1` and `true ↦ 1`, the adapted doubling stakes `H_n` define a gain process `S_n` that
converges almost surely to the extended-real limit `S`, every `S_n` has expectation `0`, and the
sequence admits no integrable minorant. -/
theorem example_4_22 :
    (∀ᵐ ω ∂ fairBernoulliMeasure,
      Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω))) ∧
    (∀ n, ∫ ω, petersburgPartialSum n ω ∂ fairBernoulliMeasure = 0) ∧
    ¬ ∃ g : BernoulliSequence → ℝ,
      Integrable g fairBernoulliMeasure ∧
        ∀ n, g ≤ᵐ[fairBernoulliMeasure] petersburgPartialSum n := by
  exact ⟨petersburgPartialSum_ae_tendsto_limit, integral_petersburgPartialSum_eq_zero,
    petersburgPartialSum_no_integrable_minorant⟩
