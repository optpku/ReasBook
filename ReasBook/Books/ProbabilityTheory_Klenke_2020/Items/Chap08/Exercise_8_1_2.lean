/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Interval
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

local instance : MeasurableSpace (Finset ℕ) := ⊤

/-
The reduced absent-minded-passenger process is governed by the reserved seats that get taken by a
passenger forced to choose uniformly at random. Starting from the still-available seats
`{1} ∪ s`, a random choice of seat `1` ends the chain, while a random choice of `j ∈ s` records
that seat `j` was taken out of order and continues only with the larger reserved seats. The
smaller seat labels are no longer available, because their owners sit down deterministically
before the next random choice.
-/
private def absentMindedPassengerChosenSeatsFromRemaining : Finset ℕ → PMF (Finset ℕ)
  | s =>
      let choices := insert 1 s
      let p : PMF ℕ := PMF.uniformOfFinset choices (by simp [choices])
      p.bindOnSupport fun j hj ↦
        if h1 : j = 1 then
          PMF.pure ∅
        else
          PMF.map (insert j)
            (absentMindedPassengerChosenSeatsFromRemaining (s.filter fun m ↦ j < m))
termination_by s => s.card
decreasing_by
  have hj' : j ∈ insert 1 s := by
    simpa [p, choices] using hj
  have hjs : j ∈ s := by
    rcases Finset.mem_insert.mp hj' with h | h
    · contradiction
    · exact h
  have hproper : s.filter (fun m ↦ j < m) ⊂ s := by
    rw [Finset.filter_ssubset]
    exact ⟨j, hjs, by simp⟩
  exact Finset.card_lt_card hproper

/-- The absent-minded passenger model on `n` seats, recorded as the random finite set of reserved
seat labels in `{2, …, n}` that are taken by a random chooser before seat `1` is finally chosen.
For every `k ≥ 2`, passenger `k` gets their own seat exactly when `k` is absent from this set, and
the first passenger gets their own seat exactly when the set is empty. -/
noncomputable def absentMindedPassengerChosenSeats (n : ℕ) : PMF (Finset ℕ) :=
  absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc 2 n)

/-- Predicate on the reduced absent-minded-passenger states saying that passenger `k` gets their
reserved seat. For `k = 1` this means that no later reserved seat is ever chosen out of order,
i.e. the recorded set is empty; for `k ≥ 2` it means that seat `k` is never chosen by a displaced
passenger. -/
def absentMindedPassengerGetsReservedSeat (k : ℕ) (chosen : Finset ℕ) : Prop :=
  if k = 1 then chosen = ∅ else k ∉ chosen

/-- The probability that passenger `k` gets their reserved seat in the absent-minded passenger
problem with `n` seats, defined from the actual reduced random process rather than by a closed
formula. -/
noncomputable def absentMindedPassengerReservedSeatProbability (n k : ℕ) : ℝ := by
  letI : MeasurableSpace (Finset ℕ) := ⊤
  exact ((absentMindedPassengerChosenSeats n).toMeasure
    {chosen | absentMindedPassengerGetsReservedSeat k chosen}).toReal

/-- Helper for Exercise 8.1.2: the recursive PMF can be viewed as an ordinary `bind` over the
uniform first choice from `insert 1 s`. -/
private lemma absentMindedPassengerChosenSeatsFromRemaining_bind (s : Finset ℕ) :
    absentMindedPassengerChosenSeatsFromRemaining s =
      (PMF.uniformOfFinset (insert 1 s) (by simp)).bind fun j ↦
        if h1 : j = 1 then
          PMF.pure ∅
        else
          PMF.map (insert j)
            (absentMindedPassengerChosenSeatsFromRemaining (s.filter fun m ↦ j < m)) := by
  rw [absentMindedPassengerChosenSeatsFromRemaining.eq_1]
  simp [PMF.bindOnSupport_eq_bind]

/-- Helper for Exercise 8.1.2: filtering the interval `Finset.Icc m n` by `j < t` produces the
next interval `Finset.Icc (j + 1) n`. -/
private lemma filter_Icc_eq_Icc_succ {m j n : ℕ} (hj : j ∈ Finset.Icc m n) :
    (Finset.Icc m n).filter (fun t ↦ j < t) = Finset.Icc (j + 1) n := by
  have hmj : m ≤ j := (Finset.mem_Icc.mp hj).1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hx
    exact ⟨Nat.succ_le_of_lt hx.2, hx.1.2⟩
  · intro hx
    have hjx : j < x := lt_of_lt_of_le (Nat.lt_succ_self j) hx.1
    exact ⟨⟨le_trans hmj (Nat.le_of_lt hjx), hx.2⟩, hjx⟩

/-- Helper for Exercise 8.1.2: every element appearing in a recorded state already belongs to the
current remaining set. -/
private lemma chosenSeatsFromRemaining_mem_remaining {s chosen : Finset ℕ} {x : ℕ}
    (hchosen : chosen ∈ (absentMindedPassengerChosenSeatsFromRemaining s).support)
    (hx : x ∈ chosen) :
    x ∈ s := by
  classical
  let P : Finset ℕ → Prop := fun s ↦
    ∀ {chosen : Finset ℕ} {x : ℕ},
      chosen ∈ (absentMindedPassengerChosenSeatsFromRemaining s).support →
        x ∈ chosen → x ∈ s
  have hP : ∀ s : Finset ℕ, (∀ t ⊂ s, P t) → P s := by
    intro s ih chosen x hchosen hx
    rw [absentMindedPassengerChosenSeatsFromRemaining_bind] at hchosen
    rcases
        (@PMF.mem_support_bind_iff _ _
          (PMF.uniformOfFinset (insert 1 s) (by simp))
          (fun j ↦
            if h1 : j = 1 then
              PMF.pure ∅
            else
              PMF.map (insert j)
                (absentMindedPassengerChosenSeatsFromRemaining (s.filter fun m ↦ j < m)))
          chosen).1 hchosen with ⟨j, hj, hbranch⟩
    have hj' : j ∈ insert 1 s := by
      simpa using hj
    by_cases h1 : j = 1
    · -- If the random chain stops at seat `1`, no reserved seat is recorded.
      have hchosenEmpty : chosen = ∅ := by
        simpa [h1] using hbranch
      subst hchosenEmpty
      simp at hx
    · -- Otherwise the next recorded seat is `j`, and the recursive output stays inside the tail.
      have hjs : j ∈ s := by
        rcases Finset.mem_insert.mp hj' with hj1 | hjs
        · exact (h1 hj1).elim
        · exact hjs
      have hbranch' :
          chosen ∈
            (PMF.map
              (insert j)
              (absentMindedPassengerChosenSeatsFromRemaining
                (s.filter fun m ↦ j < m))).support := by
        simpa [h1] using hbranch
      rcases
          (@PMF.mem_support_map_iff _ _
            (insert j)
            (absentMindedPassengerChosenSeatsFromRemaining (s.filter fun m ↦ j < m))
            chosen).1 hbranch' with
        ⟨tailChosen, htailChosen, rfl⟩
      have hproper : s.filter (fun m ↦ j < m) ⊂ s := by
        rw [Finset.filter_ssubset]
        exact ⟨j, hjs, by simp⟩
      rcases Finset.mem_insert.mp hx with rfl | hxTail
      · exact hjs
      · exact (Finset.mem_filter.mp (ih _ hproper htailChosen hxTail)).1
  have hs : P s := by
    show P s
    exact @Finset.strongInductionOn _ P s hP
  exact hs hchosen hx

/-- Helper for Exercise 8.1.2: every out-of-order reserved seat recorded by the reduced process
already belongs to the current remaining set. -/
private lemma chosenSeatsFromRemaining_subset_remaining {s chosen : Finset ℕ}
    (hchosen : chosen ∈ (absentMindedPassengerChosenSeatsFromRemaining s).support) :
    chosen ⊆ s := by
  intro x hx
  exact chosenSeatsFromRemaining_mem_remaining hchosen hx

/-- Helper for Exercise 8.1.2: the initial choice set `insert 1 (Finset.Icc m n)` has cardinality
`n - m + 2` once `m ≥ 2` and `m ≤ n`. -/
private lemma card_insert_one_Icc (hm : 2 ≤ m) (hmn : m ≤ n) :
    (insert 1 (Finset.Icc m n)).card = n - m + 2 := by
  have hnotMem : 1 ∉ Finset.Icc m n := by
    intro h
    have hm1 : m ≤ 1 := (Finset.mem_Icc.mp h).1
    omega
  rw [Finset.card_insert_of_notMem hnotMem, Nat.card_Icc]
  omega

-- Proof sketch: in the reduced model, passenger `1` gets their own seat exactly when the random
-- chain stops immediately, i.e. when no seat in `{2, …, n}` is ever chosen. That happens iff the
-- initial uniform choice is seat `1`, which has probability `1 / n`.
/-- The absent-minded first passenger gets their reserved seat with probability `1 / n`. -/
theorem absentMindedPassenger_first_passenger_reservedSeatProbability (n : ℕ) (hn : 0 < n) :
    absentMindedPassengerReservedSeatProbability n 1 = (1 : ℝ) / n := by
  classical
  letI : MeasurableSpace (Finset ℕ) := ⊤
  let choices : Finset ℕ := insert 1 (Finset.Icc 2 n)
  let p : PMF ℕ := PMF.uniformOfFinset choices (by simp [choices])
  have hchoicesCard : choices.card = n := by
    dsimp [choices]
    cases n with
    | zero => cases Nat.lt_asymm hn hn
    | succ n =>
        have hnotMem : 1 ∉ Finset.Icc 2 (n + 1) := by simp
        rw [Finset.card_insert_of_notMem hnotMem, Nat.card_Icc]
        omega
  -- Rewrite the reduced process as a first uniform choice followed by the recursive branch.
  have hmeasure :
      (absentMindedPassengerChosenSeats n).toMeasure ({∅} : Set (Finset ℕ)) =
        (p 1) := by
    rw [absentMindedPassengerChosenSeats, absentMindedPassengerChosenSeatsFromRemaining_bind]
    rw [@PMF.toMeasure_bind_apply _ _
      (PMF.uniformOfFinset (insert 1 (Finset.Icc 2 n)) (by simp))
      (fun j ↦
        if h1 : j = 1 then
          PMF.pure ∅
        else
          PMF.map (insert j)
            (absentMindedPassengerChosenSeatsFromRemaining ((Finset.Icc 2 n).filter fun m ↦ j < m)))
      ({∅} : Set (Finset ℕ))
      _
      (measurableSet_singleton _)]
    -- All nonterminal branches map through `insert j`, so they cannot land at `∅`.
    trans p 1 * ((PMF.pure ∅).toMeasure ({∅} : Set (Finset ℕ)))
    · refine tsum_eq_single 1 ?_
      intro j hj
      by_cases hj1 : j = 1
      · exact (hj hj1).elim
      · rw [dif_neg hj1]
        rw [@PMF.toMeasure_map_apply _ _
          (insert j)
          (absentMindedPassengerChosenSeatsFromRemaining ((Finset.Icc 2 n).filter fun m ↦ j < m))
          ({∅} : Set (Finset ℕ))
          _
          _
          (measurable_of_countable (insert j))
          (measurableSet_singleton _)]
        rw [show (insert j) ⁻¹' ({∅} : Set (Finset ℕ)) = (∅ : Set (Finset ℕ)) by
          ext t
          simp]
        simp
    · simp [p, choices, PMF.toMeasure_pure_apply]
  -- Convert the singleton mass to a real number and simplify the uniform first-choice weight.
  rw [absentMindedPassengerReservedSeatProbability]
  simp [absentMindedPassengerGetsReservedSeat]
  simpa [p, choices, hchoicesCard, hn.ne', one_div] using congrArg ENNReal.toReal hmeasure

/-- Helper for Exercise 8.1.2: once every remaining reserved seat label is larger than `k`, the
reduced process can no longer record seat `k`. -/
private lemma absentMindedPassengerAvoidSeatOf_lt_start {m k n : ℕ} (hkm : k < m) :
    (((absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc m n)).toMeasure
      {chosen | k ∉ chosen}).toReal) = 1 := by
  letI : MeasurableSpace (Finset ℕ) := ⊤
  have hsupport :
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc m n)).support ⊆
        {chosen | k ∉ chosen} := by
    intro chosen hchosen
    simp only [Set.mem_setOf_eq]
    intro hkchosen
    have hkInterval :
        k ∈ Finset.Icc m n :=
      chosenSeatsFromRemaining_subset_remaining hchosen hkchosen
    exact (not_lt_of_ge (Finset.mem_Icc.mp hkInterval).1) hkm
  have hmeasure :
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc m n)).toMeasure
          {chosen | k ∉ chosen} = 1 := by
    exact (@PMF.toMeasure_apply_eq_one_iff _ _
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc m n))
      ({chosen | k ∉ chosen} : Set (Finset ℕ))
      (by simp)).2 hsupport
  simpa using congrArg ENNReal.toReal hmeasure

/-- Helper for Exercise 8.1.2: inserting a seat label `j ≠ k` preserves the event that `k` is not
recorded. -/
private lemma absentMindedPassengerAvoidSeatAfterInsert_eq_tail {j k n : ℕ} (hjk : j ≠ k) :
    (((PMF.map (insert j)
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (j + 1) n))).toMeasure
      {chosen | k ∉ chosen}).toReal) =
      (((absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (j + 1) n)).toMeasure
        {chosen | k ∉ chosen}).toReal) := by
  letI : MeasurableSpace (Finset ℕ) := ⊤
  have hmeasure :
      (PMF.map (insert j)
        (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (j + 1) n))).toMeasure
          {chosen | k ∉ chosen} =
        (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (j + 1) n)).toMeasure
          {chosen | k ∉ chosen} := by
    rw [@PMF.toMeasure_map_apply _ _
      (insert j)
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (j + 1) n))
      {chosen | k ∉ chosen}
      _
      _
      (measurable_of_countable (insert j))
      (by simp)]
    congr 1
    ext chosen
    constructor
    · intro h hkChosen
      exact h (Finset.mem_insert_of_mem hkChosen)
    · intro h hkInsert
      rcases Finset.mem_insert.mp hkInsert with hkEq | hkChosen
      · exact hjk hkEq.symm
      · exact h hkChosen
  simpa using congrArg ENNReal.toReal hmeasure

/-- Helper for Exercise 8.1.2: inserting seat `k` forces the avoided-seat event to fail. -/
private lemma absentMindedPassengerAvoidSeatAfterInsert_eq_zero {k n : ℕ} :
    (((PMF.map (insert k)
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (k + 1) n))).toMeasure
      {chosen | k ∉ chosen}).toReal) = 0 := by
  letI : MeasurableSpace (Finset ℕ) := ⊤
  have hmeasure :
      (PMF.map (insert k)
        (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (k + 1) n))).toMeasure
          {chosen | k ∉ chosen} = 0 := by
    rw [@PMF.toMeasure_map_apply _ _
      (insert k)
      (absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc (k + 1) n))
      {chosen | k ∉ chosen}
      _
      _
      (measurable_of_countable (insert k))
      (by simp)]
    rw [show (insert k) ⁻¹' ({chosen | k ∉ chosen} : Set (Finset ℕ)) = (∅ : Set (Finset ℕ)) by
      ext chosen
      simp [Set.preimage]]
    simp
  simpa using congrArg ENNReal.toReal hmeasure

/-- Helper for Exercise 8.1.2: `absentMindedPassengerAvoidSeatProbability n k m` is the real
probability that the reduced process started from `Finset.Icc m n` never records seat `k`. -/
private noncomputable abbrev absentMindedPassengerAvoidSeatProbability (n k m : ℕ) : ℝ :=
  (((absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc m n)).toMeasure
    {chosen | k ∉ chosen}).toReal)

/-- Helper for Exercise 8.1.2: filtering `Finset.Icc m n` by the condition `j < k` keeps exactly
the lower interval `Finset.Icc m (k - 1)`. -/
private lemma filter_Icc_lt_eq_Icc_pred {m k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (Finset.Icc m n).filter (fun j ↦ j < k) = Finset.Icc m (k - 1) := by
  -- Translate the strict upper bound `j < k` into the closed interval endpoint `j ≤ k - 1`.
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Helper for Exercise 8.1.2: filtering `Finset.Icc m n` by `¬ j < k` keeps exactly the upper
interval `Finset.Icc k n`. -/
private lemma filter_Icc_not_lt_eq_Icc {m k n : ℕ} (hmk : m ≤ k) :
    (Finset.Icc m n).filter (fun j ↦ ¬ j < k) = Finset.Icc k n := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjmn, hjnlt⟩
    rcases Finset.mem_Icc.mp hjmn with ⟨hmj, hjn⟩
    exact Finset.mem_Icc.mpr <| by
      omega
  · intro hj
    rcases Finset.mem_Icc.mp hj with ⟨hkj, hjn⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ?_, ?_⟩
    · exact ⟨le_trans hmk hkj, hjn⟩
    · omega

/-- Helper for Exercise 8.1.2: conditioning on the first random choice gives a real recursion for
the probability of avoiding seat `k` from the interval `Finset.Icc m n`. -/
private lemma absentMindedPassengerAvoidSeatProbabilityStepReal {n k m : ℕ}
    (hm : 2 ≤ m) (hmk : m ≤ k) (hkn : k ≤ n) :
      absentMindedPassengerAvoidSeatProbability n k m =
      ((n - k + 1 : ℝ) +
          Finset.sum (Finset.Icc m (k - 1)) fun j ↦
            absentMindedPassengerAvoidSeatProbability n k (j + 1)) / (n - m + 2 : ℝ) := by
  classical
  letI : MeasurableSpace (Finset ℕ) := ⊤
  let choices : Finset ℕ := insert 1 (Finset.Icc m n)
  have hchoicesNonempty : choices.Nonempty := by
    simp [choices]
  let branch : ℕ → PMF (Finset ℕ) := fun j ↦
    if h1 : j = 1 then
      PMF.pure ∅
    else
      PMF.map (insert j)
        (absentMindedPassengerChosenSeatsFromRemaining ((Finset.Icc m n).filter fun t ↦ j < t))
  let branchProbability : ℕ → ℝ := fun j ↦
    (((branch j).toMeasure {chosen | k ∉ chosen}).toReal)
  let p : PMF ℕ := PMF.uniformOfFinset choices hchoicesNonempty
  have hmeasureSet : MeasurableSet ({chosen | k ∉ chosen} : Set (Finset ℕ)) := by
    simp
  have hnotMemOne : 1 ∉ Finset.Icc m n := by
    intro h
    have hm1 : m ≤ 1 := (Finset.mem_Icc.mp h).1
    omega
  have hkpos : 0 < k := by
    omega
  have hchoicesCardNe : choices.card ≠ 0 := by
    exact Finset.card_ne_zero.mpr hchoicesNonempty
  have hcard : choices.card = n - m + 2 := by
    simpa [choices] using card_insert_one_Icc hm (le_trans hmk hkn)
  have hbranch_one : branchProbability 1 = 1 := by
    -- Choosing seat `1` terminates the random chain immediately with the empty recorded set.
    simp [branchProbability, branch]
  have hbranch_tail {j : ℕ} (hjmn : j ∈ Finset.Icc m n) (hjk : j ≠ k) :
      branchProbability j = absentMindedPassengerAvoidSeatProbability n k (j + 1) := by
    have hj1 : j ≠ 1 := by
      have hmj : m ≤ j := (Finset.mem_Icc.mp hjmn).1
      omega
    -- Any nonterminal choice `j` continues with the tail interval `Finset.Icc (j + 1) n`.
    simpa [branchProbability, branch, hj1, absentMindedPassengerAvoidSeatProbability,
      filter_Icc_eq_Icc_succ hjmn] using
      absentMindedPassengerAvoidSeatAfterInsert_eq_tail (j := j) (k := k) (n := n) hjk
  have hbranch_lower {j : ℕ} (hj : j ∈ Finset.Icc m (k - 1)) :
      branchProbability j = absentMindedPassengerAvoidSeatProbability n k (j + 1) := by
    rcases Finset.mem_Icc.mp hj with ⟨hmj, hjkPred⟩
    have hjmn : j ∈ Finset.Icc m n := by
      have hjn : j ≤ n := by
        omega
      exact Finset.mem_Icc.mpr ⟨hmj, hjn⟩
    have hjk : j ≠ k := by
      omega
    exact hbranch_tail hjmn hjk
  have hbranch_eqk : branchProbability k = 0 := by
    have hk1 : k ≠ 1 := by
      omega
    have hkmem : k ∈ Finset.Icc m n := by
      exact Finset.mem_Icc.mpr ⟨hmk, hkn⟩
    -- Choosing seat `k` records the forbidden seat immediately, so the avoided-seat event fails.
    simpa [branchProbability, branch, hk1, absentMindedPassengerAvoidSeatProbability,
      filter_Icc_eq_Icc_succ hkmem] using
      absentMindedPassengerAvoidSeatAfterInsert_eq_zero (k := k) (n := n)
  have hbranch_upper {j : ℕ} (hj : j ∈ Finset.Icc (k + 1) n) :
      branchProbability j = 1 := by
    rcases Finset.mem_Icc.mp hj with ⟨hkjSucc, hjn⟩
    have hjmn : j ∈ Finset.Icc m n := by
      have hmj : m ≤ j := by
        omega
      exact Finset.mem_Icc.mpr ⟨hmj, hjn⟩
    have hjk : j ≠ k := by
      omega
    have hkj1 : k < j + 1 := by
      omega
    -- Once the first random choice lies above `k`, the recursion starts
    -- strictly to the right of `k`.
    calc
      branchProbability j = absentMindedPassengerAvoidSeatProbability n k (j + 1) :=
        hbranch_tail hjmn hjk
      _ = 1 := by
        simpa [absentMindedPassengerAvoidSeatProbability] using
          absentMindedPassengerAvoidSeatOf_lt_start (m := j + 1) (k := k) (n := n) hkj1
  have hpconst : ∀ j ∈ choices, (p j).toReal = (1 : ℝ) / choices.card := by
    intro j hj
    simp [p, one_div, hj]
  have hprob :
      absentMindedPassengerAvoidSeatProbability n k m =
        (Finset.sum choices branchProbability) / (choices.card : ℝ) := by
    -- Convert the bind formula to a finite average over the first random choice.
    unfold absentMindedPassengerAvoidSeatProbability
    rw [absentMindedPassengerChosenSeatsFromRemaining_bind]
    change (((p.bind branch).toMeasure {chosen | k ∉ chosen}).toReal) =
      (Finset.sum choices branchProbability) / (choices.card : ℝ)
    rw [@PMF.toMeasure_bind_apply _ _ p branch {chosen | k ∉ chosen} _ hmeasureSet]
    rw [tsum_eq_sum fun j hj ↦ by
      have hpj : p j = 0 := by
        simpa [p] using PMF.uniformOfFinset_apply_of_notMem (s := choices) (hs := hchoicesNonempty)
          (a := j) hj
      simp [hpj]]
    rw [ENNReal.toReal_sum fun j hj ↦ ENNReal.mul_ne_top (p.apply_ne_top j) (by simp)]
    calc
      (Finset.sum choices fun j ↦ (p j * (branch j).toMeasure {chosen | k ∉ chosen}).toReal)
          = Finset.sum choices (fun j ↦ (p j).toReal * branchProbability j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [branchProbability, ENNReal.toReal_mul]
      _ = Finset.sum choices (fun j ↦ ((1 : ℝ) / choices.card) * branchProbability j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hpconst j hj]
      _ = ((1 : ℝ) / choices.card) * Finset.sum choices branchProbability := by
            rw [Finset.mul_sum]
      _ = (Finset.sum choices branchProbability) / (choices.card : ℝ) := by
            simp [div_eq_mul_inv, mul_comm]
  have hupper :
      Finset.sum (Finset.Icc k n) branchProbability = (n - k : ℝ) := by
    have hIoc :
        Finset.Ioc k n = Finset.Icc (k + 1) n := by
      ext j
      simp [Finset.mem_Ioc, Finset.mem_Icc]
    -- The upper interval contributes exactly one successful outcome for each available seat.
    rw [Finset.Icc_eq_cons_Ioc hkn, Finset.sum_cons, hIoc]
    have hbranch_eqk' : ((branch k).toMeasure {chosen | k ∉ chosen}).toReal = 0 := by
      simpa [branchProbability] using hbranch_eqk
    rw [hbranch_eqk', zero_add]
    calc
      Finset.sum
          (Finset.Icc (k + 1) n)
          (fun j ↦ ((branch j).toMeasure {chosen | k ∉ chosen}).toReal)
          = Finset.sum (Finset.Icc (k + 1) n) (fun _ ↦ (1 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simpa [branchProbability] using hbranch_upper hj
      _ = (n - k : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc]
            have hNat : n + 1 - (k + 1) = n - k := by
              omega
            rw [hNat]
            norm_num [Nat.cast_sub hkn]
  have hsum :
      Finset.sum choices branchProbability =
        (n - k + 1 : ℝ) +
          Finset.sum (Finset.Icc m (k - 1)) fun j ↦
            absentMindedPassengerAvoidSeatProbability n k (j + 1) := by
    have hlower :
        Finset.sum (Finset.Icc m (k - 1)) branchProbability =
          Finset.sum (Finset.Icc m (k - 1)) fun j ↦
            absentMindedPassengerAvoidSeatProbability n k (j + 1) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact hbranch_lower hj
    have hbranch_one' : ((branch 1).toMeasure {chosen | k ∉ chosen}).toReal = 1 := by
      simpa [branchProbability] using hbranch_one
    -- Split the first choice into the terminal seat `1`, the recursive lower
    -- interval, and the upper interval.
    change Finset.sum (insert 1 (Finset.Icc m n)) branchProbability =
      (n - k + 1 : ℝ) +
        Finset.sum (Finset.Icc m (k - 1)) fun j ↦
          absentMindedPassengerAvoidSeatProbability n k (j + 1)
    rw [Finset.sum_insert hnotMemOne]
    rw [hbranch_one']
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc m n) (fun j ↦ j < k)]
    rw [filter_Icc_lt_eq_Icc_pred hkpos hkn, filter_Icc_not_lt_eq_Icc hmk, hlower, hupper]
    have hconst : (1 : ℝ) + (n - k : ℝ) = (n - k + 1 : ℝ) := by
      ring
    linarith
  -- Substitute the explicit branch sum and the choice-set cardinality into the averaged formula.
  calc
    absentMindedPassengerAvoidSeatProbability n k m
        = (Finset.sum choices branchProbability) / (choices.card : ℝ) := hprob
    _ = ((n - k + 1 : ℝ) +
          Finset.sum (Finset.Icc m (k - 1)) fun j ↦
            absentMindedPassengerAvoidSeatProbability n k (j + 1)) / (choices.card : ℝ) := by
          rw [hsum]
    _ = ((n - k + 1 : ℝ) +
          Finset.sum (Finset.Icc m (k - 1)) fun j ↦
            absentMindedPassengerAvoidSeatProbability n k (j + 1)) / (n - m + 2 : ℝ) := by
          have hmn : m ≤ n := le_trans hmk hkn
          have hdenom : ((n - m + 2 : ℕ) : ℝ) = n - m + 2 := by
            norm_num [Nat.cast_add, Nat.cast_sub hmn]
          rw [hcard, hdenom]

/-- Helper for Exercise 8.1.2: at the diagonal start `m = k`, the recursion has no tail sum and
already yields the closed form. -/
private lemma absentMindedPassengerAvoidSeatProbabilityAtTarget {n k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    absentMindedPassengerAvoidSeatProbability n k k =
      (n - k + 1 : ℝ) / (n - k + 2 : ℝ) := by
  have hkpos : 0 < k := by
    omega
  have hempty : Finset.Icc k (k - 1) = ∅ := by
    exact Finset.Icc_eq_empty_of_lt (Nat.pred_lt hkpos.ne')
  -- At the diagonal start there is no recursive lower interval left, so the sum is empty.
  rw [absentMindedPassengerAvoidSeatProbabilityStepReal (n := n) (k := k) (m := k) hk
    (le_rfl : k ≤ k) hkn]
  rw [hempty, Finset.sum_empty]
  simp

/-- Helper for Exercise 8.1.2: moving the left endpoint from `m + 1` down to `m < k` does not
change the avoided-seat probability. -/
private lemma absentMindedPassengerAvoidSeatProbability_eq_succ {n k m : ℕ}
    (hm : 2 ≤ m) (hmk : m < k) (hkn : k ≤ n) :
    absentMindedPassengerAvoidSeatProbability n k m =
      absentMindedPassengerAvoidSeatProbability n k (m + 1) := by
  have hm1 : 2 ≤ m + 1 := by
    omega
  have hm1k : m + 1 ≤ k := by
    omega
  let tail : ℝ :=
    Finset.sum (Finset.Icc (m + 1) (k - 1)) fun j ↦
      absentMindedPassengerAvoidSeatProbability n k (j + 1)
  have hsplit :
      Finset.sum (Finset.Icc m (k - 1))
          (fun j ↦ absentMindedPassengerAvoidSeatProbability n k (j + 1)) =
        absentMindedPassengerAvoidSeatProbability n k (m + 1) + tail := by
    have hIoc :
        Finset.Ioc m (k - 1) = Finset.Icc (m + 1) (k - 1) := by
      ext j
      simp [Finset.mem_Ioc, Finset.mem_Icc]
    have hnotMemTail : m ∉ Finset.Icc (m + 1) (k - 1) := by
      simp
    have hinsert :
        insert m (Finset.Icc (m + 1) (k - 1)) = Finset.Icc m (k - 1) := by
      rw [← hIoc]
      exact Finset.Ioc_insert_left (Nat.le_pred_of_lt hmk)
    -- Split the lower interval at its left endpoint `m`.
    calc
      Finset.sum (Finset.Icc m (k - 1))
          (fun j ↦ absentMindedPassengerAvoidSeatProbability n k (j + 1))
          = Finset.sum (insert m (Finset.Icc (m + 1) (k - 1)))
              (fun j ↦ absentMindedPassengerAvoidSeatProbability n k (j + 1)) := by
                rw [hinsert]
      _ = absentMindedPassengerAvoidSeatProbability n k (m + 1) +
            Finset.sum (Finset.Icc (m + 1) (k - 1))
              (fun j ↦ absentMindedPassengerAvoidSeatProbability n k (j + 1)) := by
                rw [Finset.sum_insert hnotMemTail]
      _ = absentMindedPassengerAvoidSeatProbability n k (m + 1) + tail := by
            rfl
  have hstep :
      absentMindedPassengerAvoidSeatProbability n k m =
        (absentMindedPassengerAvoidSeatProbability n k (m + 1) +
          ((n - k + 1 : ℝ) + tail)) / (n - m + 2 : ℝ) := by
    simpa [tail, hsplit, add_assoc, add_left_comm, add_comm] using
      absentMindedPassengerAvoidSeatProbabilityStepReal (n := n) (k := k) (m := m)
        hm (le_of_lt hmk) hkn
  have hstepSucc :
      absentMindedPassengerAvoidSeatProbability n k (m + 1) =
        ((n - k + 1 : ℝ) + tail) / (n - m + 1 : ℝ) := by
    have hstepSuccRaw :=
      absentMindedPassengerAvoidSeatProbabilityStepReal (n := n) (k := k) (m := m + 1)
        hm1 hm1k hkn
    have hdenom : (↑n - (↑m + 1) + 2 : ℝ) = (↑n - ↑m + 1 : ℝ) := by
      ring
    calc
      absentMindedPassengerAvoidSeatProbability n k (m + 1)
          = ((n - k + 1 : ℝ) + tail) / (↑n - (↑m + 1) + 2 : ℝ) := by
              simpa using hstepSuccRaw
      _ = ((n - k + 1 : ℝ) + tail) / (n - m + 1 : ℝ) := by
            rw [hdenom]
  have htail :
      (n - k + 1 : ℝ) + tail =
        (n - m + 1 : ℝ) * absentMindedPassengerAvoidSeatProbability n k (m + 1) := by
    have hmn : (m : ℝ) ≤ n := by
      exact_mod_cast (le_trans (Nat.le_of_lt hmk) hkn)
    have hden : (n - m + 1 : ℝ) ≠ 0 := by
      have hdenPos : (0 : ℝ) < n - m + 1 := by
        nlinarith
      linarith
    field_simp [hden] at hstepSucc
    simpa [mul_comm] using hstepSucc.symm
  -- Substitute the successor recurrence back into the left-endpoint recurrence.
  calc
    absentMindedPassengerAvoidSeatProbability n k m
        = (absentMindedPassengerAvoidSeatProbability n k (m + 1) +
            (n - m + 1 : ℝ) * absentMindedPassengerAvoidSeatProbability n k (m + 1)) /
            (n - m + 2 : ℝ) := by
              rw [hstep, htail]
    _ = absentMindedPassengerAvoidSeatProbability n k (m + 1) := by
      have hmn : (m : ℝ) ≤ n := by
        exact_mod_cast (le_trans (Nat.le_of_lt hmk) hkn)
      have hden : (n - m + 2 : ℝ) ≠ 0 := by
        have hdenPos : (0 : ℝ) < n - m + 2 := by
          nlinarith
        linarith
      field_simp [hden]
      ring

/-- Helper for Exercise 8.1.2: every interval start `m` with `2 ≤ m ≤ k` has the same avoided-seat
probability as the diagonal start `m = k`, so the common value is the closed form
`(n - k + 1) / (n - k + 2)`. -/
private lemma absentMindedPassengerAvoidSeatProbabilityFromInterval {n k m : ℕ}
    (hm : 2 ≤ m) (hmk : m ≤ k) (hkn : k ≤ n) :
    absentMindedPassengerAvoidSeatProbability n k m =
      (n - k + 1 : ℝ) / (n - k + 2 : ℝ) := by
  have hk : 2 ≤ k := by
    exact le_trans hm hmk
  -- Route correction: propagate the diagonal closed form backward from `k` down to `m`.
  refine
    (Nat.decreasingInduction (n := k)
      (motive := fun r _ ↦ m ≤ r →
        absentMindedPassengerAvoidSeatProbability n k r =
          (n - k + 1 : ℝ) / (n - k + 2 : ℝ))
      ?_ ?_ hmk) (le_rfl : m ≤ m)
  · intro r hr ih hmr
    have hr2 : 2 ≤ r := by
      exact le_trans hm hmr
    have hmrSucc : m ≤ r + 1 := by
      exact le_trans hmr (Nat.le_succ r)
    -- One backward step preserves the avoided-seat probability before reaching the diagonal.
    calc
      absentMindedPassengerAvoidSeatProbability n k r
          = absentMindedPassengerAvoidSeatProbability n k (r + 1) :=
              absentMindedPassengerAvoidSeatProbability_eq_succ (n := n) (k := k) (m := r)
                hr2 hr hkn
      _ = (n - k + 1 : ℝ) / (n - k + 2 : ℝ) := ih hmrSucc
  · intro _
    exact absentMindedPassengerAvoidSeatProbabilityAtTarget (n := n) (k := k) hk hkn

-- Proof sketch: when `n = 1`, the last passenger is also the first passenger and therefore gets
-- the reserved seat with probability `1`; for `n ≥ 2`, the last passenger gets the reserved seat
-- exactly when the reduced chain hits seat `1` before seat `n`, and the two terminal seats are
-- symmetric.
/-- The first part of Exercise 8.1.2: in the absent-minded passenger problem with `n > 0` seats,
the last
passenger gets their reserved seat with probability `1` when `n = 1`, and with probability
`1 / 2` otherwise. -/
theorem absentMindedPassenger_last_passenger_reservedSeatProbability (n : ℕ) (hn : 0 < n) :
    absentMindedPassengerReservedSeatProbability n n =
      if n = 1 then (1 : ℝ) else (1 : ℝ) / 2 := by
  by_cases h1 : n = 1
  · subst h1
    -- For one seat, the last passenger is also the first passenger.
    have hpos : 0 < 1 := by
      omega
    simpa using absentMindedPassenger_first_passenger_reservedSeatProbability 1 hpos
  · have hn2 : 2 ≤ n := by
      omega
    have htwo : 2 ≤ 2 := by
      omega
    -- For `n ≥ 2`, rewrite the public event to the reduced avoided-seat event with `k = n`.
    simpa [absentMindedPassengerReservedSeatProbability, absentMindedPassengerGetsReservedSeat,
      absentMindedPassengerChosenSeats, absentMindedPassengerAvoidSeatProbability, h1] using
      absentMindedPassengerAvoidSeatProbabilityFromInterval (n := n) (k := n) (m := 2)
        htwo hn2 (le_rfl : n ≤ n)

-- Proof sketch: for `2 ≤ k ≤ n`, passenger `k` gets their own seat exactly when the reduced
-- random chain hits seat `1` before it hits seat `k`. Conditioning on the first time the chain
-- enters `{1, k, …, n}` yields the standard recursion and the closed form.
/-- Exercise 8.1.2 (2): For `1 ≤ k ≤ n`, the `k`th passenger gets their reserved seat with
probability `1 / n` when `k = 1`, and otherwise with probability
`(n - k + 1) / (n - k + 2)`. -/
theorem absentMindedPassenger_kth_passenger_reservedSeatProbability
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    absentMindedPassengerReservedSeatProbability n k =
      if k = 1 then (1 : ℝ) / n else (n - k + 1 : ℝ) / (n - k + 2 : ℝ) := by
  by_cases hk1 : k = 1
  · subst hk1
    have hn : 0 < n := by
      omega
    -- The first passenger branch is already available as a separate theorem.
    simpa using absentMindedPassenger_first_passenger_reservedSeatProbability n hn
  · have hk2 : 2 ≤ k := by
      omega
    have htwo : 2 ≤ 2 := by
      omega
    -- For `k ≥ 2`, passenger `k` keeps the reserved seat exactly when `k` is never recorded.
    simpa [absentMindedPassengerReservedSeatProbability, absentMindedPassengerGetsReservedSeat,
      absentMindedPassengerChosenSeats, absentMindedPassengerAvoidSeatProbability, hk1] using
      absentMindedPassengerAvoidSeatProbabilityFromInterval (n := n) (k := k) (m := 2)
        htwo hk2 hkn
