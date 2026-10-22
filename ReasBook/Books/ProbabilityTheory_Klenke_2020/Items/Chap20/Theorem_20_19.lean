/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Theorem_8_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {E : Type u}

section PathSpace

variable [AddCommMonoid E]

/-- The partial sum `S_n = X₀ + ⋯ + X_{n-1}` of a one-sided increment path `ω`. -/
def randomWalkPathPartialSum (ω : ℕ → E) (n : ℕ) : E :=
  ∑ i ∈ Finset.range n, ω i

/-- The event that the walk never returns to the origin after time `0`. -/
def neverReturnsToOriginEvent : Set (ℕ → E) :=
  {ω | ∀ n : ℕ, 0 < n → randomWalkPathPartialSum ω n ≠ 0}

-- Proof sketch: unfold `randomWalkPathPartialSum` at `0`; the finite sum over an empty range
-- vanishes.
/-- The zeroth partial sum of a path is the origin. -/
theorem randomWalkPathPartialSum_zero (ω : ℕ → E) :
    randomWalkPathPartialSum ω 0 = 0 := by
  simp [randomWalkPathPartialSum]

-- Proof sketch: unfold `neverReturnsToOriginEvent`; membership is exactly the stated no-return
-- condition on positive times.
/-- Membership in `neverReturnsToOriginEvent` is the no-return condition for all positive times. -/
theorem mem_neverReturnsToOriginEvent_iff (ω : ℕ → E) :
    ω ∈ neverReturnsToOriginEvent ↔
      ∀ n : ℕ, 0 < n → randomWalkPathPartialSum ω n ≠ 0 :=
  Iff.rfl

/-- The range count `R_n`, i.e. the number of distinct visited partial sums `S₀, …, S_n`. -/
noncomputable def randomWalkPathRangeCount (ω : ℕ → E) (n : ℕ) : ℕ :=
  (Set.range fun k : Fin (n + 1) ↦ randomWalkPathPartialSum ω k).ncard

-- Proof sketch: at time `0` the walk has visited only the initial position `0`, so the image of
-- `range 1` under the partial-sum map is the singleton `{0}`.
/-- The initial range count is `1`, corresponding to the starting point alone. -/
theorem randomWalkPathRangeCount_zero (ω : ℕ → E) :
    randomWalkPathRangeCount ω 0 = 1 := by
  simp [randomWalkPathRangeCount, randomWalkPathPartialSum]

omit [AddCommMonoid E] in
/-- Helper for Theorem 20.19: iterating the one-sided shift drops the first `k` coordinates of a
path. -/
lemma iterateTail_apply (ω : Stream' E) (k j : ℕ) :
    (Stream'.tail^[k]) ω j = ω (k + j) := by
  -- Proof comment: iterate the tail map once and keep the index shift explicit through the
  -- induction.
  induction k generalizing ω j with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ, Function.comp_apply]
      simpa [Stream'.tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (ω := Stream'.tail ω) (j := j)

/-- Helper for Theorem 20.19: splitting the path at time `k` decomposes the later partial sum
into the current partial sum plus the partial sum of the shifted path. -/
lemma randomWalkPathPartialSum_add_eq (ω : ℕ → E) (k j : ℕ) :
    randomWalkPathPartialSum ω (k + j) =
      randomWalkPathPartialSum ω k + randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j := by
  -- Proof comment: split the finite sum at `k`, then rewrite the tail coordinates as shifted
  -- original coordinates.
  simp [randomWalkPathPartialSum, Finset.sum_range_add, iterateTail_apply]

end PathSpace

section Measurability

variable [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Each finite random-walk partial sum on path space is measurable. -/
theorem measurable_randomWalkPathPartialSum (n : ℕ) :
    Measurable (fun ω : ℕ → E ↦ randomWalkPathPartialSum ω n) := by
  simpa [randomWalkPathPartialSum] using
    Finset.measurable_sum (Finset.range n) fun i _ ↦ measurable_pi_apply i

variable [MeasurableSingletonClass E]

/-- The no-return event is measurable on path space once addition and singleton fibers are
measurable on the state space. -/
theorem measurableSet_neverReturnsToOriginEvent :
    MeasurableSet (neverReturnsToOriginEvent : Set (ℕ → E)) := by
  have h_eq :
      (neverReturnsToOriginEvent : Set (ℕ → E)) =
        ⋂ n : {n : ℕ // 0 < n},
          (fun ω : ℕ → E ↦ randomWalkPathPartialSum ω n.1) ⁻¹' ({(0 : E)}ᶜ) := by
    ext ω
    simp [neverReturnsToOriginEvent]
  rw [h_eq]
  refine MeasurableSet.iInter fun n ↦ ?_
  exact measurable_randomWalkPathPartialSum n.1
    (measurableSet_singleton (0 : E)).compl

end Measurability

section CancellativeMeasurability

variable [AddCancelCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
variable [MeasurableSingletonClass E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

local notation "ℐ" => MeasurableSpace.invariants Stream'.tail

/-- Helper for Theorem 20.19: the event that the first `m` positive partial sums avoid the
origin. -/
def avoidsOriginPrefixEvent (m : ℕ) : Set (ℕ → E) :=
  {ω | ∀ n : ℕ, 0 < n → n ≤ m → randomWalkPathPartialSum ω n ≠ 0}

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: membership in `avoidsOriginPrefixEvent m` is exactly the finite
no-return condition up to time `m`. -/
lemma mem_avoidsOriginPrefixEvent_iff (m : ℕ) (ω : ℕ → E) :
    ω ∈ avoidsOriginPrefixEvent m ↔
      ∀ n : ℕ, 0 < n → n ≤ m → randomWalkPathPartialSum ω n ≠ 0 :=
  Iff.rfl

/-- Helper for Theorem 20.19: the finite-horizon no-return event is measurable. -/
lemma measurableSet_avoidsOriginPrefixEvent (m : ℕ) :
    MeasurableSet (avoidsOriginPrefixEvent (E := E) m : Set (ℕ → E)) := by
  -- Proof comment: this is a finite-level analogue of `measurableSet_neverReturnsToOriginEvent`,
  -- now intersecting only the positive times `n ≤ m`.
  have h_eq :
      (avoidsOriginPrefixEvent (E := E) m : Set (ℕ → E)) =
        ⋂ n : {n : ℕ // 0 < n ∧ n ≤ m},
          (fun ω : ℕ → E ↦ randomWalkPathPartialSum ω n.1) ⁻¹' ({(0 : E)}ᶜ) := by
    ext ω
    simp [avoidsOriginPrefixEvent]
  rw [h_eq]
  refine MeasurableSet.iInter fun n ↦ ?_
  exact measurable_randomWalkPathPartialSum n.1
    (measurableSet_singleton (0 : E)).compl

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: after shifting by `k`, the infinite no-return event says that the
original walk never revisits the position reached at time `k`. -/
lemma mem_neverReturnsToOriginEvent_iterateTail_iff (ω : ℕ → E) (k : ℕ) :
    (Stream'.tail^[k]) ω ∈ neverReturnsToOriginEvent ↔
      ∀ j : ℕ, 0 < j →
        randomWalkPathPartialSum ω (k + j) ≠ randomWalkPathPartialSum ω k := by
  constructor
  · intro h j hj hEq
    -- Proof comment: if the walk revisited `S_k` at time `k + j`, then the shifted partial sum at
    -- time `j` would vanish, contradicting no return for the shifted path.
    have hShift : randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j ≠ 0 :=
      (mem_neverReturnsToOriginEvent_iff ((Stream'.tail^[k]) ω)).mp h j hj
    have hEq' :
        randomWalkPathPartialSum ω k +
            randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j =
          randomWalkPathPartialSum ω k := by
      simpa [randomWalkPathPartialSum_add_eq] using hEq
    have hEq'' :
        randomWalkPathPartialSum ω k +
            randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j =
          randomWalkPathPartialSum ω k + 0 := by
      simpa using hEq'
    exact hShift (add_left_cancel hEq'')
  · intro h
    -- Proof comment: a zero shifted partial sum forces equality `S_{k+j} = S_k` after
    -- recombining the split sum.
    exact
      (mem_neverReturnsToOriginEvent_iff ((Stream'.tail^[k]) ω)).2 <| by
        intro j hj hZero
        apply h j hj
        rw [randomWalkPathPartialSum_add_eq, hZero, add_zero]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: after shifting by `k`, the finite no-return event up to time `m`
matches the original walk avoiding a revisit to `S_k` during the next `m` steps. -/
lemma mem_avoidsOriginPrefixEvent_iterateTail_iff (ω : ℕ → E) (k m : ℕ) :
    (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m ↔
      ∀ j : ℕ, 0 < j → j ≤ m →
        randomWalkPathPartialSum ω (k + j) ≠ randomWalkPathPartialSum ω k := by
  constructor
  · intro h j hj hjm hEq
    -- Proof comment: the same cancellation argument as the infinite-horizon case works with the
    -- extra side condition `j ≤ m`.
    have hShift : randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j ≠ 0 :=
      (mem_avoidsOriginPrefixEvent_iff (E := E) m ((Stream'.tail^[k]) ω)).mp h j hj hjm
    have hEq' :
        randomWalkPathPartialSum ω k +
            randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j =
          randomWalkPathPartialSum ω k := by
      simpa [randomWalkPathPartialSum_add_eq] using hEq
    have hEq'' :
        randomWalkPathPartialSum ω k +
            randomWalkPathPartialSum ((Stream'.tail^[k]) ω) j =
          randomWalkPathPartialSum ω k + 0 := by
      simpa using hEq'
    exact hShift (add_left_cancel hEq'')
  · intro h
    -- Proof comment: a zero shifted partial sum yields the forbidden revisit in the original
    -- walk within the prescribed prefix window.
    exact
      (mem_avoidsOriginPrefixEvent_iff (E := E) m ((Stream'.tail^[k]) ω)).2 <| by
        intro j hj hjm hZero
        apply h j hj hjm
        rw [randomWalkPathPartialSum_add_eq, hZero, add_zero]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: the finite-horizon indicators converge pointwise to the indicator of
`neverReturnsToOriginEvent`. -/
lemma indicator_avoidsOriginPrefixEvent_tendsto_indicator_neverReturns (ω : ℕ → E) :
    Tendsto
      (fun m : ℕ ↦ Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ)) ω)
      atTop
      (nhds (Set.indicator neverReturnsToOriginEvent (fun _ ↦ (1 : ℝ)) ω)) := by
  by_cases hω : ω ∈ neverReturnsToOriginEvent
  · -- Proof comment: if the walk never returns, then every finite-horizon indicator is already
    -- constantly `1`.
    have hPrefix : ∀ m : ℕ, ω ∈ avoidsOriginPrefixEvent (E := E) m := by
      intro m
      rw [mem_avoidsOriginPrefixEvent_iff]
      intro n hn _
      exact (mem_neverReturnsToOriginEvent_iff ω).mp hω n hn
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall fun m ↦ by simp [hω, hPrefix m]
  · -- Proof comment: once a concrete return time is found, all larger finite-horizon indicators
    -- are constantly `0`.
    rw [mem_neverReturnsToOriginEvent_iff] at hω
    push Not at hω
    rcases hω with ⟨n, hn, hZero⟩
    have hNever : ω ∉ neverReturnsToOriginEvent := by
      rw [mem_neverReturnsToOriginEvent_iff]
      intro hMem
      exact hMem n hn hZero
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    have hNotMem : ω ∉ avoidsOriginPrefixEvent (E := E) m := by
      rw [mem_avoidsOriginPrefixEvent_iff]
      intro hMem
      exact hMem n hn hm hZero
    simp [hNotMem, hNever]

/-- Helper for Theorem 20.19: conditional probabilities of the finite-horizon no-return events
converge almost surely to the conditional probability of `neverReturnsToOriginEvent`. -/
lemma ae_tendsto_condExp_indicator_avoidsOriginPrefixEvent
    (P : Measure (ℕ → E)) [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun m : ℕ ↦
          (P[Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ)) | ℐ]) ω)
        atTop
        (nhds ((P[Set.indicator neverReturnsToOriginEvent (fun _ ↦ (1 : ℝ)) | ℐ]) ω)) := by
  -- Proof comment: dominated convergence applies to the decreasing indicator family because every
  -- term is bounded by the integrable constant `1`.
  have hMeas :
      ∀ m : ℕ,
        AEStronglyMeasurable
          (Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ))) P := by
    intro m
    exact
      (measurable_const.indicator
        (measurableSet_avoidsOriginPrefixEvent (E := E) m)).aestronglyMeasurable
  have hDom : Integrable (fun _ : ℕ → E ↦ (1 : ℝ)) P := integrable_const 1
  have hBound :
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        |Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ)) ω| ≤ 1 := by
    intro m
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ avoidsOriginPrefixEvent (E := E) m
      · simp [Set.indicator_of_mem, hω]
      · simp [Set.indicator_of_notMem, hω]
  have hPointwise :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun m : ℕ ↦
            Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ)) ω)
          atTop
          (nhds (Set.indicator neverReturnsToOriginEvent (fun _ ↦ (1 : ℝ)) ω)) :=
    Filter.Eventually.of_forall
      (indicator_avoidsOriginPrefixEvent_tendsto_indicator_neverReturns (E := E))
  exact
    tendsto_ae_condExp_of_dominated_convergence
      (P := P) (ℱ := ℐ) (hℱ := MeasurableSpace.invariants_le Stream'.tail)
      hMeas hDom hBound hPointwise

omit [AddCancelCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
  [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: the Birkhoff average of an indicator is the corresponding
cardinality ratio of visit times. -/
lemma birkhoffAverage_indicator_eq_ncardRatio (s : Set (ℕ → E)) (n : ℕ) (ω : ℕ → E) :
    birkhoffAverage ℝ Stream'.tail (Set.indicator s (fun _ ↦ (1 : ℝ))) n ω =
      ({k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ s}.ncard : ℝ) / n := by
  classical
  -- Proof comment: rewrite the Birkhoff sum as a finite sum of `0`/`1` terms and identify it
  -- with the filtered-cardinality of the times whose shifted path lies in `s`.
  let times : Set ℕ := {k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ s}
  let timesFin : times.Finite := (Set.finite_lt_nat n).subset fun _ hk ↦ hk.1
  have htimes :
      timesFin.toFinset =
        (Finset.range n).filter (fun k ↦ (Stream'.tail^[k]) ω ∈ s) := by
    ext k
    simp [times]
  have hsum :
      ∑ k ∈ Finset.range n, Set.indicator s (fun _ ↦ (1 : ℝ)) ((Stream'.tail^[k]) ω) =
        (times.ncard : ℝ) := by
    -- Proof comment: first identify the `0`/`1` sum with the filtered finset cardinality, then
    -- transport that cardinality to the finite set `times`.
    calc
      ∑ k ∈ Finset.range n, Set.indicator s (fun _ ↦ (1 : ℝ)) ((Stream'.tail^[k]) ω) =
          (((Finset.range n).filter fun k ↦ (Stream'.tail^[k]) ω ∈ s).card : ℝ) := by
            simpa only [Set.indicator_apply] using
              (Finset.sum_boole (fun k ↦ (Stream'.tail^[k]) ω ∈ s) (Finset.range n) :
                (∑ x ∈ Finset.range n,
                    if (Stream'.tail^[x]) ω ∈ s then (1 : ℝ) else 0) =
                  (((Finset.range n).filter fun k ↦ (Stream'.tail^[k]) ω ∈ s).card : ℝ))
      _ = (times.ncard : ℝ) := by
            rw [Set.ncard_eq_toFinset_card times timesFin, htimes]
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  calc
    (n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range n, Set.indicator s (fun _ ↦ (1 : ℝ)) ((Stream'.tail^[k]) ω) =
        (n : ℝ)⁻¹ * (times.ncard : ℝ) := by rw [hsum]
    _ = (times.ncard : ℝ) / n := by rw [div_eq_mul_inv, mul_comm]
    _ = ({k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ s}.ncard : ℝ) / n := by simp [times]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: the times whose shifted path never returns to the origin inject into
the visited partial sums up to time `n`. -/
lemma neverReturnsTimes_ncard_le_rangeCount (ω : ℕ → E) (n : ℕ) :
    {k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ neverReturnsToOriginEvent}.ncard ≤
      randomWalkPathRangeCount ω n := by
  let s : Set ℕ := {k | k < n ∧ (Stream'.tail^[k]) ω ∈ neverReturnsToOriginEvent}
  have hsRange : s.ncard ≤ randomWalkPathRangeCount ω n := by
    -- Proof comment: send each no-return time `k < n` to the visited value `S_k`; the no-return
    -- property makes this map injective on the chosen times.
    refine Set.ncard_le_ncard_of_injOn
      (s := s)
      (t := Set.range fun k : Fin (n + 1) ↦ randomWalkPathPartialSum ω k)
      (f := fun k ↦ randomWalkPathPartialSum ω k)
      ?_ ?_
    · intro k hk
      exact ⟨⟨k, Nat.lt_succ_of_lt hk.1⟩, rfl⟩
    · intro i hi j hj hij
      by_cases hEq : i = j
      · exact hEq
      · rcases lt_or_gt_of_ne hEq with hijlt | hjilt
        · have hiNever :=
            (mem_neverReturnsToOriginEvent_iterateTail_iff (E := E) ω i).mp hi.2
          have hstep : 0 < j - i := by
            omega
          have hcontr := hiNever (j - i) hstep
          have hEq' :
              randomWalkPathPartialSum ω (i + (j - i)) = randomWalkPathPartialSum ω i := by
            simpa [Nat.add_sub_of_le hijlt.le] using hij.symm
          exact (hcontr hEq').elim
        · have hjNever :=
            (mem_neverReturnsToOriginEvent_iterateTail_iff (E := E) ω j).mp hj.2
          have hstep : 0 < i - j := by
            omega
          have hcontr := hjNever (i - j) hstep
          have hEq' :
              randomWalkPathPartialSum ω (j + (i - j)) = randomWalkPathPartialSum ω j := by
            simpa [Nat.add_sub_of_le hjilt.le] using hij
          exact (hcontr hEq').elim
  simpa [s] using hsRange

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: every visited value up to time `n` is represented either by a last
occurrence in the suffix interval `[n - m, n]` or by a time whose next `m` steps avoid a revisit. -/
lemma rangeCount_le_suffixLength_add_avoidsPrefixTimes_ncard (ω : ℕ → E) {m n : ℕ}
    (hmn : m ≤ n) :
    randomWalkPathRangeCount ω n ≤
      (m + 1) +
        {k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard := by
  classical
  let visited : Set E := Set.range fun k : Fin (n + 1) ↦ randomWalkPathPartialSum ω k
  let suffix : Set ℕ := Set.Icc (n - m) n
  let good : Set ℕ := {k | k < n ∧ (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}
  let lastOccurrence : E → ℕ :=
    fun x ↦ Nat.findGreatest (fun k ↦ randomWalkPathPartialSum ω k = x) n
  let suffixFinite : suffix.Finite := (Set.finite_le_nat n).subset fun _ hk ↦ hk.2
  let goodFinite : good.Finite := (Set.finite_lt_nat n).subset fun _ hk ↦ hk.1
  have hsuffixNat :
      suffix.ncard = n + 1 - (n - m) := by
    change (Set.Icc (n - m) n).ncard = n + 1 - (n - m)
    exact Set.ncard_Icc_nat (n - m) n
  have hsuffixCard : suffix.ncard = m + 1 := by
    omega
  have hcover : visited.ncard ≤ (suffix ∪ good).ncard := by
    -- Proof comment: choose for each visited value its last occurrence up to time `n`; distinct
    -- visited values have distinct last occurrences.
    refine Set.ncard_le_ncard_of_injOn
      (s := visited)
      (t := suffix ∪ good)
      (f := lastOccurrence)
      ?_
      ?_
      (suffixFinite.union goodFinite)
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      let k : ℕ := lastOccurrence (randomWalkPathPartialSum ω i)
      have hk_le : k ≤ n := Nat.findGreatest_le _
      have hk_eq :
          randomWalkPathPartialSum ω k = randomWalkPathPartialSum ω i := by
        exact
          Nat.findGreatest_spec
            (P := fun l ↦ randomWalkPathPartialSum ω l = randomWalkPathPartialSum ω i)
            (Nat.lt_succ_iff.mp i.2) rfl
      by_cases hsuf : n - m ≤ k
      · exact Or.inl ⟨hsuf, hk_le⟩
      · have hk_lt_sub : k < n - m := lt_of_not_ge hsuf
        have hk_lt_n : k < n := by
          omega
        have hgoodMem : (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m := by
          rw [mem_avoidsOriginPrefixEvent_iterateTail_iff]
          intro j hj hjm hEq
          have hk_j_le_n : k + j ≤ n := by
            omega
          have hk_lt_kj : k < k + j := by
            omega
          have hnot :
              ¬ randomWalkPathPartialSum ω (k + j) = randomWalkPathPartialSum ω i := by
            exact
              Nat.findGreatest_is_greatest
                (P := fun l ↦ randomWalkPathPartialSum ω l = randomWalkPathPartialSum ω i)
                hk_lt_kj hk_j_le_n
          have hEq' :
              randomWalkPathPartialSum ω (k + j) = randomWalkPathPartialSum ω i := by
            simpa [hk_eq] using hEq
          exact (hnot hEq').elim
        exact Or.inr ⟨hk_lt_n, hgoodMem⟩
    · intro x hx y hy hxy
      rcases hx with ⟨i, hi⟩
      rcases hy with ⟨j, hj⟩
      have hxSpec :
          randomWalkPathPartialSum ω (lastOccurrence x) = x := by
        exact
          Nat.findGreatest_spec
            (P := fun k ↦ randomWalkPathPartialSum ω k = x)
            (Nat.lt_succ_iff.mp i.2) (by simpa using hi)
      have hySpec :
          randomWalkPathPartialSum ω (lastOccurrence y) = y := by
        exact
          Nat.findGreatest_spec
            (P := fun k ↦ randomWalkPathPartialSum ω k = y)
            (Nat.lt_succ_iff.mp j.2) (by simpa using hj)
      calc
        x = randomWalkPathPartialSum ω (lastOccurrence x) := hxSpec.symm
        _ = randomWalkPathPartialSum ω (lastOccurrence y) := by rw [hxy]
        _ = y := hySpec
  calc
    randomWalkPathRangeCount ω n = visited.ncard := rfl
    _ ≤ (suffix ∪ good).ncard := hcover
    _ ≤ suffix.ncard + good.ncard := Set.ncard_union_le _ _
    _ =
        (m + 1) +
          {k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard := by
      simp [good, hsuffixCard]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: the lower deterministic range-count bound becomes a lower bound by
the Birkhoff average of the no-return indicator. -/
lemma birkhoffAverage_indicator_neverReturns_le_rangeCountRatio (ω : ℕ → E) (n : ℕ) :
    birkhoffAverage ℝ Stream'.tail
        (Set.indicator neverReturnsToOriginEvent (fun _ ↦ (1 : ℝ))) n ω ≤
      (randomWalkPathRangeCount ω n : ℝ) / n := by
  -- Proof comment: rewrite the average as a counting ratio, then divide the deterministic
  -- counting inequality by `n`.
  rw [birkhoffAverage_indicator_eq_ncardRatio (E := E) (s := neverReturnsToOriginEvent)]
  have hcount :
      ({k : ℕ | k < n ∧ (Stream'.tail^[k]) ω ∈ neverReturnsToOriginEvent}.ncard : ℝ) ≤
        randomWalkPathRangeCount ω n := by
    exact_mod_cast neverReturnsTimes_ncard_le_rangeCount (E := E) ω n
  exact div_le_div_of_nonneg_right hcount (by positivity)

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E] in
/-- Helper for Theorem 20.19: the upper deterministic range-count bound becomes an upper bound by
the Birkhoff average of the finite-horizon no-return indicator plus the suffix error term. -/
lemma rangeCountRatio_le_succPrefixError_add_birkhoffAverage_indicator_avoidsOriginPrefix
    (ω : ℕ → E) {m n : ℕ} (hmn : m ≤ n) :
    (randomWalkPathRangeCount ω n : ℝ) / n ≤
      ((m + 1 : ℝ) / n) +
        birkhoffAverage ℝ Stream'.tail
          (Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ))) n ω := by
  -- Proof comment: cast the deterministic upper counting inequality to `ℝ`, divide by `n`, and
  -- rewrite the second counting ratio as a Birkhoff average.
  have hcount :
      (randomWalkPathRangeCount ω n : ℝ) ≤
        (m + 1 : ℝ) +
          ({k : ℕ | k < n ∧
              (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard : ℝ) := by
    exact_mod_cast rangeCount_le_suffixLength_add_avoidsPrefixTimes_ncard (E := E) ω hmn
  have hdiv :
      (randomWalkPathRangeCount ω n : ℝ) / n ≤
        ((m + 1 : ℝ) +
            ({k : ℕ | k < n ∧
                (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard : ℝ)) / n :=
    div_le_div_of_nonneg_right hcount (by positivity)
  rw [birkhoffAverage_indicator_eq_ncardRatio (E := E) (s := avoidsOriginPrefixEvent (E := E) m)]
  calc
    (randomWalkPathRangeCount ω n : ℝ) / n ≤
        ((m + 1 : ℝ) +
            ({k : ℕ | k < n ∧
                (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard : ℝ)) / n :=
      hdiv
    _ =
        ((m + 1 : ℝ) / n) +
          (({k : ℕ | k < n ∧
              (Stream'.tail^[k]) ω ∈ avoidsOriginPrefixEvent (E := E) m}.ncard : ℝ) / n) := by
      ring

-- Proof sketch: use the owner abstraction `IsStationaryProcess Function.eval P` for the canonical
-- coordinate process on path space; via the Chapter 20 bridge this is the shift-invariance of the
-- path law under `Stream'.tail`. In a cancellative additive state space, the event
-- `neverReturnsToOriginEvent` on the shifted increment path is exactly the event that the original
-- walk never revisits its current position after the shift time. Apply Birkhoff's ergodic theorem
-- to the indicators of this event and its finite-horizon approximations. The lower and upper
-- bounds on `R_n / n` coming from last-visit indicators then squeeze the limit to the conditional
-- probability `P⟦A | 𝒯⟧` of the no-return event `A` given the invariant `σ`-algebra
-- `𝒯 = MeasurableSpace.invariants Stream'.tail` of the shift.
/-- Theorem 20.19: for the canonical coordinate process on path space under a stationary path
law with values in a cancellative commutative additive state space, the normalized range count
converges almost surely to the conditional probability of the no-return event given the invariant
`σ`-algebra `𝒯 = MeasurableSpace.invariants Stream'.tail` of the shift. Cancellativity is the
structural hypothesis that identifies the no-return event of the shifted increment path with the
event that the original walk never revisits its current position after the shift time. The
measurability hypotheses on `E` ensure that this no-return event is a genuine measurable event, so
the right-hand side is canonically `P⟦neverReturnsToOriginEvent | ℐ⟧`. Example 20.12 supplies only
the bridge `ℐ ≤ tailRandomVariableMeasurableSpace Function.eval`, so the source-facing theorem must
stay at the invariant owner rather than the tail view. -/
theorem randomWalkPathRangeCount_tendsto_ae_condProb_invariants
    (P : Measure (ℕ → E)) [IsProbabilityMeasure P]
    (hstationary : IsStationaryProcess Function.eval P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (randomWalkPathRangeCount ω n : ℝ) / n) atTop
        (nhds ((P⟦neverReturnsToOriginEvent | ℐ⟧) ω)) := by
  let g : (ℕ → E) → ℝ := Set.indicator neverReturnsToOriginEvent (fun _ ↦ (1 : ℝ))
  let gm : ℕ → (ℕ → E) → ℝ :=
    fun m ↦ Set.indicator (avoidsOriginPrefixEvent (E := E) m) (fun _ ↦ (1 : ℝ))
  have hτ : MeasurePreserving Stream'.tail P P :=
    (canonical_process_stationary_iff_measurePreserving_tail (E := E) P).mp hstationary
  have hgInt : Integrable g P := by
    -- Proof comment: the indicator of a measurable event is integrable because it is bounded by
    -- the integrable constant `1`.
    simpa [g] using
      (integrable_const (1 : ℝ)).indicator measurableSet_neverReturnsToOriginEvent
  have hgmInt : ∀ m : ℕ, Integrable (gm m) P := by
    intro m
    -- Proof comment: the same bounded-indicator argument applies to every finite-horizon event.
    simpa [gm] using
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_avoidsOriginPrefixEvent (E := E) m)
  have hBirkhoffA :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ Stream'.tail g n ω) atTop
          (nhds ((P[g | ℐ]) ω)) :=
    birkhoffAverage_tendsto_ae_condExp_invariants (P := P) (τ := Stream'.tail) (f := g) hτ hgInt
  have hBirkhoffAm :
      ∀ m : ℕ,
        ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ Stream'.tail (gm m) n ω) atTop
            (nhds ((P[gm m | ℐ]) ω)) := by
    intro m
    exact
      birkhoffAverage_tendsto_ae_condExp_invariants
        (P := P) (τ := Stream'.tail) (f := gm m) hτ (hgmInt m)
  have hCond :
      ∀ᵐ ω ∂P,
        Tendsto (fun m : ℕ ↦ (P[gm m | ℐ]) ω) atTop (nhds ((P[g | ℐ]) ω)) := by
    simpa [g, gm] using
      ae_tendsto_condExp_indicator_avoidsOriginPrefixEvent (E := E) (P := P)
  have hBirkhoffAmAll :
      ∀ᵐ ω ∂P,
        ∀ m : ℕ,
          Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ Stream'.tail (gm m) n ω) atTop
            (nhds ((P[gm m | ℐ]) ω)) := by
    exact ae_all_iff.2 hBirkhoffAm
  filter_upwards [hBirkhoffA, hBirkhoffAmAll, hCond] with ω hωA hωAm hωCond
  let c : ℝ := (P[g | ℐ]) ω
  have hωA' : Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ Stream'.tail g n ω) atTop (nhds c) := by
    simpa [c] using hωA
  have hωCond' : Tendsto (fun m : ℕ ↦ (P[gm m | ℐ]) ω) atTop (nhds c) := by
    simpa [c] using hωCond
  -- Proof comment: after fixing `ω` in the full-measure set where all needed convergence facts
  -- hold, choose a finite horizon `m` and squeeze the range-count ratio between the lower and
  -- upper Birkhoff averages with a vanishing prefix error.
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε εpos
  obtain ⟨δ, hδpos, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ + δ + δ < ε := by
    refine ⟨ε / 4, by positivity, ?_⟩
    linarith
  obtain ⟨m, hmCond⟩ := (NormedAddCommGroup.tendsto_atTop.mp hωCond') δ hδpos
  have hδltε : δ < ε := by
    linarith
  have hmCondClose : ‖(P[gm m | ℐ]) ω - c‖ < δ := hmCond m le_rfl
  have hmCondUpper : (P[gm m | ℐ]) ω < c + δ := by
    have hAbs : |(P[gm m | ℐ]) ω - c| < δ := by
      simpa [Real.norm_eq_abs] using hmCondClose
    have hBounds := abs_lt.mp hAbs
    linarith
  obtain ⟨NA, hNA⟩ := (NormedAddCommGroup.tendsto_atTop.mp hωA') δ hδpos
  obtain ⟨NAm, hNAm⟩ := (NormedAddCommGroup.tendsto_atTop.mp (hωAm m)) δ hδpos
  have hPrefix :
      Tendsto (fun n : ℕ ↦ ((m + 1 : ℝ) / n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (m + 1 : ℝ)) atTop (nhds (m + 1 : ℝ)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      hconst.mul tendsto_one_div_atTop_nhds_zero_nat
  obtain ⟨NPrefix, hPrefixNear⟩ := (NormedAddCommGroup.tendsto_atTop.mp hPrefix) δ hδpos
  refine ⟨max (max NA NAm) (max NPrefix m), ?_⟩
  intro n hn
  have hNAle : NA ≤ n := by
    exact
      le_trans
        (le_max_left NA NAm)
        (le_trans (le_max_left (max NA NAm) (max NPrefix m)) hn)
  have hNAmle : NAm ≤ n := by
    exact
      le_trans
        (le_max_right NA NAm)
        (le_trans (le_max_left (max NA NAm) (max NPrefix m)) hn)
  have hNPrefixle : NPrefix ≤ n := by
    exact
      le_trans
        (le_max_left NPrefix m)
        (le_trans (le_max_right (max NA NAm) (max NPrefix m)) hn)
  have hmle : m ≤ n := by
    exact
      le_trans
        (le_max_right NPrefix m)
        (le_trans (le_max_right (max NA NAm) (max NPrefix m)) hn)
  let a : ℝ := (randomWalkPathRangeCount ω n : ℝ) / n
  have hLowerClose : ‖birkhoffAverage ℝ Stream'.tail g n ω - c‖ < δ := hNA n hNAle
  have hLowerBase : c - δ < birkhoffAverage ℝ Stream'.tail g n ω := by
    have hAbs : |birkhoffAverage ℝ Stream'.tail g n ω - c| < δ := by
      simpa [Real.norm_eq_abs] using hLowerClose
    have hBounds := abs_lt.mp hAbs
    linarith
  have hLowerDet : birkhoffAverage ℝ Stream'.tail g n ω ≤ a := by
    simpa [g, a] using
      birkhoffAverage_indicator_neverReturns_le_rangeCountRatio (E := E) (ω := ω) (n := n)
  have hUpperClose :
      ‖birkhoffAverage ℝ Stream'.tail (gm m) n ω - (P[gm m | ℐ]) ω‖ < δ := hNAm n hNAmle
  have hUpperBirkhoff :
      birkhoffAverage ℝ Stream'.tail (gm m) n ω < (P[gm m | ℐ]) ω + δ := by
    have hAbs : |birkhoffAverage ℝ Stream'.tail (gm m) n ω - (P[gm m | ℐ]) ω| < δ := by
      simpa [Real.norm_eq_abs] using hUpperClose
    have hBounds := abs_lt.mp hAbs
    linarith
  have hPrefixClose : ‖((m + 1 : ℝ) / n) - 0‖ < δ := hPrefixNear n hNPrefixle
  have hPrefixLt : ((m + 1 : ℝ) / n) < δ := by
    have hAbs : |(m + 1 : ℝ)| / |(n : ℝ)| < δ := by
      simpa [Real.norm_eq_abs] using hPrefixClose
    simpa [abs_of_nonneg (show 0 ≤ (m + 1 : ℝ) by positivity),
      abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)] using hAbs
  have hUpperDet :
      a ≤ ((m + 1 : ℝ) / n) + birkhoffAverage ℝ Stream'.tail (gm m) n ω := by
    simpa [gm, a] using
      rangeCountRatio_le_succPrefixError_add_birkhoffAverage_indicator_avoidsOriginPrefix
        (E := E) (ω := ω) (m := m) (n := n) hmle
  have hLower : c - ε < a := by
    linarith [hLowerBase, hLowerDet, hδltε]
  have hUpper : a < c + ε := by
    linarith [hUpperDet, hPrefixLt, hUpperBirkhoff, hmCondUpper, hδε]
  have hLeft : -ε < a - c := by
    linarith
  have hRight : a - c < ε := by
    linarith
  have hAbs : |a - c| < ε := by
    rw [abs_lt]
    exact ⟨hLeft, hRight⟩
  simpa [a, Real.norm_eq_abs] using hAbs

end CancellativeMeasurability
