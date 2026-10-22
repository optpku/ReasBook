/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Exercise 5.4.1: the local first absolute hitting layer at index `k`. -/
def absFirstHitEventLocal (X : ℕ → Ω → ℝ) (t : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j ∈ Finset.Icc 1 (k - 1), |partialSum X j ω| < t) ∧ t ≤ |partialSum X k ω|}

/-- Helper for Exercise 5.4.1: the excursion event where some earlier partial sum reaches `t`
while the pivot sum at `j` stays below `a`. -/
def prePivotExcursionEvent (X : ℕ → Ω → ℝ) (j : ℕ) (t a : ℝ) : Set Ω :=
  {ω | (∃ k ∈ Finset.Icc 1 (j - 1), t ≤ |partialSum X k ω|) ∧ |partialSum X j ω| < a}

/-- Helper for Exercise 5.4.1: the excursion event where the pivot sum at `j` stays below `a`
but some later partial sum reaches `t`. -/
def postPivotExcursionEvent (X : ℕ → Ω → ℝ) (j n : ℕ) (t a : ℝ) : Set Ω :=
  {ω | |partialSum X j ω| < a ∧ ∃ k ∈ Finset.Icc (j + 1) n, t ≤ |partialSum X k ω|}

/-- Helper for Exercise 5.4.1: two different local absolute first-hit layers are disjoint. -/
lemma absFirstHitEventLocal_disjoint (X : ℕ → Ω → ℝ) {n k l : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hl : l ∈ Finset.Icc 1 n) (hkl : k ≠ l) (t : ℝ) :
    Disjoint (absFirstHitEventLocal X t k) (absFirstHitEventLocal X t l) := by
  -- The later first-hit condition forces the earlier absolute partial sum to stay below `t`.
  rw [Set.disjoint_iff]
  intro ω hω
  rcases hω with ⟨hkω, hlω⟩
  rcases hkω with ⟨hkprev, hkge⟩
  rcases hlω with ⟨hlprev, hlge⟩
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · have hkIcc := Finset.mem_Icc.mp hk
    have hk_mem : k ∈ Finset.Icc 1 (l - 1) := by
      exact Finset.mem_Icc.mpr ⟨hkIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hkge (hlprev k hk_mem)
  · have hlIcc := Finset.mem_Icc.mp hl
    have hl_mem : l ∈ Finset.Icc 1 (k - 1) := by
      exact Finset.mem_Icc.mpr ⟨hlIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hlge (hkprev l hl_mem)

/-- Helper for Exercise 5.4.1: every absolute hit belongs to its least local first-hit layer. -/
lemma exists_absFirstHitEventLocal (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω)
    (hω : ω ∈ absHitEvent X n t) :
    ∃ k ∈ Finset.Icc 1 n, ω ∈ absFirstHitEventLocal X t k := by
  let p : ℕ → Prop := fun k ↦ k ∈ Finset.Icc 1 n ∧ t ≤ |partialSum X k ω|
  have hp : ∃ k, p k := hω
  refine ⟨Nat.find hp, (Nat.find_spec hp).1, ?_⟩
  refine ⟨?_, (Nat.find_spec hp).2⟩
  -- Minimality of `Nat.find hp` gives the strict inequality for all earlier indices.
  intro j hj
  by_contra hjge
  have hjIcc := Finset.mem_Icc.mp hj
  have hfindIcc := Finset.mem_Icc.mp (Nat.find_spec hp).1
  have hj_mem : j ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ⟨hjIcc.1, le_of_lt ?_⟩
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
      _ ≤ n := hfindIcc.2
  have hj_lt_find : j < Nat.find hp := by
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
  exact (Nat.find_min hp hj_lt_find) ⟨hj_mem, not_lt.mp hjge⟩

/-- Helper for Exercise 5.4.1: for `n > 0`, one can choose a pivot index in `Finset.Icc 1 n`
attaining the finite supremum of the partial-sum tail probabilities. -/
lemma existsPivotAbsTail_eq_sup (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hn : 0 < n) (t : ℝ) :
    ∃ j ∈ Finset.Icc 1 n,
      (Finset.Icc 1 n).sup (fun k ↦ P {ω | t ≤ |partialSum X k ω|}) =
        P {ω | t ≤ |partialSum X j ω|} := by
  have hnonempty : (Finset.Icc 1 n).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ?_⟩
    exact ⟨le_rfl, Nat.succ_le_of_lt hn⟩
  -- A finite supremum is attained on a nonempty finite set.
  simpa using
    Finset.exists_mem_eq_sup (Finset.Icc 1 n) hnonempty
      (fun k ↦ P {ω | t ≤ |partialSum X k ω|})

/-- Helper for Exercise 5.4.1: a pivot attaining the finite supremum controls every other tail
probability on `Finset.Icc 1 n`. -/
lemma tailProb_le_pivotTail_of_eq_sup (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n j : ℕ) {t : ℝ} (hj_sup :
      (Finset.Icc 1 n).sup (fun k ↦ P {ω | t ≤ |partialSum X k ω|}) =
        P {ω | t ≤ |partialSum X j ω|}) :
    ∀ k ∈ Finset.Icc 1 n, P {ω | t ≤ |partialSum X k ω|} ≤ P {ω | t ≤ |partialSum X j ω|} := by
  -- Rewrite through the chosen supremum value and compare with `Finset.le_sup`.
  intro k hk
  rw [← hj_sup]
  let tailProb : ℕ → ENNReal := fun l ↦ P {ω | t ≤ |partialSum X l ω|}
  change tailProb k ≤ (Finset.Icc 1 n).sup tailProb
  exact Finset.le_sup hk

/-- Helper for Exercise 5.4.1: on a local first-hit layer, a terminal sum below `t / 3` forces the
corresponding terminal increment to carry at least `2 * (t / 3)` of absolute size. -/
lemma absFirstHit_terminalSmall_subset_tailIncrement
    (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) {t : ℝ} :
    absFirstHitEventLocal X t k ∩ {ω | |partialSum X n ω| < t / 3} ⊆
      absFirstHitEventLocal X t k ∩
        {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
  intro ω hω
  rcases hω with ⟨hfirst, hterminal_small⟩
  refine ⟨hfirst, ?_⟩
  rcases hfirst with ⟨_, hk_hit⟩
  by_contra htail
  have hterminal_small' : |partialSum X n ω| < t / 3 := hterminal_small
  have htail_small : |partialSum X k ω - partialSum X n ω| < 2 * (t / 3) := by
    simpa [abs_sub_comm] using lt_of_not_ge htail
  -- Proof comment: if both the terminal sum and the tail increment were small, then the hit sum
  -- `S_k = (S_k - S_n) + S_n` would also stay below `t`, contradicting the layer condition.
  have htriangle :
      |partialSum X k ω| ≤
        |partialSum X k ω - partialSum X n ω| + |partialSum X n ω| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_add_le (partialSum X k ω - partialSum X n ω) (partialSum X n ω))
  have hsum_small :
      |partialSum X k ω - partialSum X n ω| + |partialSum X n ω| < t := by
    nlinarith
  exact not_lt_of_ge hk_hit (lt_of_le_of_lt htriangle hsum_small)

/-- Helper for Exercise 5.4.1: every prefix partial sum up to `n` is measurable once the first
`n` coordinates are measurable. -/
private lemma measurable_partialSum (X : ℕ → Ω → ℝ) {n k : ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i)) (hk : k ≤ n) :
    Measurable (partialSum X k) := by
  -- Proof comment: expand the finite sum and use measurability of each prefix coordinate.
  unfold partialSum
  refine Finset.measurable_sum (Finset.range k) ?_
  intro i hi
  exact hX_meas ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩

/-- Helper for Exercise 5.4.1: each local first-hit layer is measurable. -/
private lemma measurableSet_absFirstHitEventLocal (X : ℕ → Ω → ℝ) {n k : ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i)) (hk : k ≤ n) (t : ℝ) :
    MeasurableSet (absFirstHitEventLocal X t k) := by
  -- Proof comment: the layer is a finite intersection of measurable absolute-value thresholds.
  have hEq :
      absFirstHitEventLocal X t k =
        (⋂ j ∈ Finset.Icc 1 (k - 1), {ω : Ω | |partialSum X j ω| < t}) ∩
          {ω | t ≤ |partialSum X k ω|} := by
    ext ω
    simp [absFirstHitEventLocal]
  have hprev :
      MeasurableSet (⋂ j ∈ Finset.Icc 1 (k - 1), {ω : Ω | |partialSum X j ω| < t}) := by
    refine Finset.measurableSet_biInter (Finset.Icc 1 (k - 1)) fun j hj ↦ ?_
    have hj_le_k : j ≤ k := le_trans (Finset.mem_Icc.mp hj).2 (Nat.sub_le _ _)
    have hj_le_n : j ≤ n := le_trans hj_le_k hk
    exact measurableSet_lt
      (measurable_abs.comp (measurable_partialSum X hX_meas hj_le_n))
      measurable_const
  have hlast : MeasurableSet {ω : Ω | t ≤ |partialSum X k ω|} := by
    exact measurableSet_le measurable_const
      (measurable_abs.comp (measurable_partialSum X hX_meas hk))
  rw [hEq]
  exact hprev.inter hlast

/-- Helper for Exercise 5.4.1: the tuple-level prefix sum up to `j` inside a `k`-tuple. -/
private def prefixVec (k : ℕ) (z : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin k, if (i : ℕ) < j then z i else 0

/-- Helper for Exercise 5.4.1: evaluating the tuple-level prefix sum on the first `k` coordinates
recovers the original partial sum up to any `j ≤ k`. -/
private lemma prefixVec_eq_partialSum (X : ℕ → Ω → ℝ) {j k : ℕ} (hj : j ≤ k) (ω : Ω) :
    prefixVec k (fun i : Fin k ↦ X i ω) j = partialSum X j ω := by
  -- Proof comment: rewrite the tuple sum as a range sum and split off the zero tail.
  rw [prefixVec]
  calc
    ∑ i : Fin k, (if (i : ℕ) < j then X i ω else 0)
        = ∑ i ∈ Finset.range k, (if i < j then X i ω else 0) := by
            simpa using
              (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if i < j then X i ω else 0) k)
    _ = ∑ i ∈ Finset.range (j + (k - j)), (if i < j then X i ω else 0) := by
          simp [Nat.add_sub_of_le hj]
    _ = ∑ i ∈ Finset.range j, X i ω +
          ∑ i ∈ Finset.range (k - j), (if j + i < j then X (j + i) ω else 0) := by
          rw [Finset.sum_range_add]
          refine congrArg (fun x : ℝ ↦ x + _) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Finset.mem_range.mp hi]
    _ = ∑ i ∈ Finset.range j, X i ω := by
          simp
    _ = partialSum X j ω := by
          rw [partialSum]

/-- Helper for Exercise 5.4.1: tuple-level prefix sums are measurable on finite product space. -/
private lemma measurable_prefixVec (k j : ℕ) :
    Measurable (fun z : Fin k → ℝ ↦ prefixVec k z j) := by
  -- Proof comment: the tuple prefix sum is a finite measurable coordinate sum.
  unfold prefixVec
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  by_cases hij : (i : ℕ) < j
  · simpa [hij] using measurable_pi_apply i
  · simp [hij]

/-- Helper for Exercise 5.4.1: the tuple-space local first-hit condition for the absolute
threshold `t`. -/
private def absFirstHitPrefixSet (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  (⋂ j ∈ Finset.Icc 1 (k - 1), {z | |prefixVec k z j| < t}) ∩ {z | t ≤ |prefixVec k z k|}

/-- Helper for Exercise 5.4.1: the tuple-space local first-hit set is measurable. -/
private lemma measurableSet_absFirstHitPrefixSet (k : ℕ) (t : ℝ) :
    MeasurableSet (absFirstHitPrefixSet k t) := by
  -- Proof comment: the tuple first-hit set is a finite intersection of measurable threshold sets.
  unfold absFirstHitPrefixSet
  have hprev :
      MeasurableSet (⋂ j ∈ Finset.Icc 1 (k - 1), {z : Fin k → ℝ | |prefixVec k z j| < t}) := by
    refine Finset.measurableSet_biInter (Finset.Icc 1 (k - 1)) fun j hj ↦ ?_
    exact measurableSet_lt (measurable_abs.comp (measurable_prefixVec k j)) measurable_const
  have hlast : MeasurableSet {z : Fin k → ℝ | t ≤ |prefixVec k z k|} := by
    exact measurableSet_le measurable_const (measurable_abs.comp (measurable_prefixVec k k))
  exact hprev.inter hlast

/-- Helper for Exercise 5.4.1: summing the coordinates of a finite future block. -/
private def futureVecSum (m : ℕ) (z : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, z i

/-- Helper for Exercise 5.4.1: summing the future `n - k` tuple coordinates gives the tail
increment `Sₙ - Sₖ`. -/
private lemma futureVecSum_eq_tail_increment (X : ℕ → Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    futureVecSum (n - k) (fun i : Fin (n - k) ↦ X (k + i) ω) =
      partialSum X n ω - partialSum X k ω := by
  -- Proof comment: reindex the future tuple sum as the `Ico k n` block from the tail identity.
  rw [futureVecSum]
  calc
    ∑ i : Fin (n - k), X (k + i) ω
        = ∑ i ∈ Finset.range (n - k), X (k + i) ω := by
            simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X (k + i) ω) (n - k))
    _ = ∑ i ∈ Finset.Ico k n, X i ω := by
          rw [Finset.sum_Ico_eq_sum_range]
    _ = partialSum X n ω - partialSum X k ω := by
          symm
          exact partialSum_sub_eq_sum_Ico X hk ω

/-- Helper for Exercise 5.4.1: the future block sum is measurable on finite product space. -/
private lemma measurable_futureVecSum (m : ℕ) :
    Measurable (fun z : Fin m → ℝ ↦ futureVecSum m z) := by
  -- Proof comment: the future block sum is a finite measurable coordinate sum.
  unfold futureVecSum
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Exercise 5.4.1: the tuple-space large future-increment event at level
`2 * (t / 3)`. -/
private def futureLargeIncrementSet (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  {z | 2 * (t / 3) ≤ |futureVecSum m z|}

/-- Helper for Exercise 5.4.1: the tuple-space large future-increment event is measurable. -/
private lemma measurableSet_futureLargeIncrementSet (m : ℕ) (t : ℝ) :
    MeasurableSet (futureLargeIncrementSet m t) := by
  -- Proof comment: this is the measurable threshold preimage of the future tuple sum.
  unfold futureLargeIncrementSet
  exact measurableSet_le measurable_const
    (measurable_abs.comp (measurable_futureVecSum m))

/-- Helper for Exercise 5.4.1: evaluating the prefix tuple identifies the local first-hit event
with the corresponding tuple-space preimage. -/
private lemma preimage_absFirstHitPrefixSet_eq_absFirstHitEventLocal
    (X : ℕ → Ω → ℝ) (k : ℕ) (t : ℝ) :
    (fun ω ↦ fun i : Fin k ↦ X i ω) ⁻¹' absFirstHitPrefixSet k t = absFirstHitEventLocal X t k := by
  -- Proof comment: rewrite the tuple prefix sums back to the original partial sums coordinatewise.
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hzj := Set.mem_iInter.1 (Set.mem_iInter.1 hω.1 j) hj
      simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hzj
    · simpa [absFirstHitPrefixSet, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hω.2
  · intro hω
    rcases hω with ⟨hprev, hkge⟩
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun j ↦ Set.mem_iInter.2 fun hj ↦ ?_
      have hj' := Finset.mem_Icc.mp hj
      simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hprev j hj
    · simpa [absFirstHitPrefixSet, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hkge

/-- Helper for Exercise 5.4.1: the future tuple identifies the tail-increment event with the
corresponding tuple-space preimage. -/
private lemma preimage_futureLargeIncrementSet_eq_tailIncrementEvent
    (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) (t : ℝ) :
    (fun ω ↦ fun i : Fin (n - k) ↦ X (k + i) ω) ⁻¹' futureLargeIncrementSet (n - k) t =
      {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
  -- Proof comment: the future tuple sum is exactly the terminal tail increment `S_n - S_k`.
  ext ω
  simp [futureLargeIncrementSet, futureVecSum_eq_tail_increment X hk ω]

/-- Helper for Exercise 5.4.1: the filtered past indices `{i < k}` inside `Fin n`. -/
private def pastIdx (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n ↦ (i : ℕ) < k

/-- Helper for Exercise 5.4.1: the filtered future indices `{i ≥ k}` inside `Fin n`. -/
private def futureIdx (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n ↦ k ≤ (i : ℕ)

/-- Helper for Exercise 5.4.1: view `i : Fin k` as the corresponding element of `Fin n`. -/
private def pastIndex {n k : ℕ} (hk : k ≤ n) (i : Fin k) : Fin n :=
  ⟨i, lt_of_lt_of_le i.2 hk⟩

/-- Helper for Exercise 5.4.1: the embedded prefix index belongs to the filtered past block. -/
private lemma pastIndex_mem_pastIdx {n k : ℕ} (hk : k ≤ n) (i : Fin k) :
    pastIndex hk i ∈ pastIdx n k := by
  -- Proof comment: every `Fin k` index is strictly smaller than `k` by construction.
  simp [pastIdx, pastIndex, i.2]

/-- Helper for Exercise 5.4.1: `Fin k` reindexed as the subtype of the filtered past block. -/
private def pastIndexEmbedding {n k : ℕ} (hk : k ≤ n) (i : Fin k) : pastIdx n k :=
  ⟨pastIndex hk i, pastIndex_mem_pastIdx hk i⟩

/-- Helper for Exercise 5.4.1: the shifted future index `k + i` still lies in `Fin n`. -/
private lemma futureIndex_lt {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) :
    k + (i : ℕ) < n := by
  -- Proof comment: `i < n - k` is exactly the remaining room after the shift by `k`.
  omega

/-- Helper for Exercise 5.4.1: view `i : Fin (n - k)` as the corresponding future index in
`Fin n`. -/
private def futureIndex {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  ⟨k + i, futureIndex_lt hk i⟩

/-- Helper for Exercise 5.4.1: the shifted future index belongs to the filtered future block. -/
private lemma futureIndex_mem_futureIdx {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) :
    futureIndex hk i ∈ futureIdx n k := by
  -- Proof comment: the shifted index is in the future block because it is at least `k`.
  simp [futureIdx, futureIndex]

/-- Helper for Exercise 5.4.1: `Fin (n - k)` reindexed as the subtype of the filtered future
block. -/
private def futureIndexEmbedding {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : futureIdx n k :=
  ⟨futureIndex hk i, futureIndex_mem_futureIdx hk i⟩

/-- Helper for Exercise 5.4.1: reindex a filtered past tuple to the raw prefix tuple. -/
private def pastToPrefix {n k : ℕ} (hk : k ≤ n) : (pastIdx n k → ℝ) → Fin k → ℝ :=
  fun z i ↦ z (pastIndexEmbedding hk i)

/-- Helper for Exercise 5.4.1: reindex a filtered future tuple to the raw suffix tuple. -/
private def futureToSuffix {n k : ℕ} (hk : k ≤ n) :
    (futureIdx n k → ℝ) → Fin (n - k) → ℝ :=
  fun z i ↦ z (futureIndexEmbedding hk i)

/-- Helper for Exercise 5.4.1: the past reindexing map is measurable. -/
private lemma measurable_pastToPrefix {n k : ℕ} (hk : k ≤ n) :
    Measurable (pastToPrefix hk) := by
  -- Proof comment: every output coordinate is just evaluation at the matching filtered past
  -- index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastToPrefix] using
    (measurable_pi_apply (pastIndexEmbedding hk i) :
      Measurable fun z : pastIdx n k → ℝ ↦ z (pastIndexEmbedding hk i))

/-- Helper for Exercise 5.4.1: the future reindexing map is measurable. -/
private lemma measurable_futureToSuffix {n k : ℕ} (hk : k ≤ n) :
    Measurable (futureToSuffix hk) := by
  -- Proof comment: every output coordinate is evaluation at the corresponding shifted future
  -- index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [futureToSuffix] using
    (measurable_pi_apply (futureIndexEmbedding hk i) :
      Measurable fun z : futureIdx n k → ℝ ↦ z (futureIndexEmbedding hk i))

/-- Helper for Exercise 5.4.1: reindexing the filtered past tuple recovers the raw prefix tuple. -/
private lemma pastToPrefix_comp_pastCoord (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) (ω : Ω) :
    pastToPrefix hk (fun i : pastIdx n k ↦ X i ω) = fun i : Fin k ↦ X i ω := by
  -- Proof comment: the filtered past embedding has the same underlying natural index as `i`.
  funext i
  rfl

/-- Helper for Exercise 5.4.1: reindexing the filtered future tuple recovers the raw suffix
tuple. -/
private lemma futureToSuffix_comp_futureCoord (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) (ω : Ω) :
    futureToSuffix hk (fun i : futureIdx n k ↦ X i ω) =
      fun i : Fin (n - k) ↦ X (k + i) ω := by
  -- Proof comment: the future embedding records exactly the shifted index `k + i`.
  funext i
  rfl

/-- Helper for Exercise 5.4.1: the filtered past and future coordinate blocks are independent. -/
private lemma filteredPastFutureIndep (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n k : ℕ) (hk : k ≤ n) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P) :
    IndepFun (fun ω ↦ fun i : pastIdx n k ↦ X i ω)
      (fun ω ↦ fun i : futureIdx n k ↦ X i ω) P := by
  have hdisj : Disjoint (pastIdx n k) (futureIdx n k) := by
    -- Proof comment: no index can be simultaneously `< k` and `≥ k`.
    refine Finset.disjoint_left.mpr ?_
    intro i hiPast hiFuture
    simp only [pastIdx, futureIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hiPast hiFuture
    exact hiPast.not_ge hiFuture
  -- Route correction: keep the independence statement on the filtered blocks, where
  -- `iIndepFun.indepFun_finset` applies directly, instead of rebuilding it on raw tuples first.
  simpa using hX_indep.indepFun_finset (pastIdx n k) (futureIdx n k) hdisj hX_meas

/-- Helper for Exercise 5.4.1: on each first-hit layer, the layer event is independent of the
future tail-increment event. -/
private lemma absFirstHitEventLocal_inter_tailIncrement_measure_eq_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX_meas : ∀ i : Fin n, Measurable (X i)) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    {t : ℝ} {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    P (absFirstHitEventLocal X t k ∩ {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|}) =
      P (absFirstHitEventLocal X t k) *
        P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
  let pastCoord : Ω → pastIdx n k → ℝ := fun ω i ↦ X i ω
  let futureCoord : Ω → futureIdx n k → ℝ := fun ω i ↦ X i ω
  let prefixSet : Set (pastIdx n k → ℝ) := pastToPrefix (Finset.mem_Icc.mp hk).2 ⁻¹'
    absFirstHitPrefixSet k t
  let futureSet : Set (futureIdx n k → ℝ) := futureToSuffix (Finset.mem_Icc.mp hk).2 ⁻¹'
    futureLargeIncrementSet (n - k) t
  have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hIndep : IndepFun pastCoord futureCoord P :=
    filteredPastFutureIndep P X n k hk_le hX_meas hX_indep
  have hPrefixSet : MeasurableSet prefixSet := by
    -- Proof comment: pull back the measurable tuple-space first-hit set along the past reindexing.
    exact (measurableSet_absFirstHitPrefixSet k t).preimage (measurable_pastToPrefix hk_le)
  have hFutureSet : MeasurableSet futureSet := by
    -- Proof comment: pull back the measurable tuple-space future-increment set along the future
    -- reindexing.
    exact (measurableSet_futureLargeIncrementSet (n - k) t).preimage
      (measurable_futureToSuffix hk_le)
  have hPastEq :
      pastToPrefix hk_le ∘ pastCoord = fun ω ↦ fun i : Fin k ↦ X i ω := by
    -- Proof comment: the filtered past coordinates already enumerate the raw prefix tuple.
    funext ω
    exact pastToPrefix_comp_pastCoord X hk_le ω
  have hFutureEq :
      futureToSuffix hk_le ∘ futureCoord =
        fun ω ↦ fun i : Fin (n - k) ↦ X (k + i) ω := by
    -- Proof comment: the filtered future coordinates already enumerate the shifted suffix tuple.
    funext ω
    exact futureToSuffix_comp_futureCoord X hk_le ω
  have hPastPreimage :
      pastCoord ⁻¹' prefixSet = absFirstHitEventLocal X t k := by
    -- Proof comment: rewrite the past preimage through the concrete prefix tuple map.
    change (pastToPrefix hk_le ∘ pastCoord) ⁻¹' absFirstHitPrefixSet k t =
      absFirstHitEventLocal X t k
    rw [hPastEq]
    exact preimage_absFirstHitPrefixSet_eq_absFirstHitEventLocal X k t
  have hFuturePreimage :
      futureCoord ⁻¹' futureSet =
        {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
    -- Proof comment: rewrite the future preimage through the concrete shifted suffix tuple map.
    change (futureToSuffix hk_le ∘ futureCoord) ⁻¹' futureLargeIncrementSet (n - k) t =
      {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|}
    rw [hFutureEq]
    exact preimage_futureLargeIncrementSet_eq_tailIncrementEvent X hk_le t
  -- Proof comment: once both events are identified as measurable preimages, independence gives the
  -- product formula directly.
  calc
    P (absFirstHitEventLocal X t k ∩ {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|}) =
        P (pastCoord ⁻¹' prefixSet ∩ futureCoord ⁻¹' futureSet) := by
          rw [hPastPreimage, hFuturePreimage]
    _ = P (pastCoord ⁻¹' prefixSet) * P (futureCoord ⁻¹' futureSet) := by
          exact hIndep.measure_inter_preimage_eq_mul prefixSet futureSet hPrefixSet hFutureSet
    _ = P (absFirstHitEventLocal X t k) *
          P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
          rw [hPastPreimage, hFuturePreimage]

/-- Helper for Exercise 5.4.1: intersecting `absHitEvent X n t` with a measurable set splits into
the finite sum over its disjoint local first-hit layers. -/
private lemma measure_absHitEvent_inter_eq_sum_layers (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_meas : ∀ i : Fin n, Measurable (X i)) {t : ℝ} {B : Set Ω}
    (hB : MeasurableSet B) :
    P (absHitEvent X n t ∩ B) = ∑ k ∈ Finset.Icc 1 n, P (absFirstHitEventLocal X t k ∩ B) := by
  have hUnion :
      absHitEvent X n t ∩ B = ⋃ k ∈ Finset.Icc 1 n, absFirstHitEventLocal X t k ∩ B := by
    -- Proof comment: each hit belongs to its least first-hit layer, and every layer point is a
    -- hit by definition.
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hhit, hBω⟩
      rcases exists_absFirstHitEventLocal X n t ω hhit with ⟨k, hk, hkω⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ⟨hkω, hBω⟩⟩⟩
    · intro hω
      simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω
      rcases hω with ⟨k, hk, hkω, hBω⟩
      exact ⟨⟨k, hk, hkω.2⟩, hBω⟩
  have hDisjoint :
      Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun k ↦ absFirstHitEventLocal X t k ∩ B := by
    -- Proof comment: distinct first-hit layers are already disjoint, and intersecting with the
    -- same measurable set preserves disjointness.
    intro k hk l hl hkl
    refine Set.disjoint_left.2 ?_
    intro ω hωk hωl
    exact Set.disjoint_left.mp (absFirstHitEventLocal_disjoint X hk hl hkl t) hωk.1 hωl.1
  have hMeas :
      ∀ k ∈ Finset.Icc 1 n, MeasurableSet (absFirstHitEventLocal X t k ∩ B) := by
    -- Proof comment: each layer is measurable, hence so is its intersection with `B`.
    intro k hk
    exact (measurableSet_absFirstHitEventLocal X hX_meas (Finset.mem_Icc.mp hk).2 t).inter hB
  -- Proof comment: after normalizing to a finite disjoint union, the measure is the sum of the
  -- layer measures.
  rw [hUnion, measure_biUnion_finset hDisjoint hMeas]

/-- Helper for Exercise 5.4.1: the terminal increment tail at level `2 * (t / 3)` is controlled by
the two `t / 3` tails of the prefix and terminal partial sums. -/
lemma tailIncrement_tailProb_le_twoPartialTails (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) {t : ℝ} :
    P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} ≤
      P {ω | t / 3 ≤ |partialSum X k ω|} + P {ω | t / 3 ≤ |partialSum X n ω|} := by
  have hsubset :
      {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} ⊆
        {ω | t / 3 ≤ |partialSum X k ω|} ∪ {ω | t / 3 ≤ |partialSum X n ω|} := by
    intro ω hω
    by_cases hk_small : |partialSum X k ω| < t / 3
    · right
      by_contra hn_small
      have hterminal_small : |partialSum X n ω| < t / 3 := lt_of_not_ge hn_small
      -- Proof comment: if both endpoint partial sums were below `t / 3`, then the increment
      -- between them would stay below `2 * (t / 3)` by the triangle inequality.
      have htriangle :
          |partialSum X n ω - partialSum X k ω| ≤
            |partialSum X n ω| + |partialSum X k ω| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (abs_add_le (partialSum X n ω) (-partialSum X k ω))
      have htail_small : |partialSum X n ω - partialSum X k ω| < 2 * (t / 3) := by
        nlinarith
      exact not_lt_of_ge hω htail_small
    · left
      exact not_lt.mp hk_small
  calc
    P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} ≤
        P ({ω | t / 3 ≤ |partialSum X k ω|} ∪ {ω | t / 3 ≤ |partialSum X n ω|}) := P.mono hsubset
    _ ≤ P {ω | t / 3 ≤ |partialSum X k ω|} + P {ω | t / 3 ≤ |partialSum X n ω|} :=
      measure_union_le _ _

/-- Helper for Exercise 5.4.1: the only remaining load-bearing step is to factor each local
absolute first-hit layer from the future increment `Sₙ - Sₖ`, then sum the disjoint layers. -/
lemma absHit_terminalSmall_le_twoTailSup_mul_hit (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P) (hn : 0 < n) {t : ℝ} :
    P (absHitEvent X n t ∩ {ω | |partialSum X n ω| < t / 3}) ≤
      (2 * (Finset.Icc 1 n).sup (fun k ↦ P {ω | t / 3 ≤ |partialSum X k ω|})) *
        P (absHitEvent X n t) := by
  let terminalSmall : Set Ω := {ω | |partialSum X n ω| < t / 3}
  let tailSup : ENNReal := (Finset.Icc 1 n).sup fun k ↦ P {ω | t / 3 ≤ |partialSum X k ω|}
  have hTerminalSmall :
      MeasurableSet terminalSmall := by
    -- Proof comment: the terminal-small event is a measurable absolute-value threshold.
    exact measurableSet_lt
      (measurable_abs.comp (measurable_partialSum X hX_meas le_rfl))
      measurable_const
  have hHitDecomp :
      P (absHitEvent X n t) = ∑ k ∈ Finset.Icc 1 n, P (absFirstHitEventLocal X t k) := by
    -- Proof comment: apply the layer partition with `B = Set.univ`.
    simpa using
      (measure_absHitEvent_inter_eq_sum_layers P X n hX_meas (t := t) (B := Set.univ)
        MeasurableSet.univ)
  have hLayerBound :
      ∀ k ∈ Finset.Icc 1 n,
        P (absFirstHitEventLocal X t k ∩ terminalSmall) ≤
          (2 * tailSup) * P (absFirstHitEventLocal X t k) := by
    intro k hk
    have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hkTail :
        P {ω | t / 3 ≤ |partialSum X k ω|} ≤ tailSup := by
      -- Proof comment: every layer index contributes at most the common finite supremum.
      let tailProb : ℕ → ENNReal := fun j ↦ P {ω | t / 3 ≤ |partialSum X j ω|}
      change tailProb k ≤ (Finset.Icc 1 n).sup tailProb
      exact Finset.le_sup hk
    have hnTail :
        P {ω | t / 3 ≤ |partialSum X n ω|} ≤ tailSup := by
      -- Proof comment: the terminal index `n` also lies in `Finset.Icc 1 n` because `n > 0`.
      let tailProb : ℕ → ENNReal := fun j ↦ P {ω | t / 3 ≤ |partialSum X j ω|}
      change tailProb n ≤ (Finset.Icc 1 n).sup tailProb
      exact Finset.le_sup (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hn, le_rfl⟩)
    have hTailBound :
        P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} ≤ 2 * tailSup := by
      -- Proof comment: control the tail increment by the two endpoint tails and then compare both
      -- endpoint tails with the same supremum.
      calc
        P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} ≤
            P {ω | t / 3 ≤ |partialSum X k ω|} + P {ω | t / 3 ≤ |partialSum X n ω|} := by
              exact tailIncrement_tailProb_le_twoPartialTails P X hk_le
        _ ≤ tailSup + tailSup := add_le_add hkTail hnTail
        _ = 2 * tailSup := by
              simp [two_mul]
    -- Proof comment: enlarge the layer by the tail-increment event, factor by independence, and
    -- use the uniform `2 * tailSup` bound on the tail factor.
    calc
      P (absFirstHitEventLocal X t k ∩ terminalSmall) ≤
          P (absFirstHitEventLocal X t k ∩
            {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|}) := by
            exact P.mono (absFirstHit_terminalSmall_subset_tailIncrement X hk_le)
      _ = P (absFirstHitEventLocal X t k) *
            P {ω | 2 * (t / 3) ≤ |partialSum X n ω - partialSum X k ω|} := by
            exact absFirstHitEventLocal_inter_tailIncrement_measure_eq_mul P X n hX_meas hX_indep hk
      _ ≤ P (absFirstHitEventLocal X t k) * (2 * tailSup) := by
            gcongr
      _ = (2 * tailSup) * P (absFirstHitEventLocal X t k) := by
            rw [mul_comm]
  have hSumBound :
      ∑ k ∈ Finset.Icc 1 n, P (absFirstHitEventLocal X t k ∩ terminalSmall) ≤
        ∑ k ∈ Finset.Icc 1 n, (2 * tailSup) * P (absFirstHitEventLocal X t k) := by
    -- Proof comment: sum the uniform layerwise bounds over the finite partition.
    exact Finset.sum_le_sum fun k hk ↦ hLayerBound k hk
  -- Proof comment: substitute the partition of the hit event and factor out the common
  -- coefficient `2 * tailSup`.
  calc
    P (absHitEvent X n t ∩ terminalSmall) =
        ∑ k ∈ Finset.Icc 1 n, P (absFirstHitEventLocal X t k ∩ terminalSmall) := by
          simpa [terminalSmall] using
            (measure_absHitEvent_inter_eq_sum_layers P X n hX_meas (t := t) hTerminalSmall)
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (2 * tailSup) * P (absFirstHitEventLocal X t k) := hSumBound
    _ = (2 * tailSup) * ∑ k ∈ Finset.Icc 1 n, P (absFirstHitEventLocal X t k) := by
          rw [← Finset.mul_sum]
    _ = (2 * tailSup) * P (absHitEvent X n t) := by
          rw [← hHitDecomp]
    _ = (2 * (Finset.Icc 1 n).sup (fun k ↦ P {ω | t / 3 ≤ |partialSum X k ω|})) *
          P (absHitEvent X n t) := by
          rfl

-- Proof sketch: decompose according to the first index where `|S_k|` crosses `t`, compare this
-- event with the large-deviation events for the terminal differences `S_n - S_k`, use
-- independence, and optimize the union bound to obtain the factor `3`.
/-- Exercise 5.4.1: for independent real random variables `X₁, …, Xₙ` with partial sums
`S_k = X₁ + ⋯ + X_k`, Etemadi's inequality bounds the probability that one of the absolute partial
sums reaches `t` by three times the largest tail probability at level `t / 3`. This is the
canonical `0`-based Lean version using the chapter's existing `partialSum`; for the textbook
sequence `X₁, X₂, …`, apply it to `fun k ↦ X (k + 1)`. -/
theorem etemadi_inequality_abs_partial_sums (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P) {t : ℝ} (ht : 0 < t) :
    P (absHitEvent X n t) ≤
      3 *
        (Finset.Icc 1 n).sup fun k ↦
          P {ω | t / 3 ≤ |partialSum X k ω|} := by
  by_cases h0 : n = 0
  · -- The empty interval `Finset.Icc 1 0` gives the trivial base case.
    subst h0
    simp [absHitEvent]
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    let terminalTail : Set Ω := {ω | t / 3 ≤ |partialSum X n ω|}
    let hitAndTerminalSmall : Set Ω :=
      absHitEvent X n t ∩ {ω | |partialSum X n ω| < t / 3}
    let tailSup : ENNReal :=
      (Finset.Icc 1 n).sup fun k ↦ P {ω | t / 3 ≤ |partialSum X k ω|}
    have hsubset :
        absHitEvent X n t ⊆ terminalTail ∪ hitAndTerminalSmall := by
      intro ω hω
      by_cases hterminal : t / 3 ≤ |partialSum X n ω|
      · exact Or.inl hterminal
      · exact Or.inr ⟨hω, lt_of_not_ge hterminal⟩
    have hmeasure :
        P (absHitEvent X n t) ≤ P terminalTail + P hitAndTerminalSmall := by
      calc
        P (absHitEvent X n t) ≤ P (terminalTail ∪ hitAndTerminalSmall) := P.mono hsubset
        _ ≤ P terminalTail + P hitAndTerminalSmall := measure_union_le _ _
    have hterminal_le : P terminalTail ≤ tailSup := by
      dsimp [terminalTail, tailSup]
      let tailProb : ℕ → ENNReal := fun k ↦ P {ω | t / 3 ≤ |partialSum X k ω|}
      change tailProb n ≤ (Finset.Icc 1 n).sup tailProb
      exact Finset.le_sup (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hn, le_rfl⟩)
    have hsmall :
        P hitAndTerminalSmall ≤ (2 * tailSup) * P (absHitEvent X n t) := by
      simpa [hitAndTerminalSmall, tailSup] using
        absHit_terminalSmall_le_twoTailSup_mul_hit P X n hX_meas hX_indep hn
    have hhit_le_one : P (absHitEvent X n t) ≤ 1 := by
      calc
        P (absHitEvent X n t) ≤ P Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
    have hmult :
        (2 * tailSup) * P (absHitEvent X n t) ≤ (2 * tailSup) * 1 := by
      gcongr
    -- Proof comment: once the terminal-small part is controlled by `2 * tailSup`, the terminal
    -- tail itself contributes one more copy of `tailSup`, giving the factor `3`.
    calc
      P (absHitEvent X n t) ≤ P terminalTail + P hitAndTerminalSmall := hmeasure
      _ ≤ tailSup + (2 * tailSup) * P (absHitEvent X n t) := by
        exact add_le_add hterminal_le hsmall
      _ ≤ tailSup + (2 * tailSup) * 1 := by
        exact add_le_add le_rfl hmult
      _ = tailSup + 2 * tailSup := by rw [mul_one]
      _ = 3 * tailSup := by
        rw [show (3 : ENNReal) = 1 + 2 by norm_num, add_mul, one_mul]
      _ = 3 *
            (Finset.Icc 1 n).sup fun k ↦
              P {ω | t / 3 ≤ |partialSum X k ω|} := by
        rfl
