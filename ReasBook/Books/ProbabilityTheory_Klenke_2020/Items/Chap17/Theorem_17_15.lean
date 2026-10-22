/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable (Y : ℕ → Ω → ℝ)

/-- Helper for Theorem 17.15: every increment of an i.i.d. family is a.e.-measurable because each
coordinate has the same law as `Y 0`. -/
private lemma incrementAEMeasurable (hY_iid : IsIID Y μ) (i : ℕ) :
    AEMeasurable (Y i) μ := by
  -- Proof comment: identical distribution with the `0`th increment provides the needed
  -- a.e.-measurability of the `i`th coordinate.
  simpa using (hY_iid.identDistrib i 0).aemeasurable_fst

/-- Helper for Theorem 17.15: every finite partial sum is a.e.-measurable. -/
private lemma partialSumAEMeasurable (hY_iid : IsIID Y μ) (n : ℕ) :
    AEMeasurable (partialSum Y n) μ := by
  -- Proof comment: finite sums preserve a.e.-measurability, so it suffices to sum the
  -- a.e.-measurable increments over `Finset.range n`.
  simpa [partialSum] using
    (Finset.aemeasurable_fun_sum (Finset.range n) fun i hi ↦
      incrementAEMeasurable (Y := Y) hY_iid i)

/-- Helper for Theorem 17.15: the `k`th first-hit layer consists of sample points whose first
partial sum reaching `a` occurs exactly at time `k`. -/
private def firstHitLayer (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j ∈ Finset.Icc 1 (k - 1), partialSum Y j ω < a) ∧ a ≤ partialSum Y k ω}

/-- Helper for Theorem 17.15: two different first-hit layers are disjoint. -/
private lemma firstHitLayer_disjoint {n k l : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hl : l ∈ Finset.Icc 1 n) (hkl : k ≠ l) (a : ℝ) :
    Disjoint (firstHitLayer Y a k) (firstHitLayer Y a l) := by
  -- Proof comment: the later first-hit condition forces the earlier partial sum to stay below
  -- the threshold, which contradicts membership in the earlier hitting layer.
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

/-- Helper for Theorem 17.15: every path that hits the threshold by time `n` lies in its least
first-hit layer. -/
private lemma exists_firstHitLayer (n : ℕ) (a : ℝ) (ω : Ω)
    (hω : ω ∈ oneSidedHitEvent Y n a) :
    ∃ k ∈ Finset.Icc 1 n, ω ∈ firstHitLayer Y a k := by
  -- Proof comment: choose the least hitting index by `Nat.find`; its minimality exactly encodes
  -- the first-hit inequalities.
  let p : ℕ → Prop := fun k ↦ k ∈ Finset.Icc 1 n ∧ a ≤ partialSum Y k ω
  have hp : ∃ k, p k := hω
  refine ⟨Nat.find hp, (Nat.find_spec hp).1, ?_⟩
  refine ⟨?_, (Nat.find_spec hp).2⟩
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

/-- Helper for Theorem 17.15: the one-sided hit indicator is the sum of the disjoint first-hit
layer indicators. -/
private lemma firstHitLayer_indicatorSum_eq_hitIndicator (n : ℕ) (a : ℝ) :
    (fun ω ↦ Finset.sum (Finset.Icc 1 n)
      (fun k ↦ Set.indicator (firstHitLayer Y a k) (fun _ ↦ (1 : ℝ)) ω)) =
      Set.indicator (oneSidedHitEvent Y n a) (fun _ ↦ (1 : ℝ)) := by
  -- Proof comment: on the hit event exactly one first-hit layer contributes, and off the hit
  -- event every layer indicator vanishes.
  funext ω
  by_cases hω : ω ∈ oneSidedHitEvent Y n a
  · rcases exists_firstHitLayer (Y := Y) n a ω hω with ⟨k, hk, hkω⟩
    rw [Finset.sum_eq_single k]
    · simp [hω, hkω]
    · intro l hl hlk
      have hdisj := firstHitLayer_disjoint (Y := Y) hk hl hlk.symm a
      have hl_not : ω ∉ firstHitLayer Y a l := by
        intro hlω
        exact (Set.disjoint_left.mp hdisj) hkω hlω
      simp [hl_not]
    · intro hk_not_mem
      exact False.elim (hk_not_mem hk)
  · have hnone : ∀ k ∈ Finset.Icc 1 n, ω ∉ firstHitLayer Y a k := by
      intro k hk hkω
      exact hω ⟨k, hk, hkω.2⟩
    have hsum :
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ Set.indicator (firstHitLayer Y a k) (fun _ ↦ (1 : ℝ)) ω) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [hnone k hk]
    rw [hsum]
    simp [hω]

/-- Helper for Theorem 17.15: the tuple-level prefix sum up to `j` inside a `k`-tuple. -/
private def prefixVec (k : ℕ) (z : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin k, if (i : ℕ) < j then z i else 0

/-- Helper for Theorem 17.15: evaluating the tuple-level prefix sum on the first `k` coordinates
of a sample path recovers the corresponding partial sum. -/
private lemma prefixVec_eq_partialSum {j k : ℕ} (hj : j ≤ k) (ω : Ω) :
    prefixVec k (fun i : Fin k ↦ Y i ω) j = partialSum Y j ω := by
  -- Proof comment: convert the `Fin k` sum into a `range k` sum and then split the range at `j`.
  rw [prefixVec]
  calc
    ∑ i : Fin k, (if (i : ℕ) < j then Y i ω else 0)
      = ∑ i ∈ Finset.range k, (if i < j then Y i ω else 0) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if i < j then Y i ω else 0) k)
    _ = ∑ i ∈ Finset.range (j + (k - j)), (if i < j then Y i ω else 0) := by
          simp [Nat.add_sub_of_le hj]
    _ = ∑ i ∈ Finset.range j, Y i ω
          + ∑ i ∈ Finset.range (k - j), (if j + i < j then Y (j + i) ω else 0) := by
          rw [Finset.sum_range_add]
          refine congrArg (fun x : ℝ ↦ x + _) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Finset.mem_range.mp hi]
    _ = ∑ i ∈ Finset.range j, Y i ω := by
          simp
    _ = partialSum Y j ω := by
          rw [partialSum]

/-- Helper for Theorem 17.15: tuple-level prefix sums are measurable on finite product space. -/
private lemma measurable_prefixVec (k j : ℕ) :
    Measurable (fun z : Fin k → ℝ ↦ prefixVec k z j) := by
  -- Proof comment: finite sums of measurable coordinate projections remain measurable.
  unfold prefixVec
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  by_cases hij : (i : ℕ) < j
  · simpa [hij] using measurable_pi_apply i
  · simp [hij]

/-- Helper for Theorem 17.15: the tuple-space first-hit condition for the threshold `a`. -/
private def firstHitPrefixSet (k : ℕ) (a : ℝ) : Set (Fin k → ℝ) :=
  (⋂ j ∈ Finset.Icc 1 (k - 1), {z | prefixVec k z j < a}) ∩
    {z | a ≤ prefixVec k z k}

/-- Helper for Theorem 17.15: the tuple-space first-hit set is measurable. -/
private lemma measurableSet_firstHitPrefixSet (k : ℕ) (a : ℝ) :
    MeasurableSet (firstHitPrefixSet k a) := by
  -- Proof comment: the first-hit condition is a finite intersection of measurable threshold sets.
  have hprev :
      MeasurableSet
        (⋂ j ∈ Finset.Icc 1 (k - 1), {z : Fin k → ℝ | prefixVec k z j < a}) := by
    refine Finset.measurableSet_biInter (Finset.Icc 1 (k - 1)) fun j _ ↦ ?_
    exact measurableSet_lt (measurable_prefixVec k j) measurable_const
  have hlast : MeasurableSet {z : Fin k → ℝ | a ≤ prefixVec k z k} :=
    measurableSet_le measurable_const (measurable_prefixVec k k)
  simpa [firstHitPrefixSet] using hprev.inter hlast

/-- Helper for Theorem 17.15: evaluating the tuple first-hit condition on the first `k`
coordinates of a sample path recovers the concrete first-hit layer. -/
private lemma prefixTuple_mem_firstHitPrefixSet_iff {k : ℕ} (a : ℝ) (ω : Ω) :
    (fun i : Fin k ↦ Y i ω) ∈ firstHitPrefixSet k a ↔ ω ∈ firstHitLayer Y a k := by
  -- Proof comment: each tuple prefix sum rewrites to the corresponding concrete partial sum.
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hzj := Set.mem_iInter.1 (Set.mem_iInter.1 hz.1 j) hj
      simpa [prefixVec_eq_partialSum (Y := Y) (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hzj
    · simpa [prefixVec_eq_partialSum (Y := Y) (show k ≤ k by rfl) ω] using hz.2
  · intro hω
    rcases hω with ⟨hprev, hkge⟩
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun j ↦ Set.mem_iInter.2 fun hj ↦ ?_
      have hj' := Finset.mem_Icc.mp hj
      simpa [prefixVec_eq_partialSum (Y := Y) (le_trans hj'.2 (Nat.sub_le _ _)) ω] using
        hprev j hj
    · simpa [prefixVec_eq_partialSum (Y := Y) (show k ≤ k by rfl) ω] using hkge

/-- Helper for Theorem 17.15: each first-hit layer is null measurable. -/
private lemma nullMeasurableSet_firstHitLayer (hY_iid : IsIID Y μ) (a : ℝ) (k : ℕ) :
    NullMeasurableSet (firstHitLayer Y a k) μ := by
  -- Proof comment: the first-hit layer is the preimage of the measurable tuple-space first-hit
  -- set under the a.e.-measurable prefix tuple map.
  let prefixTuple : Ω → Fin k → ℝ := fun ω i ↦ Y i ω
  have hPrefixAe : AEMeasurable prefixTuple μ := by
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    simpa [prefixTuple] using incrementAEMeasurable (Y := Y) hY_iid (i : ℕ)
  have hPreimage :
      NullMeasurableSet (prefixTuple ⁻¹' firstHitPrefixSet k a) μ :=
    hPrefixAe.nullMeasurableSet_preimage (measurableSet_firstHitPrefixSet k a)
  convert hPreimage using 1
  ext ω
  simp [prefixTuple, prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) a ω]

/-- Helper for Theorem 17.15: the tuple-level future block sum. -/
private def futureVecSum (m : ℕ) (z : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, z i

/-- Helper for Theorem 17.15: summing the future `n - k` tuple coordinates gives the tail
increment `partialSum Y n - partialSum Y k`. -/
private lemma futureVecSum_eq_tailIncrement {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω) =
      partialSum Y n ω - partialSum Y k ω := by
  -- Proof comment: reindex the future tuple sum as the `Ico k n` block from the tail-sum lemma.
  rw [futureVecSum]
  calc
    ∑ i : Fin (n - k), Y (k + i) ω
      = ∑ i ∈ Finset.range (n - k), Y (k + i) ω := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Y (k + i) ω) (n - k))
    _ = ∑ i ∈ Finset.Ico k n, Y i ω := by
          rw [Finset.sum_Ico_eq_sum_range]
    _ = partialSum Y n ω - partialSum Y k ω := by
          symm
          exact partialSum_sub_eq_sum_Ico Y hk ω

/-- Helper for Theorem 17.15: summing the coordinates of a finite future block is measurable. -/
private lemma measurable_futureVecSum (m : ℕ) :
    Measurable (fun z : Fin m → ℝ ↦ futureVecSum m z) := by
  -- Proof comment: this is again a finite sum of measurable coordinate projections.
  unfold futureVecSum
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Theorem 17.15: the hit event is the finite union of its first-hit layers. -/
private lemma oneSidedHitEvent_eq_biUnion_firstHitLayer (n : ℕ) (a : ℝ) :
    (⋃ k ∈ Finset.Icc 1 n, firstHitLayer Y a k) = oneSidedHitEvent Y n a := by
  -- Proof comment: each hitting path has a least hitting index, and every first-hit layer point
  -- is tautologically a hit point.
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨k, hk, hkω⟩
    exact ⟨k, hk, hkω.2⟩
  · intro hω
    rcases exists_firstHitLayer (Y := Y) n a ω hω with ⟨k, hk, hkω⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hkω⟩⟩

/-- Helper for Theorem 17.15: if the terminal partial sum exceeds `a > 0`, then the path has
already hit `a` by time `n`. -/
private lemma endpointGe_subset_oneSidedHitEvent (n : ℕ) (a : ℝ) (ha : 0 < a) :
    {ω | a ≤ partialSum Y n ω} ⊆ oneSidedHitEvent Y n a := by
  -- Proof comment: the terminal time `n` itself witnesses the hit, once `n = 0` is ruled out by
  -- `partialSum Y 0 = 0` and `a > 0`.
  intro ω hω
  have hn_pos : 0 < n := by
    by_contra hn_pos
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    have : a ≤ 0 := by simpa [hn_zero, partialSum] using hω
    linarith
  exact ⟨n, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hn_pos, le_rfl⟩, hω⟩

/-- Helper for Theorem 17.15: the filtered past/future block independence reindexes to raw
`Fin k` and `Fin (n - k)` tuples. -/
private lemma filteredPrefixFutureIndep (hY_iid : IsIID Y μ) {n k : ℕ} (hk : k ≤ n) :
    IndepFun (fun ω ↦ fun i : Fin k ↦ Y i ω)
      (fun ω ↦ fun i : Fin (n - k) ↦ Y (k + i) ω) μ := by
  let pastIdx : Finset (Fin n) := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < k)
  let futureIdx : Finset (Fin n) := Finset.univ.filter (fun i : Fin n ↦ k ≤ (i : ℕ))
  let pastCoord : Ω → pastIdx → ℝ := fun ω i ↦ Y i ω
  let futureCoord : Ω → futureIdx → ℝ := fun ω i ↦ Y i ω
  let pastToPrefix : (pastIdx → ℝ) → (Fin k → ℝ) := fun z i ↦
    z ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by
      simp [pastIdx, i.2]⟩
  let futureToSuffix : (futureIdx → ℝ) → (Fin (n - k) → ℝ) := fun z i ↦
    z ⟨⟨k + i, by
      omega⟩, by
      simp [futureIdx]⟩
  have hFiniteIndep : iIndepFun (fun i : Fin n ↦ Y i) μ := by
    -- Proof comment: restrict the global i.i.d. family to the first `n` coordinates.
    simpa using hY_iid.iIndepFun.precomp Fin.val_injective
  have hPastCoord : AEMeasurable pastCoord μ := by
    -- Proof comment: the filtered past tuple is coordinatewise a.e.-measurable.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    simpa using incrementAEMeasurable (Y := Y) hY_iid (i : ℕ)
  have hFutureCoord : AEMeasurable futureCoord μ := by
    -- Proof comment: the filtered future tuple is coordinatewise a.e.-measurable as well.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    simpa using incrementAEMeasurable (Y := Y) hY_iid (i : ℕ)
  have hPastToPrefix : Measurable pastToPrefix := by
    -- Proof comment: reindexing the filtered past block is coordinatewise evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : pastIdx := ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by
      simp [pastIdx, i.2]⟩
    simpa [pastToPrefix, idx] using
      (measurable_pi_apply idx : Measurable fun z : pastIdx → ℝ ↦ z idx)
  have hFutureToSuffix : Measurable futureToSuffix := by
    -- Proof comment: the same coordinatewise evaluation reindexes the filtered future block.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : futureIdx := ⟨⟨k + i, by
      omega⟩, by
      simp [futureIdx]⟩
    simpa [futureToSuffix, idx] using
      (measurable_pi_apply idx : Measurable fun z : futureIdx → ℝ ↦ z idx)
  have hdisj : Disjoint pastIdx futureIdx := by
    -- Proof comment: the past/future split is by strict inequality versus its complement.
    refine Finset.disjoint_left.mpr ?_
    intro i hiPast hiFuture
    simp only [pastIdx, futureIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hiPast hiFuture
    exact hiPast.not_ge hiFuture
  have hFiltered : IndepFun pastCoord futureCoord μ := by
    -- Proof comment: independence of disjoint coordinate blocks is `iIndepFun.indepFun_finset₀`.
    have hbase := hFiniteIndep.indepFun_finset₀ pastIdx futureIdx hdisj fun i ↦
      incrementAEMeasurable (Y := Y) hY_iid (i : ℕ)
    simpa [pastCoord, futureCoord] using hbase
  have hRawTuple :
      IndepFun (pastToPrefix ∘ pastCoord) (futureToSuffix ∘ futureCoord) μ := by
    -- Proof comment: compose the filtered block independence with the concrete reindexing maps.
    exact hFiltered.comp₀ hPastCoord hFutureCoord hPastToPrefix.aemeasurable
      hFutureToSuffix.aemeasurable
  -- Proof comment: the reindexed tuples are definitionally the raw prefix and future blocks.
  simpa [Function.comp, pastToPrefix, futureToSuffix, pastCoord, futureCoord] using hRawTuple

/-- Helper for Theorem 17.15: the shifted tail block sum has the same law as its negative. -/
private lemma tailBlockSum_identDistrib_neg (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ) {n k : ℕ} (hk : k ≤ n) :
    IdentDistrib
      (fun ω ↦ futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω))
      (fun ω ↦ -futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω))
      μ μ := by
  let shifted : Fin (n - k) → Ω → ℝ := fun i ω ↦ Y (k + i) ω
  have hShiftCoord :
      ∀ i : Fin (n - k), IdentDistrib (shifted i) (fun ω ↦ -shifted i ω) μ μ := by
    intro i
    -- Proof comment: each shifted increment has the law of `Y 0`, hence also the law of its
    -- negative by symmetry of the common increment distribution.
    exact ((hY_iid.identDistrib (k + i) 0).trans hY_symm).trans
      ((hY_iid.identDistrib (k + i) 0).symm.comp measurable_neg)
  have hShiftInd : iIndepFun shifted μ := by
    -- Proof comment: reindex the i.i.d. family along the injective shift `i ↦ k + i`.
    have hInjective : Function.Injective (fun i : Fin (n - k) ↦ k + i) := by
      intro i j hij
      apply Fin.ext
      exact Nat.add_left_cancel hij
    simpa [shifted] using hY_iid.iIndepFun.precomp hInjective
  have hShiftNegInd : iIndepFun (fun i : Fin (n - k) ↦ fun ω ↦ -shifted i ω) μ := by
    -- Proof comment: independence is preserved under measurable coordinatewise negation.
    simpa [shifted, Function.comp] using
      hShiftInd.comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  have hVec :
      IdentDistrib
        (fun ω ↦ fun i : Fin (n - k) ↦ shifted i ω)
        (fun ω ↦ fun i : Fin (n - k) ↦ -shifted i ω)
        μ μ :=
    IdentDistrib.pi hShiftCoord hShiftInd hShiftNegInd
  have hSum :
      IdentDistrib
        (fun ω ↦ futureVecSum (n - k) (fun i : Fin (n - k) ↦ shifted i ω))
        (fun ω ↦ futureVecSum (n - k) (fun i : Fin (n - k) ↦ -shifted i ω))
        μ μ := by
    -- Proof comment: summing the future block is a measurable postcomposition of the tuple law.
    simpa [Function.comp] using hVec.comp (measurable_futureVecSum (n - k))
  have hNegTail :
      (fun ω ↦ futureVecSum (n - k) (fun i : Fin (n - k) ↦ -shifted i ω)) =ᵐ[μ]
        (fun ω ↦ -futureVecSum (n - k) (fun i : Fin (n - k) ↦ shifted i ω)) :=
    Filter.Eventually.of_forall fun ω ↦ by
      simp [futureVecSum]
  -- Proof comment: rewrite the negated tuple sum to the explicit negation of the original tail
  -- sum before returning to the source-facing formula.
  exact hSum.trans <| IdentDistrib.of_ae_eq hSum.aemeasurable_snd hNegTail

/-- Helper for Theorem 17.15: the canonical prefix/tail observable for a fixed layer `k ≤ n`. -/
private def prefixTailPair (n k : ℕ) (ω : Ω) : (Fin k → ℝ) × ℝ :=
  ((fun i : Fin k ↦ Y i ω),
    futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω))

/-- Helper for Theorem 17.15: reflect the tail-sum coordinate while keeping the prefix fixed. -/
private def reflectedPrefixTailPair (n k : ℕ) (ω : Ω) : (Fin k → ℝ) × ℝ :=
  ((fun i : Fin k ↦ Y i ω),
    -futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω))

/-- Helper for Theorem 17.15: the pair-space event encoding a first-hit prefix together with a
terminal endpoint still lying below `a`. -/
private def firstHitTerminalBelowSet (k : ℕ) (a : ℝ) : Set ((Fin k → ℝ) × ℝ) :=
  {p | p.1 ∈ firstHitPrefixSet k a ∧ prefixVec k p.1 k + p.2 < a}

/-- Helper for Theorem 17.15: the pair-space below-terminal event is measurable. -/
private lemma measurableSet_firstHitTerminalBelowSet (k : ℕ) (a : ℝ) :
    MeasurableSet (firstHitTerminalBelowSet k a) := by
  -- Proof comment: this is the intersection of the measurable first-hit prefix condition with a
  -- measurable affine threshold in the tail coordinate.
  have hPrefix :
      MeasurableSet {p : (Fin k → ℝ) × ℝ | p.1 ∈ firstHitPrefixSet k a} :=
    (measurableSet_firstHitPrefixSet k a).preimage measurable_fst
  have hEndpoint :
      MeasurableSet {p : (Fin k → ℝ) × ℝ | prefixVec k p.1 k + p.2 < a} := by
    exact
      measurableSet_lt
        (((measurable_prefixVec k k).comp measurable_fst).add measurable_snd)
        measurable_const
  change
    MeasurableSet
      ({p : (Fin k → ℝ) × ℝ | p.1 ∈ firstHitPrefixSet k a} ∩
        {p : (Fin k → ℝ) × ℝ | prefixVec k p.1 k + p.2 < a})
  exact hPrefix.inter hEndpoint

/-- Helper for Theorem 17.15: the reflected prefix/tail pair has the same law as the original
pair. -/
private lemma prefixTailSumPair_identDistrib_reflect
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    {n k : ℕ} (hk : k ≤ n) :
    IdentDistrib (prefixTailPair (Y := Y) n k) (reflectedPrefixTailPair (Y := Y) n k) μ μ := by
  let prefixTuple : Ω → Fin k → ℝ := fun ω i ↦ Y i ω
  let tailSum : Ω → ℝ := fun ω ↦
    futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω)
  have hPrefixAe : AEMeasurable prefixTuple μ := by
    -- Proof comment: the prefix tuple is coordinatewise a.e.-measurable.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    simpa [prefixTuple] using incrementAEMeasurable (Y := Y) hY_iid (i : ℕ)
  have hIndepTail : IndepFun prefixTuple tailSum μ := by
    -- Proof comment: compose prefix/future-tuple independence with the measurable sum on the
    -- future coordinates.
    simpa [Function.comp, prefixTuple, tailSum] using
      (filteredPrefixFutureIndep (Y := Y) hY_iid hk).comp measurable_id
        (measurable_futureVecSum (n - k))
  have hIndepNegTail : IndepFun prefixTuple (fun ω ↦ -tailSum ω) μ := by
    -- Proof comment: tail negation preserves independence because negation is measurable.
    simpa [tailSum] using hIndepTail.comp measurable_id measurable_neg
  -- Proof comment: combine the fixed prefix law with the reflected tail law on the product space.
  simpa [prefixTailPair, reflectedPrefixTailPair, prefixTuple, tailSum] using
    IdentDistrib.prodMk (IdentDistrib.refl hPrefixAe)
      (tailBlockSum_identDistrib_neg (Y := Y) hY_iid hY_symm hk) hIndepTail hIndepNegTail

/-- Helper for Theorem 17.15: the below-terminal pair event pulls back to the concrete first-hit
layer intersected with `{partialSum Y n < a}`. -/
private lemma prefixTailPair_mem_firstHitTerminalBelowSet_iff
    {n k : ℕ} (hk : k ≤ n) (a : ℝ) (ω : Ω) :
    ω ∈ prefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a ↔
      ω ∈ firstHitLayer Y a k ∧ partialSum Y n ω < a := by
  have hPrefixEq :
      prefixVec k (fun i : Fin k ↦ Y i ω) k = partialSum Y k ω :=
    prefixVec_eq_partialSum (Y := Y) (show k ≤ k by rfl) ω
  have hTailEq :
      futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω) =
        partialSum Y n ω - partialSum Y k ω :=
    futureVecSum_eq_tailIncrement (Y := Y) hk ω
  constructor
  · intro hω
    rcases hω with ⟨hPrefix, hBelow⟩
    refine ⟨(prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) a ω).mp hPrefix, ?_⟩
    have hTerminal :
        partialSum Y k ω + (partialSum Y n ω - partialSum Y k ω) < a := by
      simpa [prefixTailPair, firstHitTerminalBelowSet, hPrefixEq, hTailEq] using hBelow
    linarith
  · rintro ⟨hLayer, hBelow⟩
    refine ⟨(prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) a ω).mpr hLayer, ?_⟩
    have hTerminal :
        partialSum Y k ω + (partialSum Y n ω - partialSum Y k ω) < a := by
      linarith
    simpa [prefixTailPair, firstHitTerminalBelowSet, hPrefixEq, hTailEq] using hTerminal

/-- Helper for Theorem 17.15: the reflected below-terminal pair event has a stable pointwise
normal form on `Ω`. -/
private lemma reflectedPrefixTailPair_mem_firstHitTerminalBelowSet_iff
    {n k : ℕ} (hk : k ≤ n) (a : ℝ) (ω : Ω) :
    ω ∈ reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a ↔
      ω ∈ firstHitLayer Y a k ∧
        (partialSum Y k ω - (partialSum Y n ω - partialSum Y k ω) < a) := by
  have hPrefixEq :
      prefixVec k (fun i : Fin k ↦ Y i ω) k = partialSum Y k ω :=
    prefixVec_eq_partialSum (Y := Y) (show k ≤ k by rfl) ω
  have hTailEq :
      futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω) =
        partialSum Y n ω - partialSum Y k ω :=
    futureVecSum_eq_tailIncrement (Y := Y) hk ω
  constructor
  · intro hω
    rcases hω with ⟨hPrefix, hBelow⟩
    refine ⟨(prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) a ω).mp hPrefix, ?_⟩
    have hTerminal :
        partialSum Y k ω + (partialSum Y k ω - partialSum Y n ω) < a := by
      simpa [reflectedPrefixTailPair, firstHitTerminalBelowSet, hPrefixEq, hTailEq] using hBelow
    linarith
  · rintro ⟨hLayer, hBelow⟩
    refine ⟨(prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) a ω).mpr hLayer, ?_⟩
    have hTerminal :
        partialSum Y k ω + (partialSum Y k ω - partialSum Y n ω) < a := by
      linarith
    simpa [reflectedPrefixTailPair, firstHitTerminalBelowSet, hPrefixEq, hTailEq] using hTerminal

/-- Helper for Theorem 17.15: intersecting a first-hit layer with the terminal `<`, `=`, and `≥`
events has stable set-theoretic normal forms. -/
private lemma firstHitLayer_terminalPartition
    {n k : ℕ} (a : ℝ) :
    (firstHitLayer Y a k \ {ω | partialSum Y n ω < a} =
        firstHitLayer Y a k ∩ {ω | a ≤ partialSum Y n ω}) ∧
      ((firstHitLayer Y a k ∩ {ω | a ≤ partialSum Y n ω}) \
          {ω | partialSum Y n ω = a} =
        firstHitLayer Y a k ∩ {ω | a < partialSum Y n ω}) := by
  constructor
  · -- Proof comment: removing the strict-below terminal event is the same as intersecting with
    -- its order-theoretic complement `{a ≤ partialSum Y n}`.
    ext ω
    simp [Set.mem_diff, not_lt]
  · -- Proof comment: inside `{a ≤ partialSum Y n}`, removing the equality slice leaves the strict
    -- above event.
    ext ω
    simp [Set.mem_diff, lt_iff_le_and_ne, ne_comm, and_left_comm, and_assoc]

/-- Helper for Theorem 17.15: the below-terminal pair event pulls back to the concrete first-hit
layer intersected with `{partialSum Y n < a}`. -/
private lemma prefixTailPair_preimage_firstHitTerminalBelowSet
    {n k : ℕ} (hk : k ≤ n) (a : ℝ) :
    prefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a =
      firstHitLayer Y a k ∩ {ω | partialSum Y n ω < a} := by
  -- Proof comment: freeze the transport at the pointwise level and then package the result by
  -- extensionality.
  ext ω
  rw [prefixTailPair_mem_firstHitTerminalBelowSet_iff (Y := Y) hk a ω]
  simp [Set.mem_inter_iff]

/-- Helper for Theorem 17.15: reflecting the tail sends the below-terminal pair event into the
strict-above terminal event on the same first-hit layer. -/
private lemma reflectedPrefixTailPair_preimage_firstHitTerminalBelowSet_subset_above
    {n k : ℕ} (hk : k ≤ n) (a : ℝ) :
    reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a ⊆
      firstHitLayer Y a k ∩ {ω | a < partialSum Y n ω} := by
  -- Proof comment: after the pointwise normalization, the reflected endpoint inequality is a
  -- one-line `linarith` consequence of `a ≤ partialSum Y k`.
  intro ω hω
  rw [reflectedPrefixTailPair_mem_firstHitTerminalBelowSet_iff (Y := Y) hk a ω] at hω
  rcases hω with ⟨hLayer, hBelow⟩
  rcases hLayer with ⟨hPrev, hge⟩
  have hAbove : a < partialSum Y n ω := by
    linarith
  exact ⟨⟨hPrev, hge⟩, hAbove⟩

/-- Helper for Theorem 17.15: if the first-hit layer lands exactly at `a`, then every strict-above
terminal endpoint arises from the reflected below-terminal pair event. -/
private lemma above_mem_reflectedPrefixTailPair_preimage_firstHitTerminalBelowSet_of_exactHit
    {n k : ℕ} (hk : k ≤ n) {a : ℕ} {ω : Ω}
    (hLayer : ω ∈ firstHitLayer Y (a : ℝ) k)
    (hExact : partialSum Y k ω = (a : ℝ))
    (hAbove : (a : ℝ) < partialSum Y n ω) :
    ω ∈ reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k (a : ℝ) := by
  have hPrefix :
      (fun i : Fin k ↦ Y i ω) ∈ firstHitPrefixSet k (a : ℝ) :=
    (prefixTuple_mem_firstHitPrefixSet_iff (Y := Y) (a : ℝ) ω).mpr hLayer
  have hPrefixEq :
      prefixVec k (fun i : Fin k ↦ Y i ω) k = partialSum Y k ω :=
    prefixVec_eq_partialSum (Y := Y) (show k ≤ k by rfl) ω
  have hTailEq :
      futureVecSum (n - k) (fun i : Fin (n - k) ↦ Y (k + i) ω) =
        partialSum Y n ω - partialSum Y k ω :=
    futureVecSum_eq_tailIncrement (Y := Y) hk ω
  have hCancel : partialSum Y n ω = partialSum Y k ω + (partialSum Y n ω - partialSum Y k ω) := by
    ring
  have hReflected :
      partialSum Y k ω - (partialSum Y n ω - partialSum Y k ω) < (a : ℝ) := by
    linarith [hExact, hAbove, hCancel]
  refine ⟨hPrefix, ?_⟩
  simpa [reflectedPrefixTailPair, hPrefixEq, hTailEq, sub_eq_add_neg] using hReflected

/-- Helper for Theorem 17.15: reflecting the tail after a fixed first-hit layer sends the
below-threshold terminal event into the strict-above-threshold terminal event. -/
private lemma firstHitLayer_reflectionBelow_le_above
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℝ) :
    μ.real (firstHitLayer Y a k ∩ {ω | partialSum Y n ω < a}) ≤
      μ.real (firstHitLayer Y a k ∩ {ω | a < partialSum Y n ω}) := by
  have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hPairLaw :
      IdentDistrib (prefixTailPair (Y := Y) n k) (reflectedPrefixTailPair (Y := Y) n k) μ μ :=
    prefixTailSumPair_identDistrib_reflect (Y := Y) hY_iid hY_symm hk_le
  -- Route correction: compare both layer events through one measurable pair-space set, so the
  -- reflected law acts before any event-level transport back to `Ω`.
  calc
    μ.real (firstHitLayer Y a k ∩ {ω | partialSum Y n ω < a}) =
        μ.real (prefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a) := by
          rw [prefixTailPair_preimage_firstHitTerminalBelowSet (Y := Y) hk_le a]
    _ = μ.real (reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k a) := by
          simpa [Measure.real] using congrArg ENNReal.toReal <|
            hPairLaw.measure_mem_eq (measurableSet_firstHitTerminalBelowSet k a)
    _ ≤ μ.real (firstHitLayer Y a k ∩ {ω | a < partialSum Y n ω}) := by
          refine measureReal_mono ?_
          exact
            reflectedPrefixTailPair_preimage_firstHitTerminalBelowSet_subset_above (Y := Y) hk_le a

/-- Helper for Theorem 17.15: each first-hit layer satisfies the reflected endpoint inequality
that sums to the global reflection-principle bound. -/
private lemma firstHitLayer_reflectionBound
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℝ) :
    μ.real (firstHitLayer Y a k) ≤
      2 * μ.real (firstHitLayer Y a k ∩ {ω | a ≤ partialSum Y n ω}) -
        μ.real (firstHitLayer Y a k ∩ {ω | partialSum Y n ω = a}) := by
  let layerSet : Set Ω := firstHitLayer Y a k
  let geSet : Set Ω := {ω | a ≤ partialSum Y n ω}
  let ltSet : Set Ω := {ω | partialSum Y n ω < a}
  let eqSet : Set Ω := {ω | partialSum Y n ω = a}
  have hTerminalLt_null : NullMeasurableSet ltSet μ := by
    -- Proof comment: terminal threshold events are null measurable because the terminal partial
    -- sum is a.e.-measurable.
    simpa [ltSet] using
      nullMeasurableSet_lt (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hTerminalEq_null : NullMeasurableSet eqSet μ := by
    -- Proof comment: the terminal equality slice is likewise null measurable.
    simpa [eqSet] using
      nullMeasurableSet_eq_fun (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hSplitBelow :
      μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) = μ.real layerSet := by
    -- Proof comment: split the layer into the terminal `< a` and `≥ a` pieces.
    have hBase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μ) (s := layerSet) hTerminalLt_null
    rw [(firstHitLayer_terminalPartition (Y := Y) (n := n) (k := k) a).1] at hBase
    simpa [layerSet, ltSet, geSet] using hBase
  have hSplitEq :
      μ.real (layerSet ∩ {ω | a < partialSum Y n ω}) + μ.real (layerSet ∩ eqSet) =
        μ.real (layerSet ∩ geSet) := by
    -- Proof comment: split the terminal `≥ a` slice into its strict-above and exact-hit pieces.
    have hBase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μ) (s := layerSet ∩ geSet) hTerminalEq_null
    rw [(firstHitLayer_terminalPartition (Y := Y) (n := n) (k := k) a).2] at hBase
    have hEqInter : layerSet ∩ geSet ∩ eqSet = layerSet ∩ eqSet := by
      ext ω
      constructor
      · rintro ⟨⟨hLayer, hGe⟩, hEq⟩
        exact ⟨hLayer, hEq⟩
      · rintro ⟨hLayer, hEq⟩
        have hGe : a ≤ partialSum Y n ω := by
          rw [hEq]
        exact ⟨⟨hLayer, hGe⟩, hEq⟩
    rw [hEqInter, add_comm] at hBase
    simpa [layerSet, geSet, eqSet] using hBase
  have hReflect :
      μ.real (layerSet ∩ ltSet) ≤ μ.real (layerSet ∩ {ω | a < partialSum Y n ω}) := by
    simpa [layerSet, ltSet] using
      firstHitLayer_reflectionBelow_le_above (Y := Y) hY_iid hY_symm hk a
  -- Proof comment: substitute the two terminal partitions and then use the reflected inequality
  -- on the strict-below slice.
  have hAboveEq :
      μ.real (layerSet ∩ {ω | a < partialSum Y n ω}) =
        μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet) := by
    linarith [hSplitEq]
  have hLayerEq :
      μ.real layerSet = μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) := by
    linarith [hSplitBelow]
  calc
    μ.real (firstHitLayer Y a k) = μ.real layerSet := by rfl
    _ = μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) := hLayerEq
    _ ≤ μ.real (layerSet ∩ {ω | a < partialSum Y n ω}) + μ.real (layerSet ∩ geSet) := by
          gcongr
    _ = (μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet)) +
          μ.real (layerSet ∩ geSet) := by rw [hAboveEq]
    _ = 2 * μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet) := by ring

-- Proof sketch: stop the partial-sum process at its first entrance into `[a, ∞)` before time
-- `n`, reflect the future increments using the symmetry in law `Y₀ ≈ -Y₀`, and compare the
-- reflected endpoint distribution with the events `{a ≤ Sₙ}` and `{Sₙ = a}`.
/-- Theorem 17.15 (1): reflection principle. For a `0`-based i.i.d. real increment sequence
`Y 0, Y 1, ...` with symmetric law, the probability that one of the first `n` partial sums reaches
the level `a > 0` is bounded by `2 P[Sₙ ≥ a] - P[Sₙ = a]`, where `Sₙ = partialSum Y n`. This is
the textbook statement for `X₀ = 0` and `X_n = Y₁ + ⋯ + Y_n`, with Lean's `Y 0` representing the
textbook `Y₁`. The i.i.d. hypothesis is expressed via the chapter's canonical owner abstraction
`IsIID`. -/
theorem reflectionPrinciple_partialSum_le
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (n : ℕ) (a : ℝ) (ha : 0 < a) :
    μ.real (oneSidedHitEvent Y n a) ≤
      2 * μ.real {ω | a ≤ partialSum Y n ω} - μ.real {ω | partialSum Y n ω = a} := by
  let hitLayers : Finset ℕ := Finset.Icc 1 n
  let hitSet : Set Ω := oneSidedHitEvent Y n a
  let geSet : Set Ω := {ω | a ≤ partialSum Y n ω}
  let eqSet : Set Ω := {ω | partialSum Y n ω = a}
  have hGe_null : NullMeasurableSet geSet μ := by
    -- Proof comment: the terminal threshold event inherits null measurability from the terminal
    -- partial sum.
    simpa [geSet] using
      nullMeasurableSet_le aemeasurable_const (partialSumAEMeasurable (Y := Y) hY_iid n)
  have hEq_null : NullMeasurableSet eqSet μ := by
    -- Proof comment: the terminal equality event is the equality set of two a.e.-measurable
    -- functions.
    simpa [eqSet] using
      nullMeasurableSet_eq_fun (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y a i) (firstHitLayer Y a j) := by
    intro k hk l hl hkl
    exact (firstHitLayer_disjoint (Y := Y) hk hl hkl a).aedisjoint
  have hLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y a k) μ := by
    intro k hk
    exact nullMeasurableSet_firstHitLayer (Y := Y) hY_iid a k
  have hHitMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k) = μ.real hitSet := by
    -- Proof comment: the first-hit layers form a finite disjoint partition of the hit event.
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y a k) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hLayerPairwise hLayerNull
      _ = μ.real hitSet := by
            simpa [hitLayers, hitSet] using congrArg (Measure.real (μ := μ))
              (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n a)
  have hGeLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y a i ∩ geSet) (firstHitLayer Y a j ∩ geSet) := by
    intro k hk l hl hkl
    exact (Disjoint.mono Set.inter_subset_left Set.inter_subset_left <|
      firstHitLayer_disjoint (Y := Y) hk hl hkl a).aedisjoint
  have hGeLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y a k ∩ geSet) μ := by
    intro k hk
    exact (nullMeasurableSet_firstHitLayer (Y := Y) hY_iid a k).inter hGe_null
  have hGeUnion :
      (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ geSet) = geSet := by
    -- Proof comment: intersect the disjoint first-hit partition with the terminal `≥ a` event,
    -- then use that every terminal `≥ a` path has already hit `a`.
    calc
      (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ geSet)
        = (⋃ k ∈ hitLayers, firstHitLayer Y a k) ∩ geSet := by
            ext ω
            constructor
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨i, hi, hiω, hgeω⟩
              exact ⟨⟨i, hi, hiω⟩, hgeω⟩
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨⟨i, hi, hiω⟩, hgeω⟩
              exact ⟨i, hi, hiω, hgeω⟩
      _ = hitSet ∩ geSet := by
            simpa [hitLayers, hitSet] using
              congrArg (fun s : Set Ω ↦ s ∩ geSet)
                (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n a)
      _ = geSet := by
            apply Set.Subset.antisymm
            · exact Set.inter_subset_right
            · intro ω hω
              exact ⟨endpointGe_subset_oneSidedHitEvent (Y := Y) n a ha hω, hω⟩
  have hGeMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ geSet) = μ.real geSet := by
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ geSet)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ geSet) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hGeLayerPairwise hGeLayerNull
      _ = μ.real geSet := by rw [hGeUnion]
  have hEqLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y a i ∩ eqSet) (firstHitLayer Y a j ∩ eqSet) := by
    intro k hk l hl hkl
    exact (Disjoint.mono Set.inter_subset_left Set.inter_subset_left <|
      firstHitLayer_disjoint (Y := Y) hk hl hkl a).aedisjoint
  have hEqLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y a k ∩ eqSet) μ := by
    intro k hk
    exact (nullMeasurableSet_firstHitLayer (Y := Y) hY_iid a k).inter hEq_null
  have hEqUnion :
      (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ eqSet) = eqSet := by
    -- Proof comment: the same partition collapse works for the exact-hit terminal slice, because
    -- equality at time `n` implies the endpoint event `a ≤ partialSum Y n`.
    calc
      (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ eqSet)
        = (⋃ k ∈ hitLayers, firstHitLayer Y a k) ∩ eqSet := by
            ext ω
            constructor
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨i, hi, hiω, heqω⟩
              exact ⟨⟨i, hi, hiω⟩, heqω⟩
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨⟨i, hi, hiω⟩, heqω⟩
              exact ⟨i, hi, hiω, heqω⟩
      _ = hitSet ∩ eqSet := by
            simpa [hitLayers, hitSet] using
              congrArg (fun s : Set Ω ↦ s ∩ eqSet)
                (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n a)
      _ = eqSet := by
            apply Set.Subset.antisymm
            · exact Set.inter_subset_right
            · intro ω hω
              have hEq : partialSum Y n ω = a := by simpa [eqSet] using hω
              have hGe : a ≤ partialSum Y n ω := by rw [hEq]
              exact ⟨endpointGe_subset_oneSidedHitEvent (Y := Y) n a ha hGe, hω⟩
  have hEqMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ eqSet) = μ.real eqSet := by
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ eqSet)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y a k ∩ eqSet) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hEqLayerPairwise hEqLayerNull
      _ = μ.real eqSet := by rw [hEqUnion]
  -- Proof comment: sum the layerwise reflected bounds over the disjoint first-hit partition and
  -- collapse the two terminal sums back to the plain terminal events.
  calc
    μ.real (oneSidedHitEvent Y n a) = ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k) := by
      simpa [hitSet] using hHitMeasureSum.symm
    _ ≤ ∑ k ∈ hitLayers,
          (2 * μ.real (firstHitLayer Y a k ∩ geSet) -
            μ.real (firstHitLayer Y a k ∩ eqSet)) := by
            exact Finset.sum_le_sum fun k hk ↦
              firstHitLayer_reflectionBound (Y := Y) hY_iid hY_symm hk a
    _ = 2 * ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ geSet) -
          ∑ k ∈ hitLayers, μ.real (firstHitLayer Y a k ∩ eqSet) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * μ.real geSet - μ.real eqSet := by
          rw [hGeMeasureSum, hEqMeasureSum]
    _ = 2 * μ.real {ω | a ≤ partialSum Y n ω} -
          μ.real {ω | partialSum Y n ω = a} := by
            rfl

-- Proof sketch: in the nearest-neighbor case `Y_i ∈ {-1, 0, 1}` almost surely, the first hitting
-- time of a positive integer level lands exactly at that level, so the reflected path argument
-- from the inequality case becomes exact and yields equality.
/-- Helper for Theorem 17.15: identical distribution transports the `{-1, 0, 1}` support from
`Y 0` to every increment `Y i`. -/
private lemma increment_mem_negOneZeroOne_ae
    (hY_iid : IsIID Y μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    (i : ℕ) :
    ∀ᵐ ω ∂μ, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ) := by
  have hSet : MeasurableSet ({(-1 : ℝ), 0, 1} : Set ℝ) := by
    -- Proof comment: the three-point support set is finite, hence measurable.
    simp
  -- Proof comment: identical distribution transports the almost-sure support of `Y 0` to `Y i`.
  exact (hY_iid.identDistrib 0 i).ae_mem_snd hSet hY_step_support

/-- Helper for Theorem 17.15: almost every sample point has all increments in a fixed finite
prefix inside `{-1, 0, 1}`. -/
private lemma prefixIncrements_mem_negOneZeroOne_ae
    (hY_iid : IsIID Y μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range k, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ) := by
  induction k with
  | zero =>
      -- Proof comment: the empty prefix imposes no coordinate conditions.
      refine Filter.Eventually.of_forall fun ω i hi ↦ ?_
      have : False := by simpa using hi
      exact False.elim this
  | succ k hk =>
      -- Proof comment: append the almost sure support statement for the new last increment to the
      -- induction hypothesis on the shorter prefix.
      filter_upwards [hk, increment_mem_negOneZeroOne_ae (Y := Y) hY_iid hY_step_support k] with
        ω hPrefix hkLast i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) with rfl | hi_lt
      · simpa using hkLast
      · exact hPrefix i (Finset.mem_range.mpr hi_lt)

/-- Helper for Theorem 17.15: if the first `k` increments lie in `{-1, 0, 1}`, then the `k`th
partial sum is an integer. -/
private lemma partialSum_eq_intCast_of_stepPrefix {k : ℕ} {ω : Ω}
    (hSteps : ∀ i ∈ Finset.range k, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ)) :
    ∃ z : ℤ, partialSum Y k ω = z := by
  induction k with
  | zero =>
      -- Proof comment: the empty partial sum is the integer `0`.
      refine ⟨0, ?_⟩
      simp [partialSum]
  | succ k hk =>
      -- Proof comment: append the last step, which is one of `-1`, `0`, or `1`, to the integer
      -- representation of the shorter partial sum.
      have hPrefix : ∀ i ∈ Finset.range k, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ) := by
        intro i hi
        exact hSteps i (Finset.mem_range.mpr <|
          lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self k))
      obtain ⟨z, hz⟩ := hk hPrefix
      have hLast :
          Y k ω = (-1 : ℝ) ∨ Y k ω = 0 ∨ Y k ω = 1 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hSteps k (by simp)
      rcases hLast with hLast | hLast
      · refine ⟨z - 1, ?_⟩
        calc
          partialSum Y (k + 1) ω = partialSum Y k ω + Y k ω := by
            simp [partialSum, Finset.sum_range_succ]
          _ = (z : ℝ) + (-1 : ℝ) := by rw [hz, hLast]
          _ = ((z - 1 : ℤ) : ℝ) := by norm_num [sub_eq_add_neg]
      · rcases hLast with hLast | hLast
        · refine ⟨z, ?_⟩
          calc
            partialSum Y (k + 1) ω = partialSum Y k ω + Y k ω := by
              simp [partialSum, Finset.sum_range_succ]
            _ = (z : ℝ) + 0 := by rw [hz, hLast]
            _ = (z : ℝ) := by ring
        · refine ⟨z + 1, ?_⟩
          calc
            partialSum Y (k + 1) ω = partialSum Y k ω + Y k ω := by
              simp [partialSum, Finset.sum_range_succ]
            _ = (z : ℝ) + 1 := by rw [hz, hLast]
            _ = ((z + 1 : ℤ) : ℝ) := by norm_num

/-- Helper for Theorem 17.15: with `{-1, 0, 1}` increments, the first hit of a positive integer
level lands exactly on that level. -/
private lemma firstHitLayer_eq_natLevel_of_steps
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) {a : ℕ} (ha : 0 < a) {ω : Ω}
    (hSteps : ∀ i ∈ Finset.range k, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    (hLayer : ω ∈ firstHitLayer Y (a : ℝ) k) :
    partialSum Y k ω = (a : ℝ) := by
  rcases k with _ | k
  · cases (Nat.not_lt_zero _ (Finset.mem_Icc.mp hk).1)
  · -- Proof comment: compare the last jump with the previous integer-valued partial sum.
    have hsum : partialSum Y (k + 1) ω = partialSum Y k ω + Y k ω := by
      simp [partialSum, Finset.sum_range_succ]
    have hPrevLt : partialSum Y k ω < a := by
      by_cases hk_zero : k = 0
      · subst hk_zero
        simpa [partialSum] using (show (0 : ℝ) < a by exact_mod_cast ha)
      · have hk_pos : 0 < k := Nat.pos_iff_ne_zero.mpr hk_zero
        exact hLayer.1 k (Finset.mem_Icc.mpr ⟨hk_pos, le_rfl⟩)
    have hPrefix :
        ∀ i ∈ Finset.range k, Y i ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ) := by
      intro i hi
      exact hSteps i (Finset.mem_range.mpr <|
        lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self k))
    obtain ⟨z, hz⟩ := partialSum_eq_intCast_of_stepPrefix (Y := Y) hPrefix
    have hLast :
        Y k ω = (-1 : ℝ) ∨ Y k ω = 0 ∨ Y k ω = 1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hSteps k (by simp)
    rcases hLast with hLast | hLast
    · -- Proof comment: a final step of `-1` keeps the terminal sum below `a`, contradicting the
      -- hitting condition.
      have hImpossible : partialSum Y (k + 1) ω < a := by
        rw [hsum, hLast]
        linarith
      exact (not_lt_of_ge hLayer.2 hImpossible).elim
    · rcases hLast with hLast | hLast
      · -- Proof comment: a final step of `0` also leaves the terminal sum below `a`.
        have hImpossible : partialSum Y (k + 1) ω < a := by
          rw [hsum, hLast]
          linarith
        exact (not_lt_of_ge hLayer.2 hImpossible).elim
      · -- Proof comment: the final step must therefore be `1`, and the previous partial sum is an
        -- integer in the interval `(a - 1, a)`, hence exactly `a - 1`.
        have hz_lt : z < a := by
          exact_mod_cast (show (z : ℝ) < a by simpa [hz] using hPrevLt)
        have ha_le : (a : ℤ) ≤ z + 1 := by
          exact_mod_cast (show (a : ℝ) ≤ (z : ℝ) + 1 by simpa [hsum, hz, hLast] using hLayer.2)
        have hz_plus : z + 1 = a := by
          omega
        calc
          partialSum Y (k + 1) ω = (z : ℝ) + 1 := by rw [hsum, hz, hLast]
          _ = ((z + 1 : ℤ) : ℝ) := by norm_num
          _ = (a : ℝ) := by exact_mod_cast hz_plus

/-- Helper for Theorem 17.15: almost every path in a first-hit layer of a positive integer level
hits that level exactly. -/
private lemma firstHitLayer_eq_natLevel_ae_of_steps
    (hY_iid : IsIID Y μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℕ) (ha : 0 < a) :
    ∀ᵐ ω ∂μ, ω ∈ firstHitLayer Y (a : ℝ) k → partialSum Y k ω = (a : ℝ) := by
  -- Proof comment: on the almost-sure event where the first `k` increments all lie in
  -- `{-1, 0, 1}`, the deterministic exact-hit lemma applies pointwise on the first-hit layer.
  filter_upwards [prefixIncrements_mem_negOneZeroOne_ae (Y := Y) hY_iid hY_step_support k] with
    ω hSteps hLayer
  exact firstHitLayer_eq_natLevel_of_steps (Y := Y) hk ha hSteps hLayer

/-- Helper for Theorem 17.15: in the `{-1, 0, 1}` case, reflecting the tail of a fixed first-hit
layer matches the strict-above and strict-below endpoint events exactly. -/
private lemma firstHitLayer_reflectionBelow_eq_above_of_steps
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℕ) (ha : 0 < a) :
    μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | partialSum Y n ω < a}) =
      μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | (a : ℝ) < partialSum Y n ω}) := by
  have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hPairLaw :
      IdentDistrib (prefixTailPair (Y := Y) n k) (reflectedPrefixTailPair (Y := Y) n k) μ μ :=
    prefixTailSumPair_identDistrib_reflect (Y := Y) hY_iid hY_symm hk_le
  have hReflectedMem :
      ∀ᵐ ω ∂μ,
        ω ∈ reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k (a : ℝ) ↔
          ω ∈ firstHitLayer Y (a : ℝ) k ∩ {ω | (a : ℝ) < partialSum Y n ω} := by
    -- Proof comment: on the a.e. event where the first hit lands exactly at the integer level,
    -- the forward and reverse reflected endpoint transports become equivalent.
    filter_upwards
      [firstHitLayer_eq_natLevel_ae_of_steps (Y := Y) hY_iid hY_step_support hk a ha] with
        ω hExact
    constructor
    · intro hω
      exact
        reflectedPrefixTailPair_preimage_firstHitTerminalBelowSet_subset_above
          (Y := Y) hk_le (a : ℝ) hω
    · intro hω
      exact above_mem_reflectedPrefixTailPair_preimage_firstHitTerminalBelowSet_of_exactHit
        (Y := Y) hk_le hω.1 (hExact hω.1) hω.2
  -- Proof comment: compare both endpoint events through the reflected pair-space event and then
  -- upgrade the inclusion to equality using the exact-hit lemma above.
  calc
    μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | partialSum Y n ω < a}) =
        μ.real (prefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k (a : ℝ)) := by
          rw [prefixTailPair_preimage_firstHitTerminalBelowSet (Y := Y) hk_le (a : ℝ)]
    _ = μ.real (reflectedPrefixTailPair (Y := Y) n k ⁻¹' firstHitTerminalBelowSet k (a : ℝ)) := by
          simpa [Measure.real] using congrArg ENNReal.toReal <|
            hPairLaw.measure_mem_eq (measurableSet_firstHitTerminalBelowSet k (a : ℝ))
    _ = μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | (a : ℝ) < partialSum Y n ω}) := by
          apply MeasureTheory.measureReal_congr
          filter_upwards [hReflectedMem] with ω hω
          exact propext hω

/-- Helper for Theorem 17.15: in the `{-1,0,1}` case, each first-hit layer satisfies the exact
reflected endpoint identity that sums to the equality version of the reflection principle. -/
private lemma firstHitLayer_reflectionEqBound_of_steps
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℕ) (ha : 0 < a) :
    μ.real (firstHitLayer Y (a : ℝ) k) =
      2 * μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | (a : ℝ) ≤ partialSum Y n ω}) -
        μ.real (firstHitLayer Y (a : ℝ) k ∩ {ω | partialSum Y n ω = (a : ℝ)}) := by
  let layerSet : Set Ω := firstHitLayer Y (a : ℝ) k
  let geSet : Set Ω := {ω | (a : ℝ) ≤ partialSum Y n ω}
  let ltSet : Set Ω := {ω | partialSum Y n ω < a}
  let eqSet : Set Ω := {ω | partialSum Y n ω = (a : ℝ)}
  have hTerminalLt_null : NullMeasurableSet ltSet μ := by
    -- Proof comment: the terminal `< a` event is null measurable.
    simpa [ltSet] using
      nullMeasurableSet_lt (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hTerminalEq_null : NullMeasurableSet eqSet μ := by
    -- Proof comment: the terminal exact-hit event is null measurable as an equality set.
    simpa [eqSet] using
      nullMeasurableSet_eq_fun (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hSplitBelow :
      μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) = μ.real layerSet := by
    have hBase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μ) (s := layerSet) hTerminalLt_null
    rw [(firstHitLayer_terminalPartition (Y := Y) (n := n) (k := k) (a : ℝ)).1] at hBase
    simpa [layerSet, ltSet, geSet] using hBase
  have hSplitEq :
      μ.real (layerSet ∩ {ω | (a : ℝ) < partialSum Y n ω}) + μ.real (layerSet ∩ eqSet) =
        μ.real (layerSet ∩ geSet) := by
    have hBase :=
      MeasureTheory.measureReal_inter_add_diff₀ (μ := μ) (s := layerSet ∩ geSet) hTerminalEq_null
    rw [(firstHitLayer_terminalPartition (Y := Y) (n := n) (k := k) (a : ℝ)).2] at hBase
    have hEqInter : layerSet ∩ geSet ∩ eqSet = layerSet ∩ eqSet := by
      ext ω
      constructor
      · rintro ⟨⟨hLayer, hGe⟩, hEq⟩
        exact ⟨hLayer, hEq⟩
      · rintro ⟨hLayer, hEq⟩
        have hGe : (a : ℝ) ≤ partialSum Y n ω := by
          rw [hEq]
        exact ⟨⟨hLayer, hGe⟩, hEq⟩
    rw [hEqInter, add_comm] at hBase
    simpa [layerSet, geSet, eqSet] using hBase
  have hReflect :
      μ.real (layerSet ∩ ltSet) =
        μ.real (layerSet ∩ {ω | (a : ℝ) < partialSum Y n ω}) := by
    simpa [layerSet, ltSet] using
      firstHitLayer_reflectionBelow_eq_above_of_steps
        (Y := Y) hY_iid hY_symm hY_step_support hk a ha
  have hAboveEq :
      μ.real (layerSet ∩ {ω | (a : ℝ) < partialSum Y n ω}) =
        μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet) := by
    linarith [hSplitEq]
  have hLayerEq :
      μ.real layerSet = μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) := by
    linarith [hSplitBelow]
  -- Proof comment: substitute the exact reflected equality on the strict-below slice and the same
  -- terminal partition algebra as in the inequality case.
  calc
    μ.real (firstHitLayer Y (a : ℝ) k) = μ.real layerSet := by rfl
    _ = μ.real (layerSet ∩ ltSet) + μ.real (layerSet ∩ geSet) := hLayerEq
    _ = μ.real (layerSet ∩ {ω | (a : ℝ) < partialSum Y n ω}) +
          μ.real (layerSet ∩ geSet) := by rw [hReflect]
    _ = (μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet)) +
          μ.real (layerSet ∩ geSet) := by rw [hAboveEq]
    _ = 2 * μ.real (layerSet ∩ geSet) - μ.real (layerSet ∩ eqSet) := by ring

/-- Theorem 17.15 (2): if the common increment law is supported on `{-1, 0, 1}` almost surely,
then the reflection-principle bound is sharp for positive integer levels. -/
theorem reflectionPrinciple_partialSum_eq_of_steps_mem_neg_one_zero_one
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    (n : ℕ) (a : ℕ) (ha : 0 < a) :
    μ.real (oneSidedHitEvent Y n a) =
      2 * μ.real {ω | (a : ℝ) ≤ partialSum Y n ω} -
        μ.real {ω | partialSum Y n ω = (a : ℝ)} := by
  let hitLayers : Finset ℕ := Finset.Icc 1 n
  let hitSet : Set Ω := oneSidedHitEvent Y n (a : ℝ)
  let geSet : Set Ω := {ω | (a : ℝ) ≤ partialSum Y n ω}
  let eqSet : Set Ω := {ω | partialSum Y n ω = (a : ℝ)}
  have hGe_null : NullMeasurableSet geSet μ := by
    -- Proof comment: the terminal threshold event remains null measurable in the step-supported
    -- branch.
    simpa [geSet] using
      nullMeasurableSet_le aemeasurable_const (partialSumAEMeasurable (Y := Y) hY_iid n)
  have hEq_null : NullMeasurableSet eqSet μ := by
    -- Proof comment: the terminal exact-hit slice is again an equality event for the terminal
    -- partial sum.
    simpa [eqSet] using
      nullMeasurableSet_eq_fun (partialSumAEMeasurable (Y := Y) hY_iid n) aemeasurable_const
  have hLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y (a : ℝ) i) (firstHitLayer Y (a : ℝ) j) := by
    intro k hk l hl hkl
    exact (firstHitLayer_disjoint (Y := Y) hk hl hkl (a : ℝ)).aedisjoint
  have hLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y (a : ℝ) k) μ := by
    intro k hk
    exact nullMeasurableSet_firstHitLayer (Y := Y) hY_iid (a : ℝ) k
  have hHitMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k) = μ.real hitSet := by
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hLayerPairwise hLayerNull
      _ = μ.real hitSet := by
            simpa [hitLayers, hitSet] using congrArg (Measure.real (μ := μ))
              (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n (a : ℝ))
  have hGeLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y (a : ℝ) i ∩ geSet)
          (firstHitLayer Y (a : ℝ) j ∩ geSet) := by
    intro k hk l hl hkl
    exact (Disjoint.mono Set.inter_subset_left Set.inter_subset_left <|
      firstHitLayer_disjoint (Y := Y) hk hl hkl (a : ℝ)).aedisjoint
  have hGeLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y (a : ℝ) k ∩ geSet) μ := by
    intro k hk
    exact (nullMeasurableSet_firstHitLayer (Y := Y) hY_iid (a : ℝ) k).inter hGe_null
  have hGeUnion :
      (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ geSet) = geSet := by
    calc
      (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ geSet)
        = (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k) ∩ geSet := by
            ext ω
            constructor
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨i, hi, hiω, hgeω⟩
              exact ⟨⟨i, hi, hiω⟩, hgeω⟩
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨⟨i, hi, hiω⟩, hgeω⟩
              exact ⟨i, hi, hiω, hgeω⟩
      _ = hitSet ∩ geSet := by
            simpa [hitLayers, hitSet] using
              congrArg (fun s : Set Ω ↦ s ∩ geSet)
                (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n (a : ℝ))
      _ = geSet := by
            apply Set.Subset.antisymm
            · exact Set.inter_subset_right
            · intro ω hω
              exact ⟨endpointGe_subset_oneSidedHitEvent (Y := Y) n (a : ℝ)
                (by exact_mod_cast ha) hω, hω⟩
  have hGeMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ geSet) = μ.real geSet := by
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ geSet)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ geSet) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hGeLayerPairwise hGeLayerNull
      _ = μ.real geSet := by rw [hGeUnion]
  have hEqLayerPairwise :
      Set.Pairwise (↑hitLayers) fun i j ↦
        AEDisjoint μ (firstHitLayer Y (a : ℝ) i ∩ eqSet)
          (firstHitLayer Y (a : ℝ) j ∩ eqSet) := by
    intro k hk l hl hkl
    exact (Disjoint.mono Set.inter_subset_left Set.inter_subset_left <|
      firstHitLayer_disjoint (Y := Y) hk hl hkl (a : ℝ)).aedisjoint
  have hEqLayerNull :
      ∀ k ∈ hitLayers, NullMeasurableSet (firstHitLayer Y (a : ℝ) k ∩ eqSet) μ := by
    intro k hk
    exact (nullMeasurableSet_firstHitLayer (Y := Y) hY_iid (a : ℝ) k).inter hEq_null
  have hEqUnion :
      (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ eqSet) = eqSet := by
    calc
      (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ eqSet)
        = (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k) ∩ eqSet := by
            ext ω
            constructor
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨i, hi, hiω, heqω⟩
              exact ⟨⟨i, hi, hiω⟩, heqω⟩
            · intro hω
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
              rcases hω with ⟨⟨i, hi, hiω⟩, heqω⟩
              exact ⟨i, hi, hiω, heqω⟩
      _ = hitSet ∩ eqSet := by
            simpa [hitLayers, hitSet] using
              congrArg (fun s : Set Ω ↦ s ∩ eqSet)
                (oneSidedHitEvent_eq_biUnion_firstHitLayer (Y := Y) n (a : ℝ))
      _ = eqSet := by
            apply Set.Subset.antisymm
            · exact Set.inter_subset_right
            · intro ω hω
              have hEq : partialSum Y n ω = (a : ℝ) := by simpa [eqSet] using hω
              have hGe : (a : ℝ) ≤ partialSum Y n ω := by rw [hEq]
              exact ⟨endpointGe_subset_oneSidedHitEvent (Y := Y) n (a : ℝ)
                (by exact_mod_cast ha) hGe, hω⟩
  have hEqMeasureSum :
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ eqSet) = μ.real eqSet := by
    calc
      ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ eqSet)
        = μ.real (⋃ k ∈ hitLayers, firstHitLayer Y (a : ℝ) k ∩ eqSet) := by
            symm
            exact MeasureTheory.measureReal_biUnion_finset₀ hEqLayerPairwise hEqLayerNull
      _ = μ.real eqSet := by rw [hEqUnion]
  -- Proof comment: sum the exact layerwise reflection identities over the disjoint partition and
  -- collapse the resulting terminal sums as in the inequality case.
  calc
    μ.real (oneSidedHitEvent Y n a) = ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k) := by
      simpa [hitSet] using hHitMeasureSum.symm
    _ = ∑ k ∈ hitLayers,
          (2 * μ.real (firstHitLayer Y (a : ℝ) k ∩ geSet) -
            μ.real (firstHitLayer Y (a : ℝ) k ∩ eqSet)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact firstHitLayer_reflectionEqBound_of_steps
              (Y := Y) hY_iid hY_symm hY_step_support hk a ha
    _ = 2 * ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ geSet) -
          ∑ k ∈ hitLayers, μ.real (firstHitLayer Y (a : ℝ) k ∩ eqSet) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * μ.real geSet - μ.real eqSet := by
          rw [hGeMeasureSum, hEqMeasureSum]
    _ = 2 * μ.real {ω | (a : ℝ) ≤ partialSum Y n ω} -
          μ.real {ω | partialSum Y n ω = (a : ℝ)} := by
            rfl

end

end ProbabilityTheory
