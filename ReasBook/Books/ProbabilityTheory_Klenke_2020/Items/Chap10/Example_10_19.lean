/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.BorelCantelli
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open unitInterval

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

private noncomputable def biasedRademacherPMF (p : unitInterval) : PMF ℤ :=
  (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).map (fun b ↦ cond b (1 : ℤ) (-1))

/-- The biased Rademacher law on `ℤ` that assigns mass `p` to `1` and mass `1 - p` to `-1`. -/
def biasedRademacherLaw (p : ℝ) : Measure ℤ :=
  (ENNReal.ofReal p • Measure.dirac (1 : ℤ)) +
    (ENNReal.ofReal (1 - p) • Measure.dirac (-1 : ℤ))

-- Proof sketch: rewrite the two-point `ℤ`-valued law as the pushforward of the canonical
-- Bernoulli PMF along `Bool → ℤ`, `true ↦ 1`, `false ↦ -1`.
private theorem biasedRademacherLaw_eq_biasedRademacherPMF_toMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    biasedRademacherLaw p = (biasedRademacherPMF ⟨p, hp0, hp1⟩).toMeasure := by
  let pu : unitInterval := ⟨p, hp0, hp1⟩
  -- Proof comment: both measures live on the countable space `ℤ`, so singleton masses determine
  -- the law completely.
  refine Measure.ext_of_singleton ?_
  intro z
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  by_cases hz1 : z = 1
  · subst hz1
    -- Proof comment: the mass at `1` is the Bernoulli success probability.
    simp [biasedRademacherLaw, biasedRademacherPMF, PMF.map_apply, PMF.bernoulli_apply, pu]
    simpa [pu, unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp0)
  · by_cases hzm1 : z = -1
    · subst hzm1
      -- Proof comment: the mass at `-1` is the complementary Bernoulli probability.
      have hcoe : ENNReal.ofNNReal (toNNReal pu) = ENNReal.ofReal p := by
        simpa [pu, unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp0).symm
      simp [biasedRademacherLaw, biasedRademacherPMF, PMF.map_apply, PMF.bernoulli_apply, pu, hz1]
      calc
        ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
          simpa using (ENNReal.ofReal_sub 1 hp0)
        _ = 1 - ENNReal.ofNNReal (toNNReal pu) := by rw [hcoe]
    · -- Proof comment: away from the two support points, both laws assign zero mass.
      have hz1' : (1 : ℤ) ≠ z := by simpa [eq_comm] using hz1
      have hzm1' : (-1 : ℤ) ≠ z := by simpa [eq_comm] using hzm1
      have hpmf_zero : biasedRademacherPMF pu z = 0 := by
        rw [biasedRademacherPMF, PMF.map_apply]
        apply ENNReal.tsum_eq_zero.2
        intro b
        cases b <;> simp [hz1, hzm1]
      simp [biasedRademacherLaw, hz1', hzm1']
      simpa [pu] using hpmf_zero.symm

-- Proof sketch: both Dirac summands are finite probability fragments with weights `p` and `1-p`;
-- when `0 ≤ p ≤ 1`, these nonnegative weights sum to `1`.
/-- The biased Rademacher law is a probability measure whenever `p ∈ [0, 1]`. -/
theorem biasedRademacherLaw_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (biasedRademacherLaw p) := by
  simpa [biasedRademacherLaw_eq_biasedRademacherPMF_toMeasure hp0 hp1] using
    (show IsProbabilityMeasure ((biasedRademacherPMF ⟨p, hp0, hp1⟩).toMeasure) from inferInstance)

/-- The ratio `r = (1 - p) / p` appearing in the exponential martingale for the biased gambler's
ruin walk. -/
def gamblerRuinRatio (p : ℝ) : ℝ :=
  (1 - p) / p

/-- Helper for Example 10.19: translating a walk by a constant translates the two-point hitting
time by the same constant. -/
private lemma hittingAfter_add_const_pair_eq
    {u : ℕ → Ω → ℤ} {ω : Ω} {c a b : ℤ} :
    hittingAfter (fun n ω' ↦ c + u n ω') ({c + a, c + b} : Set ℤ) 0 ω =
      hittingAfter u ({a, b} : Set ℤ) 0 ω := by
  -- Proof comment: rewrite both hitting times through `hittingAfter_def`; after translating the
  -- target set back by `c`, the existence condition and the infimum set coincide exactly.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ (c + u j ω) ∈ ({c + a, c + b} : Set ℤ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, add_left_inj] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, add_left_inj] using hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ (c + u i ω) ∈ ({c + a, c + b} : Set ℤ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({a, b} : Set ℤ)} := by
    ext i
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, add_left_inj]
  by_cases hu : ∃ j, 0 ≤ j ∧ (c + u j ω) ∈ ({c + a, c + b} : Set ℤ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({a, b} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.19: the same translation invariance holds for singleton hitting times. -/
private lemma hittingAfter_add_const_singleton_eq
    {u : ℕ → Ω → ℤ} {ω : Ω} {c a : ℤ} :
    hittingAfter (fun n ω' ↦ c + u n ω') ({c + a} : Set ℤ) 0 ω =
      hittingAfter u ({a} : Set ℤ) 0 ω := by
  -- Proof comment: this is the singleton companion to the pair translation lemma, with the same
  -- `hittingAfter_def` normalization.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ (c + u j ω) ∈ ({c + a} : Set ℤ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_singleton_iff, add_left_inj] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        simpa [Set.mem_singleton_iff, add_left_inj] using hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ (c + u i ω) ∈ ({c + a} : Set ℤ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({a} : Set ℤ)} := by
    ext i
    simp [Set.mem_singleton_iff, add_left_inj]
  by_cases hu : ∃ j, 0 ≤ j ∧ (c + u j ω) ∈ ({c + a} : Set ℤ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({a} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.19: a variable with the biased Rademacher law has the expected singleton
atom masses at `1` and `-1`. -/
private lemma hasLaw_biasedRademacher_preimage_singletons
    {P : Measure Ω} {Y : Ω → ℤ} {p : ℝ}
    (hY : HasLaw Y (biasedRademacherLaw p) P) :
    P (Y ⁻¹' {(1 : ℤ)}) = ENNReal.ofReal p ∧
      P (Y ⁻¹' {(-1 : ℤ)}) = ENNReal.ofReal (1 - p) := by
  constructor
  · -- Proof comment: transport the singleton mass through the pushforward equality `map Y P = μ_Y`.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (1 : ℤ))]
    rw [hY.map_eq]
    simp [biasedRademacherLaw]
  · -- Proof comment: the same pushforward rewrite computes the complementary mass at `-1`.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (-1 : ℤ))]
    rw [hY.map_eq]
    simp [biasedRademacherLaw]

/-- Helper for Example 10.19: under the biased Rademacher law, the walk increments are almost
surely supported on `{-1, 1}`. -/
private lemma hasLaw_biasedRademacher_ae_eq_pm_one
    {P : Measure Ω} {Y : Ω → ℤ} {p : ℝ}
    (hY : HasLaw Y (biasedRademacherLaw p) P) :
    ∀ᵐ ω ∂P, Y ω = -1 ∨ Y ω = 1 := by
  -- Proof comment: the complement of the two-point support has zero mass after pushing forward to
  -- `biasedRademacherLaw`, because that law is supported exactly on `{-1, 1}`.
  rw [ae_iff]
  change P (Y ⁻¹' (({(-1 : ℤ), (1 : ℤ)} : Set ℤ)ᶜ)) = 0
  rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable]
  · rw [hY.map_eq]
    simp [biasedRademacherLaw, Set.mem_insert_iff, Set.mem_singleton_iff]
  · exact ((measurableSet_singleton (-1 : ℤ)).insert (1 : ℤ)).compl

/-- Helper for Example 10.19: the `m`th length-`N` block event on which every increment equals
`1`. This is the block event used to force exit from the finite interval. -/
private def allPlusBlockEvent (Y : ℕ → Ω → ℤ) (N m : ℕ) : Set Ω :=
  ⋂ j : Fin N, Y (m * N + j) ⁻¹' {(1 : ℤ)}

/-- Helper for Example 10.19: the all-`+1` block event is measurable as a finite intersection of
singleton cylinder events. -/
private lemma allPlusBlockEvent_measurable
    {Y : ℕ → Ω → ℤ} (N m : ℕ) (hY_meas : ∀ n, Measurable (Y n)) :
    MeasurableSet (allPlusBlockEvent Y N m) := by
  -- Proof comment: each block coordinate event `{Y_{mN+j} = 1}` is measurable, so the finite
  -- intersection over `j : Fin N` is measurable as well.
  classical
  refine MeasurableSet.iInter ?_
  intro j
  exact (hY_meas (m * N + j)) (measurableSet_singleton (1 : ℤ))

/-- Helper for Example 10.19: independence of the increments makes the all-`+1` block probability
factor as the product of the singleton `+1` masses across the block. -/
private lemma allPlusBlockEvent_prob_eq_prod
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} (N m : ℕ)
    (hY_indep : iIndepFun Y P) :
    P (allPlusBlockEvent Y N m) =
      ∏ j : Fin N, P (Y (m * N + j) ⁻¹' {(1 : ℤ)}) := by
  classical
  let Yblock : Fin N → Ω → ℤ := fun j ↦ Y (m * N + j)
  have hYblock_indep : iIndepFun Yblock P := by
    -- Proof comment: a single block just reindexes the original independent increments by the
    -- injective map `j ↦ m * N + j`.
    refine hY_indep.precomp ?_
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  -- Proof comment: once the block is viewed as an independent `Fin N`-indexed family, the event
  -- `{Y_{mN} = 1, …, Y_{mN+N-1} = 1}` is exactly the standard finite preimage intersection.
  simpa [allPlusBlockEvent, Yblock] using
    hYblock_indep.measure_inter_preimage_eq_mul
      (Finset.univ : Finset (Fin N))
      (fun j _ ↦ measurableSet_singleton (1 : ℤ))

/-- Helper for Example 10.19: for biased Rademacher increments, every all-`+1` block has
probability `p^N`. -/
private lemma allPlusBlockEvent_prob_eq_pow
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℤ} {p : ℝ} (N m : ℕ)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    P (allPlusBlockEvent Y N m) = (ENNReal.ofReal p) ^ N := by
  -- Proof comment: the block product formula reduces the probability to a constant product, since
  -- every increment has the same `+1` singleton mass `p`.
  rw [allPlusBlockEvent_prob_eq_prod N m hY_indep]
  have hmass : ∀ j : Fin N, P (Y (m * N + j) ⁻¹' {(1 : ℤ)}) = ENNReal.ofReal p := by
    intro j
    exact (hasLaw_biasedRademacher_preimage_singletons (hY_law (m * N + j))).1
  simp [hmass]

/-- Helper for Example 10.19: the all-`+1` block event is the preimage of the all-ones block map
on `Fin N`. -/
private lemma allPlusBlockEvent_eq_blockPreimage
    {Y : ℕ → Ω → ℤ} (N m : ℕ) :
    allPlusBlockEvent Y N m =
      (fun ω ↦ fun j : Fin N ↦ Y (m * N + (j : ℕ)) ω) ⁻¹' {f | ∀ j, f j = (1 : ℤ)} := by
  -- Proof comment: both sides say exactly that each coordinate in the length-`N` block equals
  -- `1`; the right-hand side just packages those coordinates into one `Fin N → ℤ` random variable.
  ext ω
  simp [allPlusBlockEvent]

/-- Helper for Example 10.19: the nonoverlapping all-`+1` block events form an independent family.
This is the Borel-Cantelli input used to force finite exit from the interval `{0, …, N}`. -/
private lemma iIndepSet_allPlusBlockEvent
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} (N : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P) :
    iIndepSet (allPlusBlockEvent Y N) P := by
  classical
  let blockIndexSet : ℕ → Set ℕ := fun m ↦ (Finset.Ico (m * N) (m * N + N) : Set ℕ)
  have h_disjoint : Pairwise fun m n : ℕ ↦ Disjoint (blockIndexSet m) (blockIndexSet n) := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact Set.disjoint_left.2 <| by
        intro x hxM hxN
        have hxM' : m * N ≤ x ∧ x < m * N + N := by
          simpa [blockIndexSet, Finset.mem_Ico] using hxM
        have hxN' : n * N ≤ x ∧ x < n * N + N := by
          simpa [blockIndexSet, Finset.mem_Ico] using hxN
        have hsep : m * N + N ≤ n * N := by
          calc
            m * N + N = (m + 1) * N := by rw [Nat.succ_mul]
            _ ≤ n * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
        exact not_lt_of_ge (le_trans hsep hxN'.1) hxM'.2
    · exact Set.disjoint_left.2 <| by
        intro x hxM hxN
        have hxM' : m * N ≤ x ∧ x < m * N + N := by
          simpa [blockIndexSet, Finset.mem_Ico] using hxM
        have hxN' : n * N ≤ x ∧ x < n * N + N := by
          simpa [blockIndexSet, Finset.mem_Ico] using hxN
        have hsep : n * N + N ≤ m * N := by
          calc
            n * N + N = (n + 1) * N := by rw [Nat.succ_mul]
            _ ≤ m * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hgt)
        exact not_lt_of_ge (le_trans hsep hxM'.1) hxN'.2
  let blockPullback : ∀ m : ℕ, ({n // n ∈ blockIndexSet m} → ℤ) → Fin N → ℤ := fun m f j ↦
    f ⟨m * N + (j : ℕ), by
      change m * N + (j : ℕ) ∈ (Finset.Ico (m * N) (m * N + N) : Set ℕ)
      simpa [blockIndexSet, Finset.mem_Ico, j.2]⟩
  have h_subblocks :
      iIndepFun (fun m ω (j : blockIndexSet m) ↦ Y j.1 ω) P := by
    simpa using
      (iIndepFun_block_of_pairwise_disjoint_blocks P Y blockIndexSet h_disjoint hY_indep hY_meas)
  have h_blocks :
      iIndepFun (fun m ω ↦ blockPullback m (fun j : blockIndexSet m ↦ Y j.1 ω)) P := by
    have h_blockPullback_meas : ∀ m, Measurable (blockPullback m) := by
      intro m
      -- Proof comment: `blockPullback` just evaluates a subtype-indexed block function on the
      -- canonical coordinates `m * N + j`, so each coordinate map is measurable.
      exact measurable_pi_lambda _ fun j ↦
        let hj : {n // n ∈ blockIndexSet m} := ⟨m * N + (j : ℕ), by
          change m * N + (j : ℕ) ∈ (Finset.Ico (m * N) (m * N + N) : Set ℕ)
          simpa [blockIndexSet, Finset.mem_Ico, j.2]⟩
        (measurable_pi_apply hj :
          Measurable fun f : {n // n ∈ blockIndexSet m} → ℤ ↦ f hj)
    exact h_subblocks.comp blockPullback h_blockPullback_meas
  have h_blocks_eq :
      ∀ m : ℕ, ∀ ω,
        blockPullback m (fun j : blockIndexSet m ↦ Y j.1 ω) =
          fun j : Fin N ↦ Y (m * N + (j : ℕ)) ω := by
    intro m ω
    ext j
    simp [blockPullback]
  let A : Set (Fin N → ℤ) := {f | ∀ j, f j = (1 : ℤ)}
  have hA_meas : MeasurableSet A := by
    -- Proof comment: the all-ones block cylinder is the intersection of the measurable singleton
    -- cylinders of each `Fin N` coordinate.
    have hA_eq :
        A = ⋂ j : Fin N, (Function.eval j) ⁻¹' ({(1 : ℤ)} : Set ℤ) := by
      ext f
      simp [A]
    rw [hA_eq]
    exact MeasurableSet.iInter fun j : Fin N ↦
      (measurable_pi_apply j) (measurableSet_singleton (1 : ℤ))
  refine (ProbabilityTheory.iIndepSet_iff_meas_biInter ?_).2 ?_
  · intro m
    exact allPlusBlockEvent_measurable N m hY_meas
  · intro s
    -- Route correction: instead of forcing a brittle arithmetic normalization over
    -- `(m, j) ↦ m * N + j`, pass to disjoint `Ico` blocks and then pull them back to `Fin N`.
    simpa [A, allPlusBlockEvent_eq_blockPreimage, h_blocks_eq] using
      h_blocks.measure_inter_preimage_eq_mul s (fun _ _ ↦ hA_meas)

/-- Helper for Example 10.19: because each nonoverlapping all-`+1` block has the same positive
probability, Borel-Cantelli gives that such blocks occur infinitely often almost surely. -/
private lemma ae_mem_limsup_allPlusBlockEvent
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℤ} {p : ℝ} (N : ℕ)
    (hp0 : 0 < p)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    ∀ᵐ ω ∂P, ω ∈ Filter.limsup (allPlusBlockEvent Y N) Filter.atTop := by
  have h_meas : ∀ m, MeasurableSet (allPlusBlockEvent Y N m) := by
    intro m
    exact allPlusBlockEvent_measurable N m hY_meas
  have h_indep : iIndepSet (allPlusBlockEvent Y N) P :=
    iIndepSet_allPlusBlockEvent N hY_meas hY_indep
  have hp_nonzero : ENNReal.ofReal p ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 hp0
  have h_blockProb : ∀ m : ℕ, P (allPlusBlockEvent Y N m) = (ENNReal.ofReal p) ^ N := by
    intro m
    exact allPlusBlockEvent_prob_eq_pow N m hY_indep hY_law
  have htsum :
      (∑' m : ℕ, P (allPlusBlockEvent Y N m)) = ⊤ := by
    -- Proof comment: every block has the same positive mass `p^N`, so the event series is a
    -- nonzero constant `ENNReal` series and therefore diverges to `⊤`.
    simp [h_blockProb, ENNReal.tsum_const_eq_top_of_ne_zero, hp_nonzero]
  have h_limsup :
      P (Filter.limsup (allPlusBlockEvent Y N) Filter.atTop) = 1 := by
    simpa using
      ProbabilityTheory.measure_limsup_eq_one h_meas h_indep htsum
  have h_meas_limsup :
      MeasurableSet (Filter.limsup (allPlusBlockEvent Y N) Filter.atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    refine MeasurableSet.iInter ?_
    intro n
    refine MeasurableSet.iUnion ?_
    intro m
    refine MeasurableSet.iUnion ?_
    intro _
    simpa using h_meas m
  rw [ae_iff]
  have h_fin : P (Filter.limsup (allPlusBlockEvent Y N) Filter.atTop) ≠ ⊤ := by
    rw [h_limsup]
    simp
  -- Proof comment: the limsup event has full measure, so its complement has measure zero.
  simpa [h_limsup, IsProbabilityMeasure.measure_univ] using
    measure_compl h_meas_limsup h_fin

/-- Helper for Example 10.19: on an all-`+1` block, the walk gains exactly `j` units over the
block prefix. -/
private lemma randomWalkProcess_eq_add_on_allPlusBlockEvent
    {Y : ℕ → Ω → ℤ} {N m j : ℕ} {ω : Ω}
    (hj : j ≤ N) (hblock : ω ∈ allPlusBlockEvent Y N m) :
    randomWalkProcess Y (m * N + j) ω = randomWalkProcess Y (m * N) ω + j := by
  induction j with
  | zero =>
      -- Proof comment: the block gain over a prefix of length `0` is zero.
      simp
  | succ j ih =>
      have hj' : j ≤ N := Nat.le_of_succ_le hj
      have hjlt : j < N := Nat.lt_of_succ_le hj
      have hplus : Y (m * N + j) ω = 1 := by
        have hmem :
            ω ∈ Y (m * N + (⟨j, hjlt⟩ : Fin N)) ⁻¹' ({(1 : ℤ)} : Set ℤ) :=
          Set.mem_iInter.mp hblock ⟨j, hjlt⟩
        simpa using hmem
      have hinc :
          randomWalkProcess Y (m * N + j + 1) ω =
            randomWalkProcess Y (m * N + j) ω + Y (m * N + j) ω := by
        have hinc' := randomWalkProcess_increment Y (m * N + j) ω
        omega
      -- Proof comment: append one more `+1` increment to the already-normalized prefix.
      have hstep :
          randomWalkProcess Y (m * N + j + 1) ω =
            randomWalkProcess Y (m * N) ω + ((j + 1 : ℕ) : ℤ) := by
        calc
          randomWalkProcess Y (m * N + j + 1) ω =
              randomWalkProcess Y (m * N + j) ω + Y (m * N + j) ω := hinc
          _ = randomWalkProcess Y (m * N) ω + (j : ℤ) + 1 := by
            rw [ih hj', hplus]
          _ = randomWalkProcess Y (m * N) ω + ((j + 1 : ℕ) : ℤ) := by
            omega
      simpa using hstep

/-- Helper for Example 10.19: once a length-`N` all-`+1` block appears, the gambler's-ruin walk
hits `{0, N}` no later than the end of that block. -/
private lemma hittingAfter_le_blockEnd_of_mem_allPlusBlockEvent
    {Y : ℕ → Ω → ℤ} {kB N m : ℕ} {ω : Ω}
    (hN : 0 < N) (hkB : kB ≤ N)
    (hYsigns : ∀ n, Y n ω = -1 ∨ Y n ω = 1)
    (hblock : ω ∈ allPlusBlockEvent Y N m) :
    hittingAfter (fun n ω' ↦ (kB : ℤ) + randomWalkProcess Y n ω')
      ({0, (N : ℤ)} : Set ℤ) 0 ω ≤ m * N + N := by
  let X : ℕ → Ω → ℤ := fun n ω' ↦ (kB : ℤ) + randomWalkProcess Y n ω'
  by_cases hkB_zero : kB = 0
  · -- Proof comment: if B already starts at `0`, the boundary is hit at time `0`.
    have hmem0 : X 0 ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
      have hzero : randomWalkProcess Y 0 ω = 0 := by
        simpa using congrFun (randomWalkProcess_zero Y) ω
      simp [X, hkB_zero, hzero]
    exact le_trans
      (hittingAfter_le_of_mem (by simp) hmem0)
      (by exact_mod_cast Nat.zero_le (m * N + N))
  by_cases hkB_top : kB = N
  · -- Proof comment: if B already starts at `N`, the positive boundary is hit at time `0`.
    have hmem0 : X 0 ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
      have hzero : randomWalkProcess Y 0 ω = 0 := by
        simpa using congrFun (randomWalkProcess_zero Y) ω
      simp [X, hkB_top, hzero]
    exact le_trans
      (hittingAfter_le_of_mem (by simp) hmem0)
      (by exact_mod_cast Nat.zero_le (m * N + N))
  have hkB_pos : 0 < kB := Nat.pos_of_ne_zero hkB_zero
  have hkB_lt : kB < N := lt_of_le_of_ne hkB hkB_top
  let W : ℕ → ℤ := fun n ↦ randomWalkProcess Y n ω
  let τpair : ℕ∞ := hittingAfter (fun n (_ : Unit) ↦ W n)
    ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 ()
  have hpair_eq :
      hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω = τpair := by
    simpa [X, W, τpair, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      (hittingAfter_add_const_pair_eq :
        hittingAfter
            (fun n (_ : Unit) ↦ (kB : ℤ) + W n)
            ({(kB : ℤ) + -(kB : ℤ), (kB : ℤ) + ((N : ℤ) - kB)} : Set ℤ) 0 () =
          hittingAfter (fun n (_ : Unit) ↦ W n)
            ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 ())
  by_contra hτ
  have hlt_pair : ((m * N + N : ℕ) : ℕ∞) < hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω :=
    lt_of_not_ge hτ
  have hlt_pair' : ((m * N + N : ℕ) : ℕ∞) < τpair := by
    simpa [hpair_eq] using hlt_pair
  have hlt_m : ((m * N : ℕ) : ℕ∞) < τpair := by
    exact lt_of_le_of_lt (by exact_mod_cast Nat.le_add_right (m * N) N) hlt_pair'
  have hW_zero : W 0 = 0 := by
    simpa [W] using congrFun (randomWalkProcess_zero Y) ω
  have hW_step :
      ∀ n, W (n + 1) - W n = (-1 : ℤ) ∨ W (n + 1) - W n = 1 := by
    intro n
    have hinc : W (n + 1) - W n = Y n ω := by
      simpa [W] using randomWalkProcess_increment Y n ω
    simpa [hinc] using hYsigns n
  have hpair_le_left :
      τpair ≤ hittingAfter (fun n (_ : Unit) ↦ W n) ({(-(kB : ℤ))} : Set ℤ) 0 () := by
    exact (hittingAfter_anti (fun n (_ : Unit) ↦ W n) 0
      (show ({(-(kB : ℤ))} : Set ℤ) ⊆ ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) by
        intro x hx
        simp [Set.mem_singleton_iff] at hx
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hx])
      ())
  have hpair_le_right :
      τpair ≤ hittingAfter (fun n (_ : Unit) ↦ W n) ({((N : ℤ) - kB)} : Set ℤ) 0 () := by
    exact (hittingAfter_anti (fun n (_ : Unit) ↦ W n) 0
      (show ({((N : ℤ) - kB)} : Set ℤ) ⊆ ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) by
        intro x hx
        simp [Set.mem_singleton_iff] at hx
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hx, or_comm])
      ())
  have hlt_left :
      ((m * N : ℕ) : ℕ∞) < hittingAfter (fun n (_ : Unit) ↦ W n) ({(-(kB : ℤ))} : Set ℤ) 0 () :=
    lt_of_lt_of_le hlt_m hpair_le_left
  have hlt_right :
      ((m * N : ℕ) : ℕ∞) < hittingAfter (fun n (_ : Unit) ↦ W n) ({((N : ℤ) - kB)} : Set ℤ) 0 () :=
    lt_of_lt_of_le hlt_m hpair_le_right
  have hleft :
      -(kB : ℤ) < W (m * N) := by
    refine strictLeftBoundary_before_hitting (fun n ↦ W n) ?_ ?_ ?_ (m * N) hlt_left
    · simpa using hW_zero
    · exact hW_step
    · exact_mod_cast (show -(kB : ℤ) < (0 : ℤ) by omega)
  have hright :
      W (m * N) < (N : ℤ) - kB := by
    refine strictRightBoundary_before_hitting (fun n ↦ W n) ?_ ?_ ?_ (m * N) hlt_right
    · simpa using hW_zero
    · exact hW_step
    · exact_mod_cast (show (0 : ℤ) < (N : ℤ) - kB by omega)
  let x0 : ℤ := X (m * N) ω
  have hx0_eq : x0 = (kB : ℤ) + W (m * N) := by
    rfl
  have hx0_pos : 0 < x0 := by
    rw [hx0_eq]
    omega
  have hx0_lt : x0 < N := by
    rw [hx0_eq]
    omega
  have hblockX :
      ∀ j ≤ N, X (m * N + j) ω = x0 + j := by
    intro j hj
    -- Proof comment: the all-`+1` block turns the translated walk into a deterministic arithmetic
    -- progression over the whole block.
    calc
      X (m * N + j) ω =
          (kB : ℤ) + randomWalkProcess Y (m * N + j) ω := by rfl
      _ = (kB : ℤ) + (randomWalkProcess Y (m * N) ω + j) := by
        rw [randomWalkProcess_eq_add_on_allPlusBlockEvent hj hblock]
      _ = x0 + j := by
        dsimp [x0, X]
        ring
  let xNat : ℕ := Int.toNat x0
  have hxNat_eq : (xNat : ℤ) = x0 := by
    exact Int.toNat_of_nonneg (le_of_lt hx0_pos)
  have hxNat_pos : 0 < xNat := by
    omega
  have hxNat_lt : xNat < N := by
    omega
  let jHit : ℕ := N - xNat
  have hjHit_le : jHit ≤ N := Nat.sub_le _ _
  have hreach : X (m * N + jHit) ω = N := by
    have hprefix := hblockX jHit hjHit_le
    dsimp [jHit, xNat] at hprefix ⊢
    omega
  have hmem : X (m * N + jHit) ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hreach]
  have hhit_le :
      hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω ≤ m * N + jHit := by
    exact hittingAfter_le_of_mem (by simp) hmem
  have hbound : m * N + jHit ≤ m * N + N := by
    exact Nat.add_le_add_left hjHit_le (m * N)
  have hbound' : (((m * N + jHit : ℕ) : ℕ∞)) ≤ m * N + N := by
    exact_mod_cast hbound
  exact not_lt_of_ge (le_trans hhit_le hbound') hlt_pair

/-- Helper for Example 10.19: the two-sided exit time of the biased walk is almost surely finite. -/
private lemma ae_hittingAfter_pair_lt_top
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℤ} {p : ℝ} {kB N : ℕ}
    (hN : 0 < N) (hkB : kB ≤ N) (hp0 : 0 < p)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    ∀ᵐ ω ∂P,
      hittingAfter (fun n ω' ↦ (kB : ℤ) + randomWalkProcess Y n ω')
        ({0, (N : ℤ)} : Set ℤ) 0 ω < ⊤ := by
  have hlimsup := ae_mem_limsup_allPlusBlockEvent N hp0 hY_meas hY_indep hY_law
  have hsigns : ∀ᵐ ω ∂P, ∀ n, Y n ω = -1 ∨ Y n ω = 1 := by
    exact ae_all_iff.2 fun n ↦ hasLaw_biasedRademacher_ae_eq_pm_one (hY_law n)
  filter_upwards [hlimsup, hsigns] with ω hωlim hωsigns
  have hblock_exists : ∃ m, ω ∈ allPlusBlockEvent Y N m := by
    -- Proof comment: membership in the limsup means that infinitely many all-`+1` blocks occur,
    -- hence at least one such block occurs.
    have hωlim' : ∀ n, ∃ m ≥ n, ω ∈ allPlusBlockEvent Y N m := by
      simpa [Filter.limsup_eq_iInf_iSup_of_nat] using hωlim
    rcases hωlim' 0 with ⟨m, -, hm⟩
    exact ⟨m, hm⟩
  rcases hblock_exists with ⟨m, hm⟩
  have hle :=
    hittingAfter_le_blockEnd_of_mem_allPlusBlockEvent hN hkB hωsigns hm
  have hlt_top : ((m : ℕ∞) * (N : ℕ∞) + (N : ℕ∞)) < ⊤ := by
    simpa [lt_top_iff_ne_top, ENat.coe_add, ENat.coe_mul] using
      (ENat.coe_ne_top (m * N + N))
  exact lt_of_le_of_lt hle hlt_top

/-- Helper for Example 10.19: the multiplicative factor process for the exponential transform,
with `R₀ = 1` and `R_{n+1} = r ^ Y_n`. -/
private def expFactorProcess (r : ℝ) (Y : ℕ → Ω → ℤ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦ r ^ (Y n ω : ℤ)

/-- Helper for Example 10.19: the exponential walk `r ^ X_n` is a constant multiple of the
multiplicative process generated by the factors `r ^ Y_n`. -/
private lemma expWalk_eq_scaledMultiplicativeProcess
    {Y : ℕ → Ω → ℤ} {r : ℝ} (hr0 : r ≠ 0) (kB : ℕ) :
    ∀ n ω,
      r ^ (((kB : ℤ) + randomWalkProcess Y n ω) : ℤ) =
        (r ^ kB : ℝ) * multiplicativeProcess (expFactorProcess r Y) n ω := by
  intro n ω
  induction n with
  | zero =>
      -- Proof comment: at time `0`, both sides are just the starting capital factor `r ^ kB`.
      have hzero : randomWalkProcess Y 0 ω = 0 := by
        simpa using congrFun (randomWalkProcess_zero Y) ω
      simp [hzero, multiplicativeProcess]
  | succ n ih =>
      have hinc :
          randomWalkProcess Y (n + 1) ω = randomWalkProcess Y n ω + Y n ω := by
        have hinc' := randomWalkProcess_increment Y n ω
        omega
      -- Proof comment: split off the latest increment on the additive side and match it with the
      -- latest multiplicative factor on the product side.
      calc
        r ^ (((kB : ℤ) + randomWalkProcess Y (n + 1) ω) : ℤ) =
            r ^ ((((kB : ℤ) + randomWalkProcess Y n ω) : ℤ) + Y n ω) := by
              rw [hinc]
              ring_nf
        _ = r ^ (((kB : ℤ) + randomWalkProcess Y n ω) : ℤ) * r ^ (Y n ω : ℤ) := by
              rw [zpow_add₀ hr0]
        _ = ((r ^ kB : ℝ) * multiplicativeProcess (expFactorProcess r Y) n ω) * r ^ (Y n ω : ℤ) := by
              rw [ih]
        _ = (r ^ kB : ℝ) * multiplicativeProcess (expFactorProcess r Y) (n + 1) ω := by
              simp [expFactorProcess, multiplicativeProcess_succ]
              ring

/-- Helper for Example 10.19: the exponential transform sends the boundary pair `{0, N}` of the
integer walk exactly to `{1, r ^ N}` when `0 < r` and `r ≠ 1`. -/
private lemma expWalk_mem_terminalPair_iff
    {r : ℝ} {x : ℤ} {N : ℕ} (hr0 : 0 < r) (hr1 : r ≠ 1) :
    r ^ x ∈ ({1, r ^ N} : Set ℝ) ↔ x ∈ ({0, (N : ℤ)} : Set ℤ) := by
  constructor
  · intro hx
    rcases (by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx :
        r ^ x = 1 ∨ r ^ x = r ^ N) with hx1 | hxN
    · -- Proof comment: the value `1` can only occur at exponent `0`.
      have hx0 : x = 0 := (zpow_eq_one_iff_right₀ hr0.le hr1).1 hx1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hx0]
    · -- Proof comment: injectivity of `n ↦ r ^ n` identifies the exponent with `N`.
      have hxN' : r ^ x = r ^ ((N : ℤ)) := by
        simpa using hxN
      have hxNInt : x = (N : ℤ) := (zpow_right_injective₀ hr0 hr1) hxN'
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hxNInt]
  · intro hx
    rcases (by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx :
        x = 0 ∨ x = (N : ℤ)) with hx0 | hxN
    · -- Proof comment: exponent `0` gives the lower terminal value `1`.
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hx0]
    · -- Proof comment: exponent `N` gives the upper terminal value `r ^ N`.
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hxN]

/-- Helper for Example 10.19: the exponential transform also sends the singleton boundary `{0}` to
the singleton `{1}`. -/
private lemma expWalk_hittingAfter_singleton_eq
    {u : ℕ → Ω → ℤ} {r : ℝ} (hr0 : 0 < r) (hr1 : r ≠ 1) :
    hittingAfter (fun n ω ↦ r ^ (u n ω : ℤ)) ({1} : Set ℝ) 0 =
      hittingAfter u ({0} : Set ℤ) 0 := by
  -- Proof comment: normalize both hitting times through `hittingAfter_def`; the pathwise
  -- membership conditions agree because `r ^ x = 1` is equivalent to `x = 0`.
  classical
  funext ω
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ r ^ (u j ω : ℤ) ∈ ({1} : Set ℝ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({0} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        have hu0 : u j ω = 0 := by
          exact (zpow_eq_one_iff_right₀ hr0.le hr1).1 (by simpa using hj)
        simpa [Set.mem_singleton_iff, hu0]⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by
        have hu0 : u j ω = 0 := by simpa [Set.mem_singleton_iff] using hj
        simpa [Set.mem_singleton_iff, hu0]⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ r ^ (u i ω : ℤ) ∈ ({1} : Set ℝ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({0} : Set ℤ)} := by
    ext i
    simp [Set.mem_singleton_iff, (zpow_eq_one_iff_right₀ hr0.le hr1)]
  by_cases hu : ∃ j, 0 ≤ j ∧ r ^ (u j ω : ℤ) ∈ ({1} : Set ℝ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({0} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({0} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.19: hitting `{1, r ^ N}` with the exponential walk is the same as
hitting `{0, N}` with the original integer walk. -/
private lemma expWalk_hittingAfter_pair_eq
    {u : ℕ → Ω → ℤ} {r : ℝ} {N : ℕ} (hr0 : 0 < r) (hr1 : r ≠ 1) :
    hittingAfter (fun n ω ↦ r ^ (u n ω : ℤ)) ({1, r ^ N} : Set ℝ) 0 =
      hittingAfter u ({0, (N : ℤ)} : Set ℤ) 0 := by
  -- Proof comment: this is the process-level lift of the terminal-set equivalence from
  -- `expWalk_mem_terminalPair_iff`.
  classical
  funext ω
  rw [hittingAfter_def, hittingAfter_def]
  simp only
  have hExists :
      (∃ j, 0 ≤ j ∧ r ^ (u j ω : ℤ) ∈ ({1, r ^ N} : Set ℝ)) ↔
        ∃ j, 0 ≤ j ∧ u j ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, (expWalk_mem_terminalPair_iff hr0 hr1).1 hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, (expWalk_mem_terminalPair_iff hr0 hr1).2 hj⟩
  have hSet :
      {i : ℕ | 0 ≤ i ∧ r ^ (u i ω : ℤ) ∈ ({1, r ^ N} : Set ℝ)} =
        {i : ℕ | 0 ≤ i ∧ u i ω ∈ ({0, (N : ℤ)} : Set ℤ)} := by
    ext i
    constructor <;> intro hi <;> constructor
    · exact hi.1
    · exact (expWalk_mem_terminalPair_iff hr0 hr1).1 hi.2
    · exact hi.1
    · exact (expWalk_mem_terminalPair_iff hr0 hr1).2 hi.2
  by_cases hu : ∃ j, 0 ≤ j ∧ r ^ (u j ω : ℤ) ∈ ({1, r ^ N} : Set ℝ)
  · have hv : ∃ j, 0 ≤ j ∧ u j ω ∈ ({0, (N : ℤ)} : Set ℤ) := hExists.mp hu
    rw [if_pos hu, if_pos hv, hSet]
  · have hv : ¬ ∃ j, 0 ≤ j ∧ u j ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
      exact fun hv ↦ hu (hExists.mpr hv)
    rw [if_neg hu, if_neg hv]

/-- Helper for Example 10.19: once the exit time `τ` is finite, the stopped exponential walk takes
the value `1` exactly on the ruin event `{τ = τ₀}` and otherwise the value `r ^ N`. -/
private lemma stoppedExpWalk_repr
    {P : Measure Ω} {W : ℕ → Ω → ℤ} {Z : ℕ → Ω → ℝ} {r : ℝ} {N : ℕ}
    {τ τ0 : Ω → ℕ∞} {A : Set Ω}
    (hZ_eq : ∀ n ω, Z n ω = r ^ (W n ω : ℤ))
    (hτ_def : τ = hittingAfter W ({0, (N : ℤ)} : Set ℤ) 0)
    (hτ0_def : τ0 = hittingAfter W ({0} : Set ℤ) 0)
    (hA_def : A = {ω | τ ω = τ0 ω})
    (hτ_le_τ0 : ∀ ω, τ ω ≤ τ0 ω)
    (hτ_ae_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue Z τ =ᵐ[P]
      fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω +
        Aᶜ.indicator (fun _ ↦ r ^ N) ω := by
  -- Proof comment: at the exit time, the integer walk is at `0` or `N`; the event `A` picks out
  -- precisely the first case because the singleton hitting time can only coincide with the pair
  -- hitting time when the exit point is `0`.
  filter_upwards [hτ_ae_ne_top] with ω hω
  by_cases hAω : ω ∈ A
  · have hEqτ : τ ω = τ0 ω := by simpa [hA_def] using hAω
    have hτ0_ne : τ0 ω ≠ ⊤ := by simpa [hEqτ] using hω
    have hτ0_ne' : hittingAfter W ({0} : Set ℤ) 0 ω ≠ ⊤ := by
      simpa [hτ0_def] using hτ0_ne
    have hval0 : W (τ ω).untopA ω = 0 := by
      simpa [hτ0_def, hEqτ, Set.mem_singleton_iff] using
        (hittingAfter_mem_set_of_ne_top hτ0_ne')
    have hterm : stoppedValue Z τ ω = 1 := by
      rw [stoppedValue, hZ_eq, hval0]
      simp
    have hA_ind : A.indicator (fun _ ↦ (1 : ℝ)) ω = 1 := by
      simp [Set.indicator_of_mem, hAω]
    have hAc_ind : Aᶜ.indicator (fun _ ↦ r ^ N) ω = 0 := by
      simp [Set.indicator_of_notMem, hAω]
    simpa [hA_ind, hAc_ind] using hterm
  · have hmem : W (τ ω).untopA ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
      have hτ_ne' : hittingAfter W ({0, (N : ℤ)} : Set ℤ) 0 ω ≠ ⊤ := by
        simpa [hτ_def] using hω
      simpa [hτ_def] using
        (hittingAfter_mem_set_of_ne_top hτ_ne')
    have hvalN : W (τ ω).untopA ω = N := by
      rcases (by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
          W (τ ω).untopA ω = 0 ∨ W (τ ω).untopA ω = (N : ℤ)) with hval0 | hvalN
      · have hidx_eq : (((τ ω).untopA : ℕ) : ℕ∞) = τ ω := by
          rw [WithTop.untopA_eq_untop hω]
          exact WithTop.coe_untop _ _
        have hτ0_le : τ0 ω ≤ τ ω := by
          have hmem0 : W (τ ω).untopA ω ∈ ({0} : Set ℤ) := by
            simpa [Set.mem_singleton_iff, hval0]
          have hτ0_le' : hittingAfter W ({0} : Set ℤ) 0 ω ≤ (τ ω).untopA := by
            exact hittingAfter_le_of_mem (by simp) hmem0
          have hτ0_le'' : τ0 ω ≤ (τ ω).untopA := by
            simpa [hτ0_def] using hτ0_le'
          exact le_trans hτ0_le'' hidx_eq.le
        have hEqτ : τ ω = τ0 ω := le_antisymm (hτ_le_τ0 ω) hτ0_le
        exact False.elim (hAω (by simpa [hA_def] using hEqτ))
      · exact hvalN
    have hterm : stoppedValue Z τ ω = r ^ N := by
      rw [stoppedValue, hZ_eq, hvalN]
      simp
    have hA_ind : A.indicator (fun _ ↦ (1 : ℝ)) ω = 0 := by
      simp [Set.indicator_of_notMem, hAω]
    have hAc_ind : Aᶜ.indicator (fun _ ↦ r ^ N) ω = r ^ N := by
      simp [Set.indicator_of_mem, hAω]
    simpa [hA_ind, hAc_ind] using hterm

-- Proof sketch: use the exponential transform `Z_n = r^(X_n)` with `r = (1 - p) / p`, observe
-- that this is a martingale by the one-step computation `𝔼[r^{Y_n}] = 1`, stop at the first hit of
-- `{0, N}`, and solve the resulting linear equation for the ruin probability. The walk itself is
-- expressed directly through the chapter owner `randomWalkProcess`, and the ruin event uses the
-- canonical hitting-time language `τ_{0,N} = τ_0`.
/-- Example 10.19 [Gambler's ruin problem]: for a gambler's ruin walk started from capital `kB`,
with i.i.d. increments `Y_i ∈ {-1, 1}` satisfying `𝔓[Y_i = 1] = p` and
`𝔓[Y_i = -1] = 1 - p`, the probability that B is ruined before reaching the positive total
capital `N` is `(r^kB - r^N) / (1 - r^N)` with `r = (1 - p) / p`. -/
theorem gamblerRuinProbability_eq
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} {p : ℝ} {kB N : ℕ}
    (hN : 0 < N) (hkB : kB ≤ N) (hp0 : 0 < p) (hp1 : p < 1) (hp_ne_half : p ≠ 1 / 2)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    (P {ω | hittingAfter (fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω)
        ({0, (N : ℤ)} : Set ℤ) 0 ω =
          hittingAfter (fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω)
            ({0} : Set ℤ) 0 ω}).toReal =
      ((gamblerRuinRatio p) ^ kB - (gamblerRuinRatio p) ^ N) /
        (1 - (gamblerRuinRatio p) ^ N) := by
    haveI : IsProbabilityMeasure (biasedRademacherLaw p) :=
      biasedRademacherLaw_isProbabilityMeasure hp0.le hp1.le
    letI : IsProbabilityMeasure P := (hY_law 0).isProbabilityMeasure
    let X : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω
    let Ym : ℕ → Ω → ℤ := fun n ↦ (hY_law n).aemeasurable.mk (Y n)
    let W : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Ym n ω
    let r : ℝ := gamblerRuinRatio p
    let Z : ℕ → Ω → ℝ := fun n ω ↦
      (r ^ kB : ℝ) * multiplicativeProcess (expFactorProcess r Ym) n ω
    have hr_pos : 0 < r := by
      -- Proof comment: `r = (1 - p) / p` is positive because `0 < p < 1`.
      dsimp [r, gamblerRuinRatio]
      have hnum : 0 < 1 - p := by linarith
      exact div_pos hnum hp0
    have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
    have hr_ne_one : r ≠ 1 := by
      -- Proof comment: `r = 1` would force `p = 1 / 2`, excluded by hypothesis.
      intro hr1
      have hp_eq : p = 1 / 2 := by
        dsimp [r, gamblerRuinRatio] at hr1
        have hp1ne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
        field_simp [hp0.ne', hp1ne] at hr1
        linarith
      exact hp_ne_half hp_eq
    have hratio_mean_one : p * r + (1 - p) * r⁻¹ = 1 := by
      -- Proof comment: this is the textbook one-step martingale condition for the choice
      -- `r = (1 - p) / p`.
      dsimp [r, gamblerRuinRatio]
      have hp1ne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
      field_simp [hp0.ne', hp1ne]
      ring
    have hYm_eq : ∀ n, Y n =ᵐ[P] Ym n := by
      intro n
      simpa [Ym] using (hY_law n).aemeasurable.ae_eq_mk
    have hYm_meas : ∀ n, Measurable (Ym n) := by
      intro n
      simpa [Ym] using (hY_law n).aemeasurable.measurable_mk
    have hYm_indep : iIndepFun Ym P := by
      exact hY_indep.congr hYm_eq
    have hYm_law : ∀ n, HasLaw (Ym n) (biasedRademacherLaw p) P := by
      intro n
      exact (hY_law n).congr (hYm_eq n).symm
    have hWalk_eq : ∀ᵐ ω ∂P, ∀ n, randomWalkProcess Ym n ω = randomWalkProcess Y n ω := by
      have h_all : ∀ᵐ ω ∂P, ∀ n, Y n ω = Ym n ω := by
        simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
      filter_upwards [h_all] with ω hω n
      rw [randomWalkProcess_apply, randomWalkProcess_apply]
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact (hω j).symm
    have hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω := by
      filter_upwards [hWalk_eq] with ω hω n
      simp [W, X, hω n]
    have hExp_meas : ∀ n, Measurable ((expFactorProcess r Ym) (n + 1)) := by
      intro n
      have hzpow_meas : Measurable (fun z : ℤ ↦ r ^ (z : ℤ)) := measurable_of_countable _
      simpa [expFactorProcess] using hzpow_meas.comp (hYm_meas n)
    have hExp_indep : iIndepFun (fun n ↦ (expFactorProcess r Ym) (n + 1)) P := by
      have hzpow_meas : Measurable (fun z : ℤ ↦ r ^ (z : ℤ)) := measurable_of_countable _
      simpa [expFactorProcess] using
        hYm_indep.comp (fun _ z ↦ r ^ (z : ℤ)) (fun _ ↦ hzpow_meas)
    have hExp_mean_one : ∀ n, P[(expFactorProcess r Ym) (n + 1)] = 1 := by
      intro n
      have hIntLaw :
          ∫ z : ℤ, (r ^ (z : ℤ) : ℝ) ∂ biasedRademacherLaw p =
            p * r + r⁻¹ * (1 - p) := by
        have hzpow_strMeas : StronglyMeasurable (fun z : ℤ ↦ (r ^ (z : ℤ) : ℝ)) :=
          (measurable_of_countable _).stronglyMeasurable
        have hzpow_int1 :
            Integrable (fun z : ℤ ↦ (r ^ (z : ℤ) : ℝ)) (Measure.dirac (1 : ℤ)) :=
          integrable_dirac' hzpow_strMeas (by simp)
        have hzpow_intm1 :
            Integrable (fun z : ℤ ↦ (r ^ (z : ℤ) : ℝ)) (Measure.dirac (-1 : ℤ)) :=
          integrable_dirac' hzpow_strMeas (by simp [hr_ne_zero])
        rw [biasedRademacherLaw,
          integral_add_measure
            (hzpow_int1.smul_measure (by simp))
            (hzpow_intm1.smul_measure (by simp))]
        rw [integral_smul_measure, integral_smul_measure]
        have h1mp : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
        have h1mm : (ENNReal.ofReal (1 - p)).toReal = 1 - p := by
          rw [ENNReal.toReal_ofReal]
          linarith
        simp [hzpow_strMeas, hr_ne_zero, h1mp, h1mm, mul_comm, mul_left_comm, mul_assoc]
      calc
        P[(expFactorProcess r Ym) (n + 1)] =
            ∫ z : ℤ, (r ^ (z : ℤ) : ℝ) ∂ biasedRademacherLaw p := by
              simpa [expFactorProcess] using
                (hYm_law n).integral_comp ((measurable_of_countable _).aestronglyMeasurable)
        _ = p * r + r⁻¹ * (1 - p) := hIntLaw
        _ = p * r + (1 - p) * r⁻¹ := by ring
        _ = 1 := hratio_mean_one
    let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
      Filtration.natural (multiplicativeFactorProcess (expFactorProcess r Ym))
        (stronglyMeasurable_multiplicativeFactorProcess hExp_meas)
    let τ0 : Ω → ℕ∞ := hittingAfter W ({0} : Set ℤ) 0
    let τ : Ω → ℕ∞ := hittingAfter W ({0, (N : ℤ)} : Set ℤ) 0
    let A : Set Ω := {ω | τ ω = τ0 ω}
    have hZ_eq : ∀ n ω, Z n ω = r ^ (W n ω : ℤ) := by
      intro n ω
      simpa [Z, W] using
        (expWalk_eq_scaledMultiplicativeProcess hr_ne_zero kB n ω).symm
    have hM_martingale :
        Martingale (multiplicativeProcess (expFactorProcess r Ym)) ℱ P := by
      simpa [ℱ] using
        multiplicativeProcess_martingale_of_iIndepFun_mean_one hExp_meas hExp_indep hExp_mean_one
    have hZ_martingale : Martingale Z ℱ P := by
      simpa [Z, Pi.smul_apply, smul_eq_mul] using
        (hM_martingale.smul (r ^ kB : ℝ))
    have hτ_eq : hittingAfter Z ({1, r ^ N} : Set ℝ) 0 = τ := by
      calc
        hittingAfter Z ({1, r ^ N} : Set ℝ) 0 =
            hittingAfter (fun n ω ↦ r ^ (W n ω : ℤ)) ({1, r ^ N} : Set ℝ) 0 := by
              apply funext
              intro ω
              exact hittingAfter_zero_eq_of_forall_eq (fun n ↦ hZ_eq n ω)
        _ = τ := by
              simpa [τ] using
                (expWalk_hittingAfter_pair_eq hr_pos hr_ne_one)
    have hτ0_eq : hittingAfter Z ({1} : Set ℝ) 0 = τ0 := by
      calc
        hittingAfter Z ({1} : Set ℝ) 0 =
            hittingAfter (fun n ω ↦ r ^ (W n ω : ℤ)) ({1} : Set ℝ) 0 := by
              apply funext
              intro ω
              exact hittingAfter_zero_eq_of_forall_eq (fun n ↦ hZ_eq n ω)
        _ = τ0 := by
              simpa [τ0] using
                (expWalk_hittingAfter_singleton_eq hr_pos hr_ne_one)
    have hτ_stop : IsStoppingTime ℱ τ := by
      -- Proof comment: rewrite the pair exit time as a hitting time of the adapted exponential
      -- martingale.
      rw [← hτ_eq]
      simpa [Set.insert_comm] using
        Adapted.isStoppingTime_hittingAfter
          hZ_martingale.stronglyAdapted.adapted
          ((measurableSet_singleton (r ^ N)).insert (1 : ℝ))
    have hτ0_stop : IsStoppingTime ℱ τ0 := by
      -- Proof comment: the ruin-time singleton boundary is the same exponential hitting event at
      -- level `1`.
      rw [← hτ0_eq]
      simpa using
        Adapted.isStoppingTime_hittingAfter
          hZ_martingale.stronglyAdapted.adapted
          (measurableSet_singleton (1 : ℝ))
    have hτ_ae_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
      simpa [τ, lt_top_iff_ne_top] using
        (ae_hittingAfter_pair_lt_top hN hkB hp0 hYm_meas hYm_indep hYm_law)
    have hτ_le_τ0 : ∀ ω, τ ω ≤ τ0 ω := by
      intro ω
      exact hittingAfter_anti
        W 0
        (show ({0} : Set ℤ) ⊆ ({0, (N : ℤ)} : Set ℤ) by
          intro x hx
          have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hx0])
        ω
    let F : ℕ → Ω → ℝ := fun n ω ↦
      stoppedValue Z (fun ω' ↦ min (τ ω') (n : ℕ∞)) ω
    have hF_int : ∀ n, Integrable (F n) P := by
      intro n
      exact integrable_stoppedValue ℕ (hτ_stop.min_const n)
        hZ_martingale.integrable fun ω ↦ min_le_right _ _
    have hF_expectation : ∀ n, ∫ ω, F n ω ∂P = (r ^ kB : ℝ) := by
      intro n
      have hEq :
          P[stoppedValue Z (fun ω ↦ min (τ ω) (n : ℕ∞))] =
            P[stoppedValue Z (fun _ ↦ (0 : ℕ∞))] :=
        martingale_expected_stoppedValue_eq_of_le_of_bounded
          hZ_martingale
          (isStoppingTime_const ℱ 0) (hτ_stop.min_const n)
          (fun ω ↦ by simp) (fun ω ↦ min_le_right _ _)
      calc
        ∫ ω, F n ω ∂P = ∫ ω, stoppedValue Z (fun _ ↦ (0 : ℕ∞)) ω ∂P := by
          simpa [F] using hEq
        _ = r ^ kB := by
          change ∫ ω, Z 0 ω ∂P = r ^ kB
          simp [Z, multiplicativeProcess, Measure.real_def]
    have hYm_signs : ∀ᵐ ω ∂P, ∀ n, Ym n ω = -1 ∨ Ym n ω = 1 := by
      exact ae_all_iff.2 fun n ↦ hasLaw_biasedRademacher_ae_eq_pm_one (hYm_law n)
    have hF_bound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ max 1 (r ^ N) := by
      intro n
      filter_upwards [hYm_signs] with ω hωSigns
      have hstopEq : F n ω = stoppedProcess Z τ n ω := by
        simpa [F, min_comm] using
          ((stoppedProcess_eq_stoppedValue_apply n ω :
            stoppedProcess Z τ n ω =
              stoppedValue Z (fun ω' ↦ min (n : ℕ∞) (τ ω')) ω).symm)
      by_cases hτω : τ ω ≤ n
      · have hτ_ne : τ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hτω
        have hmem : W (τ ω).untopA ω ∈ ({0, (N : ℤ)} : Set ℤ) := by
          simpa [τ] using
            (hittingAfter_mem_set_of_ne_top hτ_ne)
        have hproc : stoppedProcess Z τ n ω = Z (τ ω).untopA ω := by
          exact stoppedProcess_eq_of_ge hτω
        rw [hstopEq, hproc, hZ_eq, Real.norm_eq_abs]
        rcases (by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
            W (τ ω).untopA ω = 0 ∨ W (τ ω).untopA ω = (N : ℤ)) with h0 | hN'
        · simp [h0]
        · have hrN_nonneg : 0 ≤ r ^ N := by positivity
          simp [hN', abs_of_nonneg hrN_nonneg, hrN_nonneg, le_max_right]
      · have hlt : (n : ℕ∞) < τ ω := lt_of_not_ge hτω
        let R : ℕ → ℤ := fun m ↦ randomWalkProcess Ym m ω
        have hpair_eq :
            τ ω =
              hittingAfter (fun m (_ : Unit) ↦ R m)
                ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 () := by
          simpa [τ, W, R, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
            (hittingAfter_add_const_pair_eq :
              hittingAfter
                  (fun m (_ : Unit) ↦ (kB : ℤ) + R m)
                  ({(kB : ℤ) + -(kB : ℤ), (kB : ℤ) + ((N : ℤ) - kB)} : Set ℤ) 0 () =
                hittingAfter (fun m (_ : Unit) ↦ R m)
                  ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 ())
        have hlt_pair :
            ((n : ℕ∞) <
              hittingAfter (fun m (_ : Unit) ↦ R m)
                ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 ()) := by
          simpa [hpair_eq] using hlt
        have hR_zero : R 0 = 0 := by
          simpa [R] using congrFun (randomWalkProcess_zero Ym) ω
        have hR_step :
            ∀ m, R (m + 1) - R m = (-1 : ℤ) ∨ R (m + 1) - R m = 1 := by
          intro m
          have hinc : R (m + 1) - R m = Ym m ω := by
            simpa [R] using randomWalkProcess_increment Ym m ω
          simpa [hinc] using hωSigns m
        have hpair_le_left :
            hittingAfter (fun m (_ : Unit) ↦ R m)
              ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 () ≤
              hittingAfter (fun m (_ : Unit) ↦ R m) ({(-(kB : ℤ))} : Set ℤ) 0 () := by
          exact hittingAfter_anti
            (fun m (_ : Unit) ↦ R m) 0
            (show ({(-(kB : ℤ))} : Set ℤ) ⊆ ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) by
              intro x hx
              have hx0 : x = -(kB : ℤ) := by simpa [Set.mem_singleton_iff] using hx
              simp [Set.mem_insert_iff, Set.mem_singleton_iff, hx0])
            ()
        have hpair_le_right :
            hittingAfter (fun m (_ : Unit) ↦ R m)
              ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) 0 () ≤
              hittingAfter (fun m (_ : Unit) ↦ R m) ({((N : ℤ) - kB)} : Set ℤ) 0 () := by
          exact hittingAfter_anti
            (fun m (_ : Unit) ↦ R m) 0
            (show ({((N : ℤ) - kB)} : Set ℤ) ⊆ ({(-(kB : ℤ)), ((N : ℤ) - kB)} : Set ℤ) by
              intro x hx
              have hxN : x = (N : ℤ) - kB := by simpa [Set.mem_singleton_iff] using hx
              simp [Set.mem_insert_iff, Set.mem_singleton_iff, hxN, or_comm])
            ()
        have hlt_left :
            ((n : ℕ∞) < hittingAfter (fun m (_ : Unit) ↦ R m) ({(-(kB : ℤ))} : Set ℤ) 0 ()) :=
          lt_of_lt_of_le hlt_pair hpair_le_left
        have hlt_right :
            ((n : ℕ∞) <
              hittingAfter (fun m (_ : Unit) ↦ R m) ({((N : ℤ) - kB)} : Set ℤ) 0 ()) :=
          lt_of_lt_of_le hlt_pair hpair_le_right
        have hlt0 : ((0 : ℕ) : ℕ∞) < τ ω := by
          exact lt_of_le_of_lt (by simp) hlt
        have hnot_mem0 : W 0 ω ∉ ({0, (N : ℤ)} : Set ℤ) := by
          exact notMem_of_lt_hittingAfter hlt0 (by simp)
        have hkB_ne_zero : kB ≠ 0 := by
          intro hkB0
          apply hnot_mem0
          have hzero : randomWalkProcess Ym 0 ω = 0 := by
            simpa using congrFun (randomWalkProcess_zero Ym) ω
          simp [W, hkB0, hzero, Set.mem_insert_iff, Set.mem_singleton_iff]
        have hkB_ne_N : kB ≠ N := by
          intro hkBN
          apply hnot_mem0
          have hzero : randomWalkProcess Ym 0 ω = 0 := by
            simpa using congrFun (randomWalkProcess_zero Ym) ω
          simp [W, hkBN, hzero, Set.mem_insert_iff, Set.mem_singleton_iff]
        have hkB_pos : 0 < kB := Nat.pos_of_ne_zero hkB_ne_zero
        have hkB_lt_N : kB < N := lt_of_le_of_ne hkB hkB_ne_N
        have hleft : -(kB : ℤ) < R n := by
          refine strictLeftBoundary_before_hitting
            (fun m ↦ R m) hR_zero hR_step ?_ n hlt_left
          omega
        have hright : R n < (N : ℤ) - kB := by
          refine strictRightBoundary_before_hitting
            (fun m ↦ R m) hR_zero hR_step ?_ n hlt_right
          exact_mod_cast (Nat.sub_pos_of_lt hkB_lt_N)
        have hW_pos : 0 < W n ω := by
          change 0 < (kB : ℤ) + R n
          omega
        have hW_lt : W n ω < N := by
          change (kB : ℤ) + R n < N
          omega
        have hproc : stoppedProcess Z τ n ω = Z n ω := by
          exact stoppedProcess_eq_of_le (le_of_lt hlt)
        have hle_terminal :
            r ^ (W n ω : ℤ) ≤ max 1 (r ^ N) := by
          by_cases hr_ge_one : 1 ≤ r
          · have hW_nonneg : (0 : ℤ) ≤ W n ω := le_of_lt hW_pos
            have hW_le_N : (W n ω : ℤ) ≤ N := by exact_mod_cast hW_lt.le
            have hle_one : 1 = r ^ (0 : ℤ) := by simp
            have hleN : r ^ (W n ω : ℤ) ≤ r ^ (N : ℤ) := by
              exact zpow_le_zpow_right₀ hr_ge_one hW_le_N
            exact le_trans (by simpa [hle_one] using le_max_left 1 (r ^ N)) <|
              le_trans hleN (by simp)
          · have hr_le_one : r ≤ 1 := le_of_not_ge hr_ge_one
            have hW_nonneg : (0 : ℤ) ≤ W n ω := le_of_lt hW_pos
            have hW_le_N : (W n ω : ℤ) ≤ N := by exact_mod_cast hW_lt.le
            have hleN : r ^ (W n ω : ℤ) ≤ 1 := by
              have htmp : r ^ (0 : ℤ) ≥ r ^ (W n ω : ℤ) := by
                exact zpow_le_zpow_right_of_le_one₀ hr_pos hr_le_one hW_nonneg
              simpa using htmp
            exact le_trans hleN (le_max_left 1 (r ^ N))
        have hnonneg : 0 ≤ r ^ (W n ω : ℤ) := by positivity
        rw [hstopEq, hproc, hZ_eq, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hle_terminal
    have hF_tendsto :
        ∀ᵐ ω ∂P, Filter.Tendsto (fun n ↦ F n ω) Filter.atTop (nhds (stoppedValue Z τ ω)) := by
      filter_upwards
        [stoppedValue_truncation_ae_eventuallyEq hτ_ae_ne_top] with
          ω hω
      have hEq : (fun n ↦ F n ω) =ᶠ[Filter.atTop] fun _ ↦ stoppedValue Z τ ω := by
        simpa [Filter.EventuallyEq, F] using hω
      exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
    have hF_integral_tendsto :
        Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂P) Filter.atTop
          (nhds (∫ ω, stoppedValue Z τ ω ∂P)) := by
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ ↦ max 1 (r ^ N))
        (fun n ↦ (hF_int n).aestronglyMeasurable)
        (integrable_const (max 1 (r ^ N)))
        hF_bound hF_tendsto
    have hconst_tendsto :
        Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂P) Filter.atTop (nhds (r ^ kB : ℝ)) := by
      have hEq : (fun n ↦ ∫ ω, F n ω ∂P) = fun _ : ℕ ↦ (r ^ kB : ℝ) := by
        funext n
        exact hF_expectation n
      simpa [hEq] using
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ ↦ (r ^ kB : ℝ)) Filter.atTop (nhds (r ^ kB : ℝ)))
    have hterminal_expected : ∫ ω, stoppedValue Z τ ω ∂P = (r ^ kB : ℝ) := by
      exact tendsto_nhds_unique hF_integral_tendsto hconst_tendsto
    have hA_meas : MeasurableSet A := by
      have hτ_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τ ω = n} := by
        intro n
        exact ℱ.le n _ (hτ_stop.measurableSet_eq n)
      have hτ0_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τ0 ω = n} := by
        intro n
        exact ℱ.le n _ (hτ0_stop.measurableSet_eq n)
      have hτ_top_meas : MeasurableSet {ω | τ ω = ⊤} := by
        have hEq : {ω | τ ω = ⊤} = (⋃ n : ℕ, {ω | τ ω = n})ᶜ := by
          ext ω
          cases hτω : τ ω with
          | top =>
              simpa [hτω]
          | coe n =>
              simpa [hτω]
        rw [hEq]
        exact (MeasurableSet.iUnion hτ_eq_meas).compl
      have hτ0_top_meas : MeasurableSet {ω | τ0 ω = ⊤} := by
        have hEq : {ω | τ0 ω = ⊤} = (⋃ n : ℕ, {ω | τ0 ω = n})ᶜ := by
          ext ω
          cases hτ0ω : τ0 ω with
          | top =>
              simpa [hτ0ω]
          | coe n =>
              simpa [hτ0ω]
        rw [hEq]
        exact (MeasurableSet.iUnion hτ0_eq_meas).compl
      have hEq :
          A =
            (⋃ n : ℕ, {ω | τ ω = n} ∩ {ω | τ0 ω = n}) ∪
              ({ω | τ ω = ⊤} ∩ {ω | τ0 ω = ⊤}) := by
        ext ω
        cases hτω : τ ω with
        | top =>
            cases hτ0ω : τ0 ω with
            | top =>
                simpa [A, hτω, hτ0ω]
            | coe m =>
                simpa [A, hτω, hτ0ω]
        | coe n =>
            cases hτ0ω : τ0 ω with
            | top =>
                simpa [A, hτω, hτ0ω]
            | coe m =>
                simpa [A, hτω, hτ0ω, eq_comm]
      rw [hEq]
      exact
        (MeasurableSet.iUnion fun n ↦ (hτ_eq_meas n).inter (hτ0_eq_meas n)).union
          (hτ_top_meas.inter hτ0_top_meas)
    have hterminal_repr :
        stoppedValue Z τ =ᵐ[P]
          fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω +
            Aᶜ.indicator (fun _ ↦ r ^ N) ω := by
      exact stoppedExpWalk_repr hZ_eq rfl rfl rfl hτ_le_τ0 hτ_ae_ne_top
    have hterminal_integral :
        ∫ ω, stoppedValue Z τ ω ∂P =
          P.real A * (1 : ℝ) + P.real Aᶜ * (r ^ N) := by
      calc
        ∫ ω, stoppedValue Z τ ω ∂P =
            ∫ ω,
              (A.indicator (fun _ ↦ (1 : ℝ)) ω +
                Aᶜ.indicator (fun _ ↦ r ^ N) ω) ∂P := by
                  exact integral_congr_ae hterminal_repr
        _ = ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂P
              + ∫ ω, Aᶜ.indicator (fun _ ↦ r ^ N) ω ∂P := by
                rw [integral_add]
                · exact (integrable_const (1 : ℝ)).indicator hA_meas
                · exact (integrable_const (r ^ N : ℝ)).indicator hA_meas.compl
        _ = P.real A * (1 : ℝ) + P.real Aᶜ * (r ^ N) := by
          rw [integral_indicator_const (1 : ℝ) hA_meas,
            integral_indicator_const (r ^ N : ℝ) hA_meas.compl]
          simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    have hA_le_one : P A ≤ 1 := by
      calc
        P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := by simp
    have hA_ne_top : P A ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hA_le_one (by simp))
    have hA_compl_real : P.real Aᶜ = 1 - P.real A := by
      rw [Measure.real_def, measure_compl hA_meas hA_ne_top, measure_univ]
      rw [ENNReal.toReal_sub_of_le hA_le_one (by simp)]
      simp [Measure.real_def]
    have hA_real :
        P.real A = ((r ^ kB : ℝ) - r ^ N) / (1 - r ^ N) := by
      have haff :
          (r ^ kB : ℝ) = P.real A * (1 : ℝ) + (1 - P.real A) * (r ^ N) := by
        calc
          (r ^ kB : ℝ) = ∫ ω, stoppedValue Z τ ω ∂P := hterminal_expected.symm
          _ = P.real A * (1 : ℝ) + P.real Aᶜ * (r ^ N) := hterminal_integral
          _ = P.real A * (1 : ℝ) + (1 - P.real A) * (r ^ N) := by
            rw [hA_compl_real]
      have hden : 1 - r ^ N ≠ 0 := by
        intro hden
        have hrN_one : r ^ N = 1 := by linarith
        have hr_one : r = 1 := by
          exact (pow_eq_one_iff_of_nonneg hr_pos.le (Nat.ne_of_gt hN)).1 hrN_one
        exact hr_ne_one hr_one
      apply (eq_div_iff hden).2
      nlinarith
    have hAeq_X :
        A =ᵐ[P]
          {ω | hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω =
              hittingAfter X ({0} : Set ℤ) 0 ω} := by
      filter_upwards [hW_eq_X] with ω hω
      have hpair :
          hittingAfter W ({0, (N : ℤ)} : Set ℤ) 0 ω =
            hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω := by
        exact hittingAfter_zero_eq_of_forall_eq hω
      have hsingle :
          hittingAfter W ({0} : Set ℤ) 0 ω =
            hittingAfter X ({0} : Set ℤ) 0 ω := by
        exact hittingAfter_zero_eq_of_forall_eq hω
      apply propext
      constructor <;> intro h
      · change hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω =
          hittingAfter X ({0} : Set ℤ) 0 ω
        rw [← hpair, ← hsingle]
        simpa [A, τ, τ0] using h
      · change hittingAfter W ({0, (N : ℤ)} : Set ℤ) 0 ω =
          hittingAfter W ({0} : Set ℤ) 0 ω
        rw [hpair, hsingle]
        simpa [A, τ, τ0] using h
    have hA_toReal :
        (P A).toReal = ((r ^ kB : ℝ) - r ^ N) / (1 - r ^ N) := by
      simpa [Measure.real_def] using hA_real
    calc
      (P {ω | hittingAfter X ({0, (N : ℤ)} : Set ℤ) 0 ω =
          hittingAfter X ({0} : Set ℤ) 0 ω}).toReal = (P A).toReal := by
            rw [(measure_congr hAeq_X).symm]
      _ = ((r ^ kB : ℝ) - r ^ N) / (1 - r ^ N) := hA_toReal
      _ = ((gamblerRuinRatio p) ^ kB - (gamblerRuinRatio p) ^ N) /
            (1 - (gamblerRuinRatio p) ^ N) := by
              simp [r]

-- Proof sketch: apply `gamblerRuinProbability_eq` to the genuine finite-capital instances with
-- total capital `N + kB + 1`, rewrite
-- `(r^kB - r^(N + kB + 1)) / (1 - r^(N + kB + 1)) =
--   r^kB * (1 - r^(N + 1)) / (1 - r^(N + kB + 1))`,
-- use `0 < r < 1` when `1 / 2 < p < 1`, and pass to the limit `N → ∞`.
/-- With `kB` fixed and `p > 1 / 2`, the ruin probabilities for the finite-capital gambler's ruin
problems with total capital `kB + 1, kB + 2, …` converge to `r^kB`. -/
theorem gamblerRuinProbability_tendsto_infiniteCapital
    {P : Measure Ω} {Y : ℕ → Ω → ℤ} {p : ℝ} {kB : ℕ}
    (hp_half : 1 / 2 < p) (hp1 : p < 1)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) (biasedRademacherLaw p) P) :
    by
      have hp0 : 0 < p := lt_trans (by norm_num) hp_half
      haveI : IsProbabilityMeasure (biasedRademacherLaw p) :=
        biasedRademacherLaw_isProbabilityMeasure hp0.le hp1.le
      letI : IsProbabilityMeasure P := (hY_law 0).isProbabilityMeasure
      exact
        Filter.Tendsto
          (fun N : ℕ ↦
            let totalCapital := N + kB + 1
            let X : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω
            (P {ω | hittingAfter X ({0, (totalCapital : ℤ)} : Set ℤ) 0 ω =
                hittingAfter X ({0} : Set ℤ) 0 ω}).toReal)
          Filter.atTop
          (nhds ((gamblerRuinRatio p) ^ kB)) :=
  by
    have hp0 : 0 < p := lt_trans (by norm_num) hp_half
    haveI : IsProbabilityMeasure (biasedRademacherLaw p) :=
      biasedRademacherLaw_isProbabilityMeasure hp0.le hp1.le
    letI : IsProbabilityMeasure P := (hY_law 0).isProbabilityMeasure
    let r : ℝ := gamblerRuinRatio p
    have hp_ne_half : p ≠ 1 / 2 := ne_of_gt hp_half
    have hr_pos : 0 < r := by
      -- Proof comment: when `1 / 2 < p < 1`, the gambler's ruin ratio stays in `(0, 1)`.
      dsimp [r, gamblerRuinRatio]
      have hnum : 0 < 1 - p := by linarith
      exact div_pos hnum hp0
    have hr_lt_one : r < 1 := by
      dsimp [r, gamblerRuinRatio]
      have hp_ne_zero : p ≠ 0 := hp0.ne'
      field_simp [hp_ne_zero]
      linarith
    have hr_abs : |r| < 1 := by
      rwa [abs_of_pos hr_pos]
    let seq : ℕ → ℝ := fun N ↦
      let totalCapital := N + kB + 1
      let X : ℕ → Ω → ℤ := fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω
      (P {ω | hittingAfter X ({0, (totalCapital : ℤ)} : Set ℤ) 0 ω =
          hittingAfter X ({0} : Set ℤ) 0 ω}).toReal
    have hseq_formula :
        seq =
          fun N ↦ ((r ^ kB : ℝ) - r ^ (N + kB + 1)) / (1 - r ^ (N + kB + 1)) := by
      funext N
      have hformula :
          (P {ω | hittingAfter (fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω)
              ({0, ((N + kB + 1 : ℕ) : ℤ)} : Set ℤ) 0 ω =
                hittingAfter (fun n ω ↦ (kB : ℤ) + randomWalkProcess Y n ω)
                  ({0} : Set ℤ) 0 ω}).toReal =
            ((gamblerRuinRatio p) ^ kB - (gamblerRuinRatio p) ^ (N + kB + 1)) /
              (1 - (gamblerRuinRatio p) ^ (N + kB + 1)) := by
        exact gamblerRuinProbability_eq
          (Nat.succ_pos _) (by omega) hp0 hp1 hp_ne_half hY_indep hY_law
      simpa [seq, r]
        using hformula
    have hpow_zero : Filter.Tendsto (fun N : ℕ ↦ r ^ N) Filter.atTop (nhds (0 : ℝ)) := by
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr_abs
    have hshift_zero :
        Filter.Tendsto (fun N : ℕ ↦ r ^ (N + kB + 1)) Filter.atTop (nhds (0 : ℝ)) := by
      have hconst_mul :
          Filter.Tendsto (fun N : ℕ ↦ (r ^ (kB + 1) : ℝ) * r ^ N)
            Filter.atTop (nhds ((r ^ (kB + 1) : ℝ) * 0)) := by
        exact tendsto_const_nhds.mul hpow_zero
      simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        mul_comm, mul_left_comm, mul_assoc]
        using hconst_mul
    have hnum_tendsto :
        Filter.Tendsto (fun N : ℕ ↦ (r ^ kB : ℝ) - r ^ (N + kB + 1))
          Filter.atTop (nhds (r ^ kB : ℝ)) := by
      simpa using tendsto_const_nhds.sub hshift_zero
    have hden_tendsto :
        Filter.Tendsto (fun N : ℕ ↦ 1 - r ^ (N + kB + 1))
          Filter.atTop (nhds (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hshift_zero
    have hfrac_tendsto :
        Filter.Tendsto
          (fun N : ℕ ↦ ((r ^ kB : ℝ) - r ^ (N + kB + 1)) / (1 - r ^ (N + kB + 1)))
          Filter.atTop
          (nhds (((r ^ kB : ℝ) - 0) / (1 - 0))) := by
      simpa using hnum_tendsto.div hden_tendsto (by norm_num : (1 : ℝ) ≠ 0)
    have hseq_tendsto : Filter.Tendsto seq Filter.atTop (nhds ((gamblerRuinRatio p) ^ kB)) := by
      simpa [hseq_formula, r] using hfrac_tendsto
    simpa [seq] using hseq_tendsto
