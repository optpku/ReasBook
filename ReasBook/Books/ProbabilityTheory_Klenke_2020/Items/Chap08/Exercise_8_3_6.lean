/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

/-- The rejection-sampling index is the infimum of the accepted-index set; when that set is
nonempty, it is the first accepted proposal index. -/
noncomputable def rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → ℕ :=
  fun ω ↦ sInf {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}

/-- The rejection-sampling sample is the proposal evaluated at the rejection-sampling index; when
the accepted-index set is nonempty, this is the first accepted proposal value. -/
noncomputable def rejectionSamplingValue
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → E :=
  fun ω ↦ X (rejectionSamplingIndex X U accept ω) ω

/-- If the accepted-index set is nonempty, then the rejection-sampling index is its least
element. -/
theorem isLeast_rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) {ω : Ω}
    (hω : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty) :
    IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (rejectionSamplingIndex X U accept ω) := by
  constructor
  · simpa [rejectionSamplingIndex] using Nat.sInf_mem hω
  · intro n hn
    simpa [rejectionSamplingIndex] using (Nat.sInf_le hn)

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The acceptance probability used by rejection sampling for the proposal law `p` and the target
law `q`, with rejection constant `c`. -/
noncomputable def rejectionAcceptanceProb (p q : PMF E) (c : ℝ) (e : E) : ℝ :=
  if p e = 0 then 0 else (q e).toReal / (c * (p e).toReal)

-- Proof sketch: split on whether `p e = 0`. In the zero-mass case the definition is `0`. In the
-- nonzero case, rewrite `rejectionAcceptanceProb` and divide the domination inequality by the
-- positive number `c * (p e).toReal`.
omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
/-- Under the domination bound `q ≤ c p`, every rejection-sampling acceptance probability is at
most `1`. -/
theorem rejectionAcceptanceProb_le_one
    (p q : PMF E) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal) (e : E) :
    rejectionAcceptanceProb p q c e ≤ 1 := by
  by_cases hp : p e = 0
  · -- When the proposal mass vanishes, the acceptance probability is defined to be `0`.
    simp [rejectionAcceptanceProb, hp]
  · -- Otherwise we divide the domination inequality by the positive denominator `c * p{e}`.
    have hp_toReal_pos : 0 < (p e).toReal :=
      ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hden_pos : 0 < c * (p e).toReal :=
      mul_pos hc hp_toReal_pos
    have hdiv :
        (q e).toReal / (c * (p e).toReal) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      simpa [mul_assoc] using hdom e
    simpa [rejectionAcceptanceProb, hp] using hdiv

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
/-- Helper for Exercise 8.3.6: every rejection-sampling acceptance probability is nonnegative. -/
private theorem rejectionAcceptanceProb_nonneg
    (p q : PMF E) {c : ℝ} (hc : 0 < c) (e : E) :
    0 ≤ rejectionAcceptanceProb p q c e := by
  by_cases hp : p e = 0
  · -- Proof comment: the zero-mass branch is definitionally the value `0`.
    simp [rejectionAcceptanceProb, hp]
  · -- Proof comment: outside the zero-mass branch, the quotient has nonnegative numerator and
    -- positive denominator.
    have hp_toReal_pos : 0 < (p e).toReal :=
      ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hden_pos : 0 < c * (p e).toReal :=
      mul_pos hc hp_toReal_pos
    have hnum_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    simpa [rejectionAcceptanceProb, hp] using div_nonneg hnum_nonneg hden_pos.le

/-- Helper for Exercise 8.3.6: on `unitInterval`, the sublevel set `{u | (u : ℝ) ≤ r}` has mass
`r` whenever `0 ≤ r ≤ 1`. -/
private lemma unitIntervalSublevel_volume_eq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (volume : Measure unitInterval) {u : unitInterval | (u : ℝ) ≤ r} = ENNReal.ofReal r := by
  let rI : unitInterval := ⟨r, ⟨hr0, hr1⟩⟩
  have hset : {u : unitInterval | (u : ℝ) ≤ r} = Set.Iic rI := by
    ext u
    change ((u : ℝ) ≤ r ↔ (u : ℝ) ≤ (rI : ℝ))
    simp [rI]
  rw [hset]
  have hright : ENNReal.ofReal (rI : ℝ) = ENNReal.ofReal r := by
    simp [rI]
  rw [← hright]
  exact unitInterval.volume_Iic rI

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
/-- Helper for Exercise 8.3.6: the proposal mass at `e` times the acceptance probability equals
`c⁻¹ * q{e}` in real form. -/
private theorem toReal_mul_rejectionAcceptanceProb
    (p q : PMF E) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal) (e : E) :
    (p e).toReal * rejectionAcceptanceProb p q c e = c⁻¹ * (q e).toReal := by
  by_cases hp : p e = 0
  · have hq_toReal_eq_zero : (q e).toReal = 0 := by
      have hq_le_zero : (q e).toReal ≤ 0 := by simpa [hp] using hdom e
      exact le_antisymm hq_le_zero ENNReal.toReal_nonneg
    simp [rejectionAcceptanceProb, hp, hq_toReal_eq_zero]
  · have hp_toReal_pos : 0 < (p e).toReal :=
      ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hp_toReal_ne : (p e).toReal ≠ 0 :=
      ne_of_gt hp_toReal_pos
    simp [rejectionAcceptanceProb, hp]
    field_simp [hc.ne', hp_toReal_ne]

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
/-- Helper for Exercise 8.3.6: the singleton fiber of `rejectionSamplingValue` splits into the
disjoint first-acceptance slices together with the all-reject tail. -/
private theorem preimage_singleton_rejectionSamplingValue
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) (e : E) :
    (rejectionSamplingValue X U accept) ⁻¹' ({e} : Set E) =
      (⋃ n : ℕ,
        {ω | X n ω = e ∧ (U n ω : ℝ) ≤ accept (X n ω) ∧
          ∀ m < n, accept (X m ω) < (U m ω : ℝ)}) ∪
        ({ω | ∀ n, accept (X n ω) < (U n ω : ℝ)} ∩ {ω | X 0 ω = e}) := by
  ext ω
  constructor
  · intro hω
    by_cases hnonempty : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty
    · -- Proof comment: when some proposal is accepted, the sampled index is the least accepted
      -- one, so `ω` belongs to the corresponding first-acceptance slice.
      let n := rejectionSamplingIndex X U accept ω
      have hleast := isLeast_rejectionSamplingIndex X U accept hnonempty
      left
      refine Set.mem_iUnion.mpr ?_
      refine ⟨n, ?_⟩
      refine ⟨?_, hleast.1, ?_⟩
      · simpa [rejectionSamplingValue, n] using hω
      · intro m hm
        exact lt_of_not_ge (fun hmacc ↦ (not_lt_of_ge (hleast.2 hmacc)) hm)
    · -- Proof comment: if every proposal is rejected, then `Nat.sInf` defaults to `0`, so the
      -- sampled value is `X 0`.
      right
      refine ⟨?_, ?_⟩
      · intro n
        exact lt_of_not_ge (fun hn ↦ hnonempty ⟨n, hn⟩)
      · have hset :
          {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} = ∅ := by
          ext n
          constructor
          · intro hn
            exact (hnonempty ⟨n, hn⟩).elim
          · intro hn
            simp at hn
        simpa [rejectionSamplingValue, rejectionSamplingIndex, hset] using hω
  · rintro (hω | hω)
    · rcases Set.mem_iUnion.mp hω with ⟨n, hωn⟩
      rcases hωn with ⟨hXe, hacc, hrejs⟩
      have hnonempty : {k : ℕ | (U k ω : ℝ) ≤ accept (X k ω)}.Nonempty := ⟨n, hacc⟩
      -- Proof comment: the displayed rejection conditions show that `n` is the least accepted
      -- index, hence `rejectionSamplingValue` evaluates to `X n`.
      have hleastn : IsLeast {k : ℕ | (U k ω : ℝ) ≤ accept (X k ω)} n := by
        refine ⟨hacc, ?_⟩
        intro m hmacc
        by_cases hmn : m < n
        · exact False.elim ((not_le_of_gt (hrejs m hmn)) hmacc)
        · exact le_of_not_gt hmn
      have hindex : rejectionSamplingIndex X U accept ω = n := by
        simpa [rejectionSamplingIndex] using hleastn.isGLB.csInf_eq hnonempty
      simpa [rejectionSamplingValue, hindex] using hXe
    · rcases hω with ⟨hallReject, hX0⟩
      -- Proof comment: on the all-reject tail the accepted-index set is empty, so the sampled
      -- value again reduces to `X 0`.
      have hset : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} = ∅ := by
        ext n
        constructor
        · intro hn
          exact ((not_le_of_gt (hallReject n)) hn).elim
        · intro hn
          simp at hn
      simpa [rejectionSamplingValue, rejectionSamplingIndex, hset] using hX0

-- Proof sketch: for each `e`, compute the probability that the first accepted proposal equals
-- `e` by summing over the first acceptance time. The pairwise i.i.d. hypothesis gives a geometric
-- factor from the previous rejections and identifies the acceptance probability at time `n` with
-- `q e / c`; summing the geometric series yields exactly `q e`. Equality of singleton masses then
-- gives `HasLaw Y q.toMeasure μ`.
/-- Exercise 8.3.6: in the canonical paired formulation, if the proposal-auxiliary pairs
`(X n, U n)` form an independent sequence with common law `p × uniform[0,1]`, then the
rejection-sampling value associated to `rejectionAcceptanceProb p q c` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_pair_iIndep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω))
      (p.toMeasure.prod volume) μ) :
    -- Route correction: the remaining work is the singleton-fiber measure computation for the
    -- `sInf`-based definition of `rejectionSamplingValue`, followed by countable additivity over
    -- the disjoint first-acceptance slices.
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := by
  let accept : E → ℝ := rejectionAcceptanceProb p q c
  let pair : ℕ → Ω → E × unitInterval := fun n ω ↦ (X n ω, U n ω)
  let common : Measure (E × unitInterval) := p.toMeasure.prod volume
  let acceptSlice : E → Set (E × unitInterval) :=
    fun e ↦ {z | z.1 = e ∧ (z.2 : ℝ) ≤ accept z.1}
  let acceptTotal : Set (E × unitInterval) := {z | (z.2 : ℝ) ≤ accept z.1}
  let rejectSet : Set (E × unitInterval) := {z | accept z.1 < (z.2 : ℝ)}
  let firstSlice : E → ℕ → Set Ω :=
    fun e n ↦ {ω | X n ω = e ∧ (U n ω : ℝ) ≤ accept (X n ω) ∧
      ∀ m < n, accept (X m ω) < (U m ω : ℝ)}
  let firstSlices : E → Set Ω := fun e ↦ ⋃ n : ℕ, firstSlice e n
  let acceptedEvent : Set Ω := ⋃ e : E, firstSlices e
  let allReject : Set Ω := {ω | ∀ n, accept (X n ω) < (U n ω : ℝ)}
  let tail : E → Set Ω := fun e ↦ allReject ∩ {ω | X 0 ω = e}
  let acceptedMass : ENNReal := ENNReal.ofReal (c⁻¹)
  have haccept_meas : Measurable accept :=
    measurable_of_countable accept
  have haccept_prod_meas : Measurable fun z : E × unitInterval ↦ accept z.1 :=
    haccept_meas.comp measurable_fst
  have hu_meas : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) :=
    measurable_subtype_coe.comp measurable_snd
  have hacceptSlice_meas (e : E) : MeasurableSet (acceptSlice e) := by
    refine (measurableSet_eq_fun measurable_fst measurable_const).inter ?_
    exact measurableSet_le hu_meas haccept_prod_meas
  have hacceptTotal_meas : MeasurableSet acceptTotal :=
    measurableSet_le hu_meas haccept_prod_meas
  have hrejectSet_meas : MeasurableSet rejectSet :=
    measurableSet_lt haccept_prod_meas hu_meas
  have hacceptSlice_prod (e : E) :
      acceptSlice e = ({e} : Set E) ×ˢ {u : unitInterval | (u : ℝ) ≤ accept e} := by
    ext z
    constructor
    · intro hz
      refine ⟨hz.1, ?_⟩
      exact hz.1 ▸ hz.2
    · rintro ⟨hz1, hz2⟩
      refine ⟨hz1, ?_⟩
      exact hz1.symm ▸ hz2
  have hacceptSlice_mass (e : E) :
      common (acceptSlice e) = acceptedMass * q e := by
    have hnonneg : 0 ≤ accept e := by
      simpa [accept] using rejectionAcceptanceProb_nonneg p q hc e
    have hle_one : accept e ≤ 1 := by
      simpa [accept] using rejectionAcceptanceProb_le_one p q hc hdom e
    have hvol :
        (volume : Measure unitInterval) {u : unitInterval | (u : ℝ) ≤ accept e} =
          ENNReal.ofReal (accept e) :=
      unitIntervalSublevel_volume_eq (accept e) hnonneg hle_one
    change (p.toMeasure.prod volume) (acceptSlice e) = acceptedMass * q e
    rw [hacceptSlice_prod e, Measure.prod_prod,
      p.toMeasure_apply_singleton e (measurableSet_singleton e), hvol]
    rw [← ENNReal.ofReal_toReal (p.apply_ne_top e),
      ← ENNReal.ofReal_mul (show 0 ≤ (p e).toReal by exact ENNReal.toReal_nonneg),
      toReal_mul_rejectionAcceptanceProb p q hc hdom e]
    change ENNReal.ofReal (c⁻¹ * (q e).toReal) = ENNReal.ofReal (c⁻¹) * q e
    rw [← ENNReal.ofReal_toReal (q.apply_ne_top e),
      ENNReal.ofReal_mul (by positivity)]
    simp
  have hacceptTotal_eq : acceptTotal = ⋃ e : E, acceptSlice e := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.mpr ?_
      refine ⟨z.1, ?_⟩
      exact ⟨rfl, hz⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨e, he⟩
      exact he.2
  have hacceptSlice_pairwise : Pairwise fun e₁ e₂ ↦ Disjoint (acceptSlice e₁) (acceptSlice e₂) := by
    intro e₁ e₂ hne
    refine Set.disjoint_left.2 ?_
    intro z hz₁ hz₂
    exact hne (hz₁.1.symm.trans hz₂.1)
  have hacceptTotal_mass : common acceptTotal = acceptedMass := by
    rw [hacceptTotal_eq, MeasureTheory.measure_iUnion hacceptSlice_pairwise hacceptSlice_meas]
    simp [hacceptSlice_mass, acceptedMass, ENNReal.tsum_mul_left, q.tsum_coe]
  have hrejectMass : common rejectSet = 1 - acceptedMass := by
    have hcompl : rejectSet = acceptTotalᶜ := by
      ext z
      simp [rejectSet, acceptTotal, not_le]
    change (p.toMeasure.prod volume) rejectSet = 1 - acceptedMass
    rw [hcompl, measure_compl hacceptTotal_meas (measure_ne_top common _), hacceptTotal_mass]
    simp
  have hacceptedMass_ne_zero : acceptedMass ≠ 0 := by
    have hpos : 0 < acceptedMass := by
      simpa [acceptedMass] using (show 0 < ENNReal.ofReal (c⁻¹) by positivity)
    exact ne_of_gt hpos
  have hacceptedMass_ne_top : acceptedMass ≠ ⊤ := by
    simp [acceptedMass]
  have hacceptedMass_le_one : acceptedMass ≤ 1 := by
    calc
      acceptedMass = common acceptTotal := hacceptTotal_mass.symm
      _ ≤ common Set.univ := measure_mono (show acceptTotal ⊆ Set.univ from Set.subset_univ _)
      _ = 1 := by simp [common]
  have hfirstSlice_eq (e : E) (n : ℕ) :
      firstSlice e n =
        ⋂ i ∈ Finset.range (n + 1),
          pair i ⁻¹' (if i = n then acceptSlice e else rejectSet) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iInter₂.mpr ?_
      intro i hi
      by_cases hin : i = n
      · subst hin
        simpa [pair, acceptSlice] using ⟨hω.1, hω.2.1⟩
      · have hi_le : i ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hi_lt : i < n :=
          lt_of_le_of_ne hi_le hin
        simpa [pair, rejectSet, hin] using hω.2.2 i hi_lt
    · intro hω
      have hn :
          pair n ω ∈ (if n = n then acceptSlice e else rejectSet) := by
        exact Set.mem_iInter₂.mp hω n (by simp)
      have hn' : X n ω = e ∧ (U n ω : ℝ) ≤ accept (X n ω) := by
        simpa [pair, acceptSlice] using hn
      refine ⟨hn'.1, hn'.2, ?_⟩
      intro m hm
      have hm_mem : m ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_lt hm)
      have hm' :
          pair m ω ∈ (if m = n then acceptSlice e else rejectSet) :=
        Set.mem_iInter₂.mp hω m hm_mem
      simpa [pair, rejectSet, hm.ne] using hm'
  have hfirstSlice_null (e : E) (n : ℕ) : NullMeasurableSet (firstSlice e n) μ := by
    rw [hfirstSlice_eq e n]
    refine (Finset.range (n + 1)).nullMeasurableSet_biInter ?_
    intro i hi
    by_cases hin : i = n
    · simpa [hin] using
        (h_pair_law i).aemeasurable.nullMeasurableSet_preimage (hacceptSlice_meas e)
    · simpa [hin] using
        (h_pair_law i).aemeasurable.nullMeasurableSet_preimage hrejectSet_meas
  have hfirstSlice_mass (e : E) (n : ℕ) :
      μ (firstSlice e n) = (1 - acceptedMass) ^ n * (acceptedMass * q e) := by
    let stepSet : ℕ → Set (E × unitInterval) :=
      fun i ↦ if i = n then acceptSlice e else rejectSet
    have hstep_meas : ∀ i, i ∈ Finset.range (n + 1) → MeasurableSet (stepSet i) := by
      intro i hi
      by_cases hin : i = n
      · subst hin
        simpa [stepSet] using hacceptSlice_meas e
      · simpa [stepSet, hin] using hrejectSet_meas
    rw [hfirstSlice_eq e n,
      h_pair_iIndep.measure_inter_preimage_eq_mul (Finset.range (n + 1)) hstep_meas]
    have hstep_mass (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        μ (pair i ⁻¹' stepSet i) = if i = n then acceptedMass * q e else 1 - acceptedMass := by
      rw [← Measure.map_apply_of_aemeasurable (h_pair_law i).aemeasurable (hstep_meas i hi),
        (h_pair_law i).map_eq]
      by_cases hin : i = n
      · subst hin
        simpa [common, stepSet] using hacceptSlice_mass e
      · simpa [stepSet, hin] using hrejectMass
    have hprefix_prod :
        ∏ i ∈ Finset.range n, (if i = n then acceptedMass * q e else 1 - acceptedMass) =
          (1 - acceptedMass) ^ n := by
      calc
        ∏ i ∈ Finset.range n, (if i = n then acceptedMass * q e else 1 - acceptedMass)
            = ∏ i ∈ Finset.range n, (1 - acceptedMass) := by
                refine Finset.prod_congr rfl ?_
                intro i hi
                simp [Nat.ne_of_lt (Finset.mem_range.mp hi)]
        _ = (1 - acceptedMass) ^ n := by
              simp
    calc
      ∏ i ∈ Finset.range (n + 1), μ (pair i ⁻¹' stepSet i)
          = ∏ i ∈ Finset.range (n + 1),
              (if i = n then acceptedMass * q e else 1 - acceptedMass) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hstep_mass i hi
      _ = (1 - acceptedMass) ^ n * (acceptedMass * q e) := by
            rw [Finset.prod_range_succ, hprefix_prod]
            simp
  have hfirstSlice_pairwise (e : E) :
      Pairwise fun m n ↦ Disjoint (firstSlice e m) (firstSlice e n) := by
    intro m n hmn
    refine Set.disjoint_left.2 ?_
    intro ω hm hn
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · exact False.elim ((not_le_of_gt (hn.2.2 m hlt)) hm.2.1)
    · exact False.elim ((not_le_of_gt (hm.2.2 n hlt)) hn.2.1)
  have hfirstSlices_null (e : E) : NullMeasurableSet (firstSlices e) μ := by
    exact NullMeasurableSet.iUnion (fun n ↦ hfirstSlice_null e n)
  have hfirstSlices_measure (e : E) : μ (firstSlices e) = q e := by
    change μ (⋃ n : ℕ, firstSlice e n) = q e
    rw [MeasureTheory.measure_iUnion₀
      (fun m n hmn ↦ Disjoint.aedisjoint (hfirstSlice_pairwise e hmn))
      (fun n ↦ hfirstSlice_null e n)]
    simp_rw [hfirstSlice_mass]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have hone_sub :
        1 - (1 - acceptedMass) = acceptedMass :=
      ENNReal.sub_sub_cancel (by simp) hacceptedMass_le_one
    rw [hone_sub, ← mul_assoc, ENNReal.inv_mul_cancel hacceptedMass_ne_zero hacceptedMass_ne_top,
      one_mul]
  have hacceptedEvent_null : NullMeasurableSet acceptedEvent μ := by
    exact NullMeasurableSet.iUnion (fun e ↦ hfirstSlices_null e)
  have hfirstSlices_pairwise :
      Pairwise fun e₁ e₂ ↦ Disjoint (firstSlices e₁) (firstSlices e₂) := by
    intro e₁ e₂ hne
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    rcases Set.mem_iUnion.mp hω₁ with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hω₂ with ⟨m, hm⟩
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · exact False.elim ((not_le_of_gt (hm.2.2 n hlt)) hn.2.1)
    · exact hne (hn.1.symm.trans hm.1)
    · exact False.elim ((not_le_of_gt (hn.2.2 m hgt)) hm.2.1)
  have hacceptedEvent_measure : μ acceptedEvent = 1 := by
    change μ (⋃ e : E, firstSlices e) = 1
    rw [MeasureTheory.measure_iUnion₀
      (fun e₁ e₂ hne ↦ Disjoint.aedisjoint (hfirstSlices_pairwise hne))
      (fun e ↦ hfirstSlices_null e)]
    convert q.tsum_coe using 1
    simp [hfirstSlices_measure]
  have hallReject_eq_compl : allReject = acceptedEventᶜ := by
    ext ω
    constructor
    · intro hω hacc
      rcases Set.mem_iUnion.mp hacc with ⟨e, he⟩
      rcases Set.mem_iUnion.mp he with ⟨n, hn⟩
      exact not_lt_of_ge hn.2.1 (hω n)
    · intro hω
      by_cases hnonempty : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty
      · let n := rejectionSamplingIndex X U accept ω
        have hleast := isLeast_rejectionSamplingIndex X U accept hnonempty
        have hmem : ω ∈ acceptedEvent := by
          refine Set.mem_iUnion.mpr ?_
          refine ⟨X n ω, Set.mem_iUnion.mpr ?_⟩
          refine ⟨n, ?_⟩
          refine ⟨rfl, hleast.1, ?_⟩
          intro m hm
          exact lt_of_not_ge (fun hmacc ↦ (not_lt_of_ge (hleast.2 hmacc)) hm)
        exact False.elim (hω hmem)
      · intro n
        exact lt_of_not_ge (fun hn ↦ hnonempty ⟨n, hn⟩)
  have hallReject_zero : μ allReject = 0 := by
    have hacceptedEvent_ae_univ : acceptedEvent =ᵐ[μ] Set.univ :=
      (ae_eq_univ_iff_measure_eq hacceptedEvent_null).2 (by
        simpa using hacceptedEvent_measure)
    have hallReject_ae_empty : allReject =ᵐ[μ] (∅ : Set Ω) := by
      rw [hallReject_eq_compl]
      simpa using hacceptedEvent_ae_univ.compl
    simpa using measure_congr hallReject_ae_empty
  have htail_zero (e : E) : μ (tail e) = 0 := by
    refine measure_mono_null ?_ hallReject_zero
    intro ω hω
    exact hω.1
  have htail_null (e : E) : NullMeasurableSet (tail e) μ :=
    NullMeasurableSet.of_null (htail_zero e)
  have hfirst_tail_disjoint (e : E) : Disjoint (firstSlices e) (tail e) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    rcases Set.mem_iUnion.mp hω₁ with ⟨n, hn⟩
    exact not_lt_of_ge hn.2.1 (hω₂.1 n)
  have hpreimage_singleton_null (e : E) :
      NullMeasurableSet ((rejectionSamplingValue X U accept) ⁻¹' ({e} : Set E)) μ := by
    rw [preimage_singleton_rejectionSamplingValue X U accept e]
    exact (hfirstSlices_null e).union (htail_null e)
  have hvalue_nullMeasurable : NullMeasurable (rejectionSamplingValue X U accept) μ := by
    intro s hs
    rw [← Set.biUnion_preimage_singleton (rejectionSamplingValue X U accept) s]
    exact NullMeasurableSet.biUnion s.to_countable
      (fun e _ ↦ hpreimage_singleton_null e)
  have hvalue_aemeasurable : AEMeasurable (rejectionSamplingValue X U accept) μ :=
    hvalue_nullMeasurable.aemeasurable
  refine
    { aemeasurable := hvalue_aemeasurable
      map_eq := ?_ }
  refine Measure.ext_of_singleton ?_
  intro e
  rw [Measure.map_apply_of_aemeasurable hvalue_aemeasurable (measurableSet_singleton e),
    preimage_singleton_rejectionSamplingValue X U accept e]
  rw [MeasureTheory.measure_union₀' (hfirstSlices_null e)
    (Disjoint.aedisjoint (hfirst_tail_disjoint e)), hfirstSlices_measure, htail_zero e, add_zero,
    q.toMeasure_apply_singleton e (measurableSet_singleton e)]

/-- Independent random variables with laws `ν` and `η` have joint law `ν.prod η`. -/
theorem hasLaw_prod_of_hasLaw_of_indep
    {F G : Type*} [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ν : Measure F} {η : Measure G}
    (X : Ω → F) (Y : Ω → G)
    (hX_law : HasLaw X ν μ) (hY_law : HasLaw Y η μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (ν.prod η) μ := by
  refine
    { aemeasurable := hX_law.aemeasurable.prodMk hY_law.aemeasurable
      map_eq := ?_ }
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX_law.aemeasurable hY_law.aemeasurable).mp hXY,
    hX_law.map_eq, hY_law.map_eq]

omit [MeasurableSingletonClass E] [Countable E] in
/-- If `X` and `U` are i.i.d. families and the sequence-valued random elements are independent,
then the paired family `n ↦ (X n, U n)` is independent. -/
theorem iIndepFun_pair_of_iIndepFun_of_indepFun
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ν : Measure E}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) ν μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ := by
  rw [iIndepFun_iff_finset]
  intro s
  have hX_restrict' : iIndepFun (fun i : s ↦ X i) μ :=
    hX_iIndep.precomp Subtype.val_injective
  have hX_restrict : iIndepFun (s.restrict X) μ := by
    simpa [Finset.restrict] using hX_restrict'
  have hU_restrict' : iIndepFun (fun i : s ↦ U i) μ :=
    hU_iIndep.precomp Subtype.val_injective
  have hU_restrict : iIndepFun (s.restrict U) μ := by
    simpa [Finset.restrict] using hU_restrict'
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · change μ.map (fun ω (i : s) ↦ (X i ω, U i ω)) =
      Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
    let φ : (ℕ → E) → (s → E) := fun f i ↦ f i
    let ψ : (ℕ → unitInterval) → (s → unitInterval) := fun f i ↦ f i
    have h_indep_restrict :
        IndepFun (fun ω (i : s) ↦ X i ω) (fun ω (i : s) ↦ U i ω) μ := by
      have hφ : Measurable φ := by
        fun_prop
      have hψ : Measurable ψ := by
        fun_prop
      simpa [φ, ψ] using h_seq_indep.comp hφ hψ
    have h_map_eq :
        μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
          (Measure.pi fun i : s ↦ μ.map (X i)).prod
            (Measure.pi fun i : s ↦ μ.map (U i)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (aemeasurable_pi_lambda _ fun i : s ↦ (hX_law i).aemeasurable)
        (aemeasurable_pi_lambda _ fun i : s ↦ (hU_law i).aemeasurable)).mp h_indep_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hX_law i).aemeasurable).mp hX_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hU_law i).aemeasurable).mp hU_restrict]
    have h_pair_map_eq (i : s) :
        μ.map (fun ω ↦ (X i ω, U i ω)) = (μ.map (X i)).prod (μ.map (U i)) := by
      have h_indep_i : X i ⟂ᵢ[μ] U i := by
        simpa using h_seq_indep.comp (measurable_pi_apply (i : ℕ)) (measurable_pi_apply (i : ℕ))
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (hX_law i).aemeasurable (hU_law i).aemeasurable).mp h_indep_i]
    let e := MeasurableEquiv.arrowProdEquivProdArrow E unitInterval s
    have h_pair_vec_aemeasurable : AEMeasurable (fun ω (i : s) ↦ (X i ω, U i ω)) μ :=
      aemeasurable_pi_lambda _ fun i : s ↦
        ((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable)
    rw [← e.map_measurableEquiv_injective.eq_iff]
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable h_pair_vec_aemeasurable]
    change μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
      Measure.map e (Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω))))
    refine h_map_eq.trans ?_
    symm
    calc
      Measure.map e (Measure.pi fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
          = Measure.map e (Measure.pi fun i : s ↦ (μ.map (X i)).prod (μ.map (U i))) := by
              simp [h_pair_map_eq]
      _ = (Measure.pi fun i : s ↦ μ.map (X i)).prod (Measure.pi fun i : s ↦ μ.map (U i)) :=
            (measurePreserving_arrowProdEquivProdArrow E unitInterval s
              (fun i : s ↦ μ.map (X i)) (fun i : s ↦ μ.map (U i))).map_eq
  · intro i
    simpa [Finset.restrict] using
      (((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable) :
        AEMeasurable (fun ω ↦ (X i ω, U i ω)) μ)

/-- Corollary for Exercise 8.3.6: if the proposals `X n` are i.i.d. with law `p`, the auxiliary
variables `U n` are i.i.d. uniform on `[0,1]`, and the two sequences are independent, then the
associated rejection-sampling value has law `q`. -/
theorem hasLaw_of_rejection_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ (ν := p.toMeasure) X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (p.toMeasure.prod volume) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_of_rejection_sampling_of_pair_iIndep μ p q c X U hc hdom h_pair_iIndep h_pair_law

/-- If `N` is almost surely the first accepted proposal index, then the associated proposal value
agrees almost surely with the canonical rejection-sampling value. -/
theorem ae_eq_rejectionSamplingValue_of_ae_isLeast
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) (N : Ω → ℕ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (N ω)) :
    (fun ω ↦ X (N ω) ω) =ᵐ[μ] rejectionSamplingValue X U accept := by
  filter_upwards [hN] with ω hω
  dsimp [rejectionSamplingValue, rejectionSamplingIndex]
  rw [hω.isGLB.csInf_eq hω.nonempty]

/-- Textbook-form bridge for Exercise 8.3.6: if `N` is almost surely the first accepted index and
`Y = X N` almost surely, then `Y` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ rejectionAcceptanceProb p q c (X n ω)} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y q.toMeasure μ := by
  refine (hasLaw_of_rejection_sampling μ p q c X U hc hdom
    hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  exact hY.trans (ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U
    (rejectionAcceptanceProb p q c) N hN)
