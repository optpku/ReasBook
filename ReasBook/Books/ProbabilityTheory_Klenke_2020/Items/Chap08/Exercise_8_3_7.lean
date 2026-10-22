/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Helper for Exercise 8.3.7: the acceptance profile associated to the Radon--Nikodym density
`Q.rnDeriv P` and rejection constant `c`. -/
private noncomputable def rnDerivAcceptance
    (P Q : Measure E) (c : ℝ) : E → ℝ :=
  fun x ↦ (Q.rnDeriv P x).toReal / c

/-- Helper for Exercise 8.3.7: on `unitInterval`, the sublevel set `{u | (u : ℝ) ≤ r}` has mass
`min 1 r` whenever `r ≥ 0`. -/
private lemma unitIntervalSublevel_volume_eq (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure unitInterval) {u : unitInterval | (u : ℝ) ≤ r} =
      ENNReal.ofReal (min 1 r) := by
  let rI : unitInterval := ⟨min 1 r, by
    constructor
    · exact le_trans (by positivity) (min_le_left _ _)
    · exact min_le_left _ _⟩
  -- Proof comment: on `[0,1]`, the inequality `u ≤ r` is the same as `u ≤ min 1 r`.
  have hset : {u : unitInterval | (u : ℝ) ≤ r} = Set.Iic rI := by
    ext u
    constructor
    · intro hu
      change (u : ℝ) ≤ min 1 r
      exact le_min u.2.2 hu
    · intro hu
      exact le_trans (show (u : ℝ) ≤ (rI : ℝ) from hu) (min_le_right _ _)
  -- Proof comment: once the fiber is rewritten as an interval in `unitInterval`, `volume_Iic`
  -- gives the mass directly.
  simpa [hset, rI] using unitInterval.volume_Iic rI

/-- Helper for Exercise 8.3.7: the rejection acceptance profile is pointwise nonnegative. -/
private lemma rnDerivAcceptance_nonneg
    (P Q : Measure E) (c : ℝ) (hc : 0 < c) :
    ∀ x, 0 ≤ rnDerivAcceptance P Q c x := by
  intro x
  -- Proof comment: `rnDeriv` is nonnegative in `ENNReal`, and dividing by a positive constant
  -- preserves nonnegativity.
  exact div_nonneg (ENNReal.toReal_nonneg) hc.le

/-- Helper for Exercise 8.3.7: truncating the acceptance density by `min 1` does nothing `P`-a.e.
once the Radon--Nikodym derivative is bounded by `c`. -/
private lemma rnDerivAcceptance_truncated_ae
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c) :
    (fun x ↦ ENNReal.ofReal (min 1 (rnDerivAcceptance P Q c x))) =ᵐ[P]
      fun x ↦ ENNReal.ofReal (rnDerivAcceptance P Q c x) := by
  filter_upwards [hbounded] with x hx
  have hdiv : rnDerivAcceptance P Q c x ≤ 1 := by
    rw [rnDerivAcceptance, div_le_iff₀ hc, one_mul]
    exact hx
  -- Proof comment: the domination hypothesis turns the clipped density `min 1 accept` back into
  -- `accept` itself.
  rw [min_eq_right hdiv]

/-- Helper for Exercise 8.3.7: the acceptance density is the scaled Radon--Nikodym derivative,
viewed as an `ENNReal` density, almost everywhere with respect to `P`. -/
private lemma rnDerivAcceptance_density_ae
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) :
    (fun x ↦ ENNReal.ofReal (rnDerivAcceptance P Q c x)) =ᵐ[P]
      fun x ↦ (ENNReal.ofReal c)⁻¹ * Q.rnDeriv P x := by
  filter_upwards [Measure.rnDeriv_ne_top Q P] with x hx
  -- Proof comment: away from the null set where `rnDeriv = ⊤`, `ENNReal.ofReal ∘ toReal`
  -- recovers the original density, and the division by `c` becomes multiplication by `c⁻¹`.
  rw [rnDerivAcceptance, ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_toReal hx, div_eq_mul_inv,
    mul_comm]

/-- Helper for Exercise 8.3.7: the first coordinate of an accepted proposal pair has law
`(ENNReal.ofReal c)⁻¹ • Q`. -/
private lemma acceptedFstMap_eq_scaledTarget
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c) :
    Measure.map Prod.fst
      ((P.prod (volume : Measure unitInterval)).restrict
        {z : E × unitInterval | (z.2 : ℝ) ≤ rnDerivAcceptance P Q c z.1}) =
      (ENNReal.ofReal c)⁻¹ • Q := by
  let accept : E → ℝ := rnDerivAcceptance P Q c
  have haccept_nonneg : ∀ x, 0 ≤ accept x :=
    rnDerivAcceptance_nonneg P Q c hc
  have haccept_truncated :
      (fun x ↦ ENNReal.ofReal (min 1 (accept x))) =ᵐ[P]
        fun x ↦ ENNReal.ofReal (accept x) := by
    -- Proof comment: the Radon--Nikodym domination bound removes the truncation coming from the
    -- `unitInterval` slice.
    simpa [accept] using rnDerivAcceptance_truncated_ae P Q c hc hbounded
  have haccept_density :
      (fun x ↦ ENNReal.ofReal (accept x)) =ᵐ[P]
        fun x ↦ (ENNReal.ofReal c)⁻¹ * Q.rnDeriv P x := by
    -- Proof comment: the accepted slice density is exactly the scaled Radon--Nikodym derivative.
    simpa [accept] using rnDerivAcceptance_density_ae P Q c hc
  have hmeas_accept : Measurable accept := by
    -- Proof comment: `accept` is measurable because `rnDeriv` is measurable and all scalar
    -- operations happen in Borel spaces.
    have hmeas_rnDeriv : Measurable fun x ↦ (Q.rnDeriv P x).toReal :=
      (Measure.measurable_rnDeriv Q P).ennreal_toReal
    simpa [accept, rnDerivAcceptance] using hmeas_rnDeriv.div_const c
  let acceptedRegion : Set (E × unitInterval) :=
    {z : E × unitInterval | (z.2 : ℝ) ≤ accept z.1}
  have hacceptedRegion : MeasurableSet acceptedRegion := by
    -- Proof comment: the acceptance region is the sublevel set of two measurable coordinates.
    have hleft : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) := by
      fun_prop
    have hright : Measurable fun z : E × unitInterval ↦ accept z.1 :=
      hmeas_accept.comp measurable_fst
    simpa [acceptedRegion] using measurableSet_le hleft hright
  ext s hs
  -- Proof comment: rewrite the accepted first-coordinate mass as a product-measure integral over
  -- the vertical `unitInterval` slices above `s`.
  rw [Measure.map_apply measurable_fst hs, Measure.restrict_apply' hacceptedRegion]
  have hsliceSet :
      Prod.fst ⁻¹' s ∩ acceptedRegion =
        {z : E × unitInterval | z.1 ∈ s ∧ (z.2 : ℝ) ≤ accept z.1} := by
    ext z
    simp [acceptedRegion]
  rw [hsliceSet]
  have hsliceMeas :
      MeasurableSet {z : E × unitInterval | z.1 ∈ s ∧ (z.2 : ℝ) ≤ accept z.1} := by
    exact (hs.preimage measurable_fst).inter hacceptedRegion
  rw [Measure.prod_apply hsliceMeas]
  have hslice :
      (fun x ↦
        (volume : Measure unitInterval)
          (Prod.mk x ⁻¹' {z : E × unitInterval | z.1 ∈ s ∧ (z.2 : ℝ) ≤ accept z.1})) =
        s.indicator (fun x ↦ ENNReal.ofReal (min 1 (accept x))) := by
    ext x
    by_cases hx : x ∈ s
    · -- Proof comment: on `s`, the fiber mass is the volume of a single sublevel interval.
      simp [hx, unitIntervalSublevel_volume_eq, haccept_nonneg x]
    · -- Proof comment: outside `s`, the fiber is empty.
      simp [hx]
  rw [hslice, lintegral_indicator hs]
  calc
    ∫⁻ x in s, ENNReal.ofReal (min 1 (accept x)) ∂P
        = P.withDensity (fun x ↦ ENNReal.ofReal (min 1 (accept x))) s := by
          symm
          exact withDensity_apply _ hs
    _ = P.withDensity (fun x ↦ ENNReal.ofReal (accept x)) s := by
          rw [withDensity_congr_ae haccept_truncated]
    _ = P.withDensity (fun x ↦ (ENNReal.ofReal c)⁻¹ * Q.rnDeriv P x) s := by
          rw [withDensity_congr_ae haccept_density]
    _ = P.withDensity ((ENNReal.ofReal c)⁻¹ • Q.rnDeriv P) s := by
          rfl
    _ = ((ENNReal.ofReal c)⁻¹ • P.withDensity (Q.rnDeriv P)) s := by
          rw [withDensity_smul _ (Measure.measurable_rnDeriv Q P)]
    _ = ((ENNReal.ofReal c)⁻¹ • Q) s := by
          rw [Measure.withDensity_rnDeriv_eq _ _ hQP]

/-- Helper for Exercise 8.3.7: a single proposal-uniform pair is accepted with mass `c⁻¹`. -/
private lemma acceptedPairMass_eq_inv
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c) :
    (P.prod (volume : Measure unitInterval))
      {z : E × unitInterval | (z.2 : ℝ) ≤ rnDerivAcceptance P Q c z.1} =
        (ENNReal.ofReal c)⁻¹ := by
  let acceptedSet : Set (E × unitInterval) :=
    {z : E × unitInterval | (z.2 : ℝ) ≤ rnDerivAcceptance P Q c z.1}
  have hmeas_accept : Measurable fun x ↦ rnDerivAcceptance P Q c x := by
    -- Proof comment: `rnDerivAcceptance` inherits measurability from `rnDeriv`.
    have hmeas_rnDeriv : Measurable fun x ↦ (Q.rnDeriv P x).toReal :=
      (Measure.measurable_rnDeriv Q P).ennreal_toReal
    simpa [rnDerivAcceptance] using hmeas_rnDeriv.div_const c
  have hacceptedSet : MeasurableSet acceptedSet := by
    -- Proof comment: the accepted region is a measurable sublevel set in the pair space.
    have hleft : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) := by
      fun_prop
    have hright : Measurable fun z : E × unitInterval ↦ rnDerivAcceptance P Q c z.1 :=
      hmeas_accept.comp measurable_fst
    simpa [acceptedSet] using measurableSet_le hleft hright
  have hmap_univ :=
    congrArg
      (fun m : Measure E ↦ m Set.univ)
      (acceptedFstMap_eq_scaledTarget P Q c hc hQP hbounded)
  -- Proof comment: evaluating the pushed-forward accepted branch on `univ` gives the accepted
  -- mass of one proposal pair.
  simpa [acceptedSet, Measure.map_apply measurable_fst MeasurableSet.univ,
    Measure.restrict_apply' hacceptedSet, Measure.smul_apply, measure_univ] using hmap_univ

omit [MeasurableSpace E] in
/-- Helper for Exercise 8.3.7: if the first proposal is accepted, then
`rejectionSamplingValue` returns that head proposal. -/
private lemma rejectionSamplingValue_eq_head_of_headAccepted
    (accept : E → ℝ) (z : ℕ → E × unitInterval)
    (hhead : ((z 0).2 : ℝ) ≤ accept (z 0).1) :
    rejectionSamplingValue (fun n (_ : PUnit) ↦ (z n).1)
      (fun n (_ : PUnit) ↦ (z n).2) accept PUnit.unit = (z 0).1 := by
  let Xfull : ℕ → PUnit → E := fun n _ ↦ (z n).1
  let Ufull : ℕ → PUnit → unitInterval := fun n _ ↦ (z n).2
  have hnonempty :
      {n : ℕ | ((Ufull n PUnit.unit : unitInterval) : ℝ) ≤
        accept (Xfull n PUnit.unit)}.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [Xfull, Ufull] using hhead
  have hleast :
      IsLeast {n : ℕ | ((Ufull n PUnit.unit : unitInterval) : ℝ) ≤
        accept (Xfull n PUnit.unit)}
        (rejectionSamplingIndex Xfull Ufull accept PUnit.unit) :=
    @isLeast_rejectionSamplingIndex PUnit E Xfull Ufull accept PUnit.unit hnonempty
  have hindex :
      rejectionSamplingIndex Xfull Ufull accept PUnit.unit = 0 := by
    apply le_antisymm
    · exact hleast.2 (by simpa [Xfull, Ufull] using hhead)
    · exact Nat.zero_le _
  -- Proof comment: once the least accepted index is `0`, the sampled value is the head proposal.
  change
    Xfull (rejectionSamplingIndex Xfull Ufull accept PUnit.unit) PUnit.unit =
      Xfull 0 PUnit.unit
  simp [Xfull, hindex]

/-- Helper for Exercise 8.3.7: the probability that the first `N` proposals are all rejected is
the `N`-th power of the one-step rejection probability. -/
private lemma rejectPrefixMass_eq_pow
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c) (N : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ P.prod (volume : Measure unitInterval))
      (Set.pi (Finset.range N)
        (fun _ : ℕ ↦ {z : E × unitInterval | rnDerivAcceptance P Q c z.1 < z.2})) =
      (1 - (ENNReal.ofReal c)⁻¹) ^ N := by
  let pairLaw : Measure (E × unitInterval) := P.prod (volume : Measure unitInterval)
  let acceptedSet : Set (E × unitInterval) :=
    {z : E × unitInterval | (z.2 : ℝ) ≤ rnDerivAcceptance P Q c z.1}
  let rejectSet : Set (E × unitInterval) :=
    {z : E × unitInterval | rnDerivAcceptance P Q c z.1 < z.2}
  have hmeas_accept : Measurable fun x ↦ rnDerivAcceptance P Q c x := by
    -- Proof comment: measurability of the acceptance profile is needed for both branch events.
    have hmeas_rnDeriv : Measurable fun x ↦ (Q.rnDeriv P x).toReal :=
      (Measure.measurable_rnDeriv Q P).ennreal_toReal
    simpa [rnDerivAcceptance] using hmeas_rnDeriv.div_const c
  have hacceptedSet : MeasurableSet acceptedSet := by
    -- Proof comment: the accepted branch is a measurable `≤`-sublevel set.
    have hleft : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) := by
      fun_prop
    have hright : Measurable fun z : E × unitInterval ↦ rnDerivAcceptance P Q c z.1 :=
      hmeas_accept.comp measurable_fst
    simpa [acceptedSet] using measurableSet_le hleft hright
  have hrejectSet : MeasurableSet rejectSet := by
    -- Proof comment: the rejected branch is the complementary strict inequality event.
    have hleft : Measurable fun z : E × unitInterval ↦ rnDerivAcceptance P Q c z.1 :=
      hmeas_accept.comp measurable_fst
    have hright : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) := by
      fun_prop
    simpa [rejectSet] using measurableSet_lt hleft hright
  have haccepted_mass :
      pairLaw acceptedSet = (ENNReal.ofReal c)⁻¹ := by
    -- Proof comment: the one-step accepted mass is the total mass of the pushed-forward accepted
    -- branch computed earlier.
    simpa [pairLaw, acceptedSet] using acceptedPairMass_eq_inv P Q c hc hQP hbounded
  have hcompl : rejectSet = acceptedSetᶜ := by
    -- Proof comment: the acceptance and rejection events partition the pair space pointwise.
    ext z
    simp [rejectSet, acceptedSet, not_le]
  have hreject_mass :
      pairLaw rejectSet = 1 - (ENNReal.ofReal c)⁻¹ := by
    -- Proof comment: complementing the accepted branch identifies the one-step rejection mass.
    rw [hcompl, measure_compl hacceptedSet (measure_ne_top pairLaw acceptedSet), measure_univ,
      haccepted_mass]
  -- Proof comment: the first `N` rejections form a finite cylinder, so the product measure
  -- factors as the product of the one-step rejection mass.
  rw [Measure.infinitePi_pi (fun _ : ℕ ↦ pairLaw)]
  · simp [rejectSet, hreject_mass]
  · intro n hn
    exact hrejectSet

omit [MeasurableSpace E] in
/-- Helper for Exercise 8.3.7: after a rejected head, the rejection-sampling value is unchanged by
dropping that head as soon as some later proposal is accepted. -/
private lemma rejectionSamplingValue_eq_tail_of_headRejected_of_nonempty
    (accept : E → ℝ) (z : ℕ → E × unitInterval)
    (hheadRejected : accept (z 0).1 < (z 0).2)
    (hnonempty :
      {n : ℕ | ((z n).2 : ℝ) ≤ accept ((z n).1)}.Nonempty) :
    rejectionSamplingValue (fun n (_ : PUnit) ↦ (z n).1)
      (fun n (_ : PUnit) ↦ (z n).2) accept PUnit.unit =
        rejectionSamplingValue (fun n (_ : PUnit) ↦ (z (n + 1)).1)
          (fun n (_ : PUnit) ↦ (z (n + 1)).2) accept PUnit.unit := by
  let Xfull : ℕ → PUnit → E := fun n _ ↦ (z n).1
  let Ufull : ℕ → PUnit → unitInterval := fun n _ ↦ (z n).2
  let Xtail : ℕ → PUnit → E := fun n _ ↦ (z (n + 1)).1
  let Utail : ℕ → PUnit → unitInterval := fun n _ ↦ (z (n + 1)).2
  have htailNonempty :
      {n : ℕ | ((Utail n PUnit.unit : unitInterval) : ℝ) ≤
        accept (Xtail n PUnit.unit)}.Nonempty := by
    rcases hnonempty with ⟨m, hm⟩
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      subst hm0
      exact (not_le_of_gt hheadRejected) hm
    rcases Nat.exists_eq_add_one_of_ne_zero hm_ne_zero with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simpa [Xtail, Utail, Nat.succ_eq_add_one] using hm
  let tailIndex := rejectionSamplingIndex Xtail Utail accept PUnit.unit
  let fullIndex := rejectionSamplingIndex Xfull Ufull accept PUnit.unit
  have htailLeast :
      IsLeast {n : ℕ | ((Utail n PUnit.unit : unitInterval) : ℝ) ≤ accept (Xtail n PUnit.unit)}
        tailIndex :=
    @isLeast_rejectionSamplingIndex PUnit E Xtail Utail accept PUnit.unit htailNonempty
  have hfullLeast :
      IsLeast {n : ℕ | ((Ufull n PUnit.unit : unitInterval) : ℝ) ≤ accept (Xfull n PUnit.unit)}
        fullIndex :=
    @isLeast_rejectionSamplingIndex PUnit E Xfull Ufull accept PUnit.unit hnonempty
  have hfullIndex :
      fullIndex = tailIndex + 1 := by
    apply le_antisymm
    · -- Proof comment: the shifted least accepted index gives an accepted full index one step
      -- later, so the full least index is at most `tailIndex + 1`.
      exact Nat.sInf_le (by simpa [tailIndex, Xtail, Utail, Nat.succ_eq_add_one] using htailLeast.1)
    · -- Proof comment: the least accepted full index is positive because the head is rejected,
      -- so removing that head produces an accepted tail index bounded below by `tailIndex`.
      have hfull_pos : 0 < fullIndex := by
        have hfull_ne_zero : fullIndex ≠ 0 := by
          intro hzero
          have hheadAccepted : ((z 0).2 : ℝ) ≤ accept ((z 0).1) := by
            simpa [fullIndex, Xfull, Ufull, hzero] using hfullLeast.1
          exact (not_le_of_gt hheadRejected) hheadAccepted
        exact Nat.pos_of_ne_zero hfull_ne_zero
      rcases Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hfull_pos) with ⟨k, hk⟩
      have htailAccepted :
          ((Utail k PUnit.unit : unitInterval) : ℝ) ≤ accept (Xtail k PUnit.unit) := by
        simpa [fullIndex, Xfull, Ufull, Xtail, Utail, hk, Nat.succ_eq_add_one] using
          hfullLeast.1
      simpa [hk, Nat.succ_eq_add_one] using Nat.succ_le_succ (htailLeast.2 htailAccepted)
  -- Proof comment: once the full least accepted index is the tail index shifted by one, both
  -- sampled values are the same proposal.
  change Xfull fullIndex PUnit.unit = Xtail tailIndex PUnit.unit
  simp [Xfull, Xtail, hfullIndex]

-- Proof sketch: view each proposal-auxiliary pair `(X n, U n)` as i.i.d. with common law
-- `P.prod volume`. The acceptance event at step `n` has conditional probability
-- `(Q.rnDeriv P (X n ·)).toReal / c`, and `Q ≪ P` together with the bound by `c` identifies the
-- accepted proposal law with `Q`. Summing over the first accepted index yields the law of the
-- selected sample.
/-- Exercise 8.3.7: on a Polish space with its Borel `σ`-algebra, if `Q ≪ P` and the
Radon--Nikodym derivative `dQ/dP` is bounded by `c`, then the rejection-sampling value with
acceptance probability `x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [TopologicalSpace E] [BorelSpace E] [PolishSpace E]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := by
  let accept : E → ℝ := rnDerivAcceptance P Q c
  let pair : ℕ → Ω → E × unitInterval := fun n ω ↦ (X n ω, U n ω)
  let common : Measure (E × unitInterval) := P.prod (volume : Measure unitInterval)
  let acceptedMass : ENNReal := (ENNReal.ofReal c)⁻¹
  let acceptSlice : Set E → Set (E × unitInterval) :=
    fun s ↦ {z | z.1 ∈ s ∧ (z.2 : ℝ) ≤ accept z.1}
  let acceptTotal : Set (E × unitInterval) := {z | (z.2 : ℝ) ≤ accept z.1}
  let rejectSet : Set (E × unitInterval) := {z | accept z.1 < (z.2 : ℝ)}
  let firstSlice : Set E → ℕ → Set Ω :=
    fun s n ↦ {ω | X n ω ∈ s ∧ (U n ω : ℝ) ≤ accept (X n ω) ∧
      ∀ m < n, accept (X m ω) < (U m ω : ℝ)}
  let firstSlices : Set E → Set Ω := fun s ↦ ⋃ n : ℕ, firstSlice s n
  let acceptedEvent : Set Ω := firstSlices Set.univ
  let allReject : Set Ω := {ω | ∀ n, accept (X n ω) < (U n ω : ℝ)}
  let tail : Set E → Set Ω := fun s ↦ allReject ∩ X 0 ⁻¹' s
  -- Route correction: work directly on `Ω` by decomposing `{ω | Y ω ∈ s}` into the disjoint
  -- first-acceptance slices, then sum their geometric masses.
  have hmeas_accept : Measurable accept := by
    -- Proof comment: `accept` inherits measurability from `rnDeriv`.
    have hmeas_rnDeriv : Measurable fun x ↦ (Q.rnDeriv P x).toReal :=
      (Measure.measurable_rnDeriv Q P).ennreal_toReal
    simpa [accept, rnDerivAcceptance] using hmeas_rnDeriv.div_const c
  have hu_meas : Measurable fun z : E × unitInterval ↦ (z.2 : ℝ) := by
    fun_prop
  have haccept_prod_meas : Measurable fun z : E × unitInterval ↦ accept z.1 :=
    hmeas_accept.comp measurable_fst
  have hacceptSlice_meas (s : Set E) (hs : MeasurableSet s) : MeasurableSet (acceptSlice s) := by
    -- Proof comment: the accepted slice is a measurable cylinder over `s`.
    exact (hs.preimage measurable_fst).inter (measurableSet_le hu_meas haccept_prod_meas)
  have hacceptTotal_meas : MeasurableSet acceptTotal := by
    -- Proof comment: the total accepted region is the measurable `≤`-sublevel set.
    exact measurableSet_le hu_meas haccept_prod_meas
  have hrejectSet_meas : MeasurableSet rejectSet := by
    -- Proof comment: the rejection region is the complementary strict sublevel set.
    exact measurableSet_lt haccept_prod_meas hu_meas
  have hacceptSlice_mass (s : Set E) (hs : MeasurableSet s) :
      common (acceptSlice s) = acceptedMass * Q s := by
    have hslice_eq : Prod.fst ⁻¹' s ∩ acceptTotal = acceptSlice s := by
      ext z
      simp [acceptSlice, acceptTotal]
    have hmap :=
      congrArg
        (fun m : Measure E ↦ m s)
        (acceptedFstMap_eq_scaledTarget P Q c hc hQP hbounded)
    -- Proof comment: evaluate the accepted first-coordinate law on the measurable target set `s`.
    calc
      common (acceptSlice s) = common (Prod.fst ⁻¹' s ∩ acceptTotal) := by rw [hslice_eq]
      _ = (common.restrict acceptTotal) (Prod.fst ⁻¹' s) := by
            rw [Measure.restrict_apply' hacceptTotal_meas]
      _ = (Measure.map Prod.fst (common.restrict acceptTotal)) s := by
            symm
            rw [Measure.map_apply measurable_fst hs]
      _ = (acceptedMass • Q) s := by
            simpa [common, acceptedMass, accept] using hmap
      _ = acceptedMass * Q s := by
            simp [smul_eq_mul]
  have hacceptTotal_mass : common acceptTotal = acceptedMass := by
    -- Proof comment: the total acceptance mass is the measurable-set version with `s = univ`.
    simpa [common, acceptTotal, accept, acceptedMass] using
      acceptedPairMass_eq_inv P Q c hc hQP hbounded
  have h_ofReal_pos : 0 < ENNReal.ofReal c := by
    exact ENNReal.ofReal_pos.2 hc
  have hacceptedMass_ne_zero : acceptedMass ≠ 0 := by
    have hpos : 0 < acceptedMass := by
      exact by
        simpa [acceptedMass] using inv_pos.mpr h_ofReal_pos
    exact ne_of_gt hpos
  have hacceptedMass_ne_top : acceptedMass ≠ ⊤ := by
    exact ENNReal.inv_ne_top.2 (ne_of_gt h_ofReal_pos)
  have hacceptedMass_le_one : acceptedMass ≤ 1 := by
    calc
      acceptedMass = common acceptTotal := hacceptTotal_mass.symm
      _ ≤ common Set.univ := measure_mono (show acceptTotal ⊆ Set.univ from Set.subset_univ _)
      _ = 1 := by simp [common]
  have hrejectMass : common rejectSet = 1 - acceptedMass := by
    have hcompl : rejectSet = acceptTotalᶜ := by
      ext z
      simp [rejectSet, acceptTotal, not_le]
    -- Proof comment: rejection is the complement of the accepted region for one proposal pair.
    rw [hcompl, measure_compl hacceptTotal_meas (measure_ne_top common _), hacceptTotal_mass]
    simp
  have hfirstSlice_eq (s : Set E) (n : ℕ) :
      firstSlice s n =
        ⋂ i ∈ Finset.range (n + 1),
          pair i ⁻¹' (if i = n then acceptSlice s else rejectSet) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iInter₂.mpr ?_
      intro i hi
      by_cases hin : i = n
      · subst hin
        simpa [pair, acceptSlice] using ⟨hω.1, hω.2.1⟩
      · have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hi_lt : i < n := lt_of_le_of_ne hi_le hin
        simpa [pair, rejectSet, hin] using hω.2.2 i hi_lt
    · intro hω
      have hn :
          pair n ω ∈ (if n = n then acceptSlice s else rejectSet) := by
        exact Set.mem_iInter₂.mp hω n (by simp)
      have hn' : X n ω ∈ s ∧ (U n ω : ℝ) ≤ accept (X n ω) := by
        simpa [pair, acceptSlice] using hn
      refine ⟨hn'.1, hn'.2, ?_⟩
      intro m hm
      have hm_mem : m ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_lt hm)
      have hm' :
          pair m ω ∈ (if m = n then acceptSlice s else rejectSet) :=
        Set.mem_iInter₂.mp hω m hm_mem
      simpa [pair, rejectSet, hm.ne] using hm'
  have hfirstSlice_null (s : Set E) (hs : MeasurableSet s) (n : ℕ) :
      NullMeasurableSet (firstSlice s n) μ := by
    rw [hfirstSlice_eq s n]
    refine (Finset.range (n + 1)).nullMeasurableSet_biInter ?_
    intro i hi
    by_cases hin : i = n
    · simpa [hin] using
        (h_pair_law i).aemeasurable.nullMeasurableSet_preimage (hacceptSlice_meas s hs)
    · simpa [hin] using
        (h_pair_law i).aemeasurable.nullMeasurableSet_preimage hrejectSet_meas
  have hfirstSlice_mass (s : Set E) (hs : MeasurableSet s) (n : ℕ) :
      μ (firstSlice s n) = (1 - acceptedMass) ^ n * (acceptedMass * Q s) := by
    let stepSet : ℕ → Set (E × unitInterval) :=
      fun i ↦ if i = n then acceptSlice s else rejectSet
    have hstep_meas : ∀ i, i ∈ Finset.range (n + 1) → MeasurableSet (stepSet i) := by
      intro i hi
      by_cases hin : i = n
      · subst hin
        simpa [stepSet] using hacceptSlice_meas s hs
      · simpa [stepSet, hin] using hrejectSet_meas
    rw [hfirstSlice_eq s n,
      h_pair_iIndep.measure_inter_preimage_eq_mul (Finset.range (n + 1)) hstep_meas]
    have hstep_mass (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        μ (pair i ⁻¹' stepSet i) =
          if i = n then acceptedMass * Q s else 1 - acceptedMass := by
      rw [← Measure.map_apply_of_aemeasurable (h_pair_law i).aemeasurable (hstep_meas i hi),
        (h_pair_law i).map_eq]
      by_cases hin : i = n
      · subst hin
        simpa [common, stepSet] using hacceptSlice_mass s hs
      · simpa [stepSet, hin] using hrejectMass
    have hprefix_prod :
        ∏ i ∈ Finset.range n, (if i = n then acceptedMass * Q s else 1 - acceptedMass) =
          (1 - acceptedMass) ^ n := by
      calc
        ∏ i ∈ Finset.range n, (if i = n then acceptedMass * Q s else 1 - acceptedMass)
            = ∏ i ∈ Finset.range n, (1 - acceptedMass) := by
                refine Finset.prod_congr rfl ?_
                intro i hi
                simp [Nat.ne_of_lt (Finset.mem_range.mp hi)]
        _ = (1 - acceptedMass) ^ n := by
              simp
    -- Proof comment: independence factors the first-acceptance slice into `n` rejections and one
    -- accepted step.
    calc
      ∏ i ∈ Finset.range (n + 1), μ (pair i ⁻¹' stepSet i)
          = ∏ i ∈ Finset.range (n + 1),
              (if i = n then acceptedMass * Q s else 1 - acceptedMass) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hstep_mass i hi
      _ = (1 - acceptedMass) ^ n * (acceptedMass * Q s) := by
            rw [Finset.prod_range_succ, hprefix_prod]
            simp
  have hfirstSlice_pairwise (s : Set E) :
      Pairwise fun m n ↦ Disjoint (firstSlice s m) (firstSlice s n) := by
    intro m n hmn
    refine Set.disjoint_left.2 ?_
    intro ω hm hn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact False.elim ((not_le_of_gt (hn.2.2 m hlt)) hm.2.1)
    · exact False.elim ((not_le_of_gt (hm.2.2 n hgt)) hn.2.1)
  have hfirstSlices_null (s : Set E) (hs : MeasurableSet s) :
      NullMeasurableSet (firstSlices s) μ := by
    exact NullMeasurableSet.iUnion (fun n ↦ hfirstSlice_null s hs n)
  have hfirstSlices_measure (s : Set E) (hs : MeasurableSet s) :
      μ (firstSlices s) = Q s := by
    change μ (⋃ n : ℕ, firstSlice s n) = Q s
    rw [MeasureTheory.measure_iUnion₀
      (fun m n hmn ↦ Disjoint.aedisjoint (hfirstSlice_pairwise s hmn))
      (fun n ↦ hfirstSlice_null s hs n)]
    simp_rw [hfirstSlice_mass s hs]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have hone_sub :
        1 - (1 - acceptedMass) = acceptedMass :=
      ENNReal.sub_sub_cancel (by simp) hacceptedMass_le_one
    rw [hone_sub, ← mul_assoc, ENNReal.inv_mul_cancel hacceptedMass_ne_zero hacceptedMass_ne_top,
      one_mul]
  have hacceptedEvent_null : NullMeasurableSet acceptedEvent μ := by
    simpa [acceptedEvent] using hfirstSlices_null Set.univ MeasurableSet.univ
  have hacceptedEvent_measure : μ acceptedEvent = 1 := by
    simpa [acceptedEvent] using hfirstSlices_measure Set.univ MeasurableSet.univ
  have hallReject_eq_compl : allReject = acceptedEventᶜ := by
    ext ω
    constructor
    · intro hω hacc
      rcases Set.mem_iUnion.mp hacc with ⟨n, hn⟩
      exact not_lt_of_ge hn.2.1 (hω n)
    · intro hω
      by_cases hnonempty : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty
      · let n := rejectionSamplingIndex X U accept ω
        have hleast := isLeast_rejectionSamplingIndex X U accept hnonempty
        have hmem : ω ∈ acceptedEvent := by
          refine Set.mem_iUnion.mpr ?_
          refine ⟨n, ?_⟩
          refine ⟨by simp, hleast.1, ?_⟩
          intro m hm
          exact lt_of_not_ge (fun hmacc ↦ (not_lt_of_ge (hleast.2 hmacc)) hm)
        exact False.elim (hω hmem)
      · intro n
        exact lt_of_not_ge (fun hn ↦ hnonempty ⟨n, hn⟩)
  have hallReject_zero : μ allReject = 0 := by
    have hacceptedEvent_ae_univ : acceptedEvent =ᵐ[μ] Set.univ :=
      (ae_eq_univ_iff_measure_eq hacceptedEvent_null).2 (by simpa using hacceptedEvent_measure)
    have hallReject_ae_empty : allReject =ᵐ[μ] (∅ : Set Ω) := by
      rw [hallReject_eq_compl]
      simpa using hacceptedEvent_ae_univ.compl
    simpa using measure_congr hallReject_ae_empty
  have htail_zero (s : Set E) : μ (tail s) = 0 := by
    refine measure_mono_null ?_ hallReject_zero
    intro ω hω
    exact hω.1
  have htail_null (s : Set E) : NullMeasurableSet (tail s) μ :=
    NullMeasurableSet.of_null (htail_zero s)
  have hfirst_tail_disjoint (s : Set E) : Disjoint (firstSlices s) (tail s) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    rcases Set.mem_iUnion.mp hω₁ with ⟨n, hn⟩
    exact not_lt_of_ge hn.2.1 (hω₂.1 n)
  have hpreimage (s : Set E) :
      (rejectionSamplingValue X U accept) ⁻¹' s = firstSlices s ∪ tail s := by
    ext ω
    constructor
    · intro hω
      by_cases hnonempty : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty
      · let n := rejectionSamplingIndex X U accept ω
        have hleast := isLeast_rejectionSamplingIndex X U accept hnonempty
        left
        refine Set.mem_iUnion.mpr ?_
        refine ⟨n, ?_⟩
        refine ⟨?_, hleast.1, ?_⟩
        · simpa [rejectionSamplingValue, n] using hω
        · intro m hm
          exact lt_of_not_ge (fun hmacc ↦ (not_lt_of_ge (hleast.2 hmacc)) hm)
      · right
        refine ⟨?_, ?_⟩
        · intro n
          exact lt_of_not_ge (fun hn ↦ hnonempty ⟨n, hn⟩)
        · have hset : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} = ∅ := by
            ext n
            constructor
            · intro hn
              exact (hnonempty ⟨n, hn⟩).elim
            · intro hn
              simp at hn
          simpa [tail, rejectionSamplingValue, rejectionSamplingIndex, hset] using hω
    · rintro (hω | hω)
      · rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
        have hnonempty : {k : ℕ | (U k ω : ℝ) ≤ accept (X k ω)}.Nonempty := ⟨n, hn.2.1⟩
        have hleastn : IsLeast {k : ℕ | (U k ω : ℝ) ≤ accept (X k ω)} n := by
          refine ⟨hn.2.1, ?_⟩
          intro m hmacc
          by_cases hmn : m < n
          · exact False.elim ((not_le_of_gt (hn.2.2 m hmn)) hmacc)
          · exact le_of_not_gt hmn
        have hindex : rejectionSamplingIndex X U accept ω = n := by
          simpa [rejectionSamplingIndex] using hleastn.isGLB.csInf_eq hnonempty
        simpa [rejectionSamplingValue, hindex] using hn.1
      · have hset : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} = ∅ := by
          ext n
          constructor
          · intro hn
            exact ((not_le_of_gt (hω.1 n)) hn).elim
          · intro hn
            simp at hn
        simpa [tail, rejectionSamplingValue, rejectionSamplingIndex, hset] using hω.2
  have hvalue_nullMeasurable : NullMeasurable (rejectionSamplingValue X U accept) μ := by
    intro s hs
    rw [hpreimage s]
    exact (hfirstSlices_null s hs).union (htail_null s)
  have hvalue_aemeasurable : AEMeasurable (rejectionSamplingValue X U accept) μ :=
    hvalue_nullMeasurable.aemeasurable
  refine
    { aemeasurable := hvalue_aemeasurable
      map_eq := ?_ }
  refine Measure.ext ?_
  intro s hs
  -- Proof comment: the preimage of `s` is the disjoint union of the first-acceptance slices and a
  -- null tail, so its mass is exactly `Q s`.
  calc
    (Measure.map (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) μ) s
        = μ ((rejectionSamplingValue X U accept) ⁻¹' s) := by
            simpa [accept] using Measure.map_apply_of_aemeasurable hvalue_aemeasurable hs
    _ = μ (firstSlices s ∪ tail s) := by rw [hpreimage s]
    _ = μ (firstSlices s) + μ (tail s) := by
          rw [MeasureTheory.measure_union₀' (hfirstSlices_null s hs)
            (Disjoint.aedisjoint (hfirst_tail_disjoint s))]
    _ = Q s := by rw [hfirstSlices_measure s hs, htail_zero s, add_zero]

/-- Textbook-form i.i.d./independence variant: on a Polish space with its Borel `σ`-algebra, if
the proposals `X n` are i.i.d. with law `P`, the auxiliary variables `U n` are i.i.d. uniform on
`[0,1]`, and the two sequences are independent, then the rejection-sampling value with acceptance
probability `x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [TopologicalSpace E] [BorelSpace E] [PolishSpace E]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_rejectionSamplingValue_of_rnDeriv_le μ P Q c hc hQP hbounded X U
    h_pair_iIndep h_pair_law

/-- Textbook-form `IsLeast` bridge: on a Polish space with its Borel `σ`-algebra, if `N`
is almost surely the first accepted index and `Y = X N` almost surely, then `Y` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [TopologicalSpace E] [BorelSpace E] [PolishSpace E]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ (Q.rnDeriv P (X n ω)).toReal / c} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y Q μ := by
  let accept : E → ℝ := fun x ↦ (Q.rnDeriv P x).toReal / c
  refine (hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep μ P Q c hc hQP
    hbounded X U hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  refine hY.trans ?_
  simpa [accept] using ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U accept N hN
