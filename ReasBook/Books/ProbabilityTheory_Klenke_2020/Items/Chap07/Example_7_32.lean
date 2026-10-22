/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open Filter
open scoped MeasureTheory BigOperators Topology

/- Example 7.32 (1): the textbook assertion that a measure on `ℝ` given by a density with respect
to Lebesgue measure is absolutely continuous with respect to Lebesgue measure is the canonical
theorem `withDensity_absolutelyContinuous`, specialized to `volume`. -/
recall withDensity_absolutelyContinuous

/-- Helper for Example 7.32: an almost-everywhere positive density makes `volume` absolutely
continuous with respect to `volume.withDensity f`. -/
private theorem volume_absolutelyContinuous_withDensity_of_ae_pos (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hpos : ∀ᵐ x ∂volume, 0 < f x) :
    volume ≪ volume.withDensity f := by
  refine withDensity_absolutelyContinuous' hf ?_
  filter_upwards [hpos] with x hx
  exact ne_of_gt hx

-- Proof sketch: combine `withDensity_absolutelyContinuous` with
-- `withDensity_absolutelyContinuous'`; by `Measure.ae_le_iff_absolutelyContinuous`, the resulting
-- two one-sided absolute-continuity statements are exactly the canonical characterization of
-- equivalence of measures.
/-- Part (i) of Example 7.32: if the density is positive almost everywhere, then the density
measure induces the same almost-everywhere filter as Lebesgue measure. -/
theorem withDensity_volume_ae_eq_of_ae_pos (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hpos : ∀ᵐ x ∂volume, 0 < f x) :
    ae (volume.withDensity f) = ae volume := by
  apply le_antisymm
  · exact ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous volume f)
  · exact ae_le_iff_absolutelyContinuous.mpr
      (volume_absolutelyContinuous_withDensity_of_ae_pos f hf hpos)

-- Proof sketch: the set where `f = 0` has zero mass for `volume.withDensity f`; if that set has
-- positive Lebesgue measure, then `volume` cannot be absolutely continuous with respect to the
-- density measure.
/-- Part (i) of Example 7.32: if the zero set of the density has positive Lebesgue measure, then
Lebesgue measure is not absolutely continuous with respect to the density measure. -/
theorem not_absolutelyContinuous_volume_withDensity_of_zero_set (f : ℝ → ENNReal)
    (hf : AEMeasurable f volume) (hzero : 0 < volume {x | f x = 0}) :
    ¬ volume ≪ volume.withDensity f := by
  intro h
  have hdisj : {x | f x ≠ 0} ∩ {x | f x = 0} = ∅ := by
    ext x
    simp
  have h_withDensity_zero : volume.withDensity f {x | f x = 0} = 0 := by
    rw [withDensity_apply_eq_zero' hf]
    simp [hdisj]
  have h_volume_zero : volume {x | f x = 0} = 0 := h h_withDensity_zero
  exact (not_lt_of_ge (le_of_eq h_volume_zero)) hzero

-- Proof sketch: when `0 < p < 1`, both atoms of `Bool` have positive `Ber_p`-mass, so every
-- `Ber_p`-null measurable set is empty and hence also `Ber_q`-null.
/-- Helper for Example 7.32: a Bernoulli law with parameter in `(0,1)` has no nonempty null
sets. -/
private lemma bernoulliNullSet_eq_empty_of_zeroLtLtOne (p : NNReal) (hp_pos : 0 < p)
    (hp_lt_one : p < 1) {s : Set Bool}
    (hs : (PMF.bernoulli p hp_lt_one.le).toMeasure s = 0) :
    s = ∅ := by
  -- Rewrite null sets as sets disjoint from the PMF support, then show the support is all of
  -- `Bool` when both Bernoulli atoms have positive mass.
  have hs_disjoint :
      Disjoint (PMF.bernoulli p hp_lt_one.le).support s := by
    exact
      (PMF.toMeasure_apply_eq_zero_iff (p := PMF.bernoulli p hp_lt_one.le)
        (hs := MeasurableSet.of_discrete)).mp hs
  have hsupport : (PMF.bernoulli p hp_lt_one.le).support = Set.univ := by
    ext b
    cases b <;> simp [PMF.support_bernoulli, hp_pos.ne', hp_lt_one.ne]
  have hs_members : false ∉ s ∧ true ∉ s := by
    simpa [Set.disjoint_left, hsupport] using hs_disjoint
  ext b
  cases b <;> simp [hs_members.1, hs_members.2]

/-- Part (ii) of Example 7.32: if `p ∈ (0,1)`, then every Bernoulli law `Ber_q` is absolutely
continuous with respect to `Ber_p`. -/
theorem bernoulli_absolutelyContinuous_of_zero_lt_lt_one (p q : NNReal) (hq : q ≤ 1)
    (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    (PMF.bernoulli q hq).toMeasure ≪ (PMF.bernoulli p hp_lt_one.le).toMeasure := by
  refine AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  -- A `Ber_p`-null set is empty, so its `Ber_q`-mass vanishes as well.
  have hs_empty := bernoulliNullSet_eq_empty_of_zeroLtLtOne p hp_pos hp_lt_one hs
  simpa [hs_empty]

/-- Helper for Example 7.32: an extreme Bernoulli parameter belongs to `[0,1]`. -/
private theorem bernoulli_extreme_le_one {p : NNReal} (hp_extreme : p = 0 ∨ p = 1) : p ≤ 1 := by
  rcases hp_extreme with rfl | rfl <;> simp

-- Proof sketch: if `p` is `0` or `1`, then `Ber_p` is a Dirac mass; absolute continuity of
-- `Ber_q` with respect to this Dirac measure forces `Ber_q` to be the same Dirac mass.
/-- Part (ii) of Example 7.32: if `p ∈ {0,1}`, then `Ber_q ≪ Ber_p` holds exactly when `q = p`. -/
theorem bernoulli_absolutelyContinuous_iff_of_extreme (p q : NNReal) (hq : q ≤ 1)
    (hp_extreme : p = 0 ∨ p = 1) :
    (PMF.bernoulli q hq).toMeasure ≪
      (PMF.bernoulli p (bernoulli_extreme_le_one hp_extreme)).toMeasure ↔ q = p :=
  by
  rcases hp_extreme with rfl | rfl
  · constructor
    · intro h
      -- Test absolute continuity on the atom `{true}`, which has zero mass for `Ber_0`.
      have htrue_zero : (PMF.bernoulli q hq).toMeasure ({true} : Set Bool) = 0 := by
        refine h ?_
        simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 0 (by simp)) true
            (measurableSet_singleton true))
      simpa [PMF.bernoulli_apply] using htrue_zero
    · intro hq_zero
      subst hq_zero
      -- Once the parameters agree, the measures are identical.
      exact AbsolutelyContinuous.rfl
  · constructor
    · intro h
      -- Test absolute continuity on the atom `{false}`, which has zero mass for `Ber_1`.
      have hfalse_zero : (PMF.bernoulli q hq).toMeasure ({false} : Set Bool) = 0 := by
        refine h ?_
        simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 1 (by simp)) false
            (measurableSet_singleton false))
      have hq_ge_one : (1 : NNReal) ≤ q := by
        by_contra hq_lt_one
        have hmass_pos : 0 < (PMF.bernoulli q hq).toMeasure ({false} : Set Bool) := by
          have : 0 < ((1 : NNReal) - q : NNReal) := tsub_pos_iff_lt.mpr (lt_of_not_ge hq_lt_one)
          simpa [PMF.bernoulli_apply] using this
        exact (ne_of_gt hmass_pos) hfalse_zero
      exact le_antisymm hq hq_ge_one
    · intro hq_one
      subst hq_one
      -- Once the parameters agree, the measures are identical.
      exact AbsolutelyContinuous.rfl

-- Proof sketch: for degenerate `Ber_p`, the only way for `Ber_q` and `Ber_p` to be supported on
-- disjoint atoms is for `Ber_q` to be the complementary Dirac measure, i.e. `q = 1 - p`.
/-- Part (ii) of Example 7.32: if `p ∈ {0,1}`, then `Ber_q` and `Ber_p` are singular exactly when
`q = 1 - p`. -/
theorem bernoulli_mutuallySingular_iff_of_extreme (p q : NNReal) (hq : q ≤ 1)
    (hp_extreme : p = 0 ∨ p = 1) :
    (PMF.bernoulli q hq).toMeasure ⟂ₘ
      (PMF.bernoulli p (bernoulli_extreme_le_one hp_extreme)).toMeasure ↔ q = 1 - p := by
  rcases hp_extreme with rfl | rfl
  · constructor
    · intro h
      -- The `Ber_0` null-set witness must contain `false`, so `Ber_q` gives zero mass to
      -- `{false}` and therefore `q = 1`.
      have hfalse_mem : false ∈ h.nullSet := by
        by_contra hfalse_mem
        have hsubset : ({false} : Set Bool) ⊆ h.nullSetᶜ := by
          intro b hb
          have hb' : b = false := by simpa using hb
          simpa [hb'] using hfalse_mem
        have hfalse_zero :
            (PMF.bernoulli 0 (by simp)).toMeasure ({false} : Set Bool) = 0 := by
          exact measure_mono_null hsubset h.measure_compl_nullSet
        have hfalse_mass :
            (PMF.bernoulli 0 (by simp)).toMeasure ({false} : Set Bool) = 1 := by
          simpa [PMF.bernoulli_apply] using
            (PMF.toMeasure_apply_singleton (PMF.bernoulli 0 (by simp)) false
              (measurableSet_singleton false))
        have hfalse_pos :
            0 < (PMF.bernoulli 0 (by simp)).toMeasure ({false} : Set Bool) := by
          rw [hfalse_mass]
          simp
        exact (ne_of_gt hfalse_pos) hfalse_zero
      have hfalse_zero :
          (PMF.bernoulli q hq).toMeasure ({false} : Set Bool) = 0 := by
        exact measure_mono_null (Set.singleton_subset_iff.mpr hfalse_mem) h.measure_nullSet
      have hq_ge_one : (1 : NNReal) ≤ q := by
        by_contra hq_lt_one
        have hmass_pos : 0 < (PMF.bernoulli q hq).toMeasure ({false} : Set Bool) := by
          have : 0 < ((1 : NNReal) - q : NNReal) := tsub_pos_iff_lt.mpr (lt_of_not_ge hq_lt_one)
          simpa [PMF.bernoulli_apply] using this
        exact (ne_of_gt hmass_pos) hfalse_zero
      have hq_eq_one : q = 1 := le_antisymm hq hq_ge_one
      simpa using hq_eq_one
    · intro hq_one
      have hq_eq_one : q = 1 := by simpa using hq_one
      subst hq_eq_one
      -- The two Dirac masses live on complementary atoms, so use those atoms as the singularity
      -- partition.
      refine MutuallySingular.mk (s := ({false} : Set Bool)) (t := ({true} : Set Bool)) ?_ ?_ ?_
      · simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 1 (by simp)) false
            (measurableSet_singleton false))
      · simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 0 (by simp)) true
            (measurableSet_singleton true))
      · intro b _
        cases b <;> simp
  · constructor
    · intro h
      -- The `Ber_1` null-set witness must contain `true`, so `Ber_q` gives zero mass to
      -- `{true}` and therefore `q = 0`.
      have htrue_mem : true ∈ h.nullSet := by
        by_contra htrue_mem
        have hsubset : ({true} : Set Bool) ⊆ h.nullSetᶜ := by
          intro b hb
          have hb' : b = true := by simpa using hb
          simpa [hb'] using htrue_mem
        have htrue_zero :
            (PMF.bernoulli 1 (by simp)).toMeasure ({true} : Set Bool) = 0 := by
          exact measure_mono_null hsubset h.measure_compl_nullSet
        have htrue_mass :
            (PMF.bernoulli 1 (by simp)).toMeasure ({true} : Set Bool) = 1 := by
          simpa [PMF.bernoulli_apply] using
            (PMF.toMeasure_apply_singleton (PMF.bernoulli 1 (by simp)) true
              (measurableSet_singleton true))
        have htrue_pos :
            0 < (PMF.bernoulli 1 (by simp)).toMeasure ({true} : Set Bool) := by
          rw [htrue_mass]
          simp
        exact (ne_of_gt htrue_pos) htrue_zero
      have htrue_zero :
          (PMF.bernoulli q hq).toMeasure ({true} : Set Bool) = 0 := by
        exact measure_mono_null (Set.singleton_subset_iff.mpr htrue_mem) h.measure_nullSet
      simpa [PMF.bernoulli_apply] using htrue_zero
    · intro hq_zero
      have hq_eq_zero : q = 0 := by simpa using hq_zero
      subst hq_eq_zero
      -- The two Dirac masses live on complementary atoms, so use those atoms as the singularity
      -- partition.
      refine MutuallySingular.mk (s := ({true} : Set Bool)) (t := ({false} : Set Bool)) ?_ ?_ ?_
      · simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 0 (by simp)) true
            (measurableSet_singleton true))
      · simpa [PMF.bernoulli_apply] using
          (PMF.toMeasure_apply_singleton (PMF.bernoulli 1 (by simp)) false
            (measurableSet_singleton false))
      · intro b _
        cases b <;> simp

-- Proof sketch: `Poi_β` has full support on `ℕ` when `β > 0`, whereas `Poi_0` is the Dirac mass at
-- `0`; compare null sets with the singleton `{0}`.
/-- Helper for Example 7.32: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Rewrite the Poisson measure through its defining PMF.
  simpa [poissonMeasure, ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (ProbabilityTheory.poissonPMF r) n
      (measurableSet_singleton n))

/-- Helper for Example 7.32: a positive-rate Poisson law has no nonempty null sets. -/
private lemma poissonNullSet_eq_empty_of_pos (β : NNReal) (hβ : 0 < β) {s : Set ℕ}
    (hs : poissonMeasure β s = 0) :
    s = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun n hn ↦ ?_
  -- Every singleton has strictly positive mass when the Poisson rate is positive.
  have hsingle_zero : poissonMeasure β ({n} : Set ℕ) = 0 := by
    exact measure_mono_null (Set.singleton_subset_iff.mpr hn) hs
  have hsingle_pos : 0 < poissonMeasure β ({n} : Set ℕ) := by
    rw [poissonMeasure_apply_singleton]
    exact ENNReal.ofReal_pos.mpr (ProbabilityTheory.poissonPMFReal_pos hβ)
  exact (ne_of_gt hsingle_pos hsingle_zero).elim

/-- Part (iii) of Example 7.32: `Poi_α` is absolutely continuous with respect to `Poi_β` exactly
when `β > 0` or `α = 0`. -/
theorem poissonMeasure_absolutelyContinuous_iff (α β : NNReal) :
    poissonMeasure α ≪ poissonMeasure β ↔ 0 < β ∨ α = 0 := by
  constructor
  · intro h
    by_cases hβ : 0 < β
    · exact Or.inl hβ
    · have hβ_zero : β = 0 := le_antisymm (le_of_not_gt hβ) bot_le
      right
      by_contra hα_zero
      have hα_pos : 0 < α := pos_iff_ne_zero.mpr hα_zero
      -- When `β = 0`, the singleton `{1}` is `Poi_β`-null but not `Poi_α`-null unless `α = 0`.
      have hβ_singleton_zero : poissonMeasure β ({1} : Set ℕ) = 0 := by
        rw [hβ_zero, poissonMeasure_apply_singleton]
        simp [ProbabilityTheory.poissonPMFReal]
      have hα_singleton_zero : poissonMeasure α ({1} : Set ℕ) = 0 := h hβ_singleton_zero
      have hα_singleton_pos : 0 < poissonMeasure α ({1} : Set ℕ) := by
        rw [poissonMeasure_apply_singleton]
        exact ENNReal.ofReal_pos.mpr (ProbabilityTheory.poissonPMFReal_pos hα_pos)
      exact (ne_of_gt hα_singleton_pos hα_singleton_zero).elim
  · rintro (hβ | hα_zero)
    · refine AbsolutelyContinuous.mk fun s _ hs ↦ ?_
      -- Positive-rate Poisson laws have only the empty set as a null set.
      have hs_empty := poissonNullSet_eq_empty_of_pos β hβ hs
      simpa [hs_empty]
    · subst hα_zero
      by_cases hβ : 0 < β
      · refine AbsolutelyContinuous.mk fun s _ hs ↦ ?_
        -- Positive-rate Poisson laws have only the empty set as a null set.
        have hs_empty := poissonNullSet_eq_empty_of_pos β hβ hs
        simpa [hs_empty]
      · have hβ_zero : β = 0 := le_antisymm (le_of_not_gt hβ) bot_le
        subst hβ_zero
        -- Equal measures are absolutely continuous.
        exact AbsolutelyContinuous.rfl

-- Proof sketch: apply the strong law of large numbers to the coordinate projections under each
-- Bernoulli product measure; the empirical means converge almost surely to the parameter, so the
-- full-measure convergence sets are disjoint when `p ≠ q`.
/-- Helper for Example 7.32: under the Bernoulli product law with parameter `r`, the empirical
mean of the coordinate indicators converges almost surely to `r`. -/
private lemma bernoulliProduct_ae_tendsto_empiricalMean (r : NNReal) (hr : r ≤ 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ (PMF.bernoulli r hr).toMeasure),
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, cond (ω i) (1 : ℝ) 0) / n) atTop
        (𝓝 (r : ℝ)) := by
  let μ : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ ↦ (PMF.bernoulli r hr).toMeasure)
  let score : Bool → ℝ := fun b ↦ cond b 1 0
  let X : ℕ → (ℕ → Bool) → ℝ := fun n ↦ score ∘ Function.eval n
  have hscore_meas : Measurable score := Measurable.of_discrete
  have hcoord_law :
      ∀ n : ℕ, HasLaw (Function.eval n) ((PMF.bernoulli r hr).toMeasure) μ := by
    intro n
    simpa [μ] using
      (MeasurePreserving.hasLaw
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ (PMF.bernoulli r hr).toMeasure) n))
  have hscore_law :
      HasLaw score (Measure.map score ((PMF.bernoulli r hr).toMeasure))
        ((PMF.bernoulli r hr).toMeasure) := by
    exact ⟨hscore_meas.aemeasurable, rfl⟩
  have hX_law : ∀ n : ℕ, HasLaw (X n) (Measure.map score ((PMF.bernoulli r hr).toMeasure)) μ := by
    intro n
    simpa [X, score] using hscore_law.fun_comp (hcoord_law n)
  have hscore_integrable : Integrable score ((PMF.bernoulli r hr).toMeasure) := by
    -- The Bernoulli indicator is bounded by `1`, hence integrable under the probability law.
    refine Integrable.of_bound hscore_meas.aestronglyMeasurable 1 ?_
    filter_upwards with b
    cases b <;> norm_num [score]
  have hX_integrable : Integrable (X 0) μ := by
    exact ((hX_law 0).identDistrib hscore_law).integrable_iff.mpr hscore_integrable
  have hcoord_indep : iIndepFun Function.eval μ := by
    simpa [μ] using
      (iIndepFun_infinitePi (fun _ ↦ measurable_id) :
        iIndepFun Function.eval
          (Measure.infinitePi (fun _ : ℕ ↦ (PMF.bernoulli r hr).toMeasure)))
  have hX_pairwise : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j := by
    intro i j hij
    -- Independence of the coordinate maps is preserved by the measurable score map.
    exact (hcoord_indep.indepFun hij).comp hscore_meas hscore_meas
  have hX_ident : ∀ i : ℕ, IdentDistrib (X i) (X 0) μ μ := by
    intro i
    exact (hX_law i).identDistrib (hX_law 0)
  have hX_expectation : μ[X 0] = (r : ℝ) := by
    -- Compute the common expectation by pushing the coordinate law back to the Bernoulli PMF.
    rw [show X 0 = score ∘ Function.eval 0 by rfl]
    calc
      μ[score ∘ Function.eval 0] = ∫ b, score b ∂((PMF.bernoulli r hr).toMeasure) := by
        exact (hcoord_law 0).integral_comp hscore_meas.aestronglyMeasurable
      _ = (r : ℝ) := by
        simpa [score] using PMF.bernoulli_expectation (p := r) hr
  -- The strong law now applies to the real-valued coordinate indicators.
  have hSLLN := ProbabilityTheory.strong_law_ae_real X hX_integrable hX_pairwise hX_ident
  rw [hX_expectation] at hSLLN
  simpa [μ, X, score] using hSLLN

/-- Example 7.32: In (iv), the infinite Bernoulli product measures with distinct parameters are
mutually singular. -/
theorem bernoulli_infiniteProduct_mutuallySingular_of_ne (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≠ q) :
    infinitePi (fun _ : ℕ ↦ (PMF.bernoulli p hp).toMeasure) ⟂ₘ
      infinitePi (fun _ : ℕ ↦ (PMF.bernoulli q hq).toMeasure) := by
  let μp : Measure (ℕ → Bool) := infinitePi (fun _ : ℕ ↦ (PMF.bernoulli p hp).toMeasure)
  let μq : Measure (ℕ → Bool) := infinitePi (fun _ : ℕ ↦ (PMF.bernoulli q hq).toMeasure)
  let A_p : Set (ℕ → Bool) := {ω |
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, cond (ω i) (1 : ℝ) 0) / n) atTop (𝓝 (p : ℝ))}
  let A_q : Set (ℕ → Bool) := {ω |
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, cond (ω i) (1 : ℝ) 0) / n) atTop (𝓝 (q : ℝ))}
  have hAp_ae : ∀ᵐ ω ∂μp, ω ∈ A_p := by
    simpa [μp, A_p] using bernoulliProduct_ae_tendsto_empiricalMean p hp
  have hAq_ae : ∀ᵐ ω ∂μq, ω ∈ A_q := by
    simpa [μq, A_q] using bernoulliProduct_ae_tendsto_empiricalMean q hq
  have hAp_compl : μp A_pᶜ = 0 := by
    simpa [A_p, ae_iff] using hAp_ae
  have hAq_compl : μq A_qᶜ = 0 := by
    simpa [A_q, ae_iff] using hAq_ae
  have hpq_real : (p : ℝ) ≠ (q : ℝ) := fun h_eq ↦ hpq (NNReal.coe_injective h_eq)
  have hdisj : A_p ∩ A_q = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ ?_
    rcases hω with ⟨hpω, hqω⟩
    exact hpq_real (tendsto_nhds_unique hpω hqω)
  -- Use the two full-measure convergence sets as the singularity partition.
  refine MutuallySingular.mk hAp_compl hAq_compl ?_
  intro ω _
  by_cases hp_mem : ω ∈ A_p
  · by_cases hq_mem : ω ∈ A_q
    · exfalso
      have hnot_mem : ω ∉ A_p ∩ A_q := by simpa [hdisj]
      exact hnot_mem ⟨hp_mem, hq_mem⟩
    · exact Or.inr hq_mem
  · exact Or.inl hp_mem
