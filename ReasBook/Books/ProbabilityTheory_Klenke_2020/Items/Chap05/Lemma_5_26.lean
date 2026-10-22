/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open InformationTheory MeasureTheory
open scoped BigOperators

noncomputable section

universe u
variable {E : Type u}

/-- The extended-real cross-entropy of `p` against a nonnegative mass function `q` in base `b`. -/
def crossEntropyInBase (b : LogBase) (p : PMF E) (q : E → ENNReal) : EReal :=
  -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)))

/-- The extended-real base-`b` cross-entropy is given by its defining logarithmic series. -/
@[simp] theorem crossEntropyInBase_def (b : LogBase) (p : PMF E)
    (q : E → ENNReal) :
    crossEntropyInBase b p q =
      -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e))) :=
  rfl

/-- Helper for Lemma 5.26: when the comparison mass function agrees with `p`, the cross-entropy
coincides with the entropy. -/
private theorem crossEntropyInBase_eq_entropyInBase_of_eq (b : LogBase) (p : PMF E) :
    crossEntropyInBase b p p = entropyInBase b p := by
  -- Both quantities are the same defining series when `q = p`.
  simp [crossEntropyInBase, entropyInBase]

/-- Helper for Lemma 5.26: equality holds in the cross-entropy inequality for the diagonal choice
`q = p`. -/
private theorem entropyInBase_eq_crossEntropyInBase_of_eq (b : LogBase) (p : PMF E) :
    entropyInBase b p = crossEntropyInBase b p p := by
  -- This is the symmetric restatement of the diagonal compatibility lemma above.
  exact (crossEntropyInBase_eq_entropyInBase_of_eq b p).symm

/-- Helper for Lemma 5.26: if `q` vanishes at a point where `p` has positive mass, then the
cross-entropy diverges to `⊤`. -/
private theorem crossEntropyInBase_eq_top_of_exists_zero_on_support
    (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hzero : ∃ e, e ∈ p.support ∧ q e = 0) :
    crossEntropyInBase b p q = (⊤ : EReal) := by
  rcases hzero with ⟨e, he, hqe⟩
  let f : E → EReal := fun x ↦
    ((p x : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q x)))
  have hsum_bot : HasSum f (⊥ : EReal) := by
    rw [HasSum]
    change Filter.Tendsto (fun s : Finset E ↦ ∑ x ∈ s, f x) Filter.atTop
      (nhds (⊥ : EReal))
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro a
    have hmem :
        {s : Finset E | e ∈ s} ∈ (Filter.atTop : Filter (Finset E)) := by
      exact Filter.mem_atTop_sets.mpr ⟨{e}, by
        intro s hs
        simpa using hs⟩
    refine Filter.mem_of_superset hmem ?_
    intro s hs
    have hfe : f e = (⊥ : EReal) := by
      -- The singled-out support term is `⊥`: the logarithm contributes `⊥` and `p e` is positive.
      dsimp [f]
      have hp : (0 : EReal) < (p e : EReal) := by
        exact_mod_cast (PMF.apply_pos_iff p e).2 he
      have hlog :
          (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)) = (⊥ : EReal) := by
        have hpos : (0 : EReal) < ((Real.log (b : ℝ) : EReal)⁻¹) := by
          rw [← EReal.coe_inv]
          exact_mod_cast (inv_pos.mpr (Real.log_pos hb))
        simpa [hqe] using EReal.mul_bot_of_pos hpos
      simpa [hlog] using EReal.mul_bot_of_pos hp
    have hsbot : ∑ x ∈ s, f x = (⊥ : EReal) := by
      -- Every finite partial sum containing that term is already `⊥`.
      refine (WithBot.sum_eq_bot_iff).2 ?_
      exact ⟨e, by simpa using hs, hfe⟩
    change (∑ x ∈ s, f x) < (a : EReal)
    rw [hsbot]
    exact EReal.bot_lt_coe a
  -- The defining series therefore sums to `⊥`, and negating it gives `⊤`.
  have htsum : ∑' x : E, f x = (⊥ : EReal) := hsum_bot.tsum_eq
  rw [crossEntropyInBase_def]
  change -∑' x : E, f x = (⊤ : EReal)
  simp [htsum]

/-- Helper for Lemma 5.26: a sub-probability mass value is automatically finite. -/
private theorem q_apply_ne_top_of_tsum_le_one (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Each coordinate is bounded by the total mass, hence by `1`.
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hq_le_one ENNReal.one_lt_top)

/-- Helper for Lemma 5.26: on the positive-support branch, each logarithmic gap term rewrites to
the KL remainder plus the linear correction `p_e - q_e`. -/
private theorem cross_entropy_gap_term_identity (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) =
      (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) +
        (p e).toReal - (q e).toReal := by
  by_cases hp : p e = 0
  · -- Off the support of `p`, the identity collapses to the `klFun 0 = 1` case.
    simp [hp, klFun_zero]
  · -- On the support, positivity of both masses lets us rewrite through `log (p_e / q_e)`.
    have hq' : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
    have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
    have hp_toReal : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hq_toReal : 0 < (q e).toReal := ENNReal.toReal_pos hq' hq_top
    rw [klFun_apply]
    rw [ENNReal.toReal_div, Real.log_div hp_toReal.ne' hq_toReal.ne']
    field_simp [hq_toReal.ne']
    ring

/-- Helper for Lemma 5.26: on the positive-support branch, each pointwise logarithmic gap is at
least the corresponding mass difference. -/
private theorem log_ratio_mul_ge_mass_difference (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) ≥
      (p e).toReal - (q e).toReal := by
  -- Rewrite the gap as a nonnegative KL remainder plus the linear correction.
  have hid := cross_entropy_gap_term_identity p q hq hnozero e
  have hkl_nonneg : 0 ≤ (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) := by
    have hq_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    have hkl_nonneg : 0 ≤ klFun (((p e : ENNReal) / q e).toReal) :=
      klFun_nonneg ENNReal.toReal_nonneg
    exact mul_nonneg hq_nonneg hkl_nonneg
  linarith

/-- Helper for Lemma 5.26: if `q` differs from `p` at a positive-mass point, then the pointwise
logarithmic gap is strictly larger than the mass difference. -/
private theorem log_ratio_mul_gt_mass_difference_of_ne (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) {e : E}
    (he : e ∈ p.support) (hneq : q e ≠ p e) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) >
      (p e).toReal - (q e).toReal := by
  -- The strict gap comes from strict positivity of `klFun` away from ratio `1`.
  have hid := cross_entropy_gap_term_identity p q hq hnozero e
  have hq0 : q e ≠ 0 := hnozero e he
  have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
  have hq_real_pos : 0 < (q e).toReal := ENNReal.toReal_pos hq0 hq_top
  have hratio_ne_one : (((p e : ENNReal) / q e).toReal) ≠ 1 := by
    intro hratio
    have hdiv : (p e : ENNReal) / q e = 1 := (ENNReal.toReal_eq_one_iff _).mp hratio
    have hmul := congrArg (fun x : ENNReal ↦ q e * x) hdiv
    have hmul' : (p e : ENNReal) * (q e * (q e)⁻¹) = q e * 1 := by
      simpa only [ENNReal.div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm, one_mul] using hmul
    rw [ENNReal.mul_inv_cancel hq0 hq_top, mul_one, mul_one] at hmul'
    exact hneq hmul'.symm
  have hkl_nonneg : 0 ≤ klFun (((p e : ENNReal) / q e).toReal) :=
    klFun_nonneg ENNReal.toReal_nonneg
  have hkl_ne_zero : klFun (((p e : ENNReal) / q e).toReal) ≠ 0 := by
    intro hzero
    have hratio_eq_one :=
      (klFun_eq_zero_iff ENNReal.toReal_nonneg).mp hzero
    exact hratio_ne_one hratio_eq_one
  have hkl_pos : 0 < klFun (((p e : ENNReal) / q e).toReal) :=
    lt_of_le_of_ne hkl_nonneg (Ne.symm hkl_ne_zero)
  have hgap_pos :
      0 < (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) :=
    mul_pos hq_real_pos hkl_pos
  linarith

/-- Helper for Lemma 5.26: summing the pointwise textbook inequality over a finite set gives the
finite truncation lower bound used in the support-sum argument. -/
private theorem cross_entropy_partial_sum_bound (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (s : Finset E) :
    Finset.sum s (fun e ↦ (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal)) ≥
      Finset.sum s (fun e ↦ ((p e).toReal - (q e).toReal)) := by
  -- Sum the pointwise lower bound over the chosen truncation.
  exact Finset.sum_le_sum fun e he ↦ log_ratio_mul_ge_mass_difference p q hq hnozero e

/-- Helper for Lemma 5.26: if a finite truncation contains a support point where `q` differs from
`p`, then the truncation inequality is strict. -/
private theorem cross_entropy_partial_sum_strict (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (s : Finset E)
    {e : E} (he_mem : e ∈ s) (he_support : e ∈ p.support) (hneq : q e ≠ p e) :
    Finset.sum s (fun x ↦ (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)) >
      Finset.sum s (fun x ↦ ((p x).toReal - (q x).toReal)) := by
  classical
  -- Split off the witness index and use the strict pointwise gap there.
  let f : E → ℝ := fun x ↦
    (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)
  let g : E → ℝ := fun x ↦ (p x).toReal - (q x).toReal
  have hstrict :
      f e > g e :=
    log_ratio_mul_gt_mass_difference_of_ne p q hq hnozero he_support hneq
  have hweak :
      Finset.sum (s.erase e) g ≤ Finset.sum (s.erase e) f :=
    cross_entropy_partial_sum_bound p q hq hnozero (s.erase e)
  have hsum_strict :
      Finset.sum (s.erase e) g + g e < Finset.sum (s.erase e) f + f e :=
    add_lt_add_of_le_of_lt hweak hstrict
  have hs_g : Finset.sum (s.erase e) g + g e = Finset.sum s g :=
    Finset.sum_erase_add s g he_mem
  have hs_f : Finset.sum (s.erase e) f + f e = Finset.sum s f :=
    Finset.sum_erase_add s f he_mem
  have hs_g' :
      Finset.sum s (fun x ↦ (p x).toReal - (q x).toReal) =
        Finset.sum (s.erase e) g + g e := by
    simpa [g] using hs_g.symm
  have hs_f' :
      Finset.sum s (fun x ↦ (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)) =
        Finset.sum (s.erase e) f + f e := by
    simpa [f] using hs_f.symm
  rw [hs_g', hs_f']
  exact hsum_strict

/-- Helper for Lemma 5.26: the comparison measure `Measure.count.withDensity q` agrees with
`p.toMeasure` exactly when `q` agrees pointwise with `p`. -/
private theorem comparison_measure_eq_pmf_iff (p : PMF E) (q : E → ENNReal) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    ν = p.toMeasure ↔ q = (p : E → ENNReal) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  constructor
  · intro hν
    -- Compare the two measures on singletons to recover the pointwise masses.
    ext e
    have hsingle := congrArg (fun μ : Measure E ↦ μ {e}) hν
    simpa [ν, withDensity_apply, lintegral_count, PMF.toMeasure_apply_singleton] using hsingle
  · intro hpq
    -- Once the densities agree pointwise, both weighted counting measures have the same values on
    -- every measurable set.
    ext s hs
    have hcount :
        (Measure.count.withDensity (fun e ↦ (p e : ENNReal))) s = p.toMeasure s := by
      rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_count]
      simpa using (p.toMeasure_apply hs).symm
    simpa [ν, hpq] using hcount

/-- Helper for Lemma 5.26: on the positive-support branch, `p.toMeasure` is the weighted
comparison measure with density `p / q`. -/
private theorem pmf_toMeasure_eq_withDensity_comparison (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    p.toMeasure = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  calc
    p.toMeasure = Measure.count.withDensity (fun e ↦ (p e : ENNReal)) := by
      -- Rewrite `p.toMeasure` itself as a weighted counting measure.
      refine Measure.ext fun s hs ↦ ?_
      rw [p.toMeasure_apply hs, withDensity_apply _ hs]
      rw [← lintegral_indicator hs (fun e ↦ (p e : ENNReal)), lintegral_count]
    _ = (Measure.count.withDensity q).withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      -- Route correction: compose the counting measure with the density `q` first, then identify
      -- the remaining Radon-Nikodym factor pointwise as `p / q`.
      rw [← withDensity_mul (Measure.count : Measure E)]
      · refine withDensity_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro e
        by_cases hp : p e = 0
        · simp [hp]
        · have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
          have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hq_top, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · fun_prop
      · fun_prop
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Lemma 5.26: the discrete KL divergence against the comparison measure is exactly the
sum of the ambient gap terms. -/
private theorem cross_entropy_gap_eq_klDiv (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- The sub-probability bound makes the comparison measure finite.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  have hpν : p.toMeasure ≪ ν := by
    rw [pmf_toMeasure_eq_withDensity_comparison p q hq hnozero]
    exact withDensity_absolutelyContinuous _ _
  change klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal))
  rw [klDiv_eq_lintegral_klFun_of_ac hpν]
  have hrn : p.toMeasure.rnDeriv ν =ᵐ[ν] fun e ↦ (p e : ENNReal) / q e := by
    rw [pmf_toMeasure_eq_withDensity_comparison p q hq hnozero]
    exact Measure.rnDeriv_withDensity ν (by fun_prop)
  have hfun :
      (fun x ↦ ENNReal.ofReal (klFun (p.toMeasure.rnDeriv ν x).toReal)) =ᵐ[ν]
        fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
    -- Replace the Radon-Nikodym derivative by the explicit density `p / q`.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
    have hq_toReal_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) =
          ENNReal.ofReal (q e).toReal *
            ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [ENNReal.ofReal_toReal hq_top]
      _ = ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [← ENNReal.ofReal_mul hq_toReal_nonneg]
  · fun_prop
  · fun_prop

/-- Helper for Lemma 5.26: the total mass of the comparison measure `Measure.count.withDensity q`
is the `tsum` of the coefficients `q e`. -/
private theorem comparisonMeasure_univ_eq_tsum (q : E → ENNReal) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    ν Set.univ = ∑' e : E, q e := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  -- Evaluate the weighted counting measure on the whole space.
  change (Measure.count.withDensity q) Set.univ = ∑' e : E, q e
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]

/-- Helper for Lemma 5.26: coercion `ℝ≥0∞ → EReal` preserves zero. -/
private theorem ennrealToERealMap_zero : ((0 : ENNReal) : EReal) = 0 :=
  rfl

/-- Helper for Lemma 5.26: coercion `ℝ≥0∞ → EReal` preserves addition. -/
private theorem ennrealToERealMap_add (x y : ENNReal) :
    (((x + y : ENNReal) : EReal)) = (x : EReal) + (y : EReal) :=
  EReal.coe_ennreal_add x y

/-- Helper for Lemma 5.26: the canonical coercion `ℝ≥0∞ → EReal` as an additive homomorphism. -/
private def ennrealToERealAddHom : ENNReal →+ EReal :=
  { toFun := fun x ↦ (x : EReal)
    map_zero' := ennrealToERealMap_zero
    map_add' := ennrealToERealMap_add }

/-- Helper for Lemma 5.26: coercing a nonnegative `HasSum` statement to `EReal` preserves the
same sum. -/
private theorem hasSum_coe_ennreal_ereal {f : E → ENNReal} {a : ENNReal} (h : HasSum f a) :
    HasSum (fun e ↦ (f e : EReal)) (a : EReal) := by
  -- Map the nonnegative series through the continuous coercion into `EReal`.
  simpa [ennrealToERealAddHom] using h.map ennrealToERealAddHom continuous_coe_ennreal_ereal

/-- Helper for Lemma 5.26: the `tsum` of a nonnegative family can be coerced directly from
`ENNReal` to `EReal`. -/
private theorem tsum_coe_ennreal_ereal {f : E → ENNReal} :
    (∑' e : E, (f e : EReal)) = (((∑' e : E, f e) : ENNReal) : EReal) := by
  -- Package the canonical `ENNReal` sum once, then read off the corresponding `EReal` `tsum`.
  exact (hasSum_coe_ennreal_ereal (ENNReal.summable.hasSum : HasSum f (∑' e : E, f e))).tsum_eq

/-- Helper for Lemma 5.26: the nonnegative pointwise contribution to the cross-entropy series,
written with the minus sign absorbed into the real logarithm. -/
private def crossEntropyPositiveSummand (p : PMF E) (q : E → ENNReal) (e : E) : ENNReal :=
  ENNReal.ofReal ((p e).toReal * (-Real.log (q e).toReal))

/-- Helper for Lemma 5.26: the nonnegative pointwise contribution to the entropy series, written
with the minus sign absorbed into the real logarithm. -/
private def entropyPositiveSummand (p : PMF E) (e : E) : ENNReal :=
  ENNReal.ofReal ((p e).toReal * (-Real.log (p e).toReal))

/-- Helper for Lemma 5.26: each cross-entropy summand is the base-change factor times the
corresponding nonnegative positive-logarithm summand. -/
private theorem crossEntropyPositiveSummand_scaled (b : LogBase) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    -((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e))) =
      ((Real.log (b : ℝ) : EReal)⁻¹) * (crossEntropyPositiveSummand p q e : EReal) := by
  by_cases hp : p e = 0
  · -- Zero-mass coordinates contribute nothing to either series representation.
    simp [crossEntropyPositiveSummand, hp]
  · -- On the support, rewrite the logarithm through real values and fold the sign into the
    -- nonnegative real summand.
    have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
    have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
    have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
    have hq_toReal_le_one : (q e).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
    have hlog_nonpos : Real.log (q e).toReal ≤ 0 := by
      exact Real.log_nonpos ENNReal.toReal_nonneg hq_toReal_le_one
    have hsummand_nonneg :
        0 ≤ (p e).toReal * (-Real.log (q e).toReal) := by
      exact mul_nonneg ENNReal.toReal_nonneg (by linarith)
    -- After rewriting both logarithms into real form, the claim is a one-line ring identity.
    rw [crossEntropyPositiveSummand, EReal.coe_ennreal_ofReal, max_eq_left hsummand_nonneg]
    rw [ENNReal.log_pos_real hq0 hq_top, ← EReal.coe_ennreal_toReal (p.apply_ne_top e),
      ← EReal.coe_inv]
    exact_mod_cast (by ring :
      -((p e).toReal * ((Real.log (b : ℝ))⁻¹ * Real.log (q e).toReal)) =
        (Real.log (b : ℝ))⁻¹ * ((p e).toReal * (-Real.log (q e).toReal)))

/-- Helper for Lemma 5.26: each entropy summand is the base-change factor times the corresponding
nonnegative positive-logarithm summand. -/
private theorem entropyPositiveSummand_scaled (b : LogBase) (p : PMF E) (e : E) :
    -((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) =
      ((Real.log (b : ℝ) : EReal)⁻¹) * (entropyPositiveSummand p e : EReal) := by
  by_cases hp : p e = 0
  · -- Zero-mass coordinates contribute nothing to either series representation.
    simp [entropyPositiveSummand, hp]
  · -- On the support, rewrite the logarithm through real values and fold the sign into the
    -- nonnegative real summand.
    have hp_toReal_le_one : (p e).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one e)
    have hlog_nonpos : Real.log (p e).toReal ≤ 0 := by
      exact Real.log_nonpos ENNReal.toReal_nonneg hp_toReal_le_one
    have hsummand_nonneg :
        0 ≤ (p e).toReal * (-Real.log (p e).toReal) := by
      exact mul_nonneg ENNReal.toReal_nonneg (by linarith)
    -- The entropy summand has the same algebraic shape as the cross-entropy summand.
    rw [entropyPositiveSummand, EReal.coe_ennreal_ofReal, max_eq_left hsummand_nonneg]
    rw [ENNReal.log_pos_real hp (p.apply_ne_top e), ← EReal.coe_ennreal_toReal (p.apply_ne_top e),
      ← EReal.coe_inv]
    exact_mod_cast (by ring :
      -((p e).toReal * ((Real.log (b : ℝ))⁻¹ * Real.log (p e).toReal)) =
        (Real.log (b : ℝ))⁻¹ * ((p e).toReal * (-Real.log (p e).toReal)))

/-- Helper for Lemma 5.26: after adding the comparison mass term `q_e`, the pointwise
cross-entropy gap identity becomes an identity of nonnegative `ENNReal` summands. -/
private theorem positiveSummand_withMass_identity (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    crossEntropyPositiveSummand p q e + q e =
      entropyPositiveSummand p e +
        (ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) + p e) := by
  have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
  have hce_top : crossEntropyPositiveSummand p q e ≠ ⊤ := by
    simp [crossEntropyPositiveSummand]
  have hent_top : entropyPositiveSummand p e ≠ ⊤ := by
    simp [entropyPositiveSummand]
  have hgap_top :
      ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hleft_top : crossEntropyPositiveSummand p q e + q e ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hce_top, hq_top⟩
  have hright_inner_top :
      ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) + p e ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hgap_top, p.apply_ne_top e⟩
  have hright_top :
      entropyPositiveSummand p e +
        (ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) + p e) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hent_top, hright_inner_top⟩
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  have hp_toReal_le_one : (p e).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one e)
  have hq_toReal_le_one : (q e).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
  have hce_nonneg :
      0 ≤ (p e).toReal * (-Real.log (q e).toReal) := by
    have hlog_nonpos : Real.log (q e).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hq_toReal_le_one
    exact mul_nonneg ENNReal.toReal_nonneg (by linarith)
  have hent_nonneg :
      0 ≤ (p e).toReal * (-Real.log (p e).toReal) := by
    have hlog_nonpos : Real.log (p e).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hp_toReal_le_one
    exact mul_nonneg ENNReal.toReal_nonneg (by linarith)
  have hgap_nonneg :
      0 ≤ (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) := by
    exact mul_nonneg ENNReal.toReal_nonneg (klFun_nonneg ENNReal.toReal_nonneg)
  -- Compare both finite `ENNReal` sides after applying `toReal`.
  refine (ENNReal.toReal_eq_toReal_iff' hleft_top hright_top).mp ?_
  rw [ENNReal.toReal_add hce_top hq_top, ENNReal.toReal_add hent_top hright_inner_top,
    ENNReal.toReal_add hgap_top (p.apply_ne_top e), crossEntropyPositiveSummand,
    entropyPositiveSummand, ENNReal.toReal_ofReal hce_nonneg, ENNReal.toReal_ofReal hent_nonneg,
    ENNReal.toReal_ofReal hgap_nonneg]
  -- The remaining real identity is exactly the earlier pointwise gap decomposition.
  linarith [cross_entropy_gap_term_identity p q hq hnozero e]

/-- Helper for Lemma 5.26: summing the pointwise positive-summand identity and canceling the
comparison mass term in `ENNReal` yields the exact unscaled entropy/cross-entropy decomposition. -/
private theorem positiveSummandSeries_eq (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    (∑' e : E, crossEntropyPositiveSummand p q e) =
      (∑' e : E, entropyPositiveSummand p e) +
        (klDiv p.toMeasure ν + (1 - ν Set.univ)) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  have hgap :
      klDiv p.toMeasure ν =
        ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
    simpa [ν] using cross_entropy_gap_eq_klDiv p q hq hnozero
  have hmass : ν Set.univ = ∑' e : E, q e := by
    simpa [ν] using comparisonMeasure_univ_eq_tsum q
  have hnu_le_one : ν Set.univ ≤ 1 := by
    rw [hmass]
    exact hq
  have hnu_ne_top : ν Set.univ ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hnu_le_one ENNReal.one_lt_top)
  have hmass_cancel : (1 - ν Set.univ) + ν Set.univ = (1 : ENNReal) :=
    tsub_add_cancel_of_le hnu_le_one
  have hkl_with_mass :
      klDiv p.toMeasure ν + 1 =
        (klDiv p.toMeasure ν + (1 - ν Set.univ)) + ν Set.univ := by
    calc
      klDiv p.toMeasure ν + 1 = klDiv p.toMeasure ν + ((1 - ν Set.univ) + ν Set.univ) := by
        exact congrArg (fun t : ENNReal ↦ klDiv p.toMeasure ν + t) hmass_cancel.symm
      _ = (klDiv p.toMeasure ν + (1 - ν Set.univ)) + ν Set.univ := by
        exact (add_assoc (klDiv p.toMeasure ν) (1 - ν Set.univ) (ν Set.univ)).symm
  have hsum_with_mass :
      (∑' e : E, crossEntropyPositiveSummand p q e) + ν Set.univ =
        ((∑' e : E, entropyPositiveSummand p e) +
          (klDiv p.toMeasure ν + (1 - ν Set.univ))) + ν Set.univ := by
    -- Sum the pointwise identity before rewriting the auxiliary series.
    calc
      (∑' e : E, crossEntropyPositiveSummand p q e) + ν Set.univ
          = (∑' e : E, crossEntropyPositiveSummand p q e) + ∑' e : E, q e := by
              rw [hmass]
      _ = ∑' e : E, (crossEntropyPositiveSummand p q e + q e) := by
            rw [← ENNReal.tsum_add]
      _ = ∑' e : E,
            (entropyPositiveSummand p e +
              (ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) + p e)) := by
            refine tsum_congr fun e ↦ ?_
            exact positiveSummand_withMass_identity p q hq hnozero e
      _ = (∑' e : E, entropyPositiveSummand p e) +
            (∑' e : E, (ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) +
              p e)) := by
            rw [ENNReal.tsum_add]
      _ = (∑' e : E, entropyPositiveSummand p e) +
            ((∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal))) +
              (∑' e : E, p e)) := by
            rw [ENNReal.tsum_add]
      _ = (∑' e : E, entropyPositiveSummand p e) + (klDiv p.toMeasure ν + 1) := by
            rw [hgap, p.tsum_coe]
      _ = (∑' e : E, entropyPositiveSummand p e) +
            ((klDiv p.toMeasure ν + (1 - ν Set.univ)) + ν Set.univ) := by
            exact congrArg (fun t : ENNReal ↦ (∑' e : E, entropyPositiveSummand p e) + t)
              hkl_with_mass
      _ = ((∑' e : E, entropyPositiveSummand p e) +
            (klDiv p.toMeasure ν + (1 - ν Set.univ))) + ν Set.univ := by
            exact (add_assoc
              (∑' e : E, entropyPositiveSummand p e)
              (klDiv p.toMeasure ν + (1 - ν Set.univ))
              (ν Set.univ)).symm
  -- Cancel the common finite comparison-mass term before moving to `EReal`.
  have hsum_left :
      ν Set.univ + (∑' e : E, crossEntropyPositiveSummand p q e) =
        ν Set.univ +
          ((∑' e : E, entropyPositiveSummand p e) + (klDiv p.toMeasure ν + (1 - ν Set.univ))) := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum_with_mass
  exact (ENNReal.add_right_inj hnu_ne_top).1 hsum_left

/-- Helper for Lemma 5.26: the raw cross-entropy logarithmic summand family is the negative
base-change coefficient times the nonnegative positive-summand family. -/
private theorem crossEntropySummandFamily_eq_negativeScaledPositive (b : LogBase) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    (fun e ↦ ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)))) =
      fun e ↦ (-((Real.log (b : ℝ) : EReal)⁻¹)) * (crossEntropyPositiveSummand p q e : EReal) := by
  -- Negate the pointwise scaled identity to move the sign from the series to the coefficient.
  funext e
  have hscaled := crossEntropyPositiveSummand_scaled b p q hq hnozero e
  have hneg := congrArg Neg.neg hscaled
  simpa [neg_mul] using hneg

/-- Helper for Lemma 5.26: finite sums of negatives of coerced `ENNReal` terms collapse to the
negation of the corresponding positive finite sum. -/
private theorem sum_negCoe_ennreal_ereal (s : Finset E) (g : E → ENNReal) :
    Finset.sum s (fun e ↦ -((g e : ENNReal) : EReal)) =
      -(Finset.sum s (fun e ↦ ((g e : ENNReal) : EReal))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert e s he ih =>
      have hsum_ne_bot : Finset.sum s (fun x ↦ ((g x : ENNReal) : EReal)) ≠ ⊥ := by
        intro hbot
        rcases (WithBot.sum_eq_bot_iff.mp hbot) with ⟨x, hx, hxbot⟩
        exact EReal.coe_ennreal_ne_bot (g x) hxbot
      -- Apply `EReal.neg_add` to the finite sum of nonnegative coerced terms.
      rw [Finset.sum_insert he, Finset.sum_insert he, ih]
      symm
      exact EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot (g e))) (.inr hsum_ne_bot)

/-- Helper for Lemma 5.26: negating a series of coerced `ENNReal` terms can be packaged as a
`HasSum` statement for the negative family. -/
private theorem hasSum_negCoe_ennreal_ereal {g : E → ENNReal} {a : ENNReal} (h : HasSum g a) :
    HasSum (fun e ↦ -((g e : ENNReal) : EReal)) (-(a : EReal)) := by
  have hcoe : HasSum (fun e ↦ (g e : EReal)) (a : EReal) := hasSum_coe_ennreal_ereal h
  rw [HasSum] at hcoe ⊢
  have hpartial :
      (fun s : Finset E ↦ Finset.sum s (fun e ↦ -((g e : ENNReal) : EReal))) =
        fun s : Finset E ↦ -(Finset.sum s (fun e ↦ ((g e : ENNReal) : EReal))) := by
    funext s
    exact sum_negCoe_ennreal_ereal s g
  -- Negate the already-known positive series after rewriting the finite partial sums explicitly.
  have hneg :
      Filter.Tendsto
        (fun s : Finset E ↦ -(Finset.sum s (fun e ↦ ((g e : ENNReal) : EReal))))
        Filter.atTop (nhds (-(a : EReal))) :=
    (continuous_neg.tendsto (a : EReal)).comp hcoe
  refine Filter.Tendsto.congr' ?_ hneg
  exact Filter.Eventually.of_forall fun s ↦ (congrArg (fun u ↦ u s) hpartial).symm

/-- Helper for Lemma 5.26: a series of negatives of coerced `ENNReal` terms evaluates to the
negation of the coerced `ENNReal` `tsum`, so an outer negation recovers the positive coercion. -/
private theorem negTsum_negCoe_ennreal_ereal (g : E → ENNReal) :
    -(∑' e : E, -((g e : ENNReal) : EReal)) =
      (((∑' e : E, g e) : ENNReal) : EReal) := by
  have hneg :
      HasSum (fun e ↦ -((g e : ENNReal) : EReal))
        (-((((∑' e : E, g e) : ENNReal) : EReal))) :=
    hasSum_negCoe_ennreal_ereal (ENNReal.summable.hasSum : HasSum g (∑' e : E, g e))
  -- Cancel the two outer negations after identifying the negative-series `tsum`.
  rw [hneg.tsum_eq]
  simp

/-- Helper for Lemma 5.26: the cross-entropy is the base-change factor times the `tsum` of the
nonnegative positive-logarithm summands. -/
private theorem crossEntropyInBase_eq_scaled_positiveSummandSeries (b : LogBase)
    (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    crossEntropyInBase b p q =
      ((Real.log (b : ℝ) : EReal)⁻¹) *
        (((∑' e : E, crossEntropyPositiveSummand p q e) : ENNReal) : EReal) := by
  let c : ENNReal := ENNReal.ofReal ((Real.log (b : ℝ))⁻¹)
  have hcoeff_nonneg : 0 ≤ (Real.log (b : ℝ))⁻¹ := by
    exact le_of_lt (inv_pos.mpr (Real.log_pos hb))
  have hcoeff : (c : EReal) = ((Real.log (b : ℝ) : EReal)⁻¹) := by
    simp [c, EReal.coe_ennreal_ofReal, hcoeff_nonneg, EReal.coe_inv]
  have hfamily :
      (fun e ↦ ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)))) =
        fun e ↦ -(((c * crossEntropyPositiveSummand p q e : ENNReal) : EReal)) := by
    -- Route correction: rewrite the raw family as negatives of a purely nonnegative
    -- `ENNReal` family, so the only infinite-sum transport left is ENNReal-native.
    funext e
    rw [show
      ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e))) =
        (-((Real.log (b : ℝ) : EReal)⁻¹)) * (crossEntropyPositiveSummand p q e : EReal) by
        simpa using congrArg (fun f ↦ f e)
          (crossEntropySummandFamily_eq_negativeScaledPositive b p q hq hnozero),
      ← hcoeff]
    rw [neg_mul]
    exact (congrArg Neg.neg
      (EReal.coe_ennreal_mul c (crossEntropyPositiveSummand p q e))).symm
  -- Rewrite the defining series into the negative coercion bridge, then collapse the ENNReal sum.
  rw [crossEntropyInBase_def]
  rw [hfamily]
  rw [negTsum_negCoe_ennreal_ereal]
  rw [ENNReal.tsum_mul_left, EReal.coe_ennreal_mul, hcoeff]

/-- Helper for Lemma 5.26: the raw entropy logarithmic summand family is the negative
base-change coefficient times the nonnegative entropy-summand family. -/
private theorem entropySummandFamily_eq_negativeScaledPositive (b : LogBase) (p : PMF E) :
    (fun e ↦ ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)))) =
      fun e ↦ (-((Real.log (b : ℝ) : EReal)⁻¹)) * (entropyPositiveSummand p e : EReal) := by
  -- Negate the pointwise entropy scaling identity to move the sign to the coefficient.
  funext e
  have hscaled := entropyPositiveSummand_scaled b p e
  have hneg := congrArg Neg.neg hscaled
  simpa [neg_mul] using hneg

/-- Helper for Lemma 5.26: the entropy is the base-change factor times the `tsum` of the
nonnegative positive-logarithm summands. -/
private theorem entropyInBase_eq_scaled_positiveSummandSeries (b : LogBase)
    (hb : 1 < (b : ℝ)) (p : PMF E) :
    entropyInBase b p =
      ((Real.log (b : ℝ) : EReal)⁻¹) *
        (((∑' e : E, entropyPositiveSummand p e) : ENNReal) : EReal) := by
  let c : ENNReal := ENNReal.ofReal ((Real.log (b : ℝ))⁻¹)
  have hcoeff_nonneg : 0 ≤ (Real.log (b : ℝ))⁻¹ := by
    exact le_of_lt (inv_pos.mpr (Real.log_pos hb))
  have hcoeff : (c : EReal) = ((Real.log (b : ℝ) : EReal)⁻¹) := by
    simp [c, EReal.coe_ennreal_ofReal, hcoeff_nonneg, EReal.coe_inv]
  have hfamily :
      (fun e ↦ ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)))) =
        fun e ↦ -(((c * entropyPositiveSummand p e : ENNReal) : EReal)) := by
    -- The entropy package uses the same nonnegative-family bridge as the cross-entropy package.
    funext e
    rw [show
      ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) =
        (-((Real.log (b : ℝ) : EReal)⁻¹)) * (entropyPositiveSummand p e : EReal) by
        simpa using congrArg (fun f ↦ f e)
          (entropySummandFamily_eq_negativeScaledPositive b p),
      ← hcoeff]
    rw [neg_mul]
    exact (congrArg Neg.neg
      (EReal.coe_ennreal_mul c (entropyPositiveSummand p e))).symm
  rw [entropyInBase_def]
  rw [hfamily]
  rw [negTsum_negCoe_ennreal_ereal]
  rw [ENNReal.tsum_mul_left, EReal.coe_ennreal_mul, hcoeff]

/-- Helper for Lemma 5.26: on the positive-support branch, the cross-entropy splits as the entropy
plus the KL divergence against the comparison measure and the mass deficit of `q`. -/
private theorem cross_entropy_gap_full_decomposition (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    crossEntropyInBase b p q =
      entropyInBase b p +
        (((Real.log (b : ℝ) : EReal)⁻¹) *
          (((klDiv p.toMeasure ν) + (1 - ν Set.univ)) : ENNReal)) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  -- Route correction: cancel the duplicated comparison mass in `ENNReal` first.
  rw [crossEntropyInBase_eq_scaled_positiveSummandSeries b hb p q hq hnozero,
    entropyInBase_eq_scaled_positiveSummandSeries b hb p]
  rw [positiveSummandSeries_eq p q hq hnozero]
  -- After the ENNReal cancellation, the closing step is just coercion and distributivity.
  rw [EReal.coe_ennreal_add]
  have hsum_nonneg :
      (0 : EReal) ≤ (((∑' e : E, entropyPositiveSummand p e) : ENNReal) : EReal) := by
    exact_mod_cast (bot_le : (0 : ENNReal) ≤ ∑' e : E, entropyPositiveSummand p e)
  have hrem_nonneg :
      (0 : EReal) ≤ (((klDiv p.toMeasure ν + (1 - ν Set.univ)) : ENNReal) : EReal) := by
    exact_mod_cast (bot_le : (0 : ENNReal) ≤ klDiv p.toMeasure ν + (1 - ν Set.univ))
  rw [EReal.left_distrib_of_nonneg hsum_nonneg hrem_nonneg]

/-- Helper for Lemma 5.26: on the finite-entropy positive-support branch, equality forces the
comparison mass function to agree pointwise with `p`. -/
private theorem cross_entropy_remainder_eq_zero_iff (b : LogBase) (hb : 1 < (b : ℝ))
    (p : PMF E) (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) (htop : entropyInBase b p ≠ (⊤ : EReal)) :
    entropyInBase b p = crossEntropyInBase b p q ↔ q = (p : E → ENNReal) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- The sub-probability bound makes the comparison measure finite.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  constructor
  · intro hEq
    have hcoeff_pos : (0 : EReal) < ((Real.log (b : ℝ) : EReal)⁻¹) := by
      rw [← EReal.coe_inv]
      exact_mod_cast inv_pos.mpr (Real.log_pos hb)
    have hcoeff_ne_zero : ((Real.log (b : ℝ) : EReal)⁻¹) ≠ 0 := ne_of_gt hcoeff_pos
    have hcoeff_nonneg : (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) :=
      hcoeff_pos.le
    have hentropy_ne_bot : entropyInBase b p ≠ (⊥ : EReal) := by
      have hsum_nonpos :
          (∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)))) ≤
            (0 : EReal) := by
        refine tsum_nonpos ?_
        intro e
        have hp_nonneg : (0 : EReal) ≤ (p e : EReal) := by
          exact_mod_cast (show (0 : ENNReal) ≤ p e by simp)
        have hlog_nonpos : ENNReal.log (p e) ≤ 0 := by
          rw [ENNReal.log_le_zero_iff]
          exact p.coe_le_one e
        have hscaled_nonpos :
            (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hlog_nonpos
        exact mul_nonpos_of_nonneg_of_nonpos hp_nonneg hscaled_nonpos
      have hsum_ne_top :
          ∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) ≠
            (⊤ : EReal) := by
        have hzero_lt_top : (0 : EReal) < ⊤ := by simp
        exact ne_of_lt (lt_of_le_of_lt hsum_nonpos hzero_lt_top)
      rw [entropyInBase_def]
      intro hbot
      exact hsum_ne_top ((EReal.neg_eq_bot_iff).mp hbot)
    -- Rewrite equality so that the nonnegative KL remainder is the only possible obstruction.
    rw [cross_entropy_gap_full_decomposition b hb p q hq hnozero] at hEq
    let rem : ENNReal := klDiv p.toMeasure ν + (1 - ν Set.univ)
    have hrem_nonneg : (0 : EReal) ≤ (rem : EReal) := by
      exact_mod_cast (bot_le : (0 : ENNReal) ≤ rem)
    have hmul_nonneg :
        (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) := by
      exact mul_nonneg hcoeff_nonneg hrem_nonneg
    have hEq' :
        ((entropyInBase b p).toReal : EReal) =
          ((entropyInBase b p).toReal : EReal) +
            (((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal)) := by
      -- Replace the finite entropy value by its real coercion before cancelling it.
      have hcoe : entropyInBase b p = ((entropyInBase b p).toReal : EReal) := by
        symm
        exact EReal.coe_toReal htop hentropy_ne_bot
      have hEq'' := hEq
      rw [hcoe] at hEq''
      simpa [rem, ν] using hEq''
    have hmul_le_zero :
        ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) ≤ 0 := by
      have hle :
          ((entropyInBase b p).toReal : EReal) +
              (((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal)) ≤
            ((entropyInBase b p).toReal : EReal) + 0 := by
        simpa [hEq', add_comm, add_left_comm, add_assoc] using le_of_eq hEq'.symm
      exact EReal.addLECancellable_coe (entropyInBase b p).toReal hle
    have hmul_zero :
        ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) = 0 := by
      exact le_antisymm hmul_le_zero hmul_nonneg
    have hrem_zero_e : (rem : EReal) = 0 := by
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hmul_zero).resolve_left hcoeff_ne_zero
    have hrem_zero : rem = 0 := by
      simpa using hrem_zero_e
    have hkl_zero : klDiv p.toMeasure ν = 0 := by
      exact (add_eq_zero_iff_of_nonneg bot_le bot_le).mp hrem_zero |>.1
    -- Converse Gibbs inequality identifies the comparison measure with `p.toMeasure`.
    have hν_eq : ν = p.toMeasure := by
      have hzero_iff : klDiv p.toMeasure ν = 0 ↔ p.toMeasure = ν := klDiv_eq_zero_iff
      exact (hzero_iff.mp hkl_zero).symm
    exact (comparison_measure_eq_pmf_iff p q).mp hν_eq
  · intro hpq
    -- Once `q` agrees with `p`, the defining logarithmic series coincide termwise.
    cases hpq
    exact entropyInBase_eq_crossEntropyInBase_of_eq b p

-- Proof sketch: rewrite the difference between the two sides as the base-change factor
-- `(Real.log (b : ℝ))⁻¹` times the Kullback-Leibler divergence term
-- `∑ p(e) * log (p(e) / q(e))`, use the standard inequality `log x ≤ x - 1`, and identify the
-- equality case from strictness unless the entropy side is already `⊤`.
/-- Auxiliary inequality for Lemma 5.26: the base-`b` entropy of `p` is bounded above by the
base-`b`
cross-entropy against any sub-probability mass function `q`. -/
theorem entropyInBase_le_crossEntropyInBase (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1) :
    entropyInBase b p ≤ crossEntropyInBase b p q := by
  classical
  -- Route correction: the viable proof has to split first on whether `q` vanishes on `p.support`,
  -- then compare the positive-support branch through a KL-type nonnegative remainder.
  by_cases hzero : ∃ e, e ∈ p.support ∧ q e = 0
  · -- On the singular branch, the cross-entropy is already `⊤`.
    rw [crossEntropyInBase_eq_top_of_exists_zero_on_support b hb p q hzero]
    exact le_top
  · -- The positive-support branch is controlled by the nonnegative full-index KL remainder.
    have hnozero : ∀ e ∈ p.support, q e ≠ 0 := by
      intro e he hqe
      exact hzero ⟨e, he, hqe⟩
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    rw [cross_entropy_gap_full_decomposition b hb p q hq hnozero]
    have hcoeff_nonneg : (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) := by
      rw [← EReal.coe_inv]
      exact_mod_cast inv_nonneg.mpr (le_of_lt (Real.log_pos hb))
    have hrem_nonneg :
        (0 : EReal) ≤
          (((klDiv p.toMeasure (Measure.count.withDensity q)) +
              (1 - (Measure.count.withDensity q) Set.univ)) : ENNReal) := by
      exact_mod_cast (bot_le :
        (0 : ENNReal) ≤
          klDiv p.toMeasure (Measure.count.withDensity q) +
            (1 - (Measure.count.withDensity q) Set.univ))
    have hmul_nonneg :
        (0 : EReal) ≤
          ((Real.log (b : ℝ) : EReal)⁻¹ *
            (((klDiv p.toMeasure (Measure.count.withDensity q)) +
                (1 - (Measure.count.withDensity q) Set.univ)) : ENNReal)) := by
      exact mul_nonneg hcoeff_nonneg hrem_nonneg
    -- Adding a nonnegative remainder to the entropy yields the desired comparison.
    exact le_add_of_nonneg_right hmul_nonneg

/-- Lemma 5.26, equality part: for a sub-probability mass function `q`, equality between entropy
and cross-entropy occurs exactly when the entropy is infinite or `q` agrees pointwise with `p`. -/
theorem entropyInBase_eq_crossEntropyInBase_iff (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1) :
    entropyInBase b p = crossEntropyInBase b p q ↔
      entropyInBase b p = (⊤ : EReal) ∨ q = (p : E → ENNReal) := by
  constructor
  · intro hEq
    by_cases htop : entropyInBase b p = (⊤ : EReal)
    · -- If the entropy is already infinite, this is one of the stated equality cases.
      exact Or.inl htop
    · -- On the finite-entropy branch, equality can only happen when the KL remainder vanishes.
      have hcross_ne_top : crossEntropyInBase b p q ≠ (⊤ : EReal) := by
        rw [← hEq]
        exact htop
      have hnozero : ∀ e ∈ p.support, q e ≠ 0 := by
        intro e he hqe
        exact hcross_ne_top (crossEntropyInBase_eq_top_of_exists_zero_on_support b hb p q
          ⟨e, he, hqe⟩)
      exact Or.inr ((cross_entropy_remainder_eq_zero_iff b hb p q hq hnozero htop).1 hEq)
  · intro h
    rcases h with htop | hpq
    · -- The inequality already forces the cross-entropy to be `⊤` once the entropy is `⊤`.
      have hle : entropyInBase b p ≤ crossEntropyInBase b p q :=
        entropyInBase_le_crossEntropyInBase b hb p q hq
      have hcross_top : crossEntropyInBase b p q = (⊤ : EReal) := by
        have htop_le : (⊤ : EReal) ≤ crossEntropyInBase b p q := by
          rw [← htop]
          exact hle
        exact le_antisymm le_top htop_le
      rw [htop, hcross_top]
    · -- The diagonal case has already been reduced to the defining-series identity.
      cases hpq
      exact entropyInBase_eq_crossEntropyInBase_of_eq b p
