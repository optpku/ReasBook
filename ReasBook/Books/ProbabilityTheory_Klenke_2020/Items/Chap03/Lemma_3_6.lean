/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped BigOperators Topology

/-- Weak convergence of `ℕ`-valued laws, expressed as pointwise convergence of the singleton
probabilities. -/
def natLawWeaklyConvergesTo (μn : ℕ → PMF ℕ) (μ : PMF ℕ) : Prop :=
  ∀ k : ℕ, Tendsto (fun n ↦ ((μn n) k).toReal) atTop (𝓝 ((μ k).toReal))

/-- Setwise convergence of `ℕ`-valued laws, expressed through the associated probability measures
on the discrete measurable space `ℕ`. -/
def natLawSetwiseConvergesTo (μn : ℕ → PMF ℕ) (μ : PMF ℕ) : Prop :=
  ∀ A : Set ℕ,
    Tendsto (fun n ↦ ((μn n).toMeasure A).toReal) atTop (𝓝 ((μ.toMeasure A).toReal))

/-- Convergence of the probability generating functions on the whole unit interval `[0,1]`. -/
def probabilityGeneratingFunctionsConvergeOnUnitInterval
    (μn : ℕ → PMF ℕ) (μ : PMF ℕ) : Prop :=
  ∀ z : Set.Icc (0 : ℝ) 1,
    Tendsto (fun n ↦ probabilityGeneratingFunctionReal (μn n) z) atTop
      (𝓝 (probabilityGeneratingFunctionReal μ z))

/-- The pgfs converge on `[0,1]` exactly when their defining power series converge pointwise
there. -/
theorem probabilityGeneratingFunctionsConvergeOnUnitInterval_iff
    (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    probabilityGeneratingFunctionsConvergeOnUnitInterval μn μ ↔
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun n ↦ ∑' k : ℕ, ((μn n) k).toReal * z ^ k) atTop
          (𝓝 (∑' k : ℕ, (μ k).toReal * z ^ k)) := by
  constructor
  · intro h z hz
    simpa [probabilityGeneratingFunctionReal_apply] using h ⟨z, hz⟩
  · intro h z
    simpa [probabilityGeneratingFunctionReal_apply] using h z z.2

/-- Convergence of the probability generating functions on some initial interval `[0,η)` with
`η ∈ (0,1)`. -/
def probabilityGeneratingFunctionsConvergeOnInitialInterval
    (μn : ℕ → PMF ℕ) (μ : PMF ℕ) : Prop :=
  ∃ η ∈ Set.Ioo (0 : ℝ) 1,
    ∀ z ∈ Set.Ico (0 : ℝ) η,
      Tendsto (fun n ↦ probabilityGeneratingFunctionReal (μn n) z) atTop
        (𝓝 (probabilityGeneratingFunctionReal μ z))

/-- Convergence of the pgfs on some `[0,η)` means pointwise convergence of their defining power
series on that interval. -/
theorem probabilityGeneratingFunctionsConvergeOnInitialInterval_iff
    (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    probabilityGeneratingFunctionsConvergeOnInitialInterval μn μ ↔
      ∃ η ∈ Set.Ioo (0 : ℝ) 1,
        ∀ z ∈ Set.Ico (0 : ℝ) η,
          Tendsto (fun n ↦ ∑' k : ℕ, ((μn n) k).toReal * z ^ k) atTop
            (𝓝 (∑' k : ℕ, (μ k).toReal * z ^ k)) := by
  simp [probabilityGeneratingFunctionsConvergeOnInitialInterval,
    probabilityGeneratingFunctionReal_apply]

/-- Helper for Lemma 3.6: the real-valued singleton masses of a probability mass function sum to
`1`. -/
theorem pmf_toReal_tsum_eq_one (p : PMF ℕ) : ∑' k : ℕ, (p k).toReal = 1 := by
  -- Convert the `ENNReal` normalization of a `PMF` to the real-valued series used below.
  simpa [PMF.tsum_coe] using
    (ENNReal.tsum_toReal_eq (fun k => p.apply_ne_top k) :
      (∑' k : ℕ, p k).toReal = ∑' k : ℕ, (p k).toReal).symm

/-- Helper for Lemma 3.6: the probability of a set is the real series of its singleton masses. -/
theorem pmf_measure_toReal_eq_tsum_indicator (p : PMF ℕ) (A : Set ℕ) :
    (p.toMeasure A).toReal = ∑' k : ℕ, A.indicator (fun j => (p j).toReal) k := by
  -- Rewrite the measure as the `ENNReal` sum over singletons and then pass to `toReal`.
  rw [PMF.toMeasure_apply_eq_tsum, ENNReal.tsum_toReal_eq]
  · refine tsum_congr ?_
    intro k
    by_cases hk : k ∈ A <;> simp [hk]
  · intro k
    by_cases hk : k ∈ A <;> simp [hk, p.apply_ne_top]

/-- Helper for Lemma 3.6: the indicator-mass series of a set is summable because it is dominated
by the full mass series. -/
theorem pmf_indicator_summable (p : PMF ℕ) (A : Set ℕ) :
    Summable (fun k : ℕ => A.indicator (fun j => (p j).toReal) k) := by
  -- The indicator terms are nonnegative and bounded by the summable total-mass series.
  refine Summable.of_nonneg_of_le ?_ ?_ (ENNReal.summable_toReal p.tsum_coe_ne_top)
  · intro k
    by_cases hk : k ∈ A <;> simp [hk]
  · intro k
    by_cases hk : k ∈ A <;> simp [hk]

/-- Helper for Lemma 3.6: the real probability of a finite set is the corresponding finite sum of
singleton masses. -/
theorem pmf_measure_toReal_finset (p : PMF ℕ) (s : Finset ℕ) :
    ((p.toMeasure (s : Set ℕ)).toReal) = ∑ k ∈ s, (p k).toReal := by
  -- Convert the finite `ENNReal` mass formula to a real-valued finite sum.
  rw [p.toMeasure_apply_finset, ENNReal.toReal_sum (fun a _ha => p.apply_ne_top a)]

/-- Helper for Lemma 3.6: the tail mass above `m` is the complement of the prefix
`{0, ..., m}`. -/
theorem tail_measure_toReal_eq_one_sub_prefix (p : PMF ℕ) (m : ℕ) :
    ((p.toMeasure {k : ℕ | m < k}).toReal) =
      1 - ∑ k ∈ Finset.range (m + 1), (p k).toReal := by
  -- Rewrite the tail as the complement of the finite prefix and apply the probability-mass
  -- normalization on `univ`.
  have htail :
      {k : ℕ | m < k} = (((Finset.range (m + 1)) : Finset ℕ) : Set ℕ)ᶜ := by
    ext k
    simp
  have hcompl :=
    MeasureTheory.measureReal_compl (μ := p.toMeasure)
      (s := (((Finset.range (m + 1)) : Finset ℕ) : Set ℕ))
      ((Finset.range (m + 1)).finite_toSet.measurableSet)
  have hprefix :
      (p.toMeasure (Set.Iio (m + 1) : Set ℕ)).toReal =
        ∑ k ∈ Finset.range (m + 1), (p k).toReal := by
    have hset : (Set.Iio (m + 1) : Set ℕ) = (((Finset.range (m + 1)) : Finset ℕ) : Set ℕ) := by
      ext k
      simp
    rw [hset]
    simpa using pmf_measure_toReal_finset p (Finset.range (m + 1))
  simpa [htail, hprefix, MeasureTheory.Measure.real] using hcompl

/-- Helper for Lemma 3.6: intersecting a set with the finite prefix `{0, ..., m}` rewrites its
probability as the filtered prefix sum of the singleton masses. -/
theorem pmf_measure_toReal_inter_prefix_eq_sum_filter (p : PMF ℕ) (A : Set ℕ) (m : ℕ)
    [DecidablePred fun k => k ∈ A] :
    ((p.toMeasure (A ∩ ((((Finset.range (m + 1)) : Finset ℕ) : Set ℕ)))).toReal) =
      (∑ k ∈ (Finset.range (m + 1)).filter (fun k => k ∈ A), (p k).toReal) := by
  -- Rewrite the prefix intersection as the set of the filtered finite prefix.
  have hset :
      A ∩ ((((Finset.range (m + 1)) : Finset ℕ) : Set ℕ)) =
        ((((Finset.range (m + 1)).filter (fun k => k ∈ A)) : Finset ℕ) : Set ℕ) := by
    ext k
    simp [and_comm]
  rw [hset]
  -- The resulting set is finite, so its mass is the corresponding finite sum.
  simpa using pmf_measure_toReal_finset p ((Finset.range (m + 1)).filter (fun k => k ∈ A))

/-- Helper for Lemma 3.6: splitting a set into a finite prefix and a tail bounds the difference of
the corresponding probabilities by the prefix singleton errors and the two tail masses. -/
theorem setwise_cutoff_measureReal_bound (p q : PMF ℕ) (A : Set ℕ) (m : ℕ) :
    |((p.toMeasure A).toReal - (q.toMeasure A).toReal)| ≤
      (∑ k ∈ Finset.range (m + 1), |(p k).toReal - (q k).toReal|) +
        ((p.toMeasure {k : ℕ | m < k}).toReal + (q.toMeasure {k : ℕ | m < k}).toReal) := by
  classical
  let B : Set ℕ := ((((Finset.range (m + 1)) : Finset ℕ) : Set ℕ))
  have hB_meas : MeasurableSet B := (Finset.range (m + 1)).finite_toSet.measurableSet
  have hp_split :
      (p.toMeasure (A \ B)).toReal + (p.toMeasure (A ∩ B)).toReal = (p.toMeasure A).toReal := by
    -- Decompose `A` into its tail part and its finite prefix part.
    simpa [B] using
      (MeasureTheory.measureReal_diff_add_inter (μ := p.toMeasure) (s := A) (t := B) hB_meas)
  have hq_split :
      (q.toMeasure (A \ B)).toReal + (q.toMeasure (A ∩ B)).toReal = (q.toMeasure A).toReal := by
    -- Apply the same decomposition to the comparison law.
    simpa [B] using
      (MeasureTheory.measureReal_diff_add_inter (μ := q.toMeasure) (s := A) (t := B) hB_meas)
  have htail_subset : A \ B ⊆ {k : ℕ | m < k} := by
    intro k hk
    simp [B] at hk ⊢
    exact hk.2
  have hp_tail_le :
      (p.toMeasure (A \ B)).toReal ≤ (p.toMeasure {k : ℕ | m < k}).toReal :=
    MeasureTheory.measureReal_mono (μ := p.toMeasure) htail_subset
  have hq_tail_le :
      (q.toMeasure (A \ B)).toReal ≤ (q.toMeasure {k : ℕ | m < k}).toReal :=
    MeasureTheory.measureReal_mono (μ := q.toMeasure) htail_subset
  have htail_abs :
      |(p.toMeasure (A \ B)).toReal - (q.toMeasure (A \ B)).toReal| ≤
        (p.toMeasure {k : ℕ | m < k}).toReal + (q.toMeasure {k : ℕ | m < k}).toReal := by
    -- The tail difference is bounded by the sum of the two tail masses.
    have hp_nonneg : 0 ≤ (p.toMeasure (A \ B)).toReal := ENNReal.toReal_nonneg
    have hq_nonneg : 0 ≤ (q.toMeasure (A \ B)).toReal := ENNReal.toReal_nonneg
    have habs :
        |(p.toMeasure (A \ B)).toReal - (q.toMeasure (A \ B)).toReal| ≤
          (p.toMeasure (A \ B)).toReal + (q.toMeasure (A \ B)).toReal := by
      simpa [abs_of_nonneg hp_nonneg, abs_of_nonneg hq_nonneg] using
        (abs_sub_le ((p.toMeasure (A \ B)).toReal) 0 ((q.toMeasure (A \ B)).toReal))
    exact le_trans habs (add_le_add hp_tail_le hq_tail_le)
  have hprefix_abs :
      |(p.toMeasure (A ∩ B)).toReal - (q.toMeasure (A ∩ B)).toReal| ≤
        ∑ k ∈ Finset.range (m + 1), |(p k).toReal - (q k).toReal| := by
    -- Rewrite the prefix masses as finite filtered sums and bound by the full prefix error sum.
    rw [pmf_measure_toReal_inter_prefix_eq_sum_filter, pmf_measure_toReal_inter_prefix_eq_sum_filter]
    let s := (Finset.range (m + 1)).filter (fun k => k ∈ A)
    have hsum :
        |∑ k ∈ s, ((p k).toReal - (q k).toReal)| ≤
          ∑ k ∈ s, |(p k).toReal - (q k).toReal| := by
      simpa using Finset.abs_sum_le_sum_abs (fun k ↦ (p k).toReal - (q k).toReal) s
    have hfilter_le :
        ∑ k ∈ s, |(p k).toReal - (q k).toReal| ≤
          ∑ k ∈ Finset.range (m + 1), |(p k).toReal - (q k).toReal| := by
      rw [show s = (Finset.range (m + 1)).filter (fun k => k ∈ A) by rfl]
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases hkA : k ∈ A
      · simp [hkA]
      · simp [hkA]
    have hsub :
        (∑ k ∈ s, (p k).toReal) - ∑ k ∈ s, (q k).toReal =
          ∑ k ∈ s, ((p k).toReal - (q k).toReal) := by
      rw [← Finset.sum_sub_distrib]
    rw [hsub]
    exact le_trans hsum hfilter_le
  -- Combine the prefix/tail decomposition with the triangle inequality.
  calc
    |(p.toMeasure A).toReal - (q.toMeasure A).toReal|
        = |((p.toMeasure (A \ B)).toReal + (p.toMeasure (A ∩ B)).toReal) -
            ((q.toMeasure (A \ B)).toReal + (q.toMeasure (A ∩ B)).toReal)| := by
            rw [hp_split, hq_split]
    _ = |((p.toMeasure (A \ B)).toReal - (q.toMeasure (A \ B)).toReal) +
          ((p.toMeasure (A ∩ B)).toReal - (q.toMeasure (A ∩ B)).toReal)| := by ring
    _ ≤ |(p.toMeasure (A \ B)).toReal - (q.toMeasure (A \ B)).toReal| +
          |(p.toMeasure (A ∩ B)).toReal - (q.toMeasure (A ∩ B)).toReal| := by
          simpa [Real.norm_eq_abs] using
            (norm_add_le
              ((p.toMeasure (A \ B)).toReal - (q.toMeasure (A \ B)).toReal)
              ((p.toMeasure (A ∩ B)).toReal - (q.toMeasure (A ∩ B)).toReal))
    _ ≤ ((p.toMeasure {k : ℕ | m < k}).toReal + (q.toMeasure {k : ℕ | m < k}).toReal) +
          ∑ k ∈ Finset.range (m + 1), |(p k).toReal - (q k).toReal| := by
          gcongr
    _ = (∑ k ∈ Finset.range (m + 1), |(p k).toReal - (q k).toReal|) +
          ((p.toMeasure {k : ℕ | m < k}).toReal + (q.toMeasure {k : ℕ | m < k}).toReal) := by
          ring

/-- Helper for Lemma 3.6: convergence of the singleton masses implies setwise convergence on every
subset of `ℕ`. -/
theorem setwise_converges_of_mass_converges (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    natLawWeaklyConvergesTo μn μ → natLawSetwiseConvergesTo μn μ := by
  intro hmass A
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hμsum :
      Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, (μ k).toReal) atTop (𝓝 1) := by
    -- The prefix masses of `μ` exhaust the total mass `1`.
    simpa [pmf_toReal_tsum_eq_one] using
      ((ENNReal.summable_toReal μ.tsum_coe_ne_top).hasSum.tendsto_sum_nat)
  rw [Metric.tendsto_atTop] at hμsum
  rcases hμsum (ε / 4) (by positivity) with ⟨m, hm⟩
  have hμtail_lt : ((μ.toMeasure {k : ℕ | m < k}).toReal) < ε / 4 := by
    -- Choose the cutoff so that the target law has small tail above `m`.
    have hdist := hm (m + 1) (Nat.le_succ m)
    have habs :
        |1 - ∑ k ∈ Finset.range (m + 1), (μ k).toReal| < ε / 4 := by
      simpa [Real.dist_eq, abs_sub_comm] using hdist
    have hnonneg :
        0 ≤ 1 - ∑ k ∈ Finset.range (m + 1), (μ k).toReal := by
      rw [← tail_measure_toReal_eq_one_sub_prefix]
      exact ENNReal.toReal_nonneg
    simpa [tail_measure_toReal_eq_one_sub_prefix, abs_of_nonneg hnonneg] using habs
  have herror :
      Tendsto
        (fun n ↦ ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal|)
        atTop (𝓝 0) := by
    -- The finite prefix of singleton errors tends to zero termwise and hence as a finite sum.
    have hterm :
        ∀ k ∈ Finset.range (m + 1),
          Tendsto (fun n ↦ |((μn n) k).toReal - (μ k).toReal|) atTop (𝓝 0) := by
      intro k hk
      have hk' :
          Tendsto (fun n ↦ ((μn n) k).toReal - (μ k).toReal) atTop (𝓝 0) := by
        simpa using
          (hmass k).sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (μ k).toReal) atTop (𝓝 ((μ k).toReal)))
      simpa using hk'.abs
    simpa using tendsto_finset_sum (Finset.range (m + 1)) hterm
  rw [Metric.tendsto_atTop] at herror
  rcases herror (ε / 4) (by positivity) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have herror_lt :
      ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| < ε / 4 := by
    have hsum_nonneg :
        0 ≤ ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| := by
      exact Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    simpa [Real.dist_eq, abs_of_nonneg hsum_nonneg] using hN n hn
  have hprefix_diff_le :
      |∑ k ∈ Finset.range (m + 1), (((μn n) k).toReal - (μ k).toReal)| ≤
        ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (fun k ↦ ((μn n) k).toReal - (μ k).toReal) (Finset.range (m + 1)))
  have hμn_tail_lt : (((μn n).toMeasure {k : ℕ | m < k}).toReal) < ε / 2 := by
    -- The approximating tail is controlled by the target tail plus the prefix mass error.
    have htail_eq :
        (((μn n).toMeasure {k : ℕ | m < k}).toReal) =
          1 - ∑ k ∈ Finset.range (m + 1), ((μn n) k).toReal := by
      simpa using tail_measure_toReal_eq_one_sub_prefix (μn n) m
    have hprefix_tail :
        (((μn n).toMeasure {k : ℕ | m < k}).toReal) - ((μ.toMeasure {k : ℕ | m < k}).toReal) =
          ∑ k ∈ Finset.range (m + 1), ((μ k).toReal - ((μn n) k).toReal) := by
      rw [htail_eq, tail_measure_toReal_eq_one_sub_prefix]
      have hsum_sub :
          (∑ k ∈ Finset.range (m + 1), ((μ k).toReal - ((μn n) k).toReal)) =
            (∑ k ∈ Finset.range (m + 1), (μ k).toReal) -
              ∑ k ∈ Finset.range (m + 1), ((μn n) k).toReal := by
        rw [Finset.sum_sub_distrib]
      rw [hsum_sub]
      ring
    have htail_diff_le :
        |(((μn n).toMeasure {k : ℕ | m < k}).toReal) - ((μ.toMeasure {k : ℕ | m < k}).toReal)| ≤
          ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| := by
      calc
        |(((μn n).toMeasure {k : ℕ | m < k}).toReal) - ((μ.toMeasure {k : ℕ | m < k}).toReal)| =
            |∑ k ∈ Finset.range (m + 1), ((μ k).toReal - ((μn n) k).toReal)| := by
              rw [hprefix_tail]
        _ ≤ ∑ k ∈ Finset.range (m + 1), |(μ k).toReal - ((μn n) k).toReal| := by
              simpa using
                (Finset.abs_sum_le_sum_abs (fun k ↦ (μ k).toReal - ((μn n) k).toReal)
                  (Finset.range (m + 1)))
        _ = ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [abs_sub_comm]
    have htail_le :
        (((μn n).toMeasure {k : ℕ | m < k}).toReal) ≤
          ((μ.toMeasure {k : ℕ | m < k}).toReal) +
            ∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal| := by
      have := abs_le.mp htail_diff_le
      linarith
    linarith
  have hmain_le := setwise_cutoff_measureReal_bound (μn n) μ A m
  have hmain_lt :
      |(((μn n).toMeasure A).toReal) - ((μ.toMeasure A).toReal)| < ε := by
    have hbound :
        |(((μn n).toMeasure A).toReal) - ((μ.toMeasure A).toReal)| ≤
          (∑ k ∈ Finset.range (m + 1), |((μn n) k).toReal - (μ k).toReal|) +
            ((((μn n).toMeasure {k : ℕ | m < k}).toReal) +
              ((μ.toMeasure {k : ℕ | m < k}).toReal)) := hmain_le
    linarith
  simpa [Real.dist_eq] using hmain_lt

/-- Helper for Lemma 3.6: the pgf series is summable on `[0,1)` because the coefficients are
dominated by the mass series. -/
theorem pgf_series_summable (p : PMF ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun t : ℕ ↦ (p t).toReal * z ^ t) := by
  -- Each weighted term is nonnegative and bounded by the corresponding singleton mass.
  refine Summable.of_nonneg_of_le
    (fun t ↦ mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz0 _)) ?_
    (ENNReal.summable_toReal p.tsum_coe_ne_top)
  intro t
  have hzpow_le_one : z ^ t ≤ 1 := pow_le_one₀ hz0 hz1.le
  have hp_nonneg : 0 ≤ (p t).toReal := ENNReal.toReal_nonneg
  nlinarith

/-- Helper for Lemma 3.6: the shifted singleton masses form a summable series. -/
theorem shifted_mass_summable (p : PMF ℕ) (k : ℕ) :
    Summable (fun t : ℕ ↦ (p (t + k)).toReal) := by
  -- A shifted subseries of the summable full mass series is summable.
  have hk : Function.Injective (fun t : ℕ ↦ t + k) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  exact (ENNReal.summable_toReal p.tsum_coe_ne_top).comp_injective hk

/-- Helper for Lemma 3.6: every shifted residual pgf series is summable on `[0,1)`. -/
theorem shifted_residual_summable (p : PMF ℕ) (k : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun t : ℕ ↦ (p (t + k)).toReal * z ^ t) := by
  -- The shifted weighted terms are dominated by the shifted mass series.
  refine Summable.of_nonneg_of_le
    (fun t ↦ mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz0 _)) ?_
    (shifted_mass_summable p k)
  intro t
  have hzpow_le_one : z ^ t ≤ 1 := pow_le_one₀ hz0 hz1.le
  have hp_nonneg : 0 ≤ (p (t + k)).toReal := ENNReal.toReal_nonneg
  nlinarith

/-- Helper for Lemma 3.6: splitting the pgf at index `k` isolates the residual power series. -/
theorem pgf_split_at (p : PMF ℕ) (k : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (∑' t : ℕ, (p t).toReal * z ^ t) =
      (∑ j ∈ Finset.range k, (p j).toReal * z ^ j) +
        z ^ k * (∑' t : ℕ, (p (t + k)).toReal * z ^ t) := by
  -- Split the series at `k` and factor the common power `z ^ k` out of the tail.
  have hsplit :
      (∑ j ∈ Finset.range k, (p j).toReal * z ^ j) +
        ∑' t : ℕ, (p (t + k)).toReal * z ^ (t + k) =
          ∑' t : ℕ, (p t).toReal * z ^ t := by
    simpa using Summable.sum_add_tsum_nat_add k (pgf_series_summable p hz0 hz1)
  calc
    (∑' t : ℕ, (p t).toReal * z ^ t) =
        (∑ j ∈ Finset.range k, (p j).toReal * z ^ j) +
          ∑' t : ℕ, (p (t + k)).toReal * z ^ (t + k) := by
          simpa using hsplit.symm
    _ = (∑ j ∈ Finset.range k, (p j).toReal * z ^ j) +
          z ^ k * (∑' t : ℕ, (p (t + k)).toReal * z ^ t) := by
          congr 1
          calc
            (∑' t : ℕ, (p (t + k)).toReal * z ^ (t + k)) =
                ∑' t : ℕ, z ^ k * ((p (t + k)).toReal * z ^ t) := by
                  refine tsum_congr ?_
                  intro t
                  calc
                    (p (t + k)).toReal * z ^ (t + k) =
                        (p (t + k)).toReal * (z ^ t * z ^ k) := by
                          rw [pow_add]
                    _ = z ^ k * ((p (t + k)).toReal * z ^ t) := by ring
            _ = z ^ k * (∑' t : ℕ, (p (t + k)).toReal * z ^ t) := by
                  rw [tsum_mul_left]

/-- Helper for Lemma 3.6: one coefficient can be split off from the shifted residual series. -/
theorem shifted_residual_split (p : PMF ℕ) (k : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (∑' t : ℕ, (p (t + k)).toReal * z ^ t) =
      (p k).toReal + z * (∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ t) := by
  -- Split off the zeroth term and factor one power of `z` from the remaining tail.
  have hsplit :
      (∑ j ∈ Finset.range 1, (p (j + k)).toReal * z ^ j) +
        ∑' t : ℕ, (p ((t + 1) + k)).toReal * z ^ (t + 1) =
          ∑' t : ℕ, (p (t + k)).toReal * z ^ t := by
    simpa [Nat.add_assoc] using
      Summable.sum_add_tsum_nat_add 1 (shifted_residual_summable p k hz0 hz1)
  calc
    (∑' t : ℕ, (p (t + k)).toReal * z ^ t) =
        (∑ j ∈ Finset.range 1, (p (j + k)).toReal * z ^ j) +
          ∑' t : ℕ, (p ((t + 1) + k)).toReal * z ^ (t + 1) := by
          simpa using hsplit.symm
    _ = (p k).toReal + ∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ (t + 1) := by
          simp [Nat.add_left_comm, Nat.add_comm]
    _ = (p k).toReal + z * (∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ t) := by
          congr 1
          calc
            (∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ (t + 1)) =
                ∑' t : ℕ, z * ((p (t + (k + 1))).toReal * z ^ t) := by
                  refine tsum_congr ?_
                  intro t
                  calc
                    (p (t + (k + 1))).toReal * z ^ (t + 1) =
                        (p (t + (k + 1))).toReal * (z ^ t * z) := by
                          rw [pow_succ]
                    _ = z * ((p (t + (k + 1))).toReal * z ^ t) := by ring
            _ = z * (∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ t) := by
                  rw [tsum_mul_left]

/-- Helper for Lemma 3.6: the shifted residual differs from its leading coefficient by at most the
evaluation point `z`. -/
theorem shifted_residual_singleton_error_le (p : PMF ℕ) (k : ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z < 1) :
    |((∑' t : ℕ, (p (t + k)).toReal * z ^ t) - (p k).toReal)| ≤ z := by
  -- Rewrite the error as `z` times a nonnegative shifted tail and bound that tail by total mass `1`.
  let tail : ℝ := ∑' t : ℕ, (p (t + (k + 1))).toReal * z ^ t
  have htail_nonneg : 0 ≤ tail := by
    -- Every term in the shifted tail is nonnegative.
    dsimp [tail]
    refine tsum_nonneg ?_
    intro t
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz0 _)
  have htail_le_shifted_mass :
      tail ≤ ∑' t : ℕ, (p (t + (k + 1))).toReal := by
    -- Dropping the factor `z ^ t ≤ 1` can only increase the nonnegative series.
    dsimp [tail]
    refine Summable.tsum_le_tsum ?_ (shifted_residual_summable p (k + 1) hz0 hz1)
      (shifted_mass_summable p (k + 1))
    intro t
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hz0 hz1.le)
  have hshifted_mass_le_one :
      (∑' t : ℕ, (p (t + (k + 1))).toReal) ≤ 1 := by
    -- The shifted mass series is a tail of the full mass series, whose total sum is `1`.
    have hsplit_mass :
        (∑ j ∈ Finset.range (k + 1), (p j).toReal) + ∑' t : ℕ, (p (t + (k + 1))).toReal =
          1 := by
      simpa [pmf_toReal_tsum_eq_one] using
        Summable.sum_add_tsum_nat_add (k + 1) (ENNReal.summable_toReal p.tsum_coe_ne_top)
    have hprefix_nonneg :
        0 ≤ ∑ j ∈ Finset.range (k + 1), (p j).toReal := by
      exact Finset.sum_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)
    linarith
  have htail_le_one : tail ≤ 1 := le_trans htail_le_shifted_mass hshifted_mass_le_one
  have hdiff :
      ((∑' t : ℕ, (p (t + k)).toReal * z ^ t) - (p k).toReal) = z * tail := by
    -- The split formula isolates the leading coefficient exactly.
    have hsplit := shifted_residual_split p k hz0 hz1
    dsimp [tail]
    linarith
  rw [hdiff, abs_of_nonneg (mul_nonneg hz0 htail_nonneg)]
  nlinarith

/-- Helper for Lemma 3.6: convergence of singleton masses implies convergence of the probability
generating functions on the whole unit interval. -/
theorem pgf_converges_on_unit_of_mass_converges (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    natLawWeaklyConvergesTo μn μ →
      probabilityGeneratingFunctionsConvergeOnUnitInterval μn μ := by
  intro hmass z
  rcases z with ⟨z, hz0, hz1⟩
  by_cases hzEq : z = 1
  · -- At `z = 1`, every pgf equals the total mass `1`.
    subst hzEq
    have hconst :
        (fun n : ℕ ↦ probabilityGeneratingFunctionReal (μn n) (1 : ℝ)) = fun _ ↦ (1 : ℝ) := by
      funext n
      simp [probabilityGeneratingFunctionReal_apply, pmf_toReal_tsum_eq_one]
    rw [hconst]
    simpa [probabilityGeneratingFunctionReal_apply, pmf_toReal_tsum_eq_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)))
  · have hzlt : z < 1 := lt_of_le_of_ne hz1 hzEq
    -- For `0 ≤ z < 1`, use dominated convergence with the geometric majorant `z^k`.
    simpa [probabilityGeneratingFunctionReal_apply] using
      (tendsto_tsum_of_dominated_convergence (bound := fun k : ℕ => z ^ k) (by
        exact summable_geometric_of_lt_one hz0 hzlt) (by
          intro k
          simpa [mul_comm] using (hmass k).const_mul (z ^ k)) (by
            filter_upwards with n k
            have hpk : ((μn n) k).toReal ≤ 1 := by
              have hpk' : ((μn n).toMeasure).real ({k} : Set ℕ) ≤ 1 :=
                MeasureTheory.measureReal_le_one (μ := (μn n).toMeasure) (s := ({k} : Set ℕ))
              simpa [MeasureTheory.Measure.real_def, PMF.toMeasure_apply_singleton,
                measurableSet_singleton] using hpk'
            have hzpow_nonneg : 0 ≤ z ^ k := pow_nonneg hz0 _
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg hzpow_nonneg)]
            nlinarith))

/-- Helper for Lemma 3.6: convergence of the probability generating functions on an initial
interval should imply convergence of the singleton masses by coefficient extraction. -/
theorem mass_converges_of_pgf_converges_on_initial_interval (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    probabilityGeneratingFunctionsConvergeOnInitialInterval μn μ →
      natLawWeaklyConvergesTo μn μ := by
  intro hpgf
  rcases (probabilityGeneratingFunctionsConvergeOnInitialInterval_iff μn μ).mp hpgf with
    ⟨η, hη, hseries⟩
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih
  rw [Metric.tendsto_atTop]
  intro ε hε
  let z : ℝ := min (η / 2) (ε / 5)
  have hz_pos : 0 < z := by
    -- Choose a strictly positive evaluation point that is small enough for the final error bound.
    dsimp [z]
    refine lt_min ?_ ?_
    · have hηpos : 0 < η := hη.1
      linarith
    · linarith
  have hz0 : 0 ≤ z := le_of_lt hz_pos
  have hz_eta : z < η := by
    -- The point `z` lies in the initial interval of pgf convergence.
    have hz_le : z ≤ η / 2 := by
      dsimp [z]
      exact min_le_left _ _
    have hhalf_lt : η / 2 < η := by
      linarith
    exact lt_of_le_of_lt hz_le hhalf_lt
  have hz1 : z < 1 := lt_trans hz_eta hη.2
  have hz_small : z ≤ ε / 5 := by
    dsimp [z]
    exact min_le_right _ _
  have hz_mem : z ∈ Set.Ico (0 : ℝ) η := ⟨hz0, hz_eta⟩
  let residual : PMF ℕ → ℕ → ℝ := fun p m ↦ ∑' t : ℕ, (p (t + m)).toReal * z ^ t
  have hfull :
      Tendsto (fun n ↦ ∑' t : ℕ, ((μn n) t).toReal * z ^ t) atTop
        (𝓝 (∑' t : ℕ, (μ t).toReal * z ^ t)) :=
    hseries z hz_mem
  have hprefix :
      Tendsto (fun n ↦ ∑ j ∈ Finset.range k, ((μn n) j).toReal * z ^ j) atTop
        (𝓝 (∑ j ∈ Finset.range k, (μ j).toReal * z ^ j)) := by
    -- The finite prefix converges because each earlier coefficient already converges.
    refine tendsto_finset_sum (Finset.range k) ?_
    intro j hj
    simpa using (ih j (Finset.mem_range.mp hj)).mul_const (z ^ j)
  have hscaled_eq_seq :
      (fun n ↦ z ^ k * residual (μn n) k) =
        (fun n ↦ (∑' t : ℕ, ((μn n) t).toReal * z ^ t) -
          ∑ j ∈ Finset.range k, ((μn n) j).toReal * z ^ j) := by
    -- `pgf_split_at` expresses the scaled residual as the pgf minus its finite prefix.
    funext n
    have hsplit := pgf_split_at (μn n) k hz0 hz1
    dsimp [residual]
    linarith
  have hscaled_eq_lim :
      z ^ k * residual μ k =
        (∑' t : ℕ, (μ t).toReal * z ^ t) - ∑ j ∈ Finset.range k, (μ j).toReal * z ^ j := by
    -- The same decomposition holds for the limiting law.
    have hsplit := pgf_split_at μ k hz0 hz1
    dsimp [residual]
    linarith
  have hscaled :
      Tendsto (fun n ↦ z ^ k * residual (μn n) k) atTop (𝓝 (z ^ k * residual μ k)) := by
    -- Subtracting the convergent prefix from the convergent pgf leaves the scaled residual.
    rw [hscaled_eq_seq]
    simpa [hscaled_eq_lim] using hfull.sub hprefix
  have hz_ne : z ≠ 0 := ne_of_gt hz_pos
  have hzpow_ne : z ^ k ≠ 0 := pow_ne_zero k hz_ne
  have hresidual :
      Tendsto (fun n ↦ residual (μn n) k) atTop (𝓝 (residual μ k)) := by
    -- Cancel the nonzero factor `z ^ k` to recover convergence of the residual series itself.
    simpa [residual, hzpow_ne, mul_assoc] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (z ^ k)⁻¹) atTop (𝓝 ((z ^ k)⁻¹))).mul hscaled
  rw [Metric.tendsto_atTop] at hresidual
  rcases hresidual (ε / 2) (by positivity) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hresidual_lt : |residual (μn n) k - residual μ k| < ε / 2 := by
    simpa [Real.dist_eq] using hN n hn
  have hleft_error :
      |((μn n) k).toReal - residual (μn n) k| ≤ z := by
    -- Each coefficient is within `z` of its shifted residual evaluation.
    dsimp [residual]
    simpa [abs_sub_comm] using shifted_residual_singleton_error_le (μn n) k hz0 hz1
  have hright_error :
      |residual μ k - (μ k).toReal| ≤ z := by
    -- The same coefficient-residual estimate holds for the limit law.
    dsimp [residual]
    simpa using shifted_residual_singleton_error_le μ k hz0 hz1
  have hstep1 :
      |((μn n) k).toReal - (μ k).toReal| ≤
        |((μn n) k).toReal - residual (μn n) k| +
          |residual (μn n) k - (μ k).toReal| := by
    exact abs_sub_le ((μn n) k).toReal (residual (μn n) k) (μ k).toReal
  have hstep2 :
      |residual (μn n) k - (μ k).toReal| ≤
        |residual (μn n) k - residual μ k| + |residual μ k - (μ k).toReal| := by
    exact abs_sub_le (residual (μn n) k) (residual μ k) (μ k).toReal
  have hmain_lt : |((μn n) k).toReal - (μ k).toReal| < ε := by
    linarith
  simpa [Real.dist_eq] using hmain_lt

-- Proof sketch: prove `(i) → (ii)` by controlling the tail of the discrete laws uniformly in the
-- target set, `(ii) → (i)` by testing singleton sets, and use the elementary theory of power
-- series to identify `(i)`, `(iii)`, and `(iv)`.
/-- Lemma 3.6: For probability laws on `ℕ`, convergence of singleton masses, convergence on all
subsets, convergence of the probability generating functions on `[0,1]`, and convergence on some
interval `[0,η)` with `η ∈ (0,1)` are equivalent. This is the notion of weak convergence used in
the text. -/
theorem natLawWeakConvergence_tfae (μn : ℕ → PMF ℕ) (μ : PMF ℕ) :
    List.TFAE
      [natLawWeaklyConvergesTo μn μ,
        natLawSetwiseConvergesTo μn μ,
        probabilityGeneratingFunctionsConvergeOnUnitInterval μn μ,
        probabilityGeneratingFunctionsConvergeOnInitialInterval μn μ] := by
  tfae_have 1 → 2 := by
    -- First use the discrete tail argument to pass from singleton masses to arbitrary sets.
    exact setwise_converges_of_mass_converges μn μ
  tfae_have 2 → 1 := by
    -- Testing setwise convergence on singleton sets recovers the defining weak convergence.
    intro hset k
    simpa [natLawSetwiseConvergesTo, natLawWeaklyConvergesTo,
      PMF.toMeasure_apply_singleton, measurableSet_singleton] using hset {k}
  tfae_have 3 → 4 := by
    -- Restricting convergence from `[0,1]` to `[0, 1 / 2)` is immediate.
    intro hpgf
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro z hz
    exact hpgf ⟨z, hz.1, hz.2.le.trans (by norm_num)⟩
  tfae_have 1 → 3 := by
    -- The forward pgf implication now follows from the dominated-convergence helper.
    exact pgf_converges_on_unit_of_mass_converges μn μ
  tfae_have 4 → 1 := by
    -- The only remaining step is the coefficient-extraction argument on a small interval.
    exact mass_converges_of_pgf_converges_on_initial_interval μn μ
  tfae_finish
