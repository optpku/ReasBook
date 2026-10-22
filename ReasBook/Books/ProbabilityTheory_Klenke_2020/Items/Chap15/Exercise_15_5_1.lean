/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

noncomputable section

/-- Helper for Exercise 15.5.1: the witness probability space uses `ULift ℕ`-indexed coordinate
pairs so that the ambient space lives in the requested universe `Type u`. -/
private abbrev heavyTailCLTSpace : Type u :=
  ULift.{u} ℕ → ℝ × ℝ

/-- Helper for Exercise 15.5.1: the rare-spike probability at time `n` is the summable weight
`(n + 1)⁻²`. -/
private def spikeWeightReal (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ (2 : ℕ))⁻¹

/-- Helper for Exercise 15.5.1: the `n`th rare-spike law keeps mass `1 - pₙ` at `0` and uses the
heavy-tailed law `ν` with mass `pₙ`. -/
private def rareSpikeLaw (ν : ProbabilityMeasure ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - spikeWeightReal n) • Measure.dirac 0 +
    ENNReal.ofReal (spikeWeightReal n) • (ν : Measure ℝ)

/-- Helper for Exercise 15.5.1: the fixed heavy-tail law is the image of Lebesgue measure on
`[0, 1]` under `x ↦ x⁻¹`. -/
private def unitIntervalInvMeasure : Measure ℝ :=
  Measure.map (fun x : ℝ ↦ x⁻¹) (volume.restrict (Set.Icc 0 1))

/-- Helper for Exercise 15.5.1: the inverse-image law of Lebesgue measure on `[0, 1]` is a
probability measure. -/
private lemma unitIntervalInvMeasure_isProbability :
    IsProbabilityMeasure unitIntervalInvMeasure := by
  -- Proof comment: `volume.restrict (Icc 0 1)` already has total mass `1`, and pushforwards
  -- preserve probability measures.
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  simpa [unitIntervalInvMeasure] using
    (Measure.isProbabilityMeasure_map
      (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
      measurable_inv.aemeasurable)

/-- Helper for Exercise 15.5.1: package the inverse-image heavy-tail law as a
`ProbabilityMeasure`. -/
private def unitIntervalInvLaw : ProbabilityMeasure ℝ :=
  ⟨unitIntervalInvMeasure, unitIntervalInvMeasure_isProbability⟩

/-- Helper for Exercise 15.5.1: the `n`th coordinate pair law combines a standard Gaussian first
coordinate with the rare heavy-tail spike on the second coordinate. -/
private def pairMarginal (ν : ProbabilityMeasure ℝ) (n : ℕ) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (rareSpikeLaw ν n)

/-- Helper for Exercise 15.5.1: reindex the coordinate laws along `ULift ℕ` for the ambient
product space. -/
private def pairMarginalAt (ν : ProbabilityMeasure ℝ) : ULift.{u} ℕ → Measure (ℝ × ℝ) :=
  fun i ↦ pairMarginal ν i.down

/-- Helper for Exercise 15.5.1: the `n`th coordinate pair on the witness product space. -/
private def pairCoordinate (n : ℕ) : heavyTailCLTSpace → ℝ × ℝ :=
  fun ω ↦ ω ⟨n⟩

/-- Helper for Exercise 15.5.1: the Gaussian core coordinate is the first component of the `n`th
pair coordinate. -/
private def gaussianCoordinate (n : ℕ) : heavyTailCLTSpace → ℝ :=
  fun ω ↦ (pairCoordinate n ω).1

/-- Helper for Exercise 15.5.1: the rare heavy-tail spike is the second component of the `n`th
pair coordinate. -/
private def spikeCoordinate (n : ℕ) : heavyTailCLTSpace → ℝ :=
  fun ω ↦ (pairCoordinate n ω).2

/-- Helper for Exercise 15.5.1: the witness summand is the Gaussian core plus the rare spike. -/
private def heavyTailSummand (n : ℕ) : heavyTailCLTSpace → ℝ :=
  fun ω ↦ gaussianCoordinate n ω + spikeCoordinate n ω

/-- Helper for Exercise 15.5.1: the spike weights are nonnegative. -/
private lemma spikeWeightReal_nonneg (n : ℕ) :
    0 ≤ spikeWeightReal n := by
  -- Proof comment: `spikeWeightReal n` is a reciprocal square.
  simpa [spikeWeightReal] using
    (inv_nonneg.mpr (show 0 ≤ ((n + 1 : ℝ) ^ (2 : ℕ)) by positivity))

/-- Helper for Exercise 15.5.1: every spike weight is strictly positive. -/
private lemma spikeWeightReal_pos (n : ℕ) :
    0 < spikeWeightReal n := by
  -- Proof comment: `(n + 1)^2` is positive, so its reciprocal is positive.
  simpa [spikeWeightReal] using
    (inv_pos.mpr (show 0 < ((n + 1 : ℝ) ^ (2 : ℕ)) by positivity))

/-- Helper for Exercise 15.5.1: every spike weight is at most `1`. -/
private lemma spikeWeightReal_le_one (n : ℕ) :
    spikeWeightReal n ≤ 1 := by
  -- Proof comment: `(n + 1)^2 ≥ 1`, so its reciprocal is at most `1`.
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hsq_ge_one : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ((n + 1 : ℝ) - 1), hn]
  have hsq_ne : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
    positivity
  have hdiv : 1 / ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 := by
    field_simp [hsq_ne]
    nlinarith
  simpa [spikeWeightReal, one_div] using hdiv

/-- Helper for Exercise 15.5.1: the spike weights form a summable series. -/
private lemma summable_spikeWeightReal :
    Summable spikeWeightReal := by
  -- Proof comment: this is the shifted `p`-series with exponent `2`.
  have hsquare : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) := by
    exact Real.summable_nat_pow_inv.mpr (by norm_num)
  simpa [spikeWeightReal] using
    (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℕ))⁻¹) 1).2 hsquare

/-- Helper for Exercise 15.5.1: the rare-spike law is a probability measure because the two
weights add up to `1`. -/
private lemma rareSpikeLawIsProbability (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    IsProbabilityMeasure (rareSpikeLaw ν n) := by
  -- Proof comment: the zero atom carries mass `1 - pₙ` and the heavy-tail part carries mass `pₙ`.
  refine ⟨?_⟩
  have hzero_nonneg : 0 ≤ 1 - spikeWeightReal n := by
    exact sub_nonneg.mpr (spikeWeightReal_le_one n)
  have hweight_nonneg : 0 ≤ spikeWeightReal n := spikeWeightReal_nonneg n
  calc
    rareSpikeLaw ν n Set.univ
        = ENNReal.ofReal (1 - spikeWeightReal n) + ENNReal.ofReal (spikeWeightReal n) := by
            simp [rareSpikeLaw]
    _ = ENNReal.ofReal ((1 - spikeWeightReal n) + spikeWeightReal n) := by
          rw [← ENNReal.ofReal_add hzero_nonneg hweight_nonneg]
    _ = 1 := by
          ring_nf
          norm_num

/-- Helper for Exercise 15.5.1: the product coordinate law is a probability measure. -/
private lemma pairMarginalIsProbability (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    IsProbabilityMeasure (pairMarginal ν n) := by
  -- Proof comment: products of probability measures are probability measures.
  letI : IsProbabilityMeasure (rareSpikeLaw ν n) := rareSpikeLawIsProbability ν n
  simpa [pairMarginal] using
    (show IsProbabilityMeasure ((gaussianReal 0 1).prod (rareSpikeLaw ν n)) by infer_instance)

/-- Helper for Exercise 15.5.1: under the rare-spike law, the event `x ≠ 0` has probability at
most the rare-spike weight `pₙ`. -/
private lemma rareSpikeLaw_nonzero_event_le_weight (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    rareSpikeLaw ν n {x : ℝ | x ≠ 0} ≤ ENNReal.ofReal (spikeWeightReal n) := by
  -- Proof comment: the atom at `0` contributes nothing to `{x | x ≠ 0}`, and the heavy-tail law
  -- contributes at most its full mass `1`.
  calc
    rareSpikeLaw ν n {x : ℝ | x ≠ 0}
        = ENNReal.ofReal (spikeWeightReal n) * (ν : Measure ℝ) {x : ℝ | x ≠ 0} := by
            simp [rareSpikeLaw]
    _ ≤ ENNReal.ofReal (spikeWeightReal n) * 1 := by
          have hprob : (ν : Measure ℝ) {x : ℝ | x ≠ 0} ≤ 1 := by
            simpa using (prob_le_one (μ := (ν : Measure ℝ)) (s := {x : ℝ | x ≠ 0}))
          exact mul_le_mul_left' hprob _
    _ = ENNReal.ofReal (spikeWeightReal n) := by
          simp

/-- Helper for Exercise 15.5.1: a real-valued random variable with infinite absolute first moment
has `∫⁻ ENNReal.ofReal |f| = ⊤`. -/
private lemma lintegral_abs_eq_top_of_notIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hfin : ¬ Integrable f μ) :
    ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ = ⊤ := by
  -- Proof comment: if the absolute `lintegral` were finite, then `|f|` would be integrable, and
  -- hence so would `f`.
  by_contra htop
  have hHasFinite : HasFiniteIntegral (fun ω ↦ |f ω|) μ := by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ abs_nonneg (f ω))]
    simpa [lt_top_iff_ne_top] using htop
  have hIntAbs : Integrable (fun ω ↦ |f ω|) μ := ⟨hf.norm, hHasFinite⟩
  have hIntNorm : Integrable (fun ω ↦ ‖f ω‖) μ := by
    simpa [Real.norm_eq_abs] using hIntAbs
  exact hfin ((integrable_norm_iff hf).1 hIntNorm)

/-- Helper for Exercise 15.5.1: the inverse-image heavy-tail law has infinite absolute first
moment because `x ↦ x⁻¹` is not integrable on `[0, 1]`. -/
private lemma unitIntervalInvLaw_notIntegrable :
    ¬ Integrable id (unitIntervalInvLaw : Measure ℝ) := by
  -- Proof comment: integrability of `id` under the pushforward law would pull back to
  -- integrability of `x ↦ x⁻¹` on `[0, 1]`, contradicting the interval-integrability criterion at
  -- a singularity.
  intro hInt
  have hPullback : Integrable (fun x : ℝ ↦ x⁻¹) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    simpa [unitIntervalInvLaw, unitIntervalInvMeasure, Function.comp] using
      (integrable_map_measure
        (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (f := fun x : ℝ ↦ x⁻¹) (g := id)
        aestronglyMeasurable_id measurable_inv.aemeasurable).mp hInt
  have hIntOn : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Set.Icc (0 : ℝ) 1) volume := by
    simpa [IntegrableOn] using hPullback
  have hInterval : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 1 := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num)).2 hIntOn
  have hImpossible :
      ¬ (IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 1) := by
    intro h
    have hfalse : ¬ ((0 : ℝ) = 1 ∨ (0 : ℝ) ∉ Set.uIcc (0 : ℝ) 1) := by
      simp
    exact hfalse ((intervalIntegrable_inv_iff (a := (0 : ℝ)) (b := (1 : ℝ))).1 h)
  exact hImpossible hInterval

/-- Helper for Exercise 15.5.1: each rare-spike law still has nonintegrable identity because the
heavy-tail component appears with positive weight. -/
private lemma rareSpikeLaw_notIntegrable (ν : ProbabilityMeasure ℝ)
    (hν : ¬ Integrable id (ν : Measure ℝ)) (n : ℕ) :
    ¬ Integrable id (rareSpikeLaw ν n) := by
  -- Proof comment: integrability for the sum measure would imply integrability for the positive
  -- scalar multiple of `ν`, and hence for `ν` itself.
  intro hInt
  have hsmul : Integrable id (ENNReal.ofReal (spikeWeightReal n) • (ν : Measure ℝ)) := by
    exact (integrable_add_measure.mp (by simpa [rareSpikeLaw] using hInt)).2
  have hweight_ne_zero : ENNReal.ofReal (spikeWeightReal n) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (spikeWeightReal_pos n)
  exact hν ((integrable_smul_measure hweight_ne_zero ENNReal.ofReal_ne_top).mp hsmul)

/-- Helper for Exercise 15.5.1: the rare-spike law has infinite absolute first moment. -/
private lemma rareSpikeLaw_lintegral_abs_eq_top (ν : ProbabilityMeasure ℝ)
    (hν : ¬ Integrable id (ν : Measure ℝ)) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |x| ∂rareSpikeLaw ν n = ⊤ := by
  -- Proof comment: this is the previous nonintegrability statement rewritten as a `lintegral`.
  exact
    lintegral_abs_eq_top_of_notIntegrable
      (hf := aestronglyMeasurable_id)
      (rareSpikeLaw_notIntegrable ν hν n)

/-- Helper for Exercise 15.5.1: if `Y` is integrable and `Z` has infinite absolute first moment,
then `Y + Z` also has infinite absolute first moment. -/
private lemma lintegral_abs_add_integrable_eq_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y Z : Ω → ℝ}
    (hY : Integrable Y P)
    (hZ_meas : AEStronglyMeasurable Z P)
    (hZ : ∫⁻ ω, ENNReal.ofReal |Z ω| ∂P = ⊤) :
    ∫⁻ ω, ENNReal.ofReal |Y ω + Z ω| ∂P = ⊤ := by
  -- Proof comment: otherwise `Y + Z` would be integrable, so subtracting the integrable `Y`
  -- would force `Z` to be integrable as well.
  by_contra htop
  have hHasFinite : HasFiniteIntegral (fun ω ↦ |Y ω + Z ω|) P := by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ abs_nonneg (Y ω + Z ω))]
    simpa [lt_top_iff_ne_top] using htop
  have hIntAbs : Integrable (fun ω ↦ |Y ω + Z ω|) P := by
    exact ⟨(hY.1.add hZ_meas).norm, hHasFinite⟩
  have hIntSum : Integrable (fun ω ↦ Y ω + Z ω) P := by
    exact
      (integrable_norm_iff (hY.1.add hZ_meas)).1
        (by simpa [Real.norm_eq_abs] using hIntAbs)
  have hIntZ : Integrable Z P := by
    convert hIntSum.sub hY using 1
    ext ω
    change Z ω = (Y ω + Z ω) - Y ω
    ring
  have hltZ : (∫⁻ ω, ENNReal.ofReal |Z ω| ∂P) < ⊤ := by
    rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ abs_nonneg (Z ω))]
    simpa [Real.norm_eq_abs] using hIntZ.norm.2
  have hZ_ne_top : ∫⁻ ω, ENNReal.ofReal |Z ω| ∂P ≠ ⊤ := ne_of_lt hltZ
  exact hZ_ne_top hZ

/-- Helper for Exercise 15.5.1: once a real sequence is eventually zero, its partial sums stabilize
after the last nonzero coordinate. -/
private lemma partialSumCoordinateProcess_eventually_constant
    (ω : ℕ → ℝ) (hω : ∀ᶠ n in atTop, ω n = 0) :
    ∃ N : ℕ, (fun n ↦ partialSum coordinateProcess n ω) =ᶠ[atTop]
      fun _ ↦ partialSum coordinateProcess N ω := by
  -- Proof comment: every tail block `Ico N n` vanishes once all later coordinates are zero.
  rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
  refine ⟨N, Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩⟩
  have htail :
      ∑ i ∈ Finset.Ico N n, coordinateProcess i ω = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    exact hN i (Finset.mem_Ico.1 hi).1
  have hdiff := partialSum_sub_eq_sum_Ico coordinateProcess hn ω
  have hEq : partialSum coordinateProcess n ω - partialSum coordinateProcess N ω = 0 := by
    simpa [htail] using hdiff
  exact sub_eq_zero.mp hEq

/-- Helper for Exercise 15.5.1: if a real sequence is eventually zero, then its `√n`-normalized
partial sums tend to `0`. -/
private lemma normalizedRarePart_tendsto_zero_ae
    (ω : ℕ → ℝ) (hω : ∀ᶠ n in atTop, ω n = 0) :
    Tendsto
      (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum coordinateProcess n ω)
      atTop (𝓝 0) := by
  -- Proof comment: the stabilized partial sum is a constant, and the prefactor `(√n)⁻¹` tends to
  -- `0`.
  rcases partialSumCoordinateProcess_eventually_constant ω hω with ⟨N, hN⟩
  let c : ℝ := partialSum coordinateProcess N ω
  have hinv :
      Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have hsqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt
  have hconst :
      Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * c) atTop (𝓝 0) := by
    simpa [c, zero_mul] using hinv.mul_const c
  have heq :
      (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum coordinateProcess n ω) =ᶠ[atTop]
        fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * c := by
    filter_upwards [hN] with n hn
    simp [c, hn]
  exact Tendsto.congr' heq.symm hconst

/-- Helper for Exercise 15.5.1: partial sums commute with pointwise addition. -/
private lemma partialSum_add
    {Ω : Type*} [MeasurableSpace Ω] (Y Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum (fun k ω' ↦ Y k ω' + Z k ω') n ω =
      partialSum Y n ω + partialSum Z n ω := by
  -- Proof comment: finite sums distribute over pointwise addition.
  simp [partialSum, Finset.sum_add_distrib]

-- Proof sketch: take a centered real law in the Gaussian domain of attraction with finite second
-- moment but infinite first absolute moment, realize an independent sequence with this law on an
-- infinite product probability space, and then apply the one-dimensional central limit theorem to
-- the raw `√n`-normalized partial sums built from the chapter owner `partialSum`.
/- Exercise 15.5.1 is `source-facing`: it asks for an independent sequence of measurable real
random variables with infinite first absolute moments whose raw `√n`-normalized partial sums
converge in distribution. The project owner for the finite sums themselves is `partialSum`, so the
statement reuses that owner directly instead of introducing a parallel public wrapper for the same
construction. -/
/-- Exercise 15.5.1: there exists an independent sequence `X₁, X₂, ...` of real random variables
such that every absolute first moment is infinite, but the normalized sums
`(X₁ + ⋯ + X_n) / √n` converge in distribution to the standard Gaussian law. In Lean's `0`-based
indexing, these are the maps `ω ↦ (√n)⁻¹ * partialSum X n ω`. -/
theorem exists_heavyTailStandardCLTExample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      (∀ n, Measurable (X n)) ∧
        iIndepFun X P ∧
        (∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂P = ⊤) ∧
        TendstoInDistribution
          (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum X n ω)
          atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
  -- Route correction: use a product-space witness with exact Gaussian coordinates for the CLT
  -- core and summably rare heavy-tail spikes for the infinite first moments.
  let ν : ProbabilityMeasure ℝ := unitIntervalInvLaw
  have hν_notInt : ¬ Integrable id (ν : Measure ℝ) := by
    simpa [ν] using unitIntervalInvLaw_notIntegrable
  let Ω : Type u := heavyTailCLTSpace
  letI : ∀ i : ULift.{u} ℕ, IsProbabilityMeasure (pairMarginalAt ν i) := fun i ↦
    pairMarginalIsProbability ν i.down
  let P : Measure Ω := Measure.infinitePi (pairMarginalAt ν)
  let Y : ℕ → Ω → ℝ := gaussianCoordinate
  let Z : ℕ → Ω → ℝ := spikeCoordinate
  let X : ℕ → Ω → ℝ := heavyTailSummand
  have hY_meas : ∀ n, Measurable (Y n) := by
    -- Proof comment: each Gaussian coordinate is a measurable evaluation map followed by `Prod.fst`.
    intro n
    simpa [Y, gaussianCoordinate, pairCoordinate] using
      (measurable_fst.comp (measurable_pi_apply (ULift.up n)))
  have hZ_meas : ∀ n, Measurable (Z n) := by
    -- Proof comment: each spike coordinate is a measurable evaluation map followed by `Prod.snd`.
    intro n
    simpa [Z, spikeCoordinate, pairCoordinate] using
      (measurable_snd.comp (measurable_pi_apply (ULift.up n)))
  have hX_meas : ∀ n, Measurable (X n) := by
    -- Proof comment: each witness summand is the sum of its measurable Gaussian and spike parts.
    intro n
    simpa [X, heavyTailSummand] using (hY_meas n).add (hZ_meas n)
  have hPairLaw : ∀ n, HasLaw (pairCoordinate n) (pairMarginal ν n) P := by
    -- Proof comment: each coordinate projection on the infinite product has the prescribed pair
    -- marginal law.
    intro n
    simpa [P, pairMarginalAt, pairMarginal, pairCoordinate] using
      (MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi (pairMarginalAt ν) (ULift.up n)) :
        HasLaw (Function.eval (ULift.up n)) (pairMarginalAt ν (ULift.up n)) P)
  have hY_law : ∀ n, HasLaw (Y n) (gaussianReal 0 1) P := by
    -- Proof comment: compose the pair-coordinate law with the first projection of the product
    -- measure.
    intro n
    letI : IsProbabilityMeasure (rareSpikeLaw ν n) := rareSpikeLawIsProbability ν n
    have hfst :
        HasLaw Prod.fst (gaussianReal 0 1) (pairMarginal ν n) :=
      (measurePreserving_fst (μ := gaussianReal 0 1) (ν := rareSpikeLaw ν n)).hasLaw
    simpa [Y, gaussianCoordinate, pairCoordinate, Function.comp, pairMarginal] using
      (HasLaw.comp hfst (hPairLaw n))
  have hZ_law : ∀ n, HasLaw (Z n) (rareSpikeLaw ν n) P := by
    -- Proof comment: compose the pair-coordinate law with the second projection of the product
    -- measure.
    intro n
    letI : IsProbabilityMeasure (rareSpikeLaw ν n) := rareSpikeLawIsProbability ν n
    have hsnd :
        HasLaw Prod.snd (rareSpikeLaw ν n) (pairMarginal ν n) :=
      (measurePreserving_snd (μ := gaussianReal 0 1) (ν := rareSpikeLaw ν n)).hasLaw
    simpa [Z, spikeCoordinate, pairCoordinate, Function.comp, pairMarginal] using
      (HasLaw.comp hsnd (hPairLaw n))
  have hPair_indep : iIndepFun pairCoordinate P := by
    -- Proof comment: independence is the standard infinite-product independence of the coordinate
    -- projections.
    let hProd :
        iIndepFun (fun i : ULift.{u} ℕ ↦ fun ω : Ω ↦ ω i) P :=
      iIndepFun_infinitePi (P := pairMarginalAt ν) (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
    simpa [P, pairCoordinate] using hProd.precomp ULift.up_injective
  have hY_indep : iIndepFun Y P := by
    -- Proof comment: measurable postcomposition by `Prod.fst` preserves independence.
    simpa [Y, gaussianCoordinate, pairCoordinate] using
      hPair_indep.comp (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst)
  have hX_indep : iIndepFun X P := by
    -- Proof comment: the final summands come from the coordinatewise measurable map
    -- `(a, b) ↦ a + b`.
    simpa [X, heavyTailSummand, pairCoordinate] using
      hPair_indep.comp (fun _ z ↦ z.1 + z.2) (fun _ ↦ measurable_fst.add measurable_snd)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    -- Proof comment: every Gaussian core coordinate has the same standard Gaussian law.
    intro n
    exact (hY_law n).identDistrib (hY_law 0)
  have hY_int : ∀ n, Integrable (Y n) P := by
    -- Proof comment: standard Gaussian coordinates lie in `L²`, hence in `L¹` on a probability
    -- space.
    intro n
    exact ((hY_law n).hasGaussianLaw.memLp_two).integrable (by norm_num)
  have hX_abs_top : ∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂P = ⊤ := by
    -- Proof comment: each spike coordinate already has infinite absolute first moment, and adding
    -- the integrable Gaussian core cannot restore integrability.
    intro n
    have hZ_top : ∫⁻ ω, ENNReal.ofReal |Z n ω| ∂P = ⊤ := by
      have hZ_ident : IdentDistrib (Z n) id P (rareSpikeLaw ν n) :=
        (hZ_law n).identDistrib HasLaw.id
      have hZ_notInt : ¬ Integrable (Z n) P := by
        intro hInt
        exact rareSpikeLaw_notIntegrable ν hν_notInt n ((hZ_ident.integrable_iff).mp hInt)
      exact
        lintegral_abs_eq_top_of_notIntegrable
          (hf := (hZ_meas n).aestronglyMeasurable)
          hZ_notInt
    simpa [X, heavyTailSummand] using
      lintegral_abs_add_integrable_eq_top
        (hY_int n)
        ((hZ_meas n).aestronglyMeasurable)
        hZ_top
  let A : ℕ → Set Ω := fun n ↦ {ω | Z n ω ≠ 0}
  have hA_prob_le : ∀ n, P (A n) ≤ ENNReal.ofReal (spikeWeightReal n) := by
    -- Proof comment: rewrite the event probability through the spike-coordinate law and apply the
    -- rare-spike mass bound.
    intro n
    calc
      P (A n) = (Measure.map (Z n) P) {x : ℝ | x ≠ 0} := by
        rw [show A n = (Z n) ⁻¹' {x : ℝ | x ≠ 0} by
          ext ω
          simp [A]]
        exact (Measure.map_apply (hZ_meas n) ((measurableSet_singleton (0 : ℝ)).compl)).symm
      _ = rareSpikeLaw ν n {x : ℝ | x ≠ 0} := by
        simpa using congrArg (fun μ : Measure ℝ => μ {x : ℝ | x ≠ 0}) (hZ_law n).map_eq
      _ ≤ ENNReal.ofReal (spikeWeightReal n) := rareSpikeLaw_nonzero_event_le_weight ν n
  have hweight_tsum_ne_top : (∑' n, ENNReal.ofReal (spikeWeightReal n)) ≠ ⊤ := by
    -- Proof comment: the comparison series is summable because `∑ (n + 1)⁻² < ∞`.
    exact ne_of_lt summable_spikeWeightReal.tsum_ofReal_lt_top
  have hA_tsum_ne_top : (∑' n, P (A n)) ≠ ⊤ := by
    -- Proof comment: the event probabilities are bounded termwise by the summable spike weights.
    refine ne_top_of_le_ne_top hweight_tsum_ne_top ?_
    exact ENNReal.tsum_le_tsum hA_prob_le
  have hAe_eventually_zero : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Z n ω = 0 := by
    -- Proof comment: first Borel-Cantelli says only finitely many rare spikes occur almost surely.
    filter_upwards
      [MeasureTheory.ae_eventually_notMem (μ := P) (s := A) hA_tsum_ne_top] with ω hω
    filter_upwards [hω] with n hn
    simpa [A] using hn
  have hRare_ae :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Z n ω) atTop (𝓝 0) := by
    -- Proof comment: once the spike coordinates vanish eventually, the normalized spike partial
    -- sums are eventually a constant divided by `√n`.
    filter_upwards [hAe_eventually_zero] with ω hω
    simpa [Z, spikeCoordinate, pairCoordinate, partialSum, coordinateProcess] using
      normalizedRarePart_tendsto_zero_ae (fun k ↦ Z k ω) hω
  have hRare_tendsto :
      TendstoInMeasure P
        (fun n : ℕ => fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Z n ω)
        atTop (fun _ ↦ (0 : ℝ)) := by
    -- Proof comment: almost-sure convergence implies convergence in measure on a probability
    -- space.
    refine tendstoInMeasure_of_tendsto_ae ?_ hRare_ae
    intro n
    exact ((partialSum_measurable Z hZ_meas n).const_mul _).aestronglyMeasurable
  have hY_mean_zero : P[Y 0] = 0 := by
    -- Proof comment: transport the standard Gaussian mean through the coordinate law.
    rw [(hY_law 0).integral_eq]
    simp
  have hY_second : P[(Y 0) ^ (2 : ℕ)] = 1 := by
    -- Proof comment: for a centered variable, the second moment equals the variance.
    have hY_var : Var[Y 0; P] = 1 := by
      rw [(hY_law 0).variance_eq]
      simpa using (variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    calc
      P[(Y 0) ^ (2 : ℕ)] = Var[Y 0; P] := by
        symm
        rw [variance_eq_integral (hY_meas 0).aemeasurable, hY_mean_zero]
        simp
      _ = 1 := hY_var
  have hCore :
      TendstoInDistribution
        (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum Y n ω)
        atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    -- Proof comment: the Gaussian core already satisfies the exact classical CLT hypotheses.
    simpa [Y, partialSum] using
      (tendstoInDistribution_inv_sqrt_mul_sum
        (P := P) (P' := gaussianReal 0 1) (X := Y) (Y := id)
        HasLaw.id hY_mean_zero hY_second hY_indep hY_ident)
  have hFinal :
      TendstoInDistribution
        (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum X n ω)
        atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    -- Proof comment: the total normalized sum is the Gaussian core plus a perturbation that
    -- vanishes in measure, so Slutsky finishes the argument.
    change
      TendstoInDistribution
        (fun (n : ℕ) ω ↦
          (Real.sqrt (n : ℝ))⁻¹ * partialSum (fun k ω' ↦ Y k ω' + Z k ω') n ω)
        atTop id (fun _ ↦ P) (gaussianReal 0 1)
    simpa [partialSum_add, mul_add, zero_add] using
      hCore.add_of_tendstoInMeasure_const
        hRare_tendsto
        (fun n ↦ ((partialSum_measurable Z hZ_meas n).const_mul _).aemeasurable)
  exact ⟨Ω, inferInstance, P, inferInstance, X, hX_meas, hX_indep, hX_abs_top, hFinal⟩
