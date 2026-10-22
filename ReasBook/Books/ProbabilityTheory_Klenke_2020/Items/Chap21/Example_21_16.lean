/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_15

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

/-- Helper for Example 21.16: the strictly positive first hitting time `τ_[X, A]` of `A` by `X`,
with value `⊤` when the path never enters `A` after time `0`. -/
private def strictHittingTime (X : NNReal → Ω → ℝ) (A : Set ℝ) : Ω → WithTop NNReal :=
  fun ω ↦
    if _ : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A then
      ((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal)
    else ⊤

scoped notation:arg "τ_[" X ", " A "]" => strictHittingTime X A

omit [MeasurableSpace Ω] in
/-- Helper for Example 21.16: the strictly positive hitting time is infinite exactly when the path
avoids the target set at every positive time. -/
private theorem strictHittingTime_eq_top_iff
    (X : NNReal → Ω → ℝ) (A : Set ℝ) (ω : Ω) :
    (τ_[X, A]) ω = ⊤ ↔ ∀ t : NNReal, 0 < t → X t ω ∉ A := by
  -- Proof comment: unfold the `if`; the `⊤` branch is exactly the failure of any positive hit.
  by_cases h : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A
  · rcases h with ⟨t, ht, hA⟩
    have h' : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A := ⟨t, ht, hA⟩
    constructor
    · intro hEq
      have hne :
          (((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ := by
        simpa using
          (show (((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ from
            WithTop.coe_ne_top)
      exact False.elim <| hne <| by simpa [strictHittingTime, h'] using hEq
    · intro hAvoid
      exact False.elim (hAvoid t ht hA)
  · constructor
    · intro _ t ht hA
      exact h ⟨t, ht, hA⟩
    · intro _
      simp [strictHittingTime, h]

private def sqrtBoundaryGapProcess (B : NNReal → Ω → ℝ) (K : ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ B t ω - K * Real.sqrt (t : ℝ)

/-- Helper for Example 21.16: the dyadic time grid `2^{-n}` used to probe the Brownian path near
`0`. -/
private def dyadicTime (n : ℕ) : NNReal :=
  ((2 : NNReal)⁻¹) ^ n

omit [MeasurableSpace Ω] in
/-- Helper for Example 21.16: if a path hits a target set before every dyadic time, then its
strictly positive first hitting time is `0`. -/
private lemma strictHittingTime_eq_zero_of_hits_every_dyadic
    {X : NNReal → Ω → ℝ} {A : Set ℝ} {ω : Ω}
    (hhit : ∀ n : ℕ, ∃ t : NNReal, 0 < t ∧ t ≤ dyadicTime n ∧ X t ω ∈ A) :
    (τ_[X, A]) ω = 0 := by
  let S : Set NNReal := {t : NNReal | 0 < t ∧ X t ω ∈ A}
  have hτ_ne_top : (τ_[X, A]) ω ≠ ⊤ := by
    rcases hhit 0 with ⟨t, ht0, -, ht_mem⟩
    exact fun htop ↦ (strictHittingTime_eq_top_iff X A ω).1 htop t ht0 ht_mem
  rcases WithTop.ne_top_iff_exists.mp hτ_ne_top with ⟨τ, hτ_eq⟩
  have hτ_le : ∀ n : ℕ, τ ≤ dyadicTime n := by
    intro n
    rcases hhit n with ⟨t, ht0, ht_le, ht_mem⟩
    have hle_t : (τ_[X, A]) ω ≤ (t : WithTop NNReal) := by
      by_cases hex : ∃ s : NNReal, 0 < s ∧ X s ω ∈ A
      · have hBddBelow : BddBelow S := by
          refine ⟨0, fun s hs ↦ hs.1.le⟩
        have hsInf_le : sInf S ≤ t := by
          exact csInf_le hBddBelow (show t ∈ S from ⟨ht0, ht_mem⟩)
        have hsInf_le_top :
            (((sInf S : NNReal) : WithTop NNReal)) ≤ (t : WithTop NNReal) := by
          exact_mod_cast hsInf_le
        simpa [strictHittingTime, S, hex] using hsInf_le_top
      · exact False.elim (hex ⟨t, ht0, ht_mem⟩)
    have hle_t' : (τ : WithTop NNReal) ≤ (t : WithTop NNReal) := by
      simpa [hτ_eq] using hle_t
    exact WithTop.coe_le_coe.mp <|
      le_trans hle_t' (show (t : WithTop NNReal) ≤ (dyadicTime n : WithTop NNReal) from by
        exact_mod_cast ht_le)
  by_cases hτ0 : τ = 0
  · simpa [hτ0] using hτ_eq.symm
  · have hτ_ne_zero : (τ : ENNReal) ≠ 0 := by
      exact_mod_cast hτ0
    rcases ENNReal.exists_inv_two_pow_lt (a := (τ : ENNReal)) hτ_ne_zero with ⟨n, hn⟩
    have hdyadic_lt : dyadicTime n < τ := by
      exact ENNReal.coe_lt_coe.mp (by simpa [dyadicTime, ← inv_pow] using hn)
    exact False.elim ((not_lt_of_ge (hτ_le n)) hdyadic_lt)

/-- Helper for Example 21.16: the dyadic time grid decreases with `n`. -/
private lemma dyadicTime_antitone : Antitone dyadicTime := by
  -- Proof comment: powers of a number in `[0, 1]` decrease when the exponent increases.
  intro n m hnm
  dsimp [dyadicTime]
  rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
  calc
    ((2 : NNReal)⁻¹) ^ (n + k) = ((2 : NNReal)⁻¹) ^ n * ((2 : NNReal)⁻¹) ^ k := by
      rw [pow_add]
    _ ≤ ((2 : NNReal)⁻¹) ^ n * 1 := by
      gcongr
      exact pow_le_one₀ (by positivity) (by norm_num)
    _ = ((2 : NNReal)⁻¹) ^ n := by simp

/-- Helper for Example 21.16: the rational event that the gap process is strictly positive at
some rational time before the dyadic horizon `2^{-n}`. -/
private def positiveDyadicHitEvent
    (B : NNReal → Ω → ℝ) (K : ℝ) (n : ℕ) : Set Ω :=
  ⋃ q : {q : ℚ≥0 // 0 < (q : NNReal) ∧ (q : NNReal) ≤ dyadicTime n},
    {ω | K * Real.sqrt (q.1 : ℝ) < B (q.1 : NNReal) ω}

/-- Helper for Example 21.16: each dyadic rational-hit event is measurable in the Brownian natural
filtration at time `dyadicTime n`. -/
private lemma measurableSet_positiveDyadicHitEvent
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ)
    (n : ℕ) :
    MeasurableSet[(Filtration.natural B hB.stronglyMeasurable) (dyadicTime n)]
      (positiveDyadicHitEvent B K n) := by
  -- Proof comment: each witness event depends on a single Brownian coordinate with time at most
  -- `dyadicTime n`, so it is measurable in the natural filtration at that stage.
  let ℱ := Filtration.natural B hB.stronglyMeasurable
  let hStronglyAdapted :=
    Filtration.stronglyAdapted_natural (u := B) (hum := hB.stronglyMeasurable)
  refine MeasurableSet.iUnion fun q ↦ ?_
  have hq_le : (q.1 : NNReal) ≤ dyadicTime n := q.2.2
  have hmeas :
      Measurable[(ℱ (dyadicTime n))] (B (q.1 : NNReal)) :=
    ((hStronglyAdapted (q.1 : NNReal)).mono <|
      ℱ.mono hq_le).measurable
  change
    MeasurableSet[(ℱ (dyadicTime n))] ((B (q.1 : NNReal)) ⁻¹' Set.Ioi (K * Real.sqrt (q.1 : ℝ)))
  exact hmeas measurableSet_Ioi

omit [MeasurableSpace Ω] in
/-- Helper for Example 21.16: shrinking the dyadic horizon can only remove rational hit
witnesses. -/
private lemma positiveDyadicHitEvent_antitone
    {B : NNReal → Ω → ℝ} (K : ℝ) :
    Antitone (positiveDyadicHitEvent B K) := by
  -- Proof comment: any rational witness below `2^{-m}` is automatically below `2^{-n}` whenever
  -- `n ≤ m`.
  intro n m hnm ω hω
  rcases Set.mem_iUnion.mp hω with ⟨q, hq⟩
  have hq_mem : 0 < (q.1 : NNReal) ∧ (q.1 : NNReal) ≤ dyadicTime n := by
    refine ⟨q.2.1, le_trans q.2.2 (dyadicTime_antitone hnm)⟩
  exact Set.mem_iUnion.mpr ⟨⟨q.1, hq_mem⟩, hq⟩

/-- Helper for Example 21.16: the initial Brownian right-limit σ-algebra can be computed along the
dyadic times `2^{-n}`. -/
private lemma brownianInitialSigma_eq_iInfDyadicStagesLocal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    Filtration.rightCont (Filtration.natural B hB.stronglyMeasurable) 0 =
      ⨅ n : ℕ, (Filtration.natural B hB.stronglyMeasurable) (dyadicTime n) := by
  -- Proof comment: reuse the established dyadic description of the Brownian initial σ-algebra.
  simpa using brownianInitialSigma_eq_iInf_dyadicStages (hB := hB)

/-- Helper for Example 21.16: the tail intersection of the dyadic rational-hit events is
measurable in the Brownian initial right-limit σ-algebra. -/
private lemma iInter_positiveDyadicHitEvent_mem_brownianInitialSigma
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) :
    MeasurableSet[
      Filtration.rightCont (Filtration.natural B hB.stronglyMeasurable) 0]
      (⋂ n : ℕ, positiveDyadicHitEvent B K n) := by
  let ℱ := Filtration.natural B hB.stronglyMeasurable
  have htail :
      ∀ n : ℕ,
        (⋂ m : ℕ, positiveDyadicHitEvent B K (n + m)) =
          ⋂ m : ℕ, positiveDyadicHitEvent B K m := by
    intro n
    ext ω
    constructor
    · intro hω
      refine Set.mem_iInter.mpr fun m ↦ ?_
      by_cases hnm : n ≤ m
      · rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
        exact Set.mem_iInter.mp hω k
      · have hm_le_n : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnm)
        have hn_mem : ω ∈ positiveDyadicHitEvent B K n := (Set.mem_iInter.mp hω) 0
        exact (positiveDyadicHitEvent_antitone (B := B) K hm_le_n) hn_mem
    · intro hω
      exact Set.mem_iInter.mpr fun m ↦ (Set.mem_iInter.mp hω) (n + m)
  -- Proof comment: rewrite the initial σ-algebra as the infimum over dyadic stages and show that
  -- the tail event is measurable in every stage using the antitone dyadic family.
  rw [brownianInitialSigma_eq_iInfDyadicStagesLocal (hB := hB),
    MeasurableSpace.measurableSet_iInf]
  intro n
  rw [← htail n]
  exact MeasurableSet.iInter fun m ↦
    ℱ.mono (dyadicTime_antitone <| Nat.le_add_right n m) _
      (measurableSet_positiveDyadicHitEvent hB K (n + m))

/-- Helper for Example 21.16: the standard Gaussian upper tail above any real threshold has
strictly positive mass. -/
private lemma standardGaussianUpperTail_pos (K : ℝ) :
    0 < (gaussianReal 0 1) (Set.Ioi K) := by
  -- Proof comment: the nonempty interval `(K, K + 1)` lies inside `Set.Ioi K`, and Gaussian
  -- measure is absolutely continuous with respect to Lebesgue measure.
  have hgauss_ne : gaussianReal 0 1 (Set.Ioi K) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo K (K + 1)) = 0 := by
      exact measure_mono_null (by
        intro x hx
        exact hx.1) (gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero)
    have hvol_pos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Ioo K (K + 1)) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol_pos.ne' hvol_zero
  exact pos_iff_ne_zero.mpr hgauss_ne

/-- Helper for Example 21.16: the dyadic endpoint `(1 / 2)^n` written as a nonnegative rational. -/
private def dyadicRatTime (n : ℕ) : ℚ≥0 :=
  ((2 : ℚ≥0)⁻¹) ^ n

/-- Helper for Example 21.16: the rational dyadic endpoint agrees with the `NNReal` dyadic time
after coercion. -/
private lemma dyadicRatTime_coe (n : ℕ) :
    ((dyadicRatTime n : ℚ≥0) : NNReal) = dyadicTime n := by
  apply NNReal.coe_injective
  simp [dyadicRatTime, dyadicTime, inv_pow]

omit [MeasurableSpace Ω] in
/-- Helper for Example 21.16: an endpoint exceedance at the dyadic time already belongs to the
corresponding rational-hit event. -/
private lemma endpointExceedance_subset_positiveDyadicHitEvent
    {B : NNReal → Ω → ℝ} (K : ℝ) (n : ℕ) :
    {ω | K * Real.sqrt (dyadicTime n : ℝ) < B (dyadicTime n) ω} ⊆
      positiveDyadicHitEvent B K n := by
  intro ω hω
  let q : ℚ≥0 := dyadicRatTime n
  have hq_eq : (q : NNReal) = dyadicTime n := by
    simpa [q] using dyadicRatTime_coe n
  have hq_eq_real : (q : ℝ) = (dyadicTime n : ℝ) := by
    change ((q : NNReal) : ℝ) = (dyadicTime n : ℝ)
    exact_mod_cast hq_eq
  have hq_mem : 0 < (q : NNReal) ∧ (q : NNReal) ≤ dyadicTime n := by
    constructor
    · have hq_pos : 0 < q := by
        dsimp [q, dyadicRatTime]
        positivity
      exact_mod_cast hq_pos
    · exact hq_eq.le
  refine Set.mem_iUnion.mpr ⟨⟨q, hq_mem⟩, ?_⟩
  simpa [hq_eq, hq_eq_real] using hω

/-- Helper for Example 21.16: the Brownian one-time exceedance at the dyadic horizon has the same
probability as the standard Gaussian upper tail above `K`. -/
private lemma dyadicEndpointExceedance_prob_eq_standardGaussianTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) (n : ℕ) :
    μ {ω | K * Real.sqrt (dyadicTime n : ℝ) < B (dyadicTime n) ω} =
      (gaussianReal 0 1) (Set.Ioi K) := by
  let t : NNReal := dyadicTime n
  have ht_pos : 0 < t := by
    dsimp [t, dyadicTime]
    positivity
  have hBt : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
  have hBtmeas : Measurable (B t) := (hB.stronglyMeasurable t).measurable
  have hsqrt_pos : 0 < Real.sqrt (t : ℝ) := by
    exact Real.sqrt_pos.2 (show 0 < (t : ℝ) by exact_mod_cast ht_pos)
  have hscale_meas : Measurable (fun x : ℝ ↦ Real.sqrt (t : ℝ) * x) := by
    fun_prop
  have hgauss_map :
      (gaussianReal 0 1).map (fun x : ℝ ↦ Real.sqrt (t : ℝ) * x) = gaussianReal 0 t := by
    simpa [Real.sq_sqrt, ht_pos.le] using
      (gaussianReal_map_const_mul
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (c := Real.sqrt (t : ℝ)))
  have htail_eq :
      μ {ω | K * Real.sqrt (t : ℝ) < B t ω} =
        (gaussianReal 0 t) (Set.Ioi (K * Real.sqrt (t : ℝ))) := by
    have hmap_eq := congrArg (fun ν : Measure ℝ => ν (Set.Ioi (K * Real.sqrt (t : ℝ)))) hBt.map_eq
    simpa [Measure.map_apply hBtmeas measurableSet_Ioi] using hmap_eq
  have hscaled_tail :
      ((gaussianReal 0 1).map (fun x : ℝ ↦ Real.sqrt (t : ℝ) * x))
          (Set.Ioi (K * Real.sqrt (t : ℝ))) =
        (gaussianReal 0 1) ((fun x : ℝ ↦ Real.sqrt (t : ℝ) * x) ⁻¹' Set.Ioi
          (K * Real.sqrt (t : ℝ))) := by
    rw [Measure.map_apply hscale_meas measurableSet_Ioi]
  have hratio : (K * Real.sqrt (t : ℝ)) / Real.sqrt (t : ℝ) = K := by
    rw [mul_comm, mul_div_cancel_left₀]
    exact hsqrt_pos.ne'
  -- Proof comment: push the one-time Brownian tail through the Gaussian marginal and the
  -- deterministic scaling map `x ↦ √t x`.
  calc
    μ {ω | K * Real.sqrt (dyadicTime n : ℝ) < B (dyadicTime n) ω}
        = μ {ω | K * Real.sqrt (t : ℝ) < B t ω} := by
            simp [t]
    _ = (gaussianReal 0 t) (Set.Ioi (K * Real.sqrt (t : ℝ))) := htail_eq
    _ = (gaussianReal 0 1).map (fun x : ℝ ↦ Real.sqrt (t : ℝ) * x)
          (Set.Ioi (K * Real.sqrt (t : ℝ))) := by
            rw [hgauss_map]
    _ = (gaussianReal 0 1) ((fun x : ℝ ↦ Real.sqrt (t : ℝ) * x) ⁻¹'
          Set.Ioi (K * Real.sqrt (t : ℝ))) := hscaled_tail
    _ = (gaussianReal 0 1) (Set.Ioi K) := by
          rw [Set.preimage_const_mul_Ioi₀ (K * Real.sqrt (t : ℝ)) hsqrt_pos, hratio]

/-- Helper for Example 21.16: every dyadic rational-hit event has probability at least the
standard Gaussian upper tail above `K`. -/
private lemma positiveDyadicHitEvent_prob_ge_standardGaussianTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) (n : ℕ) :
    (gaussianReal 0 1) (Set.Ioi K) ≤ μ (positiveDyadicHitEvent B K n) := by
  calc
    (gaussianReal 0 1) (Set.Ioi K) =
        μ {ω | K * Real.sqrt (dyadicTime n : ℝ) < B (dyadicTime n) ω} := by
          rw [dyadicEndpointExceedance_prob_eq_standardGaussianTail hB K n]
    _ ≤ μ (positiveDyadicHitEvent B K n) := by
      exact measure_mono (endpointExceedance_subset_positiveDyadicHitEvent (B := B) K n)

-- Proof sketch: consider the tail event that for every dyadic horizon `2^{-n}` there is already a
-- rational time `q ≤ 2^{-n}` with `B q > K * sqrt q`. This event belongs to the Brownian initial
-- right-limit σ-algebra, so Blumenthal's `0`-`1` law applies; and each dyadic stage has
-- probability at least the fixed positive Gaussian tail above `K`, so the tail event itself has
-- positive probability. On that event, the strictly positive hitting time of `[0, ∞)` is forced
-- to be `0`.
/-- Example 21.16: for Brownian motion `B` and every `K`, the first strictly positive time at
which `B t ≥ K * sqrt t` is almost surely equal to `0`. Equivalently,
`inf {t > 0 : K * sqrt t ≤ B t} = 0` almost surely. -/
theorem brownianSqrtBoundaryHittingTime_ae_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) :
    ∀ᵐ ω ∂μ,
      (τ_[(sqrtBoundaryGapProcess B K), Set.Ici (0 : ℝ)]) ω = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ℱ := Filtration.natural B hB.stronglyMeasurable
  let E : Set Ω := ⋂ n : ℕ, positiveDyadicHitEvent B K n
  have hstage_meas : ∀ n : ℕ, MeasurableSet (positiveDyadicHitEvent B K n) := by
    intro n
    refine MeasurableSet.iUnion fun q ↦ ?_
    change MeasurableSet ((B (q.1 : NNReal)) ⁻¹' Set.Ioi (K * Real.sqrt (q.1 : ℝ)))
    exact (hB.stronglyMeasurable (q.1 : NNReal)).measurable measurableSet_Ioi
  have hE_meas :
      MeasurableSet[Filtration.rightCont ℱ 0] E := by
    simpa [E] using iInter_positiveDyadicHitEvent_mem_brownianInitialSigma (hB := hB) K
  have hE_eq_iInf : μ E = ⨅ n : ℕ, μ (positiveDyadicHitEvent B K n) := by
    simpa [E] using
      (positiveDyadicHitEvent_antitone (B := B) K).measure_iInter
        (fun n ↦ (hstage_meas n).nullMeasurableSet) ⟨0, measure_ne_top μ _⟩
  have hE_ge :
      (gaussianReal 0 1) (Set.Ioi K) ≤ μ E := by
    rw [hE_eq_iInf]
    exact le_iInf fun n ↦ positiveDyadicHitEvent_prob_ge_standardGaussianTail hB K n
  have hE_pos : 0 < μ E := by
    exact lt_of_lt_of_le (standardGaussianUpperTail_pos K) hE_ge
  have hE_one : μ E = 1 := by
    rcases measure_zero_or_one_of_mem_brownian_initial_sigma_algebra (hB := hB) hE_meas with
      hE_zero | hE_one
    · exact False.elim <| (ne_of_gt hE_pos) hE_zero
    · exact hE_one
  have hE_ae : ∀ᵐ ω ∂μ, ω ∈ E := by
    have hE_meas_ambient : MeasurableSet E := by
      simpa [E] using MeasurableSet.iInter hstage_meas
    exact (mem_ae_iff_prob_eq_one hE_meas_ambient).2 hE_one
  filter_upwards [hE_ae] with ω hω
  have hω' : ω ∈ ⋂ n : ℕ, positiveDyadicHitEvent B K n := by
    simpa [E] using hω
  -- Proof comment: every dyadic-stage witness on `E` gives a positive time with
  -- `B t - K * sqrt t ≥ 0`, so the strictly positive hitting time is forced to be `0`.
  refine strictHittingTime_eq_zero_of_hits_every_dyadic
    (X := sqrtBoundaryGapProcess B K) (A := Set.Ici (0 : ℝ)) (ω := ω) ?_
  intro n
  rcases Set.mem_iUnion.mp (Set.mem_iInter.mp hω' n) with ⟨q, hq⟩
  change K * Real.sqrt (q.1 : ℝ) < B (q.1 : NNReal) ω at hq
  refine ⟨(q.1 : NNReal), q.2.1, q.2.2, ?_⟩
  · have hq_nonneg : 0 ≤ (q.1 : ℝ) := by exact_mod_cast q.1.2
    have hgap_nonneg :
        0 ≤ sqrtBoundaryGapProcess B K (q.1 : NNReal) ω := by
      dsimp [sqrtBoundaryGapProcess]
      rw [show (((q.1 : NNReal) : ℝ)) = q.1 by rfl]
      linarith
    simpa [Set.mem_Ici] using hgap_nonneg

end ProbabilityTheory
