/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Corollary_22_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

namespace ProbabilityTheory

/-- Helper for Theorem 22.11: reuse the coarse-mesh lower-mass lemma from Theorem 22.1. -/

syntax "theorem22_1LowerMass" : term

elab_rules : term
  | `(theorem22_1LowerMass) =>
      mkConstWithFreshMVarLevels
        "_private.Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_1.0.\
ProbabilityTheory.IsBrownianMotion.eventually_invSucc_le_measureReal_geometricIncrementEvent".toName

variable {Ω : Type u} [MeasurableSpace Ω]
section HartmanWintner

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)

local notation "S" => partialSum (fun k ↦ X (k + 1))

/- Theorem 22.11 is `source-facing`: its primitive data are the iid textbook-indexed increments
`X₁, X₂, …`, expressed through the chapter owner `partialSum` for the associated random walk. The
`core/canonical` owner on the comparison side is the Brownian-motion law of the iterated logarithm
`IsBrownianMotion.ae_limsup_div_sqrt_two_mul_t_log_log_eq_one`, while Corollary 22.7 supplies the
`bridge/view` from the iid partial-sum process to a stopped Brownian motion. -/

/-- Helper for Theorem 22.11: the discrete limsup functional on path space `ℕ → ℝ` is measurable.
-/
private theorem measurable_embeddedSequenceLimsup :
    Measurable
      (fun u : ℕ → ℝ ↦
        limsup
          (fun n ↦
            u (n + 1) /
              Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
          atTop) := by
  -- Proof comment: each normalized coordinate map is measurable on the product space, so the
  -- packaged `Measurable.limsup` theorem applies directly to the tail `limsup`.
  refine Measurable.limsup fun n ↦ ?_
  exact (measurable_pi_apply (n + 1)).div_const _

/-- Helper for Theorem 22.11: the real-valued embedding increments telescope back to the stopping
times. -/
private theorem embeddingTime_incrementSum_eq
    {space : Type u} [MeasurableSpace space]
    (stoppingTime : ℕ → space → NNReal)
    (hτ0 : stoppingTime 0 = 0)
    (hτmono : Monotone stoppingTime) :
    ∀ n ω,
      (∑ i ∈ Finset.range n, ((stoppingTime (i + 1) ω - stoppingTime i ω : NNReal) : ℝ)) =
        (stoppingTime n ω : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro ω
      -- Proof comment: both the empty increment sum and the initial stopping time are `0`.
      simp [hτ0]
  | succ n ih =>
      intro ω
      -- Proof comment: append the next increment and then collapse the resulting `tsub` by
      -- monotonicity of the stopping times.
      calc
        (∑ i ∈ Finset.range (n + 1),
            ((stoppingTime (i + 1) ω - stoppingTime i ω : NNReal) : ℝ)) =
            (∑ i ∈ Finset.range n,
                ((stoppingTime (i + 1) ω - stoppingTime i ω : NNReal) : ℝ)) +
              ((stoppingTime (n + 1) ω - stoppingTime n ω : NNReal) : ℝ) := by
                rw [Finset.sum_range_succ]
        _ = (stoppingTime n ω : ℝ) +
              ((stoppingTime (n + 1) ω - stoppingTime n ω : NNReal) : ℝ) := by
                rw [ih ω]
        _ = (stoppingTime (n + 1) ω : ℝ) := by
                have hle : stoppingTime n ω ≤ stoppingTime (n + 1) ω :=
                  (show stoppingTime n ≤ stoppingTime (n + 1) from hτmono (Nat.le_succ n)) ω
                simpa [add_comm] using
                  congrArg (fun x : NNReal ↦ (x : ℝ)) (tsub_add_cancel_of_le hle)

/-- Helper for Theorem 22.11: the iid embedding increments satisfy the strong law, so the
embedded stopping times obey `(stoppingTime (n + 1)) / (n + 1) → 1` almost surely.
-/
private theorem ae_tendsto_embeddingTime_div_nat_one
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space)
    (stoppingTime : ℕ → space → NNReal)
    (hτ0 : stoppingTime 0 = 0)
    (hτmono : Monotone stoppingTime)
    (hτIID :
      IsIID (fun n ω ↦ stoppingTime (n + 1) ω - stoppingTime n ω) (law : Measure space))
    (hτmean : ∫ ω, (stoppingTime 1 ω : ℝ) ∂(law : Measure space) = 1) :
    ∀ᵐ ω ∂(law : Measure space),
      Tendsto (fun n : ℕ ↦ (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ)) atTop (nhds 1) := by
  let Δ : ℕ → space → ℝ :=
    fun n ω ↦ ((stoppingTime (n + 1) ω - stoppingTime n ω : NNReal) : ℝ)
  have hΔ_iid : IsIID Δ (law : Measure space) := by
    refine ⟨hτIID.iIndepFun.comp (fun _ ↦ fun x : NNReal ↦ (x : ℝ)) ?_, ?_⟩
    · intro n
      exact measurable_coe_nnreal_real
    · intro i j
      simpa [Δ] using (hτIID.identDistrib i j).comp measurable_coe_nnreal_real
  have hΔ0_aestrong : AEStronglyMeasurable (Δ 0) (law : Measure space) := by
    simpa [Δ, hτ0] using (hΔ_iid.identDistrib 0 0).aemeasurable_fst.aestronglyMeasurable
  have hΔ0_nonneg : 0 ≤ᵐ[(law : Measure space)] Δ 0 := by
    filter_upwards with ω
    positivity
  have hΔ0_integrable : Integrable (Δ 0) (law : Measure space) := by
    refine ⟨hΔ0_aestrong, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hΔ0_nonneg]
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have htoReal :
        ENNReal.toReal
            (∫⁻ ω, ENNReal.ofReal (Δ 0 ω) ∂(law : Measure space)) = 1 := by
      calc
        ENNReal.toReal
            (∫⁻ ω, ENNReal.ofReal (Δ 0 ω) ∂(law : Measure space)) =
            ∫ ω, Δ 0 ω ∂(law : Measure space) := by
              symm
              exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hΔ0_nonneg hΔ0_aestrong
        _ = 1 := by
              simpa [Δ, hτ0] using hτmean
    have : False := by
      simpa [htop] using htoReal
    exact False.elim this
  have hΔ_pairwise : Pairwise fun i j ↦ IndepFun (Δ i) (Δ j) (law : Measure space) := by
    intro i j hij
    exact hΔ_iid.iIndepFun.indepFun hij
  have hΔ_expect : ∫ ω, Δ 0 ω ∂(law : Measure space) = 1 := by
    simpa [Δ, hτ0] using hτmean
  have hΔ_limit :
      ∀ᵐ ω ∂(law : Measure space),
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Δ i ω) / n) atTop (nhds 1) := by
    -- Proof comment: this is the strong law for the real-valued iid increment family.
    simpa [hΔ_expect] using
      (ProbabilityTheory.strong_law_ae_real Δ hΔ0_integrable hΔ_pairwise
        (fun n ↦ hΔ_iid.identDistrib n 0))
  filter_upwards [hΔ_limit] with ω hω
  have hω_shift :
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Δ i ω) / (n + 1 : ℝ))
        atTop (nhds 1) := by
    -- Proof comment: shifting the strong-law average by one step preserves the same `atTop`
    -- limit.
    convert hω.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    norm_num
  -- Proof comment: the increment sums telescope exactly to the embedded stopping times.
  simpa [Δ, embeddingTime_incrementSum_eq (stoppingTime := stoppingTime) hτ0 hτmono] using hω_shift

/-- Helper for Theorem 22.11: the unit interval oscillation event records a Brownian increment
larger than `√(n + 1)` somewhere on `[n, n + 1]`. -/
private def unitIntervalOscillationEvent
    {space : Type u} [MeasurableSpace space]
    (brownian : NNReal → space → ℝ) (n : ℕ) : Set space :=
  {ω | ∃ t ∈ Set.Icc (n : NNReal) ((n + 1 : ℕ) : NNReal),
      Real.sqrt (n + 1 : ℝ) < |brownian t ω - brownian (n : NNReal) ω|}

/-- Helper for Theorem 22.11: the Brownian LIL normalizer is positive once `t > exp 1`, because
both `t` and `log log t` are then positive. -/
private theorem lilNormalizer_pos_of_exp_one_lt
    {t : NNReal} (ht : Real.exp 1 < (t : ℝ)) :
    0 < IsBrownianMotion.lilNormalizer t := by
  have hlogt_gt_one : 1 < Real.log (t : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) ht)
  have hloglog_pos : 0 < Real.log (Real.log (t : ℝ)) := Real.log_pos hlogt_gt_one
  have ht_pos : 0 < (t : ℝ) := by
    exact
      lt_trans Real.zero_lt_one
        (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) ht)
  -- Proof comment: past `exp 1`, both factors under the square root are strictly positive.
  rw [IsBrownianMotion.lilNormalizer]
  exact Real.sqrt_pos.2 (by positivity)

/-- Helper for Theorem 22.11: once `exp 1 < s ≤ t`, the Brownian LIL normalizer is monotone from
`s` to `t`. -/
private theorem lilNormalizer_le_of_le_of_exp_one_lt
    {s t : NNReal} (hs : Real.exp 1 < (s : ℝ)) (hst : s ≤ t) :
    IsBrownianMotion.lilNormalizer s ≤ IsBrownianMotion.lilNormalizer t := by
  have hs_pos : 0 < (s : ℝ) := by
    exact
      lt_trans Real.zero_lt_one
        (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) hs)
  have hst_real : (s : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hst
  have ht : Real.exp 1 < (t : ℝ) := lt_of_lt_of_le hs hst_real
  have hlog_s_gt_one : 1 < Real.log (s : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hs)
  have hlog_s_pos : 0 < Real.log (s : ℝ) := lt_trans zero_lt_one hlog_s_gt_one
  have hlog_mono : Real.log (s : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log hs_pos hst_real
  have hloglog_mono :
      Real.log (Real.log (s : ℝ)) ≤ Real.log (Real.log (t : ℝ)) := by
    exact Real.log_le_log hlog_s_pos hlog_mono
  have hloglog_s_nonneg : 0 ≤ Real.log (Real.log (s : ℝ)) :=
    (Real.log_pos hlog_s_gt_one).le
  -- Proof comment: beyond `exp (exp 1)`, both factors inside the normalizer are monotone, so the
  -- square root preserves the comparison.
  rw [IsBrownianMotion.lilNormalizer, IsBrownianMotion.lilNormalizer]
  refine Real.sqrt_le_sqrt ?_
  have hleft :
      2 * (s : ℝ) * Real.log (Real.log (s : ℝ)) ≤
        2 * (t : ℝ) * Real.log (Real.log (s : ℝ)) := by
    gcongr
  have hright :
      2 * (t : ℝ) * Real.log (Real.log (s : ℝ)) ≤
        2 * (t : ℝ) * Real.log (Real.log (t : ℝ)) := by
    gcongr
  exact hleft.trans hright

/-- Helper for Theorem 22.11: shifting and recentering a Brownian motion at a deterministic time
again yields a Brownian motion. -/
private theorem incrementProcess_isBrownianMotion
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) {brownian : NNReal → space → ℝ}
    (hBrownian : IsBrownianMotion (law : Measure space) brownian) (s : NNReal) :
    IsBrownianMotion (law : Measure space)
      (fun t ω ↦ brownian (s + t) ω - brownian s ω) := by
  -- Proof comment: the increment process is a deterministic time shift of `brownian`, so the
  -- defining Brownian-motion fields transport directly along the translated mesh.
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · funext ω
    simp
  · intro n t ht
    have hTranslated :
        ∀ i j, i ≤ j → (fun i ↦ s + t i) i ≤ (fun i ↦ s + t i) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) s
    simpa [add_assoc] using hBrownian.indepIncrements n (fun i ↦ s + t i) hTranslated
  · intro u t r
    simpa [add_assoc, add_left_comm, add_comm] using
      hBrownian.stationaryIncrements (s + u) t r
  · intro t ht
    have hId :
        IdentDistrib
          (fun ω ↦ brownian (s + t) ω - brownian s ω)
          (fun ω ↦ brownian t ω - brownian 0 ω)
          (law : Measure space) (law : Measure space) := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hBrownian.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := s)
    have hLaw0 : HasLaw (fun ω ↦ brownian t ω - brownian 0 ω) (gaussianReal 0 t)
        (law : Measure space) := by
      simpa [hBrownian.zero] using hBrownian.gaussian_marginal ht
    exact hId.symm.hasLaw hLaw0
  · filter_upwards [hBrownian.continuous_paths] with ω hω
    have hShift : Continuous (fun t : NNReal ↦ brownian (s + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hShift.sub continuous_const

/-- Helper for Theorem 22.11: evaluating the Gaussian tail profile at the Brownian scaling
threshold `a / √T` yields the explicit Mills-type factor used for anchored window estimates. -/
private theorem gaussianTailUpperBound_scaledBrownianWindowThreshold
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) =
      (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
        Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  have hT_real_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := by
    positivity
  have hExponent :
      -((a / Real.sqrt (T : ℝ)) ^ 2) / 2 = -(a ^ 2) / (2 * (T : ℝ)) := by
    -- Proof comment: reduce `(a / √T)^2` to `a^2 / T` using `√T ^ 2 = T`.
    field_simp [hsqrtT_ne, hT_real_pos.ne']
    rw [Real.sq_sqrt hT_real_pos.le]
  calc
    2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)))
        = 2 *
            (((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) /
              (a / Real.sqrt (T : ℝ))) := by
              rw [gaussianPDFReal_def]
              simp [hExponent]
    _ = (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
          field_simp [ha.ne', hsqrtT_ne, show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]

/-- Helper for Theorem 22.11: the one-sided Brownian increment tail on an anchored window
`[s, s + T]` has the standard reflection-principle Gaussian profile. -/
private theorem anchoredIncrement_measureReal_le_profile
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) {brownian : NNReal → space → ℝ}
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    {s T : NNReal} {a : ℝ} (ha : 0 < a) (hT : 0 < T) :
    (law : Measure space).real {ω | ∃ t ∈ Set.Icc s (s + T), a < brownian t ω - brownian s ω} ≤
      (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
        Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  let W : NNReal → space → ℝ := fun u ω ↦ brownian (s + u) ω - brownian s ω
  let E : Set space := {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, a < W u ω}
  have hW : IsBrownianMotion (law : Measure space) W := by
    -- Proof comment: shift Brownian motion to the window's left endpoint and recenter it there.
    simpa [W] using incrementProcess_isBrownianMotion law hBrownian s
  have hEvent_eq :
      {ω | ∃ t ∈ Set.Icc s (s + T), a < brownian t ω - brownian s ω} = E := by
    ext ω
    constructor
    · rintro ⟨t, ht, hωt⟩
      refine ⟨t - s, ?_, ?_⟩
      · constructor
        · positivity
        · exact (tsub_le_iff_right).2 (by simpa [add_assoc, add_left_comm, add_comm] using ht.2)
      · simpa [W, add_tsub_cancel_of_le ht.1] using hωt
    · rintro ⟨u, hu, hωu⟩
      refine ⟨s + u, ?_, ?_⟩
      · constructor
        · simpa using le_add_of_nonneg_right hu.1
        · simpa [add_assoc] using add_le_add_left hu.2 s
      · simpa [W, add_assoc, add_left_comm, add_comm] using hωu
  let Y : space → ℝ := fun ω ↦ W T ω / Real.sqrt (T : ℝ)
  have hT_real_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT_real_pos
  have hRun : (law : Measure space) E = 2 * (law : Measure space) {ω | a < W T ω} := by
    simpa [E] using
      runningMaximum_eq_two_mul_brownianTerminalTail (hB := hW) (a := a) ha (T := T) hT
  have hMarginal : HasLaw (W T) (gaussianReal 0 T) (law : Measure space) :=
    hW.gaussian_marginal hT
  have hScale :
      HasLaw (fun z : ℝ ↦ (Real.sqrt (T : ℝ))⁻¹ * z) (gaussianReal 0 1) (gaussianReal 0 T) := by
    let c : ℝ := (Real.sqrt (T : ℝ))⁻¹
    let d : NNReal := ⟨c ^ 2, sq_nonneg c⟩
    have hmap :
        (gaussianReal 0 T).map (fun z : ℝ ↦ c * z) = gaussianReal 0 1 := by
      have hmap0 :
          (gaussianReal 0 T).map (c * ·) = gaussianReal 0 (d * T) := by
        simpa [d] using (gaussianReal_map_const_mul (μ := 0) (v := T) c)
      have hvar : d * T = 1 := by
        ext
        simp [c, d, NNReal.coe_mul, hT_real_pos.ne', Real.sq_sqrt hT_real_pos.le]
      rw [hvar] at hmap0
      simpa [c] using hmap0
    refine ⟨?_, hmap⟩
    fun_prop
  have hY : HasLaw Y (gaussianReal 0 1) (law : Measure space) := by
    -- Proof comment: normalize the terminal increment by `√T` to reach the standard Gaussian.
    simpa [Y, Function.comp, div_eq_mul_inv, mul_comm] using hScale.comp hMarginal
  have hx_pos : 0 < a / Real.sqrt (T : ℝ) := by
    positivity
  have hTailIci :
      (law : Measure space).real {ω | a / Real.sqrt (T : ℝ) ≤ Y ω} ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    simpa [MeasureTheory.Measure.real_def, Y] using
      (ProbabilityTheory.HasLaw.standardNormal_tail_bounds
        (P := (law : Measure space)) (X := Y) hY hx_pos).2
  have hTailSubset :
      {ω | a < W T ω} ⊆ {ω | a / Real.sqrt (T : ℝ) ≤ Y ω} := by
    intro ω hω
    have hScaled : a / Real.sqrt (T : ℝ) < Y ω := by
      simpa [Y] using (div_lt_div_of_pos_right hω hsqrtT_pos)
    exact hScaled.le
  have hTailIoi :
      (law : Measure space).real {ω | a < W T ω} ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    exact MeasureTheory.measureReal_mono hTailSubset |>.trans hTailIci
  calc
    (law : Measure space).real {ω | ∃ t ∈ Set.Icc s (s + T), a < brownian t ω - brownian s ω}
        = (law : Measure space).real E := by rw [hEvent_eq]
    _ = 2 * (law : Measure space).real {ω | a < W T ω} := by
          rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def, hRun,
            ENNReal.toReal_mul]
          norm_num
    _ ≤ 2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) := by
          gcongr
    _ =
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
            exact gaussianTailUpperBound_scaledBrownianWindowThreshold ha hT

/-- Helper for Theorem 22.11: the absolute Brownian increment on an anchored window `[s, s + T]`
is controlled by the sum of the positive and negative reflection-principle tails. -/
private theorem anchoredAbsIncrement_measureReal_le_profile
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) {brownian : NNReal → space → ℝ}
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    {s T : NNReal} {a : ℝ} (ha : 0 < a) (hT : 0 < T) :
    (law : Measure space).real {ω | ∃ t ∈ Set.Icc s (s + T), a < |brownian t ω - brownian s ω|} ≤
      2 *
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  let Eabs : Set space := {ω | ∃ t ∈ Set.Icc s (s + T), a < |brownian t ω - brownian s ω|}
  let Epos : Set space := {ω | ∃ t ∈ Set.Icc s (s + T), a < brownian t ω - brownian s ω}
  let Eneg : Set space := {ω | ∃ t ∈ Set.Icc s (s + T), a < (-brownian t ω) - (-brownian s ω)}
  have hSubset : Eabs ⊆ Epos ∪ Eneg := by
    intro ω hω
    rcases hω with ⟨t, ht, hωt⟩
    by_cases hnonneg : 0 ≤ brownian t ω - brownian s ω
    · left
      exact ⟨t, ht, by simpa [abs_of_nonneg hnonneg] using hωt⟩
    · right
      have hneg : a < -(brownian t ω - brownian s ω) := by
        simpa [abs_of_neg (lt_of_not_ge hnonneg)] using hωt
      have hneg' : a < (-brownian t ω) - (-brownian s ω) := by
        linarith
      exact ⟨t, ht, hneg'⟩
  have hNegBrownian : IsBrownianMotion (law : Measure space) (fun t ω ↦ -brownian t ω) :=
    IsBrownianMotion.neg_isBrownianMotion hBrownian
  have hUnion :
      (law : Measure space).real (Epos ∪ Eneg) ≤
        (law : Measure space).real Epos + (law : Measure space).real Eneg :=
    MeasureTheory.measureReal_union_le (μ := (law : Measure space)) Epos Eneg
  have hPos :
      (law : Measure space).real Epos ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) :=
    anchoredIncrement_measureReal_le_profile law hBrownian ha hT
  have hNeg :
      (law : Measure space).real Eneg ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
    simpa [Eneg] using
      anchoredIncrement_measureReal_le_profile
        law hNegBrownian ha hT
  calc
    (law : Measure space).real Eabs ≤ (law : Measure space).real (Epos ∪ Eneg) := by
      simpa [MeasureTheory.Measure.real_def] using
        (ENNReal.toReal_mono (measure_ne_top (law : Measure space) (Epos ∪ Eneg))
          (measure_mono hSubset))
    _ ≤ (law : Measure space).real Epos + (law : Measure space).real Eneg := hUnion
    _ ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) +
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := add_le_add hPos hNeg
    _ =
        2 *
          (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
            Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by ring

/-- Helper for Theorem 22.11: summable real event masses imply almost-sure eventual avoidance by
the first Borel-Cantelli lemma. -/
private theorem ae_eventually_notMem_of_summable_measureReal
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) {s : ℕ → Set space}
    (hs : Summable (fun n : ℕ ↦ (law : Measure space).real (s n))) :
    ∀ᵐ ω ∂(law : Measure space), ∀ᶠ n in atTop, ω ∉ s n := by
  have htsum : (∑' n, (law : Measure space) (s n)) ≠ ⊤ := by
    -- Proof comment: summability of the real masses lifts to finiteness of the ENNReal series
    -- used by the measurable Borel-Cantelli API.
    simpa [MeasureTheory.Measure.real_def] using hs.tsum_ofReal_ne_top
  exact
    MeasureTheory.ae_eventually_notMem
      (μ := (law : Measure space)) (s := s) htsum

/-- Helper for Theorem 22.11: the large unit-interval oscillation event has the Gaussian
reflection-principle upper bound. -/
private theorem unitIntervalOscillationEvent_measure_le
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (n : ℕ) :
    (law : Measure space) (unitIntervalOscillationEvent brownian n) ≤
      ENNReal.ofReal
        (4 *
          (gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) /
            Real.sqrt (n + 1 : ℝ))) := by
  let W : NNReal → space → ℝ :=
    fun t ω ↦ brownian ((n : NNReal) + t) ω - brownian (n : NNReal) ω
  let a : ℝ := Real.sqrt (n + 1 : ℝ)
  let Epos : Set space := {ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, a < W t ω}
  let Eneg : Set space := {ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, a < -W t ω}
  have hW : IsBrownianMotion (law : Measure space) W := by
    -- Proof comment: shift the Brownian motion to the left endpoint `n`.
    simpa [W] using
      incrementProcess_isBrownianMotion law hBrownian (n : NNReal)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hEventSubset :
      unitIntervalOscillationEvent brownian n ⊆ Epos ∪ Eneg := by
    intro ω hω
    rcases hω with ⟨t, ht, hOsc⟩
    have hn_le_t : (n : NNReal) ≤ t := ht.1
    have ht_le : t ≤ ((n + 1 : ℕ) : NNReal) := ht.2
    have hSub_mem : t - n ∈ Set.Icc (0 : NNReal) 1 := by
      constructor
      · exact zero_le _
      · refine NNReal.coe_le_coe.mp ?_
        rw [NNReal.coe_sub hn_le_t]
        have hSubReal : (t : ℝ) - n ≤ 1 := by
          have ht_real : (t : ℝ) ≤ n + 1 := by
            exact_mod_cast ht_le
          linarith
        simpa using hSubReal
    have hRewrite : W (t - n) ω = brownian t ω - brownian (n : NNReal) ω := by
      simp [W, add_tsub_cancel_of_le hn_le_t]
    have hAbs : a < |W (t - n) ω| := by
      simpa [a, hRewrite] using hOsc
    by_cases hNonneg : 0 ≤ W (t - n) ω
    · left
      exact ⟨t - n, hSub_mem, by simpa [abs_of_nonneg hNonneg] using hAbs⟩
    · right
      have hNeg : W (t - n) ω < 0 := lt_of_not_ge hNonneg
      exact ⟨t - n, hSub_mem, by simpa [abs_of_neg hNeg] using hAbs⟩
  have hPos :
      (law : Measure space) Epos ≤
        ENNReal.ofReal
          (2 * (gaussianPDFReal 0 1 a / a)) := by
    have hRun :
        (law : Measure space) Epos =
          2 * (law : Measure space) {ω | a < W 1 ω} := by
      simpa [Epos] using
        runningMaximum_eq_two_mul_brownianTerminalTail
          (hB := hW) (a := a) ha (T := (1 : NNReal)) (by positivity)
    have hLaw : HasLaw (W 1) (gaussianReal 0 1) (law : Measure space) :=
      hW.gaussian_marginal (by positivity)
    have hTailClosed :
        ((law : Measure space) {ω | a ≤ W 1 ω}).toReal ≤
          gaussianPDFReal 0 1 a / a := by
      simpa [MeasureTheory.Measure.real_def] using
        (ProbabilityTheory.HasLaw.standardNormal_tail_bounds
          (P := (law : Measure space)) (X := W 1) hLaw ha).2
    have hTailOpen :
        ((law : Measure space) {ω | a < W 1 ω}).toReal ≤
          gaussianPDFReal 0 1 a / a := by
      refine le_trans ?_ hTailClosed
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono fun _ hω ↦ show a ≤ W 1 _ from le_of_lt hω)
    have hPosReal :
        ((law : Measure space) Epos).toReal ≤
          2 * (gaussianPDFReal 0 1 a / a) := by
      rw [hRun, ENNReal.toReal_mul]
      norm_num
      gcongr
    have hProfile_nonneg : 0 ≤ 2 * (gaussianPDFReal 0 1 a / a) := by
      have hDiv_nonneg : 0 ≤ gaussianPDFReal 0 1 a / a := by
        exact div_nonneg (gaussianPDFReal_nonneg 0 1 a) ha.le
      nlinarith
    exact
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hProfile_nonneg).2 hPosReal
  have hNeg :
      (law : Measure space) Eneg ≤
        ENNReal.ofReal
          (2 * (gaussianPDFReal 0 1 a / a)) := by
    have hWneg : IsBrownianMotion (law : Measure space) (fun t ω ↦ -W t ω) :=
      IsBrownianMotion.neg_isBrownianMotion hW
    have hRun :
        (law : Measure space) Eneg =
          2 * (law : Measure space) {ω | a < -W 1 ω} := by
      simpa [Eneg] using
        runningMaximum_eq_two_mul_brownianTerminalTail
          (hB := hWneg) (a := a) ha (T := (1 : NNReal)) (by positivity)
    have hLaw :
        HasLaw (fun ω ↦ -W 1 ω) (gaussianReal 0 1) (law : Measure space) := by
      simpa using ProbabilityTheory.gaussianReal_neg (hW.gaussian_marginal (by positivity))
    have hTailClosed :
        ((law : Measure space) {ω | a ≤ -W 1 ω}).toReal ≤
          gaussianPDFReal 0 1 a / a := by
      simpa [MeasureTheory.Measure.real_def] using
        (ProbabilityTheory.HasLaw.standardNormal_tail_bounds
          (P := (law : Measure space)) (X := fun ω ↦ -W 1 ω) hLaw ha).2
    have hTailOpen :
        ((law : Measure space) {ω | a < -W 1 ω}).toReal ≤
          gaussianPDFReal 0 1 a / a := by
      refine le_trans ?_ hTailClosed
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono fun _ hω ↦ show a ≤ -W 1 _ from le_of_lt hω)
    have hNegReal :
        ((law : Measure space) Eneg).toReal ≤
          2 * (gaussianPDFReal 0 1 a / a) := by
      rw [hRun, ENNReal.toReal_mul]
      norm_num
      gcongr
    have hProfile_nonneg : 0 ≤ 2 * (gaussianPDFReal 0 1 a / a) := by
      have hDiv_nonneg : 0 ≤ gaussianPDFReal 0 1 a / a := by
        exact div_nonneg (gaussianPDFReal_nonneg 0 1 a) ha.le
      nlinarith
    exact
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hProfile_nonneg).2 hNegReal
  -- Proof comment: split the absolute-value event into positive and negative excursions of the
  -- shifted Brownian increment process, then bound both sides by the same Gaussian tail.
  calc
    (law : Measure space) (unitIntervalOscillationEvent brownian n)
        ≤ (law : Measure space) (Epos ∪ Eneg) := measure_mono hEventSubset
    _ ≤ (law : Measure space) Epos + (law : Measure space) Eneg := measure_union_le _ _
    _ ≤
        ENNReal.ofReal (2 * (gaussianPDFReal 0 1 a / a)) +
          ENNReal.ofReal (2 * (gaussianPDFReal 0 1 a / a)) := by
            exact add_le_add hPos hNeg
    _ = ENNReal.ofReal
          (4 * (gaussianPDFReal 0 1 a / a)) := by
            have hProfile_nonneg : 0 ≤ 2 * (gaussianPDFReal 0 1 a / a) := by
              have hDiv_nonneg : 0 ≤ gaussianPDFReal 0 1 a / a := by
                exact div_nonneg (gaussianPDFReal_nonneg 0 1 a) ha.le
              nlinarith
            rw [← ENNReal.ofReal_add hProfile_nonneg hProfile_nonneg]
            ring
    _ = ENNReal.ofReal
          (4 *
            (gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) /
              Real.sqrt (n + 1 : ℝ))) := by
            simp [a]

/-- Helper for Theorem 22.11: evaluating the standard Gaussian density at `√(n + 1)` yields the
explicit factor `exp (-(n + 1) / 2) / √(2π)`. -/
private theorem gaussianPDFReal_sqrt_natSucc_eq (n : ℕ) :
    gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp ( - ((n + 1 : ℝ) / 2)) := by
  have hsq : (Real.sqrt (n + 1 : ℝ)) ^ (2 : ℕ) = n + 1 := by
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  calc
    gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ))
        = (1 / Real.sqrt (2 * Real.pi)) *
            Real.exp (-(Real.sqrt (n + 1 : ℝ)) ^ 2 / 2) := by
              simp [gaussianPDFReal_def, div_eq_mul_inv, mul_left_comm, mul_comm]
    _ = (1 / Real.sqrt (2 * Real.pi)) * Real.exp ( - ((n + 1 : ℝ) / 2)) := by
          rw [hsq]
          congr 1
          ring_nf

/-- Helper for Theorem 22.11: the unit-interval oscillation event is dominated by a geometric
majorant with ratio `exp (-1 / 2)`. -/
private theorem unitIntervalOscillationEvent_measure_le_geometric
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (n : ℕ) :
    let q : ℝ := Real.exp (-(1 / 2 : ℝ))
    (law : Measure space) (unitIntervalOscillationEvent brownian n) ≤
      ENNReal.ofReal ((((4 : ℝ) / Real.sqrt (2 * Real.pi)) * q) * q ^ n) := by
  dsimp
  have hMeasure := unitIntervalOscillationEvent_measure_le law brownian hBrownian n
  refine hMeasure.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hsqrt_pos : 0 < Real.sqrt (n + 1 : ℝ) := by
    positivity
  have hsqrt_one_le : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
    have hSqrt :
        Real.sqrt (1 : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by
      have hOneLe : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact Real.sqrt_le_sqrt hOneLe
    simp at hSqrt
    exact hSqrt
  have hPow :
      Real.exp ( - ((n + 1 : ℝ) / 2)) =
        Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) ^ n := by
    calc
      Real.exp ( - ((n + 1 : ℝ) / 2))
          = Real.exp (-(1 / 2 : ℝ) + n * (-(1 / 2 : ℝ))) := by ring_nf
      _ = Real.exp (-(1 / 2 : ℝ)) * Real.exp (n * (-(1 / 2 : ℝ))) := by
            rw [Real.exp_add]
      _ = Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) ^ n := by
            rw [Real.exp_nat_mul]
  calc
    4 *
        (gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) /
          Real.sqrt (n + 1 : ℝ))
        ≤ 4 * gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) := by
            have hPdf_nonneg : 0 ≤ gaussianPDFReal 0 1 (Real.sqrt (n + 1 : ℝ)) := by
              exact gaussianPDFReal_nonneg 0 1 _
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (div_le_iff₀ hsqrt_pos).2 <| by nlinarith
    _ = ((4 : ℝ) / Real.sqrt (2 * Real.pi)) *
          Real.exp ( - ((n + 1 : ℝ) / 2)) := by
          rw [gaussianPDFReal_sqrt_natSucc_eq n]
          ring_nf
    _ = (((4 : ℝ) / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2 : ℝ))) *
          Real.exp (-(1 / 2 : ℝ)) ^ n := by
          rw [hPow]
          ring_nf

/-- Helper for Theorem 22.11: the large unit-interval oscillation events form a summable family.
-/
private theorem unitIntervalOscillationEvent_tsum_ne_top
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian) :
    (∑' n : ℕ, (law : Measure space) (unitIntervalOscillationEvent brownian n)) ≠ ⊤ := by
  let q : ℝ := Real.exp (-(1 / 2 : ℝ))
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt_one : q < 1 := by
    dsimp [q]
    simp using (Real.exp_lt_one_iff.mpr (by norm_num : (-(1 / 2 : ℝ)) < 0))
  have hSummable :
      Summable
        (fun n : ℕ ↦
          (((4 : ℝ) / Real.sqrt (2 * Real.pi)) * q) * q ^ n) := by
    exact (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left _
  have hDominated :
      (∑' n : ℕ,
        ENNReal.ofReal ((((4 : ℝ) / Real.sqrt (2 * Real.pi)) * q) * q ^ n)) ≠ ⊤ := by
    exact hSummable.tsum_ofReal_ne_top
  have hCompare :
      (∑' n : ℕ, (law : Measure space) (unitIntervalOscillationEvent brownian n)) ≤
        ∑' n : ℕ, ENNReal.ofReal ((((4 : ℝ) / Real.sqrt (2 * Real.pi)) * q) * q ^ n) := by
    refine ENNReal.tsum_le_tsum ?_
    intro n
    simpa [q] using unitIntervalOscillationEvent_measure_le_geometric law brownian hBrownian n
  exact ne_top_of_le_ne_top hDominated hCompare

/-- Helper for Theorem 22.11: almost every Brownian path has no large `√(n + 1)` oscillation on
any sufficiently far unit interval `[n, n + 1]`. -/
private theorem ae_eventually_unitIntervalBrownianIncrement_le_sqrtSucc
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian) :
    ∀ᵐ ω ∂(law : Measure space),
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ Set.Icc (n : NNReal) ((n + 1 : ℕ) : NNReal),
          |brownian t ω - brownian (n : NNReal) ω| ≤ Real.sqrt (n + 1 : ℝ) := by
  have hBad :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ n : ℕ in atTop, ω ∉ unitIntervalOscillationEvent brownian n := by
    simpa using
      (MeasureTheory.ae_eventually_notMem
        (μ := (law : Measure space))
        (s := unitIntervalOscillationEvent brownian)
        (unitIntervalOscillationEvent_tsum_ne_top law brownian hBrownian))
  filter_upwards [hBad] with ω hω
  filter_upwards [hω] with n hn t ht
  -- Proof comment: on the good tail, the defining bad event is absent, so every point in
  -- `[n, n + 1]` satisfies the desired oscillation bound.
  by_contra hgt
  exact hn ⟨t, ht, lt_of_not_ge hgt⟩

/-- Helper for Theorem 22.11: every tail point `t ≥ a ^ N` lies in some geometric block
`[a ^ n, a ^ (n + 1)]` with `n ≥ N`. -/
private theorem exists_mem_geometricBlock
    {a : NNReal} (ha : 1 < (a : ℝ)) {N : ℕ} {t : NNReal} (ht : a ^ N ≤ t) :
    ∃ n, N ≤ n ∧ t ∈ Set.Icc (a ^ n) (a ^ (n + 1)) := by
  let u : ℕ → NNReal := fun k ↦ a ^ (N + k)
  have hu_tendsto :
      Tendsto (fun k : ℕ ↦ ((u k : NNReal) : ℝ)) atTop atTop := by
    simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt ha).comp (Filter.tendsto_add_atTop_nat N)
  obtain ⟨K, hK⟩ :
      ∃ K : ℕ, (t : ℝ) < ((u K : NNReal) : ℝ) := by
    exact (hu_tendsto.eventually_gt_atTop (t : ℝ)).exists
  let k := Nat.findGreatest (fun j ↦ u j ≤ t) K
  have hk_le : k ≤ K := Nat.findGreatest_le (P := fun j ↦ u j ≤ t) K
  have hk_spec : u k ≤ t := by
    refine Nat.findGreatest_spec (P := fun j ↦ u j ≤ t) (m := 0) (Nat.zero_le K) ?_
    simpa [u] using ht
  have hnext_not_le : ¬ u (k + 1) ≤ t := by
    have hk_lt_K : k < K := by
      by_contra hk_ge
      have hk_eq : k = K := le_antisymm hk_le (Nat.le_of_not_lt hk_ge)
      have : ((u K : NNReal) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast (hk_eq ▸ hk_spec)
      exact (not_le_of_gt hK) this
    exact
      Nat.findGreatest_is_greatest (P := fun j ↦ u j ≤ t) (k := k + 1) (n := K)
        (by simp [k]) (Nat.succ_le_of_lt hk_lt_K)
  refine ⟨N + k, Nat.le_add_right N k, ?_⟩
  rw [Set.mem_Icc]
  constructor
  · simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk_spec
  · have hnext_lt : t < u (k + 1) := lt_of_not_ge hnext_not_le
    exact le_of_lt <| by
      simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext_lt

/-- Helper for Theorem 22.11: every sufficiently large deterministic time belongs to a middle
geometric block `[a ^ (k + 1), a ^ (k + 2)]`, which is the block shape needed for the stopping-time
window comparison. -/
private theorem exists_mem_geometricMiddleBlock
    {a : NNReal} (ha : 1 < (a : ℝ)) {t : NNReal} (ht : a ≤ t) :
    ∃ k : ℕ, t ∈ Set.Icc (a ^ (k + 1)) (a ^ (k + 2)) := by
  rcases exists_mem_geometricBlock (a := a) ha (N := 1) (by simpa using ht) with
      ⟨n, hn, htBlock⟩
  refine ⟨n - 1, ?_⟩
  have hn_pos : 1 ≤ n := hn
  have hk1 : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
  have hk2 : n - 1 + 2 = n + 1 := by omega
  simpa [hk1, hk2] using htBlock

/-- Helper for Theorem 22.11: if `τ (n + 1) / (n + 1)` is eventually trapped between `1 / a` and
`a`, then the random time `τ (n + 1)` eventually lies in the multiplicative window around
`n + 1`. -/
private theorem eventually_stoppingTime_mem_relativeWindow
    {space : Type u} [MeasurableSpace space]
    (stoppingTime : ℕ → space → NNReal) {ω : space} {a : NNReal}
    (ha : 1 < (a : ℝ))
    (hω :
      Tendsto (fun n : ℕ ↦ (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ)) atTop (nhds 1)) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (a : ℝ)) * (n + 1 : ℝ) ≤ (stoppingTime (n + 1) ω : ℝ) ∧
        (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) * (n + 1 : ℝ) := by
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / (a : ℝ)) <
            (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ) ∧
          (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ) < (a : ℝ) := by
    have hLeft : (1 / (a : ℝ)) < 1 := by
      have ha_pos : 0 < (a : ℝ) := lt_trans zero_lt_one ha
      by_contra hNot
      have hge : 1 ≤ 1 / (a : ℝ) := le_of_not_gt hNot
      have hmul := mul_le_mul_of_nonneg_left hge ha_pos.le
      have hcontr : (a : ℝ) ≤ 1 := by
        simpa [one_div, ha_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
      exact (not_le_of_gt ha) hcontr
    have hRight : (1 : ℝ) < (a : ℝ) := ha
    exact hω.eventually (Ioo_mem_nhds hLeft hRight)
  refine hEventually.mono ?_
  intro n hn
  rcases hn with ⟨hnLeft, hnRight⟩
  have hn_pos : 0 < (n + 1 : ℝ) := by positivity
  constructor
  · exact (lt_div_iff₀ hn_pos).mp hnLeft |>.le
  · exact (div_lt_iff₀ hn_pos).mp hnRight |>.le

/-- Helper for Theorem 22.11: the unit-interval Brownian oscillation scale `2 √(n + 1)` is
eventually negligible compared with the LIL normalizer `√(2 (n + 1) log log (n + 1))` after any
fixed reciprocal factor `1 / (m + 1)`. -/
private theorem eventually_two_mul_sqrtSucc_le_invSucc_mul_lilNormalizer
    (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (n + 1 : ℝ) ≤
        (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
  have hNat :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    convert
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)) using 1
    funext n
    simp [Nat.cast_add]
  have hLog :
      Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNat
  have hLogLog :
      Tendsto (fun n : ℕ ↦ Real.log (Real.log (n + 1 : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLog
  have hEventuallyLarge :
      ∀ᶠ n : ℕ in atTop,
        2 * (m + 1 : ℝ) ^ 2 ≤ Real.log (Real.log (n + 1 : ℝ)) := by
    exact hLogLog.eventually_ge_atTop (2 * (m + 1 : ℝ) ^ 2)
  filter_upwards [hEventuallyLarge] with n hn
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (n + 1 : ℝ) := by
    positivity
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n + 1 : ℝ)) := by
    exact le_trans (by positivity) hn
  have hright_nonneg :
      0 ≤ (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
    positivity
  rw [← sq_le_sq₀ hleft_nonneg hright_nonneg]
  -- Proof comment: once `log log (n + 1)` dominates `2 (m + 1)^2`, squaring both sides reduces
  -- the estimate to a linear inequality in `log log (n + 1)`.
  rw [IsBrownianMotion.lilNormalizer]
  have hleft_sq :
      (2 * Real.sqrt (n + 1 : ℝ)) ^ 2 = 4 * (n + 1 : ℝ) := by
    calc
      (2 * Real.sqrt (n + 1 : ℝ)) ^ 2
          = 4 * (Real.sqrt (n + 1 : ℝ)) ^ 2 := by ring
      _ = 4 * (n + 1 : ℝ) := by
          rw [Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)]
  have hright_sq :
      ((1 / (m + 1 : ℝ)) *
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))) ^ 2 =
        (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) / (m + 1 : ℝ) ^ 2 := by
    calc
      ((1 / (m + 1 : ℝ)) *
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))) ^ 2
          = (1 / (m + 1 : ℝ)) ^ 2 *
              (Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))) ^ 2 := by
                ring
      _ = (1 / (m + 1 : ℝ)) ^ 2 *
            (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) := by
              rw [Real.sq_sqrt (show 0 ≤ 2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)) by
                positivity)]
      _ = (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) / (m + 1 : ℝ) ^ 2 := by
              field_simp [show (m + 1 : ℝ) ≠ 0 by positivity]
  have hm_sq_pos : 0 < (m + 1 : ℝ) ^ 2 := by
    positivity
  have hScaled :
      2 ≤ Real.log (Real.log (n + 1 : ℝ)) / (m + 1 : ℝ) ^ 2 := by
    exact (le_div_iff₀ hm_sq_pos).2 hn
  have hSquared :
      4 * (n + 1 : ℝ) ≤
        (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) / (m + 1 : ℝ) ^ 2 := by
    have hMul :=
      mul_le_mul_of_nonneg_left hScaled (show 0 ≤ 2 * (n + 1 : ℝ) by positivity)
    have hMul' :
        4 * (n + 1 : ℝ) ≤
          2 * (n + 1 : ℝ) * (Real.log (Real.log (n + 1 : ℝ)) / (m + 1 : ℝ) ^ 2) := by
      have hFour :
          4 * (n + 1 : ℝ) = (2 * (n + 1 : ℝ)) * 2 := by ring
      rw [hFour]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
    convert hMul' using 1
    · ring
    · ring
  calc
    (2 * Real.sqrt (n + 1 : ℝ)) ^ 2 = 4 * (n + 1 : ℝ) := hleft_sq
    _ ≤ (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) / (m + 1 : ℝ) ^ 2 := hSquared
    _ = ((1 / (m + 1 : ℝ)) *
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))) ^ 2 := hright_sq.symm

/-- Helper for Theorem 22.11: once a comparison sequence already has limsup `1`, any second
sequence that stays within every reciprocal error envelope `1 / (m + 1)` has the expected
reciprocal-gap limsup upper bounds. -/
private theorem limsupEqOne_isBoundedUnder {v : ℕ → ℝ}
    (hDiscrete : limsup v atTop = 1) :
    Filter.IsBoundedUnder (· ≤ ·) atTop v := by
  by_contra hNotBounded
  have hZero : limsup v atTop = 0 :=
    Real.limsup_of_not_isBoundedUnder hNotBounded
  simp [hDiscrete] at hZero

/-- Helper for Theorem 22.11: a sequence with limsup `1` is also cobounded below along `atTop`.
-/
private theorem limsupEqOne_isCoboundedUnder {v : ℕ → ℝ}
    (hDiscrete : limsup v atTop = 1) :
    Filter.IsCoboundedUnder (· ≤ ·) atTop v := by
  by_contra hNotCobounded
  have hZero : limsup v atTop = 0 :=
    Real.limsup_of_not_isCoboundedUnder hNotCobounded
  simp [hDiscrete] at hZero

/-- Helper for Theorem 22.11: reciprocal window-error bounds force the pointwise difference
`u - v` to converge to `0` along `atTop`. -/
private theorem windowError_tendsto_zero
    {u v : ℕ → ℝ}
    (hErr : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, |u n - v n| ≤ 1 / (m + 1 : ℝ)) :
    Tendsto (fun n : ℕ ↦ u n - v n) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < -a by linarith)
    refine (hErr m).mono ?_
    intro n hn
    have hLower : -(1 / (m + 1 : ℝ)) ≤ u n - v n := (abs_le.mp hn).1
    linarith
  · intro a ha
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt ha
    refine (hErr m).mono ?_
    intro n hn
    have hUpper : u n - v n ≤ 1 / (m + 1 : ℝ) := (abs_le.mp hn).2
    linarith

/-- Helper for Theorem 22.11: once a comparison sequence already has limsup `1`, any second
sequence that stays within every reciprocal error envelope `1 / (m + 1)` eventually has the same
limsup. -/
private theorem samplewise_embeddedLimsup_eq_one_of_discreteLIL_and_windowError
    {u v : ℕ → ℝ}
    (hDiscrete : limsup v atTop = 1)
    (hErr : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, |u n - v n| ≤ 1 / (m + 1 : ℝ)) :
    limsup u atTop = 1 := by
  let d : ℕ → ℝ := fun n ↦ u n - v n
  have hDiff : Tendsto d atTop (nhds 0) :=
    windowError_tendsto_zero hErr
  have hBoundedV : Filter.IsBoundedUnder (· ≤ ·) atTop v :=
    limsupEqOne_isBoundedUnder hDiscrete
  have hCoboundedV : Filter.IsCoboundedUnder (· ≤ ·) atTop v :=
    limsupEqOne_isCoboundedUnder hDiscrete
  have hBoundedDiffAbove : Filter.IsBoundedUnder (· ≤ ·) atTop d :=
    hDiff.isBoundedUnder_le
  have hBoundedDiffBelow : Filter.IsBoundedUnder (· ≥ ·) atTop d :=
    hDiff.isBoundedUnder_ge
  have hUpper :
      limsup u atTop ≤ 1 := by
    have hAdd :
        limsup (fun n : ℕ ↦ d n + v n) atTop ≤ limsup d atTop + limsup v atTop :=
      limsup_add_le
        (u := d) (v := v) hBoundedDiffBelow hBoundedDiffAbove hCoboundedV hBoundedV
    have hDecomp : (fun n : ℕ ↦ d n + v n) = u := by
      funext n
      dsimp [d]
      ring
    simpa [hDecomp, hDiscrete, hDiff.limsup_eq] using hAdd
  have hLower :
      1 ≤ limsup u atTop := by
    have hAdd :
        limsup v atTop + liminf d atTop ≤ limsup (fun n : ℕ ↦ v n + d n) atTop :=
      le_limsup_add
        (u := v) (v := d) hBoundedV hCoboundedV hBoundedDiffAbove hBoundedDiffBelow
    have hDecomp : (fun n : ℕ ↦ v n + d n) = u := by
      funext n
      dsimp [d]
      ring
    simpa [hDecomp, hDiscrete, hDiff.liminf_eq] using hAdd
  -- Proof comment: once the difference sequence tends to `0`, the additive limsup transport
  -- lemmas show that `u` and `v` have the same limsup.
  exact le_antisymm hUpper hLower

/-- Helper for Theorem 22.11: if a subsequence `u ∘ τ` is frequently at least `c`, the index map
`τ` tends to `atTop`, and the ambient sequence `u` is eventually bounded above, then `c ≤ limsup u`.
-/
private theorem le_limsup_of_frequently_ge_subseq
    {u : ℕ → ℝ} {σ : ℕ → ℕ} {c C : ℝ}
    (hσ : Tendsto σ atTop atTop)
    (hUpper : ∀ᶠ n : ℕ in atTop, u n ≤ C)
    (hFreq : ∃ᶠ n : ℕ in atTop, c ≤ u (σ n)) :
    c ≤ limsup u atTop := by
  let v : ℕ → ℝ := fun n ↦ u (σ n)
  have hUpperSubseq : ∀ᶠ n : ℕ in atTop, v n ≤ C := by
    simpa [v] using hσ.eventually hUpper
  have hBoundedSubseq : atTop.IsBoundedUnder (· ≤ ·) v := by
    exact isBoundedUnder_of_eventually_le hUpperSubseq
  have hSubseq :
      c ≤ limsup u (Filter.map σ atTop) := by
    have hBase : c ≤ limsup v atTop := by
      exact Filter.le_limsup_of_frequently_le hFreq hBoundedSubseq
    simpa [v, limsup_comp] using hBase
  have hBoundedFull : atTop.IsBoundedUnder (· ≤ ·) u := by
    exact isBoundedUnder_of_eventually_le hUpper
  have hCoboundedSubseq :
      (Filter.map σ atTop).IsCoboundedUnder (· ≤ ·) u := by
    simpa [v] using
      (Filter.IsCoboundedUnder.of_frequently_ge hFreq : atTop.IsCoboundedUnder (· ≤ ·) v)
  exact le_trans hSubseq <|
    Filter.limsup_le_limsup_of_le hσ hCoboundedSubseq hBoundedFull

/-- Helper for Theorem 22.11: the Brownian law of the iterated logarithm transfers from continuous
time to the integer skeleton `n ↦ brownian (n + 1)` once unit-interval oscillations are known to
be negligible. -/
private theorem ae_limsup_integerBrownian_ge_one_sub_invSucc
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (m : ℕ) :
    ∀ᵐ ω ∂(law : Measure space),
      1 - 1 / (m + 1 : ℝ) ≤
        limsup
          (fun n : ℕ ↦
            brownian (n + 1 : NNReal) ω /
              Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
          atTop := by
  let αNat : ℕ := 16 * (m + 1) ^ 2
  let α : NNReal := (αNat : NNReal)
  have hα : 1 < (α : ℝ) := by
    have hαNat : 1 < αNat := by
      dsimp [αNat]
      have hsq_pos : 0 < (m + 1) ^ 2 := by
        positivity
      omega
    have hαReal : (1 : ℝ) < (αNat : ℝ) := by
      exact_mod_cast hαNat
    simpa [α] using hαReal
  have hUpper :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ t in atTop, IsBrownianMotion.lilRatio brownian ω t ≤ (2 : ℝ) := by
    have hSummable :=
      IsBrownianMotion.summable_geometricUpperBlock_measureReal
        (B := brownian) hBrownian (α := (2 : NNReal)) (by norm_num)
    -- Proof comment: reuse the completed upper-side geometric-block argument at the fixed ratio
    -- `2` to bound the Brownian LIL ratio from above on every large tail.
    exact
      IsBrownianMotion.ae_eventually_lilRatio_le_of_geometricUpperBlockSummable
        (B := brownian) hBrownian (α := (2 : NNReal)) (by norm_num) hSummable
  have hUpperNeg :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ t in atTop, IsBrownianMotion.lilRatio (fun s ω ↦ -brownian s ω) ω t ≤ (2 : ℝ) := by
    have hNegBrownian :
        IsBrownianMotion (law : Measure space) (fun s ω ↦ -brownian s ω) :=
      IsBrownianMotion.neg_isBrownianMotion hBrownian
    have hSummableNeg :=
      IsBrownianMotion.summable_geometricUpperBlock_measureReal
        (B := fun t ω ↦ -brownian t ω) hNegBrownian (α := (2 : NNReal)) (by norm_num)
    -- Proof comment: the same upper-side argument applied to `-brownian` gives the lower control
    -- on the previous mesh point that the geometric lower transfer needs.
    exact
      IsBrownianMotion.ae_eventually_lilRatio_le_of_geometricUpperBlockSummable
        (B := fun t ω ↦ -brownian t ω) hNegBrownian (α := (2 : NNReal)) (by norm_num)
        hSummableNeg
  have hFreq := by
    exact
      IsBrownianMotion.geometricIncrementEvents_force_frequently_of_eventually_inv_le_measureReal
        (B := brownian) hBrownian hα
        (by
          -- Proof comment: the coarse mesh `α = 16 (m + 1)^2` is exactly the owner theorem from
          -- Theorem 22.1, so we import its already-proved harmonic lower-mass estimate verbatim.
          simpa [MeasureTheory.Measure.real_def, α, αNat] using
            theorem22_1LowerMass (μ := (law : Measure space)) (B := brownian) hBrownian m)
  filter_upwards [hUpper, hUpperNeg, hFreq] with ω hUpperω hUpperNegω hFreqω
  let u : ℕ → ℝ := fun n ↦ IsBrownianMotion.lilRatio brownian ω (n + 1 : NNReal)
  let meshIndex : ℕ → ℕ := fun n ↦ αNat ^ (n + 1) - 1
  have hMeshTimeTendsto :
      Tendsto
        (fun n : ℕ ↦ α ^ (n + 1))
        atTop atTop := by
    have hαNN : (1 : NNReal) < α := by
      exact_mod_cast hα
    exact
      ((tendsto_pow_atTop_atTop_of_one_lt hαNN :
        Tendsto (fun n : ℕ ↦ α ^ n) atTop atTop)).comp (tendsto_add_atTop_nat 1)
  have hMeshIndex_time :
      ∀ n : ℕ, ((meshIndex n + 1 : ℕ) : NNReal) = α ^ (n + 1) := by
    intro n
    dsimp [meshIndex, α, αNat]
    have hpow_pos : 0 < αNat ^ (n + 1) := by
      have hαNat_pos : 0 < αNat := by
        dsimp [αNat]
        positivity
      exact Nat.pow_pos hαNat_pos
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hpow_pos)
  have hMeshIndex_time_add :
      ∀ n : ℕ, (meshIndex n : NNReal) + 1 = α ^ (n + 1) := by
    intro n
    simpa [Nat.cast_add] using hMeshIndex_time n
  have hMeshIndexTendsto : Tendsto meshIndex atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro N
    have hLarge :
        ∀ᶠ n : ℕ in atTop, N + 1 ≤ αNat ^ (n + 1) := by
      have hαNat_one_lt : 1 < αNat := by
        dsimp [αNat]
        have hsq_pos : 0 < (m + 1) ^ 2 := by
          exact Nat.pow_pos (Nat.succ_pos m)
        omega
      have hPowSucc :
          Tendsto (fun n : ℕ ↦ αNat ^ (n + 1)) atTop atTop := by
        exact
          ((tendsto_pow_atTop_atTop_of_one_lt hαNat_one_lt :
            Tendsto (fun n : ℕ ↦ αNat ^ n) atTop atTop).comp (tendsto_add_atTop_nat 1))
      exact hPowSucc.eventually_ge_atTop (N + 1)
    filter_upwards [hLarge] with n hn
    dsimp [meshIndex]
    exact Nat.le_pred_of_lt (lt_of_lt_of_le (Nat.lt_succ_self N) hn)
  have hUpperDiscrete :
      ∀ᶠ n : ℕ in atTop, u n ≤ (2 : ℝ) := by
    have hSucc : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : NNReal)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    -- Proof comment: the same upper bound also restricts to the full integer skeleton, giving
    -- the boundedness input needed for the subsequence limsup comparison.
    simpa [u] using hSucc.eventually hUpperω
  have hFreqMesh :
      ∃ᶠ n : ℕ in atTop,
        (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤ u (meshIndex n) := by
    have hFreqMeshBase := by
      exact
        IsBrownianMotion.frequently_ge_lilRatio_geometricMesh_of_geometricIncrement
          (B := brownian) (ω := ω) hα (C := 2) (by positivity) hUpperNegω hFreqω
    -- Proof comment: because `α` is an integer-valued mesh ratio, these geometric mesh times are
    -- literal integer indices of the discrete sequence `u`.
    refine hFreqMeshBase.mono ?_
    intro n hn
    have hn' :
        (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤
          IsBrownianMotion.lilRatio brownian ω ((meshIndex n : NNReal) + 1) := by
      simpa [hMeshIndex_time_add n] using hn
    simpa [u] using hn'
  have hLimsup :
      (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤ limsup u atTop := by
    exact
      le_limsup_of_frequently_ge_subseq hMeshIndexTendsto hUpperDiscrete hFreqMesh
  have hArithmetic :
      1 - 1 / (m + 1 : ℝ) ≤
        (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) := by
    -- Proof comment: the textbook coarse mesh `α = 16 (m + 1)^2` was chosen precisely so that
    -- the geometric lower constant already dominates the target reciprocal margin.
    have hk_pos : 0 < (m + 1 : ℝ) := by
      positivity
    have hαeq : (α : ℝ) = 16 * (m + 1 : ℝ) ^ 2 := by
      simp [α, αNat, Nat.cast_mul, Nat.cast_pow]
    have hsqrt :
        Real.sqrt (16 * (m + 1 : ℝ) ^ 2) = 4 * (m + 1 : ℝ) := by
      rw [show 16 * (m + 1 : ℝ) ^ 2 = (4 * (m + 1 : ℝ)) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [hαeq, hsqrt]
    field_simp [hk_pos.ne']
    nlinarith
  have hDiscreteLimsup :
      (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤
        limsup
          (fun n : ℕ ↦
            brownian (n + 1 : NNReal) ω /
              Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
          atTop := by
    simpa [u, IsBrownianMotion.lilRatio] using hLimsup
  exact le_trans hArithmetic hDiscreteLimsup

/-- Helper for Theorem 22.11: the Brownian law of the iterated logarithm transfers from continuous
time to the integer skeleton `n ↦ brownian (n + 1)` once unit-interval oscillations are known to
be negligible. -/
private theorem samplewise_integerBrownian_limsup_le_one_add_invSucc
    {space : Type u} [MeasurableSpace space]
    (brownian : NNReal → space → ℝ) {ω : space}
    (hFullω :
      limsup
        (fun t : NNReal ↦
          brownian t ω /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop = 1)
    (hFullNegω :
      limsup
        (fun t : NNReal ↦
          (-brownian t ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop = 1)
    (m : ℕ)
    (hUpperFullω :
      limsup
        (fun t : NNReal ↦
          brownian t ω /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop ≤
          1 + 1 / (m + 1 : ℝ)) :
    limsup
        (fun n : ℕ ↦
          brownian (n + 1 : NNReal) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop
      ≤ 1 + 1 / (m + 1 : ℝ) := by
  let ratio : NNReal → ℝ := fun t ↦
    brownian t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ)))
  let ratioNeg : NNReal → ℝ := fun t ↦
    (-brownian t ω) / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ)))
  let ratioNat : ℕ → ℝ := fun n ↦
    brownian (n + 1 : NNReal) ω /
      Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))
  let τ : ℕ → NNReal := fun n ↦ (n + 1 : NNReal)
  have hτ_tendsto : Tendsto τ atTop atTop := by
    convert
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : NNReal)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)) using 1
    funext n
    simp [τ, Nat.cast_add]
  have hBoundedFull : atTop.IsBoundedUnder (· ≤ ·) ratio := by
    by_contra hNot
    have hZero : limsup ratio atTop = 0 := Real.limsup_of_not_isBoundedUnder hNot
    exact zero_ne_one (hZero.symm.trans hFullω)
  have hBoundedNeg : atTop.IsBoundedUnder (· ≤ ·) ratioNeg := by
    by_contra hNot
    have hZero : limsup ratioNeg atTop = 0 := Real.limsup_of_not_isBoundedUnder hNot
    exact zero_ne_one (hZero.symm.trans hFullNegω)
  have hEventuallyLowerSubseq :
      ∀ᶠ n : ℕ in atTop, (-2 : ℝ) ≤ ratio (τ n) := by
    have hEventuallyNeg :
        ∀ᶠ t : NNReal in atTop, ratioNeg t < (2 : ℝ) := by
      have hlt : limsup ratioNeg atTop < 2 := by
        linarith [hFullNegω]
      exact Filter.eventually_lt_of_limsup_lt hlt hBoundedNeg
    -- Proof comment: the negated Brownian LIL gives an eventual lower bound for the original
    -- ratio, and restricting along `t = n + 1` produces the coboundedness required for the
    -- subsequence limsup comparison.
    refine (hτ_tendsto.eventually hEventuallyNeg).mono ?_
    intro n hn
    have hneg : -ratio (τ n) < 2 := by
      simpa [ratioNeg, ratio, neg_div] using hn
    linarith
  have hSubseq :
      limsup (fun n : ℕ ↦ ratio (τ n)) atTop ≤
        limsup ratio atTop := by
    have hCoboundedSubseq :
        (Filter.map τ atTop).IsCoboundedUnder (· ≤ ·) ratio := by
      simpa [τ] using
        (Filter.IsCoboundedUnder.of_frequently_ge hEventuallyLowerSubseq.frequently :
          atTop.IsCoboundedUnder (· ≤ ·) (fun n ↦ ratio (τ n)))
    have hMap : limsup (fun n : ℕ ↦ ratio (τ n)) atTop = limsup ratio (Filter.map τ atTop) :=
      (limsup_comp ratio τ atTop).symm
    rw [hMap]
    exact Filter.limsup_le_limsup_of_le hτ_tendsto hCoboundedSubseq hBoundedFull
  have hSubseqNat : limsup ratioNat atTop ≤ limsup ratio atTop := by
    simpa [ratioNat, ratio, τ, Nat.cast_add] using hSubseq
  exact le_trans hSubseqNat hUpperFullω

/-- Helper for Theorem 22.11: the Brownian law of the iterated logarithm transfers from continuous
time to the integer skeleton `n ↦ brownian (n + 1)` once unit-interval oscillations are known to
be negligible. -/
private theorem ae_limsup_integerBrownian_div_sqrt_two_mul_n_log_log_eq_one
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian) :
    ∀ᵐ ω ∂(law : Measure space),
      limsup
        (fun n : ℕ ↦
          brownian (n + 1 : NNReal) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop = 1 := by
  have hFull :
      ∀ᵐ ω ∂(law : Measure space),
        limsup
          (fun t : NNReal ↦
            brownian t ω /
              Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
          atTop = 1 :=
    IsBrownianMotion.ae_limsup_div_sqrt_two_mul_t_log_log_eq_one hBrownian
  have hFullNeg :
      ∀ᵐ ω ∂(law : Measure space),
        limsup
          (fun t : NNReal ↦
            (-brownian t ω) /
              Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
          atTop = 1 :=
    IsBrownianMotion.ae_limsup_div_sqrt_two_mul_t_log_log_eq_one
      (IsBrownianMotion.neg_isBrownianMotion hBrownian)
  have hUpper :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ m : ℕ,
          limsup
              (fun n : ℕ ↦
                brownian (n + 1 : NNReal) ω /
                  Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
              atTop
            ≤ 1 + 1 / (m + 1 : ℝ) := by
    exact ae_all_iff.2 fun m ↦ by
      have hUpperFull :
          ∀ᵐ ω ∂(law : Measure space),
            limsup
              (fun t : NNReal ↦
                brownian t ω /
                  Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
              atTop ≤
                1 + 1 / (m + 1 : ℝ) :=
        IsBrownianMotion.ae_limsup_le_one_add_invSucc hBrownian m
      filter_upwards [hFull, hFullNeg, hUpperFull] with ω hFullω hFullNegω hUpperFullω
      exact
        samplewise_integerBrownian_limsup_le_one_add_invSucc
          brownian hFullω hFullNegω m hUpperFullω
  have hLower :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ m : ℕ,
          1 - 1 / (m + 1 : ℝ) ≤
            limsup
              (fun n : ℕ ↦
                brownian (n + 1 : NNReal) ω /
                  Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
              atTop := by
    -- Proof comment: the difficult part is the lower transfer from continuous time to the
    -- integer skeleton, so we isolate it in the dedicated companion theorem above.
    refine ae_all_iff.2 ?_
    intro m
    exact ae_limsup_integerBrownian_ge_one_sub_invSucc law brownian hBrownian m
  -- Proof comment: after separating the easy upper restriction from the harder lower transfer,
  -- the existing reciprocal-gap squeeze identifies the discrete Brownian limsup with `1`.
  filter_upwards [hUpper, hLower] with ω hUpperω hLowerω
  have hEqω :
      limsup
        (fun n : ℕ ↦
          brownian (n + 1 : NNReal) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop = 1 := by
    exact
      IsBrownianMotion.eq_one_of_forall_invSucc_bounds
        (x := limsup
          (fun n : ℕ ↦
            brownian (n + 1 : NNReal) ω /
              Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
          atTop)
        hUpperω hLowerω
  exact hEqω

/-- Helper for Theorem 22.11: one can choose a geometric ratio `a > 1` close enough to `1` so
that the anchored-window reflection profile carries power decay exponent larger than `2`.
-/
private theorem exists_geometricScale_exponent_gt_two
    (m : ℕ) :
    ∃ a : NNReal, 1 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
      2 < (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1)) := by
  let δ : ℝ := 1 / (224 * (m + 1 : ℝ) ^ 2)
  let a : NNReal := ⟨1 + δ, by
    have hδ_nonneg : 0 ≤ δ := by
      dsimp [δ]
      positivity
    linarith⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    -- Proof comment: the explicit choice `a = 1 + δ` is strictly larger than `1`.
    change 1 < 1 + δ
    linarith
  · have hδ_le_one : δ ≤ 1 := by
      have hden_ge_one : (1 : ℝ) ≤ 224 * (m + 1 : ℝ) ^ 2 := by
        have hm_one_le : (1 : ℝ) ≤ (m + 1 : ℝ) := by
          positivity
        have hsq_one_le : (1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by
          nlinarith
        nlinarith
      have hden_pos : 0 < 224 * (m + 1 : ℝ) ^ 2 := by
        positivity
      -- Proof comment: the denominator is at least `1`, so the perturbation `δ` is at most `1`.
      dsimp [δ]
      exact (one_div_le (show (0 : ℝ) < 1 by norm_num) hden_pos).2 hden_ge_one
    change 1 + δ ≤ 2
    linarith
  · let D : ℝ := 16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have ha_gt_one : 1 < (a : ℝ) := by
      change 1 < 1 + δ
      linarith
    have ha_le_two : (a : ℝ) ≤ 2 := by
      have hδ_le_one : δ ≤ 1 := by
        have hden_ge_one : (1 : ℝ) ≤ 224 * (m + 1 : ℝ) ^ 2 := by
          have hm_one_le : (1 : ℝ) ≤ (m + 1 : ℝ) := by
            positivity
          have hsq_one_le : (1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by
            nlinarith
          nlinarith
        have hden_pos : 0 < 224 * (m + 1 : ℝ) ^ 2 := by
          positivity
        dsimp [δ]
        exact (one_div_le (show (0 : ℝ) < 1 by norm_num) hden_pos).2 hden_ge_one
      change 1 + δ ≤ 2
      linarith
    have hCube :
        (a : ℝ) ^ 3 - 1 = δ * ((a : ℝ) ^ 2 + (a : ℝ) + 1) := by
      change (1 + δ) ^ 3 - 1 = δ * ((1 + δ) ^ 2 + (1 + δ) + 1)
      ring_nf
    have hCoeff_le : (a : ℝ) ^ 2 + (a : ℝ) + 1 ≤ 7 := by
      -- Proof comment: the auxiliary ratio was chosen in `[1, 2]`, so the cubic factor is
      -- bounded by the coarse constant `7`.
      nlinarith
    have hD_le_half : D ≤ 1 / 2 := by
      dsimp [D]
      rw [hCube]
      have hmain :
          16 * (m + 1 : ℝ) ^ 2 * (δ * ((a : ℝ) ^ 2 + (a : ℝ) + 1)) ≤
            16 * (m + 1 : ℝ) ^ 2 * (δ * 7) := by
        gcongr
      refine hmain.trans ?_
      have hEq : 16 * (m + 1 : ℝ) ^ 2 * (δ * 7) = 1 / 2 := by
        dsimp [δ]
        field_simp
        ring
      simpa [hEq]
    have hD_pos : 0 < D := by
      dsimp [D]
      positivity
    have hInv : (2 : ℝ) ≤ 1 / D := by
      have := one_div_le_one_div_of_le hD_pos hD_le_half
      simpa using this
    have hTwoLtTwoA : (2 : ℝ) < 2 * (a : ℝ) := by
      nlinarith
    have hTwoALe : 2 * (a : ℝ) ≤ (a : ℝ) * (1 / D) := by
      have ha_nonneg : 0 ≤ (a : ℝ) := by
        positivity
      have := mul_le_mul_of_nonneg_left hInv ha_nonneg
      simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using this
    -- Proof comment: since `D ≤ 1 / 2`, its reciprocal dominates `2`, and multiplying by
    -- `a > 1` upgrades the exponent beyond the quadratic threshold.
    have hFinal : (2 : ℝ) < (a : ℝ) * (1 / D) := lt_of_lt_of_le hTwoLtTwoA hTwoALe
    simpa [D, div_eq_mul_inv] using hFinal

/-- Helper for Theorem 22.11: the anchored geometric bad event on block `k` records an oscillation
larger than the reciprocal-margin threshold somewhere on `[a^k, a^(k + 3)]`. -/
private def geometricWindowBadEvent
    {space : Type u} [MeasurableSpace space]
    (brownian : NNReal → space → ℝ) (m : ℕ) (a : NNReal) (k : ℕ) : Set space :=
  {ω | ∃ t ∈ Set.Icc (a ^ k) (a ^ (k + 3)),
      (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer (a ^ (k + 1)) <
        |brownian t ω - brownian (a ^ k) ω|}

/-- Helper for Theorem 22.11: the anchored Gaussian window profile on the block
`[a ^ k, a ^ (k + 3)]` is bounded by a power of `k + 1`. -/
private theorem geometricWindowProfile_le_rpow
    (m : ℕ) {a : NNReal} (ha : 1 < (a : ℝ)) (k : ℕ)
    (hkLarge : Real.exp (Real.exp 1) < ((a ^ (k + 1) : NNReal) : ℝ)) :
    let p : ℝ := (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))
    let C : ℝ :=
      (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
        Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
        (Real.log (a : ℝ)) ^ (-p)
    let s : NNReal := a ^ (k + 1)
    let T : NNReal := a ^ (k + 3) - a ^ k
    let threshold : ℝ := (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer s
    2 * (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / threshold)) *
        Real.exp (-(threshold ^ 2) / (2 * (T : ℝ))) ≤
      C * (k + 1 : ℝ) ^ (-p) := by
  dsimp
  let p : ℝ := (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))
  let C : ℝ :=
    (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
      Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
      (Real.log (a : ℝ)) ^ (-p)
  let s : NNReal := a ^ (k + 1)
  let T : NNReal := a ^ (k + 3) - a ^ k
  let threshold : ℝ := (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer s
  have ha_pos : 0 < (a : ℝ) := lt_trans zero_lt_one ha
  have hs_eq :
      (s : ℝ) = (a : ℝ) ^ (k + 1) := by
    simp [s, NNReal.coe_pow]
  have hpow_le : a ^ k ≤ a ^ (k + 3) := by
    exact_mod_cast pow_right_mono₀ ha.le (show k ≤ k + 3 by omega)
  have hT_eq :
      (T : ℝ) = ((a : ℝ) ^ k) * (((a : ℝ) ^ 3) - 1) := by
    rw [show T = a ^ (k + 3) - a ^ k by rfl, NNReal.coe_sub hpow_le, NNReal.coe_pow,
      NNReal.coe_pow]
    ring
  have hlog_s_gt_exp : Real.exp 1 < Real.log (s : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos (Real.exp 1)) hkLarge)
  have hlog_s_pos : 0 < Real.log (s : ℝ) := lt_trans (Real.exp_pos 1) hlog_s_gt_exp
  have hloglog_s_ge_one : 1 ≤ Real.log (Real.log (s : ℝ)) := by
    have : 1 < Real.log (Real.log (s : ℝ)) := by
      simpa using (Real.log_lt_log (Real.exp_pos 1) hlog_s_gt_exp)
    exact this.le
  have hprofile_prefactor :
      2 * (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / threshold)) =
        (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
          Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
          (Real.sqrt (Real.log (Real.log (s : ℝ))))⁻¹ := by
    -- Proof comment: rewrite the window length as `a^k * (a^3 - 1)` and cancel the common
    -- `sqrt (a^(k + 1))` factor against the threshold.
    rw [hT_eq, hs_eq, threshold, IsBrownianMotion.lilNormalizer]
    have hsqrt_two_pi :
        Real.sqrt (2 * Real.pi) = Real.sqrt (2 : ℝ) * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by positivity) Real.pi]
    have hsqrt_T :
        Real.sqrt (((a : ℝ) ^ k) * (((a : ℝ) ^ 3) - 1)) =
          Real.sqrt ((a : ℝ) ^ k) * Real.sqrt (((a : ℝ) ^ 3) - 1) := by
      rw [Real.sqrt_mul (show 0 ≤ (a : ℝ) ^ k by positivity) (show 0 ≤ ((a : ℝ) ^ 3) - 1 by
        nlinarith [show (1 : ℝ) < (a : ℝ) ^ 3 by exact one_lt_pow₀ ha 3])]
    have hsqrt_inner :
        Real.sqrt (2 * ((a : ℝ) ^ (k + 1)) * Real.log (Real.log ((a : ℝ) ^ (k + 1)))) =
          Real.sqrt (2 : ℝ) * Real.sqrt ((a : ℝ) ^ (k + 1)) *
            Real.sqrt (Real.log (Real.log ((a : ℝ) ^ (k + 1)))) := by
      calc
        Real.sqrt (2 * ((a : ℝ) ^ (k + 1)) * Real.log (Real.log ((a : ℝ) ^ (k + 1))))
            = Real.sqrt ((2 : ℝ) * ((a : ℝ) ^ (k + 1))) *
                Real.sqrt (Real.log (Real.log ((a : ℝ) ^ (k + 1)))) := by
                  rw [Real.sqrt_mul
                    (show 0 ≤ (2 : ℝ) * ((a : ℝ) ^ (k + 1)) by positivity)
                    (show 0 ≤ Real.log (Real.log ((a : ℝ) ^ (k + 1))) by
                      simpa [hs_eq] using hloglog_s_ge_one)]
        _ = (Real.sqrt (2 : ℝ) * Real.sqrt ((a : ℝ) ^ (k + 1))) *
              Real.sqrt (Real.log (Real.log ((a : ℝ) ^ (k + 1)))) := by
              rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by positivity)
                (show 0 ≤ ((a : ℝ) ^ (k + 1)) by positivity)]
        _ = Real.sqrt (2 : ℝ) * Real.sqrt ((a : ℝ) ^ (k + 1)) *
              Real.sqrt (Real.log (Real.log ((a : ℝ) ^ (k + 1)))) := by ring
    have hsqrt_ratio :
        Real.sqrt (((a : ℝ) ^ k) * (((a : ℝ) ^ 3) - 1)) /
          Real.sqrt ((a : ℝ) ^ (k + 1)) =
            Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) := by
      rw [hsqrt_T]
      have hpow_succ : (a : ℝ) ^ (k + 1) = (a : ℝ) ^ k * (a : ℝ) := by
        rw [pow_succ]
      rw [hpow_succ, Real.sqrt_mul (show 0 ≤ (a : ℝ) ^ k by positivity)
        (show 0 ≤ (a : ℝ) by positivity)]
      field_simp [show Real.sqrt ((a : ℝ) ^ k) ≠ 0 by positivity,
        show Real.sqrt (a : ℝ) ≠ 0 by positivity]
      rw [Real.sq_sqrt (show 0 ≤ (a : ℝ) by positivity)]
      rw [Real.div_eq_mul_inv, Real.sqrt_eq_inv]
      ring_nf
    have hsqrt_loglog_ne :
        Real.sqrt (Real.log (Real.log ((a : ℝ) ^ (k + 1)))) ≠ 0 := by
      positivity
    rw [hsqrt_two_pi, hsqrt_inner]
    field_simp [show Real.sqrt (2 : ℝ) ≠ 0 by positivity,
      show Real.sqrt Real.pi ≠ 0 by positivity,
      show Real.sqrt ((a : ℝ) ^ (k + 1)) ≠ 0 by positivity,
      hsqrt_loglog_ne]
    rw [hsqrt_ratio]
    ring
  have hExponentArg :
      -(threshold ^ 2) / (2 * (T : ℝ)) = -p * Real.log (Real.log (s : ℝ)) := by
    -- Proof comment: the chosen threshold turns the Gaussian exponent into a constant multiple
    -- of `log log (a ^ (k + 1))`.
    rw [threshold, IsBrownianMotion.lilNormalizer, hT_eq, hs_eq]
    dsimp [p]
    rw [pow_two, Real.sq_sqrt (show 0 ≤ 2 * ((a : ℝ) ^ (k + 1)) *
      Real.log (Real.log ((a : ℝ) ^ (k + 1))) by
      positivity)]
    field_simp [ha_pos.ne', show ((a : ℝ) ^ k) ≠ 0 by positivity]
    ring
  have hExponent :
      Real.exp (-(threshold ^ 2) / (2 * (T : ℝ))) =
        (Real.log (s : ℝ)) ^ (-p) := by
    rw [hExponentArg, mul_comm, Real.exp_mul, Real.exp_log hlog_s_pos]
  have hLogPow :
      (Real.log (s : ℝ)) ^ (-p) =
        (Real.log (a : ℝ)) ^ (-p) * (k + 1 : ℝ) ^ (-p) := by
    have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos ha
    calc
      (Real.log (s : ℝ)) ^ (-p)
          = (((k + 1 : ℝ) * Real.log (a : ℝ))) ^ (-p) := by
              rw [hs_eq, Real.log_rpow ha_pos]
              ring_nf
      _ = ((Real.log (a : ℝ)) * (k + 1 : ℝ)) ^ (-p) := by ring
      _ = (Real.log (a : ℝ)) ^ (-p) * (k + 1 : ℝ) ^ (-p) := by
            rw [Real.mul_rpow hloga_pos.le (show 0 ≤ (k + 1 : ℝ) by positivity)]
  have hInvSqrt_le_one :
      (Real.sqrt (Real.log (Real.log (s : ℝ))))⁻¹ ≤ 1 := by
    have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (s : ℝ))) := by
      exact (Real.one_le_sqrt).2 hloglog_s_ge_one
    have hsqrt_pos : 0 < Real.sqrt (Real.log (Real.log (s : ℝ))) := by
      positivity
    exact (inv_le_one₀ hsqrt_pos).2 hsqrt_ge_one
  have hRpow_nonneg : 0 ≤ (Real.log (s : ℝ)) ^ (-p) := by
    exact Real.rpow_nonneg hlog_s_pos.le _
  calc
    2 * (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / threshold)) *
        Real.exp (-(threshold ^ 2) / (2 * (T : ℝ)))
        =
      ((((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
          Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
          (Real.sqrt (Real.log (Real.log (s : ℝ))))⁻¹) *
        (Real.log (s : ℝ)) ^ (-p) := by
            rw [hprofile_prefactor, hExponent]
            ring
    _ ≤
      ((((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
          Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ))) *
        (Real.log (s : ℝ)) ^ (-p) := by
          have :
              (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
                  Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
                  (Real.sqrt (Real.log (Real.log (s : ℝ))))⁻¹
                ≤
                (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
                  Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) * 1 := by
                gcongr
          simpa using mul_le_mul_of_nonneg_right this hRpow_nonneg
    _ = C * (k + 1 : ℝ) ^ (-p) := by
          dsimp [C]
          rw [hLogPow]
          ring

/-- Helper for Theorem 22.11: the anchored geometric bad-event family has an eventual `k^(-p)`
majorant once the geometric ratio `a` is fixed. -/
private theorem geometricWindowBadEvent_measureReal_eventually_le_rpow
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (m : ℕ) {a : NNReal} (ha : 1 < (a : ℝ)) :
    let p : ℝ := (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))
    ∃ C > 0, ∀ᶠ k : ℕ in atTop,
      (law : Measure space).real (geometricWindowBadEvent brownian m a k) ≤
        C * (k + 1 : ℝ) ^ (-p) := by
  let p : ℝ := (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))
  let C : ℝ :=
    (((8 : ℝ) * (m + 1 : ℝ)) / Real.sqrt Real.pi) *
      Real.sqrt (((a : ℝ) ^ 3 - 1) / (a : ℝ)) *
      (Real.log (a : ℝ)) ^ (-p)
  refine ⟨C, ?_, ?_⟩
  · have hp_pos : 0 < p := by
      dsimp [p]
      positivity
    have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos ha
    dsimp [C]
    positivity
  · have hPowTendsto :
        Tendsto (fun k : ℕ ↦ ((a ^ (k + 1) : NNReal) : ℝ)) atTop atTop := by
      simpa [NNReal.coe_pow] using
        ((tendsto_pow_atTop_atTop_of_one_lt ha : Tendsto (fun k : ℕ ↦ (a : ℝ) ^ k) atTop atTop)).comp
          (tendsto_add_atTop_nat 1)
    have hEventuallyLarge :
        ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp 1) < ((a ^ (k + 1) : NNReal) : ℝ) := by
      exact hPowTendsto.eventually_gt_atTop (Real.exp (Real.exp 1))
    filter_upwards [hEventuallyLarge] with k hkLarge
    let s : NNReal := a ^ (k + 1)
    let T : NNReal := a ^ (k + 3) - a ^ k
    let threshold : ℝ := (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer s
    have ha_pos : 0 < (a : ℝ) := lt_trans zero_lt_one ha
    have hs_large : Real.exp 1 < (s : ℝ) := by
      exact
        lt_trans
          (by simpa using (Real.one_lt_exp_iff.2 (Real.exp_pos 1)))
          hkLarge
    have hs_pos : 0 < (s : ℝ) := by
      exact
        lt_trans Real.zero_lt_one
          (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) hs_large)
    have hthreshold_pos : 0 < threshold := by
      -- Proof comment: the block threshold is a positive scalar multiple of the positive
      -- normalizer at time `a^(k + 1)`.
      dsimp [threshold]
      exact mul_pos (by positivity) (lilNormalizer_pos_of_exp_one_lt hs_large)
    have hpow_le : a ^ k ≤ a ^ (k + 3) := by
      exact_mod_cast pow_right_mono₀ ha.le (show k ≤ k + 3 by omega)
    have hT_pos : 0 < T := by
      have hpow_lt :
          ((a ^ k : NNReal) : ℝ) < ((a ^ (k + 3) : NNReal) : ℝ) := by
        simpa [NNReal.coe_pow] using pow_lt_pow_right₀ ha (show k < k + 3 by omega)
      have hT_real_pos : 0 < (T : ℝ) := by
        simpa [T, NNReal.coe_sub hpow_le] using sub_pos.mpr hpow_lt
      exact_mod_cast hT_real_pos
    have hReflect :=
      anchoredAbsIncrement_measureReal_le_profile
        law hBrownian (s := a ^ k) (T := T) (a := threshold) hthreshold_pos hT_pos
    have hProfile_le :
        2 * (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / threshold)) *
            Real.exp (-(threshold ^ 2) / (2 * (T : ℝ))) ≤
          C * (k + 1 : ℝ) ^ (-p) := by
      simpa [p, C, s, T, threshold] using
        geometricWindowProfile_le_rpow (m := m) ha k hkLarge
    exact hReflect.trans hProfile_le

/-- Helper for Theorem 22.11: the anchored geometric bad-event family is summable for the chosen
geometric ratio `a`. -/
private theorem summable_geometricWindowBadEvent_measureReal
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (m : ℕ) {a : NNReal} (ha : 1 < (a : ℝ))
    (hExponent_gt_one :
      1 < (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))) :
    Summable (fun k : ℕ ↦ (law : Measure space).real (geometricWindowBadEvent brownian m a k)) := by
  let p : ℝ := (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1))
  rcases geometricWindowBadEvent_measureReal_eventually_le_rpow law brownian hBrownian m ha with
    ⟨C, hC_pos, hTail⟩
  rcases Filter.eventually_atTop.1 hTail with ⟨N, hN⟩
  have hSeries :
      Summable (fun k : ℕ ↦ C * (k + 1 : ℝ) ^ (-p)) := by
    have hBase :
        Summable (fun k : ℕ ↦ C * (k : ℝ) ^ (-p)) := by
      refine (Real.summable_nat_rpow.mpr ?_).mul_left C
      simpa [p] using hExponent_gt_one
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm, p] using
      ((_root_.summable_nat_add_iff 1).2 hBase)
  have hSeriesShift :
      Summable (fun k : ℕ ↦ C * (k + N + 1 : ℝ) ^ (-p)) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm, p] using
      ((_root_.summable_nat_add_iff N).2 hSeries)
  have hShift :
      Summable
        (fun k : ℕ ↦ (law : Measure space).real (geometricWindowBadEvent brownian m a (k + N))) := by
    refine Summable.of_nonneg_of_le (fun k ↦ ENNReal.toReal_nonneg) ?_ hSeriesShift
    intro k
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm, p] using
      hN (k + N) (Nat.le_add_left N k)
  exact (_root_.summable_nat_add_iff N).1 hShift

/-- Helper for Theorem 22.11: a middle-block membership plus the tail inequality
`a^(K + 2) ≤ n + 1` forces the block index to satisfy `K ≤ k`. -/
private theorem geometricMiddleBlock_index_ge_of_powTail
    {a : NNReal} (ha : 1 < (a : ℝ)) {K n k : ℕ}
    (hnTailLarge : ((a ^ (K + 2) : NNReal) : ℝ) ≤ (n + 1 : ℝ))
    (hkBlock : (n + 1 : NNReal) ∈ Set.Icc (a ^ (k + 1)) (a ^ (k + 2))) :
    K ≤ k := by
  -- Proof comment: if `k < K`, then monotonicity of the geometric mesh would force
  -- `a^(K + 2) ≤ a^(k + 2)`, contradicting strict growth of powers for `a > 1`.
  by_contra hkNot
  have hk_lt : k < K := lt_of_not_ge hkNot
  have hpow_lt :
      ((a : ℝ) ^ (k + 2)) < ((a : ℝ) ^ (K + 2)) := by
    exact pow_lt_pow_right₀ ha (show k + 2 < K + 2 by omega)
  have hpow_le :
      ((a : ℝ) ^ (K + 2)) ≤ ((a : ℝ) ^ (k + 2)) := by
    exact le_trans hnTailLarge (by exact_mod_cast hkBlock.2)
  exact (not_le_of_gt hpow_lt) hpow_le

/-- Helper for Theorem 22.11: if the embedded time lies in the relative window around `n + 1`
and `n + 1` is in the middle geometric block, then both times lie in the longer block
`[a^k, a^(k + 3)]`. -/
private theorem relativeWindow_mem_longGeometricBlock
    {space : Type u} [MeasurableSpace space]
    (stoppingTime : ℕ → space → NNReal) {ω : space} {a : NNReal}
    (ha : 1 < (a : ℝ)) {n k : ℕ}
    (hnRelative :
      (1 / (a : ℝ)) * (n + 1 : ℝ) ≤ (stoppingTime (n + 1) ω : ℝ) ∧
        (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) * (n + 1 : ℝ))
    (hkBlock : (n + 1 : NNReal) ∈ Set.Icc (a ^ (k + 1)) (a ^ (k + 2))) :
    (n + 1 : NNReal) ∈ Set.Icc (a ^ k) (a ^ (k + 3)) ∧
      stoppingTime (n + 1) ω ∈ Set.Icc (a ^ k) (a ^ (k + 3)) := by
  have ha_pos : 0 < (a : ℝ) := lt_trans zero_lt_one ha
  have hk_to_left :
      (a : ℝ) ^ k ≤ (1 / (a : ℝ)) * (n + 1 : ℝ) := by
    have hkLower_real : ((a ^ (k + 1) : NNReal) : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast hkBlock.1
    calc
      (a : ℝ) ^ k = (1 / (a : ℝ)) * ((a : ℝ) ^ (k + 1)) := by
        rw [pow_succ']
        field_simp [ha_pos.ne']
        ring
      _ ≤ (1 / (a : ℝ)) * (n + 1 : ℝ) := by
        gcongr
  have hk_tau_lower : (a : ℝ) ^ k ≤ (stoppingTime (n + 1) ω : ℝ) := by
    exact hk_to_left.trans hnRelative.1
  have hk_tau_upper : (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) ^ (k + 3) := by
    calc
      (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) * (n + 1 : ℝ) := hnRelative.2
      _ ≤ (a : ℝ) * ((a ^ (k + 2) : NNReal) : ℝ) := by
        gcongr
        exact_mod_cast hkBlock.2
      _ = (a : ℝ) ^ (k + 3) := by
          rw [NNReal.coe_pow, pow_succ']
          ring
  have hk_det_mem : (n + 1 : NNReal) ∈ Set.Icc (a ^ k) (a ^ (k + 3)) := by
    constructor
    · have hkLower :
          ((a ^ k : NNReal) : ℝ) ≤ ((a ^ (k + 1) : NNReal) : ℝ) := by
        exact_mod_cast pow_right_mono₀ ha.le (show k ≤ k + 1 by omega)
      exact_mod_cast le_trans hkLower (by exact_mod_cast hkBlock.1)
    · have hkUpper :
          ((a ^ (k + 2) : NNReal) : ℝ) ≤ ((a ^ (k + 3) : NNReal) : ℝ) := by
        exact_mod_cast pow_right_mono₀ ha.le (show k + 2 ≤ k + 3 by omega)
      exact_mod_cast le_trans (by exact_mod_cast hkBlock.2) hkUpper
  have hk_tau_mem : stoppingTime (n + 1) ω ∈ Set.Icc (a ^ k) (a ^ (k + 3)) := by
    -- Proof comment: after transporting the relative-window bounds to the geometric mesh,
    -- both endpoints are available as `NNReal` interval membership facts.
    constructor <;> exact_mod_cast ‹_›
  exact ⟨hk_det_mem, hk_tau_mem⟩

/-- Helper for Theorem 22.11: outside the anchored bad event, every point in the long geometric
block satisfies the threshold oscillation bound. -/
private theorem geometricWindowBadEvent_compl_le_threshold
    {space : Type u} [MeasurableSpace space]
    (brownian : NNReal → space → ℝ) (m : ℕ) {a : NNReal} {k : ℕ} {ω : space}
    (hkBad : ω ∉ geometricWindowBadEvent brownian m a k) :
    ∀ {t : NNReal}, t ∈ Set.Icc (a ^ k) (a ^ (k + 3)) →
      |brownian t ω - brownian (a ^ k) ω| ≤
        (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer (a ^ (k + 1)) := by
  intro t ht
  -- Proof comment: the complement of `geometricWindowBadEvent` is exactly the universal
  -- threshold bound over the long block `[a^k, a^(k + 3)]`.
  by_contra hgt
  exact hkBad ⟨t, ht, lt_of_not_ge hgt⟩

/-- Helper for Theorem 22.11: once the deterministic time `n + 1` and the embedded time
`τ (n + 1)` lie in the same long geometric block, the bad-event complement gives the raw Brownian
window error bound at scale `(m + 1)⁻¹`. -/
private theorem sameBlock_stoppedBrownian_rawError_le_invSucc
    {space : Type u} [MeasurableSpace space]
    (brownian : NNReal → space → ℝ) (stoppingTime : ℕ → space → NNReal)
    (m : ℕ) {ω : space} {a : NNReal} (ha : 1 < (a : ℝ)) {n k : ℕ}
    (hkLarge : Real.exp (Real.exp 1) < ((a ^ (k + 1) : NNReal) : ℝ))
    (hnRelative :
      (1 / (a : ℝ)) * (n + 1 : ℝ) ≤ (stoppingTime (n + 1) ω : ℝ) ∧
        (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) * (n + 1 : ℝ))
    (hkBlock : (n + 1 : NNReal) ∈ Set.Icc (a ^ (k + 1)) (a ^ (k + 2)))
    (hkBad : ω ∉ geometricWindowBadEvent brownian m a k) :
    |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| ≤
      (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
  have hk_large_exp_one : Real.exp 1 < ((a ^ (k + 1) : NNReal) : ℝ) := by
    exact
      lt_trans
        (by simpa using (Real.one_lt_exp_iff.2 (Real.exp_pos 1)))
        hkLarge
  let threshold : ℝ :=
    (1 / (4 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer (a ^ (k + 1))
  rcases relativeWindow_mem_longGeometricBlock stoppingTime ha hnRelative hkBlock with
    ⟨hk_det_mem, hk_tau_mem⟩
  have hGood :=
    geometricWindowBadEvent_compl_le_threshold brownian m hkBad
  have hTauBound :
      |brownian (stoppingTime (n + 1) ω) ω - brownian (a ^ k) ω| ≤ threshold := by
    simpa [threshold] using hGood hk_tau_mem
  have hDetBound :
      |brownian (n + 1 : NNReal) ω - brownian (a ^ k) ω| ≤ threshold := by
    simpa [threshold] using hGood hk_det_mem
  have hTriangle :
      |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| ≤
        threshold + threshold := by
    refine le_trans (abs_sub_le _ _ _) ?_
    simpa [abs_sub_comm] using add_le_add hTauBound hDetBound
  have hNormalizerMono :
      IsBrownianMotion.lilNormalizer (a ^ (k + 1)) ≤
        IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
    -- Proof comment: the middle-block lower bound places `a^(k + 1)` before `n + 1`,
    -- so monotonicity transfers the local block normalizer to the target normalizer.
    exact lilNormalizer_le_of_le_of_exp_one_lt hk_large_exp_one hkBlock.1
  have hThreshold_le :
      threshold + threshold ≤
        (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
    calc
      threshold + threshold
          = (1 / (2 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer (a ^ (k + 1)) := by
              dsimp [threshold]
              ring
      _ ≤ (1 / (2 * (m + 1 : ℝ))) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
            gcongr
      _ ≤ (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
            positivity
  -- Proof comment: both times are controlled relative to the same anchor `a^k`, so one
  -- triangle inequality plus normalizer monotonicity closes the comparison.
  exact hTriangle.trans hThreshold_le

/-- Helper for Theorem 22.11: a raw comparison between the stopped Brownian path and the
deterministic integer skeleton should be proved before dividing by the LIL normalizer. -/
private theorem ae_eventually_stoppedBrownian_integerWindowError_le_invSucc
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (stoppingTime : ℕ → space → NNReal)
    (hTimeLLN :
      ∀ᵐ ω ∂(law : Measure space),
        Tendsto (fun n : ℕ ↦ (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ)) atTop (nhds 1))
    (m : ℕ) :
    ∀ᵐ ω ∂(law : Measure space),
      ∀ᶠ n : ℕ in atTop,
        |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| ≤
          (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) := by
  obtain ⟨a, ha, ha_le_two, hExponent⟩ := exists_geometricScale_exponent_gt_two m
  have hRelativeWindow :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ n : ℕ in atTop,
          (1 / (a : ℝ)) * (n + 1 : ℝ) ≤ (stoppingTime (n + 1) ω : ℝ) ∧
            (stoppingTime (n + 1) ω : ℝ) ≤ (a : ℝ) * (n + 1 : ℝ) := by
    -- Proof comment: the strong law for the embedding times already packages the relative-window
    -- control once the geometric ratio `a > 1` is fixed.
    filter_upwards [hTimeLLN] with ω hω
    exact eventually_stoppingTime_mem_relativeWindow stoppingTime ha hω
  -- Route correction: the missing part is no longer the deterministic ratio choice. The remaining
  -- work is to turn `anchoredAbsIncrement_measureReal_le_profile` into a summable same-block bad
  -- event family for this `a`, apply Borel-Cantelli, and then combine that block control with
  -- `hRelativeWindow` and `exists_mem_geometricMiddleBlock`.
  have hExponent_gt_one :
      1 < (a : ℝ) / (16 * (m + 1 : ℝ) ^ 2 * ((a : ℝ) ^ 3 - 1)) :=
    lt_trans one_lt_two hExponent
  have hSummable :
      Summable (fun k : ℕ ↦ (law : Measure space).real (geometricWindowBadEvent brownian m a k)) :=
    summable_geometricWindowBadEvent_measureReal
      law brownian hBrownian m ha hExponent_gt_one
  have hAvoid :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ k : ℕ in atTop, ω ∉ geometricWindowBadEvent brownian m a k := by
    exact ae_eventually_notMem_of_summable_measureReal law hSummable
  have hPowLarge :
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp 1) < ((a ^ (k + 1) : NNReal) : ℝ) := by
    have hPowTendsto :
        Tendsto (fun k : ℕ ↦ ((a ^ (k + 1) : NNReal) : ℝ)) atTop atTop := by
      simpa [NNReal.coe_pow] using
        ((tendsto_pow_atTop_atTop_of_one_lt ha : Tendsto (fun k : ℕ ↦ (a : ℝ) ^ k) atTop atTop)).comp
          (tendsto_add_atTop_nat 1)
    exact hPowTendsto.eventually_gt_atTop (Real.exp (Real.exp 1))
  filter_upwards [hRelativeWindow, hAvoid] with ω hRelativeWindowω hAvoidω
  rcases Filter.eventually_atTop.1 hAvoidω with ⟨Kbad, hKbad⟩
  rcases Filter.eventually_atTop.1 hPowLarge with ⟨Klarge, hKlarge⟩
  let K := max Kbad Klarge
  have hNat :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    convert
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)) using 1
    funext n
    simp [Nat.cast_add]
  have hTailLarge :
      ∀ᶠ n : ℕ in atTop, ((a ^ (K + 2) : NNReal) : ℝ) ≤ (n + 1 : ℝ) := by
    exact hNat.eventually_ge_atTop ((a ^ (K + 2) : NNReal) : ℝ)
  refine (hRelativeWindowω.and hTailLarge.and Ici_mem_atTop (1 : ℕ)).mono ?_
  intro n hn
  rcases hn with ⟨hnRelative, hnTailLarge, hnOne⟩
  have hn_ge_a : (a : ℝ) ≤ (n + 1 : ℝ) := by
    have : (a : ℝ) ≤ 2 := ha_le_two
    linarith
  rcases exists_mem_geometricMiddleBlock (a := a) ha (t := (n + 1 : NNReal))
      (by exact_mod_cast hn_ge_a) with ⟨k, hkBlock⟩
  have hk_ge_K : K ≤ k := by
    -- Proof comment: the growth tail `a^(K + 2) ≤ n + 1` and the chosen middle block together
    -- force the block index to lie beyond the bad-event and largeness tails.
    exact geometricMiddleBlock_index_ge_of_powTail ha hnTailLarge hkBlock
  have hk_bad : ω ∉ geometricWindowBadEvent brownian m a k := by
    exact hKbad k (le_trans (le_max_left _ _) hk_ge_K)
  have hk_large : Real.exp (Real.exp 1) < ((a ^ (k + 1) : NNReal) : ℝ) := by
    exact hKlarge k (le_trans (le_max_right _ _) hk_ge_K)
  -- Proof comment: after extracting the tail index and the block membership, the remaining
  -- work is the deterministic same-block comparison packaged in one helper.
  exact
    sameBlock_stoppedBrownian_rawError_le_invSucc brownian stoppingTime m ha hk_large
      hnRelative hkBlock hk_bad

/-- Helper for Theorem 22.11: once the embedded stopping times satisfy
`stoppingTime (n + 1) / (n + 1) → 1` almost surely, the stopped Brownian integer skeleton differs
from the deterministic integer skeleton by an eventually negligible normalized error.
-/
private theorem ae_eventually_stoppedBrownian_discreteRatioError_le_invSucc
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (stoppingTime : ℕ → space → NNReal)
    (hTimeLLN :
      ∀ᵐ ω ∂(law : Measure space),
        Tendsto (fun n : ℕ ↦ (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ)) atTop (nhds 1))
    (m : ℕ) :
    ∀ᵐ ω ∂(law : Measure space),
      ∀ᶠ n : ℕ in atTop,
        |brownian (stoppingTime (n + 1) ω) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) -
          brownian (n + 1 : NNReal) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))| ≤
          1 / (m + 1 : ℝ) := by
  have hWindow :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ᶠ n : ℕ in atTop,
          |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| ≤
            (1 / (m + 1 : ℝ)) * IsBrownianMotion.lilNormalizer (n + 1 : NNReal) :=
    ae_eventually_stoppedBrownian_integerWindowError_le_invSucc
      law brownian hBrownian stoppingTime hTimeLLN m
  have hEventuallyLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp 1 < (n + 1 : ℝ) := by
    have hNat :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      convert
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)) using 1
      funext n
      simp [Nat.cast_add]
    exact hNat.eventually_gt_atTop (Real.exp 1)
  filter_upwards [hWindow, hEventuallyLarge] with ω hWindowω hLarge
  refine hWindowω.mono ?_
  intro n hnWindow
  have hlog_gt_one : 1 < Real.log (n + 1 : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hLarge)
  have hloglog_pos : 0 < Real.log (Real.log (n + 1 : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hden_pos :
      0 < Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) := by
    apply Real.sqrt_pos.2
    positivity
  have hdiv :
      |brownian (stoppingTime (n + 1) ω) ω /
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) -
        brownian (n + 1 : NNReal) ω /
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))| =
        |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| /
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) := by
    -- Proof comment: after pulling the common denominator out of the difference, the normalized
    -- error is exactly the raw numerator error divided by the positive LIL normalizer.
    rw [sub_div, abs_div, abs_of_pos hden_pos]
  rw [hdiv]
  have hle :
      |brownian (stoppingTime (n + 1) ω) ω - brownian (n + 1 : NNReal) ω| /
          Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) ≤
        1 / (m + 1 : ℝ) := by
    refine (div_le_iff₀ hden_pos).2 ?_
    simpa [IsBrownianMotion.lilNormalizer] using hnWindow
  exact hle

/-- Helper for Theorem 22.11: once the textbook walk is realized as a Brownian motion sampled at
stopping times whose iid increments have mean `1`, the normalized stopped Brownian coordinates have
almost-sure limsup `1`.
-/
private theorem ae_limsup_embeddedBrownian_div_sqrt_two_mul_n_log_log_eq_one
    {space : Type u} [MeasurableSpace space]
    (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
    (hBrownian : IsBrownianMotion (law : Measure space) brownian)
    (stoppingTime : ℕ → space → NNReal)
    (hτ0 : stoppingTime 0 = 0)
    (hτmono : Monotone stoppingTime)
    (hτIID :
      IsIID (fun n ω ↦ stoppingTime (n + 1) ω - stoppingTime n ω) (law : Measure space))
    (hτmean : (law : Measure space)[fun ω ↦ (stoppingTime 1 ω : ℝ)] = 1) :
    ∀ᵐ ω ∂(law : Measure space),
      limsup
        (fun n : ℕ ↦
          brownian (stoppingTime (n + 1) ω) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop = 1 := by
  -- Route correction: the previous proof attempt tried to compare the stopped process directly to
  -- the continuous-time Brownian LIL. The stable first bridge is the strong law
  -- `stoppingTime (n + 1) / (n + 1) → 1`, proved separately above.
  have hTimeLLN :
      ∀ᵐ ω ∂(law : Measure space),
        Tendsto (fun n : ℕ ↦ (stoppingTime (n + 1) ω : ℝ) / (n + 1 : ℝ)) atTop (nhds 1) :=
    ae_tendsto_embeddingTime_div_nat_one law stoppingTime hτ0 hτmono hτIID hτmean
  have hInteger :
      ∀ᵐ ω ∂(law : Measure space),
        limsup
          (fun n : ℕ ↦
            brownian (n + 1 : NNReal) ω /
              Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
          atTop = 1 :=
    ae_limsup_integerBrownian_div_sqrt_two_mul_n_log_log_eq_one
      law brownian hBrownian
  have hError :
      ∀ᵐ ω ∂(law : Measure space),
        ∀ m : ℕ,
          ∀ᶠ n : ℕ in atTop,
            |brownian (stoppingTime (n + 1) ω) ω /
                Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))) -
              brownian (n + 1 : NNReal) ω /
                Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ)))| ≤
              1 / (m + 1 : ℝ) := by
    -- Proof comment: package the fixed-`m` normalized window-error bounds onto one almost-sure
    -- set with `ae_all_iff`, so the deterministic limsup squeeze can consume them directly.
    exact ae_all_iff.2
      (fun m ↦
        ae_eventually_stoppedBrownian_discreteRatioError_le_invSucc
          law brownian hBrownian stoppingTime hTimeLLN m)
  -- Proof comment: the theorem now reduces to the deterministic squeeze helper: the Brownian
  -- integer skeleton provides the comparison sequence with limsup `1`, and the stopped-time
  -- process is eventually within every reciprocal envelope of that comparison sequence.
  filter_upwards [hInteger, hError] with ω hIntegerω hErrorω
  exact
    samplewise_embeddedLimsup_eq_one_of_discreteLIL_and_windowError
      hIntegerω hErrorω

-- Proof sketch: apply Corollary 22.7 to realize the chapter's canonical textbook-indexed
-- partial-sum process `n ↦ partialSum (fun k ↦ X (k + 1)) n` as a stopped Brownian motion with iid
-- time increments of mean `1`, use the Brownian law of the iterated logarithm from Theorem 22.1,
-- and compare the random times with deterministic time via the strong law of large numbers for the
-- stopping-time increments.
/-- Theorem 22.11: Hartman--Wintner's law of the iterated logarithm. If `X₁, X₂, …` are iid real
random variables with mean `0` and variance `1`, then the normalized textbook partial sums
`Sₙ = partialSum (fun k ↦ X (k + 1)) n` satisfy `limsup Sₙ / sqrt(2 n log log n) = 1` almost
surely. -/
theorem ae_limsup_textbookPartialSum_div_sqrt_two_mul_n_log_log_eq_one
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : Var[X 1; P] = 1) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          S (n + 1) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop = 1 := by
  sorry

end HartmanWintner

end ProbabilityTheory
