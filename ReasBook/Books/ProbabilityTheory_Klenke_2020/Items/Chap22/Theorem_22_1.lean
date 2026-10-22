/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19Core
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Lemma_22_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12

open Filter MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/-- Helper for Theorem 22.1: the law-of-the-iterated-logarithm normalizer
`√(2 t log log t)`. -/
noncomputable abbrev lilNormalizer (t : NNReal) : ℝ :=
  Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ)))

/-- Helper for Theorem 22.1: the normalized Brownian coordinate used in the global LIL. -/
noncomputable abbrev lilRatio (B : NNReal → Ω → ℝ) (ω : Ω) (t : NNReal) : ℝ :=
  B t ω / lilNormalizer t

/-- Helper for Theorem 22.1: the geometric mesh `tₙ = αⁿ` used in both one-sided LIL arguments. -/
private def geometricMesh (α : NNReal) : ℕ → NNReal := fun n ↦ α ^ n

/-- Helper for Theorem 22.1: the upper-half bad event on the `n`th geometric block. -/
private def geometricUpperBlock
    (B : NNReal → Ω → ℝ) (α : NNReal) (n : ℕ) : Set Ω :=
  {ω | ∃ t ∈ Set.Icc (geometricMesh α n) (geometricMesh α (n + 1)),
      (α : ℝ) * lilNormalizer (geometricMesh α n) < B t ω}

/-- Helper for Theorem 22.1: the lower-half increment event on the `n`th geometric block. -/
private def geometricIncrementEvent
    (B : NNReal → Ω → ℝ) (α : NNReal) (n : ℕ) : Set Ω :=
  let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
  let τ := geometricMesh α
  {ω | (1 / β) * lilNormalizer (τ (n + 1)) ≤ B (τ (n + 1)) ω - B (τ n) ω}

/-- Helper for Theorem 22.1: summable real-valued event masses imply almost-sure eventual
avoidance by the first Borel--Cantelli lemma. -/
private lemma ae_eventually_notMem_of_summable_measureReal
    (P : Measure Ω) [IsProbabilityMeasure P] {s : ℕ → Set Ω}
    (hs : Summable (fun n : ℕ ↦ (P (s n)).toReal)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ s n := by
  have htsum : (∑' n, P (s n)) ≠ ⊤ := by
    -- Proof comment: summability of the real masses lifts to finiteness of the ENNReal series.
    simpa [ENNReal.ofReal_toReal, measure_ne_top] using hs.tsum_ofReal_ne_top
  exact MeasureTheory.ae_eventually_notMem htsum

/-- Helper for Theorem 22.1: if independent measurable events have non-summable real masses, then
their limsup event has full measure by the second Borel--Cantelli lemma. -/
private lemma ae_mem_limsup_of_notSummable_measureReal
    (P : Measure Ω) [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    (hE_meas : ∀ n, MeasurableSet (E n)) (hE_indep : iIndepSet E P)
    (hE_notSummable : ¬ Summable (fun n : ℕ ↦ P.real (E n))) :
    ∀ᵐ ω ∂P, ω ∈ Filter.limsup E atTop := by
  have hE_tsum : (∑' n : ℕ, P (E n)) = ⊤ := by
    apply not_not.mp
    intro hE_tsum
    -- Proof comment: a finite ENNReal series would make the real masses summable, contradicting
    -- the assumed harmonic-size lower bound route.
    exact hE_notSummable <| by
      simpa [Measure.real_def] using (ENNReal.summable_toReal hE_tsum)
  have hLimsup_one : P (Filter.limsup E atTop) = 1 := by
    simpa using
      ProbabilityTheory.measure_limsup_eq_one (μ := P) (s := E) hE_meas hE_indep hE_tsum
  have hLimsup_meas : MeasurableSet (Filter.limsup E atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n =>
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hE_meas m
  rw [ae_iff]
  have hcompl : P ((Filter.limsup E atTop)ᶜ) = 0 := by
    rw [measure_compl hLimsup_meas (measure_ne_top P _), hLimsup_one, measure_univ]
    simp
  simpa [Set.setOf_mem_eq] using hcompl

/-- Helper for Theorem 22.1: the geometric mesh `αⁿ` is monotone once `α > 1`. -/
private lemma geometricMesh_monotone
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    Monotone (geometricMesh α) := by
  intro i j hij
  exact_mod_cast pow_right_mono₀ hα.le hij

/-- Helper for Theorem 22.1: negating a Brownian motion preserves the Brownian-motion structure. -/
lemma neg_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (fun t ω ↦ -B t ω) := by
  -- Route correction: the scaling route is wrong here because scaling by `-1` changes neither the
  -- Brownian time mesh nor the target process definitionally. The stable bridge is the direct
  -- fieldwise proof on the Brownian structure.
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the time-zero value remains `0` after pointwise negation.
    funext ω
    simp [hB.zero]
  · -- Proof comment: independent increments transport through the measurable negation map.
    simpa using hB.indepIncrements.neg
  · intro r s t
    -- Proof comment: each translated increment of `-B` is the negation of the corresponding
    -- increment of `B`, so stationary increments are preserved.
    convert (hB.stationaryIncrements r s t).comp measurable_neg using 1
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under negation.
    simpa using ProbabilityTheory.gaussianReal_neg (hB.gaussian_marginal ht)
  · -- Proof comment: pointwise negation preserves continuity of every sample path.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.neg

/-- Helper for Theorem 22.1: if a real number lies between `1 ± 1 / (m + 1)` for every `m`,
then it equals `1`. -/
lemma eq_one_of_forall_invSucc_bounds {x : ℝ}
    (hupper : ∀ m : ℕ, x ≤ 1 + 1 / (m + 1 : ℝ))
    (hlower : ∀ m : ℕ, 1 - 1 / (m + 1 : ℝ) ≤ x) :
    x = 1 := by
  -- Proof comment: strict separation from `1` would leave a positive gap, and some reciprocal
  -- `1 / (m + 1)` is eventually smaller than that gap.
  apply le_antisymm
  · by_contra hx
    have hxGap : 0 < x - 1 := sub_pos.mpr (lt_of_not_ge hx)
    rcases exists_nat_one_div_lt hxGap with ⟨m, hm⟩
    have hupperm := hupper m
    have hbound : x - 1 ≤ 1 / (m + 1 : ℝ) := by
      linarith
    exact (not_le_of_gt hm) hbound
  · by_contra hx
    have hxGap : 0 < 1 - x := sub_pos.mpr (lt_of_not_ge hx)
    rcases exists_nat_one_div_lt hxGap with ⟨m, hm⟩
    have hlowerm := hlower m
    have hbound : 1 - x ≤ 1 / (m + 1 : ℝ) := by
      linarith
    exact (not_le_of_gt hm) hbound

/-- Helper for Theorem 22.1: on a geometric grid `τ n = α ^ n` with `α > 1`, the law-of-the-
iterated-logarithm normalizer grows by at least the expected `sqrt α` factor eventually. -/
lemma eventually_geometricNormalizer_ratio_le_invSqrt
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    let τ : ℕ → NNReal := geometricMesh α
    ∀ᶠ n in atTop, lilNormalizer (τ n) ≤ (1 / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1)) := by
  let τ : ℕ → NNReal := geometricMesh α
  have hτ_tendsto :
      Tendsto (fun n : ℕ ↦ ((τ n : NNReal) : ℝ)) atTop atTop := by
    simpa [τ, geometricMesh] using
      (tendsto_pow_atTop_atTop_of_one_lt hα : Tendsto (fun n : ℕ ↦ (α : ℝ) ^ n) atTop atTop)
  have hEventuallyLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp 1 < ((τ n : NNReal) : ℝ) := by
    exact hτ_tendsto.eventually_gt_atTop (Real.exp 1)
  have hτ_mono : Monotone τ := by
    simpa [τ] using geometricMesh_monotone hα
  filter_upwards [hEventuallyLarge] with n hnLarge
  have hτ_le : τ n ≤ τ (n + 1) := hτ_mono (Nat.le_succ n)
  have hnLargeNext : Real.exp 1 < ((τ (n + 1) : NNReal) : ℝ) := by
    exact lt_of_lt_of_le hnLarge (by exact_mod_cast hτ_le)
  have hτ_real_pos : 0 < ((τ n : NNReal) : ℝ) := by
    exact lt_trans Real.zero_lt_one
      (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) hnLarge)
  have hsqrtα_pos : 0 < Real.sqrt (α : ℝ) := by
    positivity
  have hloglog_pos :
      0 < Real.log (Real.log ((τ n : NNReal) : ℝ)) := by
    have hlog_gt_one : 1 < Real.log ((τ n : NNReal) : ℝ) := by
      simpa using (Real.log_lt_log (Real.exp_pos 1) hnLarge)
    exact Real.log_pos hlog_gt_one
  have hloglog_mono :
      Real.log (Real.log ((τ n : NNReal) : ℝ)) ≤
        Real.log (Real.log ((τ (n + 1) : NNReal) : ℝ)) := by
    have hlog_gt_one : 1 < Real.log ((τ n : NNReal) : ℝ) := by
      simpa using (Real.log_lt_log (Real.exp_pos 1) hnLarge)
    have hlog_mono :
        Real.log ((τ n : NNReal) : ℝ) ≤ Real.log ((τ (n + 1) : NNReal) : ℝ) := by
      exact Real.log_le_log hτ_real_pos (by exact_mod_cast hτ_le)
    exact Real.log_le_log (lt_trans zero_lt_one hlog_gt_one) hlog_mono
  have hCore :
      Real.sqrt (α : ℝ) * lilNormalizer (τ n) ≤ lilNormalizer (τ (n + 1)) := by
    have hInner_nonneg :
        0 ≤ 2 * ((τ n : NNReal) : ℝ) * Real.log (Real.log ((τ n : NNReal) : ℝ)) := by
      positivity
    have hEq :
        Real.sqrt
            ((α : ℝ) * (2 * ((τ n : NNReal) : ℝ) *
              Real.log (Real.log ((τ n : NNReal) : ℝ)))) =
          Real.sqrt (α : ℝ) * lilNormalizer (τ n) := by
      simpa [lilNormalizer] using
        (Real.sqrt_mul (show 0 ≤ (α : ℝ) by positivity) hInner_nonneg)
    rw [← hEq, lilNormalizer]
    refine Real.sqrt_le_sqrt ?_
    have hτsucc_eq :
        (((τ (n + 1) : NNReal) : ℝ)) = (α : ℝ) * ((τ n : NNReal) : ℝ) := by
      simp [τ, geometricMesh, pow_succ, mul_comm]
    have hloglog_mono' :
        Real.log (Real.log ((τ n : NNReal) : ℝ)) ≤
          Real.log (Real.log ((α : ℝ) * ((τ n : NNReal) : ℝ))) := by
      simpa [hτsucc_eq] using hloglog_mono
    rw [hτsucc_eq]
    calc
      (α : ℝ) * (2 * ((τ n : NNReal) : ℝ) * Real.log (Real.log ((τ n : NNReal) : ℝ))) ≤
          (α : ℝ) * (2 * ((τ n : NNReal) : ℝ) *
            Real.log (Real.log ((α : ℝ) * ((τ n : NNReal) : ℝ)))) := by
              gcongr
      _ = 2 * ((α : ℝ) * ((τ n : NNReal) : ℝ)) *
            Real.log (Real.log ((α : ℝ) * ((τ n : NNReal) : ℝ))) := by ring
  -- Proof comment: multiply the target inequality by the positive factor `√α` and use the
  -- square-level comparison proved above.
  have hTarget :
      lilNormalizer (τ n) ≤ lilNormalizer (τ (n + 1)) / Real.sqrt (α : ℝ) := by
    exact (le_div_iff₀' hsqrtα_pos).2 hCore
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hTarget

/-- Helper for Theorem 22.1: the law-of-the-iterated-logarithm normalizer is positive once
`t > exp 1`, because both `t` and `log log t` are then positive. -/
private lemma lilNormalizer_pos_of_exp_one_lt {t : NNReal} (ht : Real.exp 1 < (t : ℝ)) :
    0 < lilNormalizer t := by
  have hlogt_gt_one : 1 < Real.log (t : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) ht)
  have hloglog_pos : 0 < Real.log (Real.log (t : ℝ)) := Real.log_pos hlogt_gt_one
  have ht_pos : 0 < (t : ℝ) := by
    exact lt_trans Real.zero_lt_one (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) ht)
  rw [lilNormalizer]
  exact Real.sqrt_pos.2 (by positivity)

/-- Helper for Theorem 22.1: once `exp 1 < s ≤ t`, the normalizer `√(2 t log log t)` is
monotone from `s` to `t`. -/
private lemma lilNormalizer_le_of_le_of_exp_one_lt
    {s t : NNReal} (hs : Real.exp 1 < (s : ℝ)) (hst : s ≤ t) :
    lilNormalizer s ≤ lilNormalizer t := by
  have hs_pos : 0 < (s : ℝ) := by
    exact lt_trans Real.zero_lt_one (lt_trans (by simpa using (Real.one_lt_exp_iff.2 zero_lt_one)) hs)
  have hst_real : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have ht : Real.exp 1 < (t : ℝ) := lt_of_lt_of_le hs hst_real
  have hlog_s_gt_one : 1 < Real.log (s : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hs)
  have hlog_s_pos : 0 < Real.log (s : ℝ) := lt_trans zero_lt_one hlog_s_gt_one
  have hlog_t_gt_one : 1 < Real.log (t : ℝ) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) ht)
  have hlog_mono : Real.log (s : ℝ) ≤ Real.log (t : ℝ) := Real.log_le_log hs_pos hst_real
  have hloglog_mono :
      Real.log (Real.log (s : ℝ)) ≤ Real.log (Real.log (t : ℝ)) := by
    exact Real.log_le_log hlog_s_pos hlog_mono
  have hloglog_s_nonneg : 0 ≤ Real.log (Real.log (s : ℝ)) := (Real.log_pos hlog_s_gt_one).le
  rw [lilNormalizer, lilNormalizer]
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

/-- Helper for Theorem 22.1: every tail point `t ≥ αᴺ` lies in some geometric block
`[αⁿ, αⁿ⁺¹]` with `n ≥ N`. -/
private lemma exists_mem_geometricBlock
    {α : NNReal} (hα : 1 < (α : ℝ)) {N : ℕ} {t : NNReal}
    (ht : geometricMesh α N ≤ t) :
    ∃ n, N ≤ n ∧ t ∈ Set.Icc (geometricMesh α n) (geometricMesh α (n + 1)) := by
  let u : ℕ → NNReal := fun k ↦ geometricMesh α (N + k)
  have hu_tendsto :
      Tendsto (fun k : ℕ ↦ ((u k : NNReal) : ℝ)) atTop atTop := by
    simpa [u, geometricMesh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt hα).comp (Filter.tendsto_add_atTop_nat N)
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
        (by simpa [k] using Nat.lt_succ_self k) (Nat.succ_le_of_lt hk_lt_K)
  refine ⟨N + k, Nat.le_add_right N k, ?_⟩
  rw [Set.mem_Icc]
  constructor
  · simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk_spec
  · have hnext_lt : t < u (k + 1) := lt_of_not_ge hnext_not_le
    exact le_of_lt <| by
      simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext_lt

/-- Helper for Theorem 22.1: comparing two quantities divided by the same positive scale is
equivalent to comparing the original numerators. -/
private lemma div_le_inv_mul_iff {a b K : ℝ} (hK : 0 < K) :
    a / K ≤ K⁻¹ * b ↔ a ≤ b := by
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_right h hK.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hK.ne', inv_mul_cancel₀] using h'
  · intro h
    have hInv_nonneg : 0 ≤ K⁻¹ := by positivity
    have h' := mul_le_mul_of_nonneg_left h hInv_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'

/-- Helper for Theorem 22.1: evaluating the standard Gaussian density at the Brownian scaling
threshold `a / √T` yields the explicit Mills-profile factor used in the reflection bound. -/
private lemma gaussianTailUpperBound_scaledThreshold
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
    -- Proof comment: collapse `(a / √T)^2` to `a^2 / T` using `√T ^ 2 = T`.
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

/-- Helper for Theorem 22.1: Theorem 21.19 together with the standard-normal Mills upper bound
gives the Gaussian tail estimate for the Brownian running maximum. -/
private lemma reflectionPrincipleRunningMaximum_bound
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    μ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a < B t ω} ≤
      ENNReal.ofReal
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  let E : Set Ω := {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a < B t ω}
  let Y : Ω → ℝ := fun ω ↦ B T ω / Real.sqrt (T : ℝ)
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hT_real_pos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT_real_pos
  have hRun : μ E = 2 * μ {ω | a < B T ω} := by
    simpa [E] using
      runningMaximum_eq_two_mul_brownianTerminalTail (hB := hB) (a := a) ha (T := T) hT
  have hMarginal : HasLaw (B T) (gaussianReal 0 T) μ := hB.gaussian_marginal hT
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
  have hY : HasLaw Y (gaussianReal 0 1) μ := by
    simpa [Y, Function.comp, div_eq_mul_inv, mul_comm] using hScale.comp hMarginal
  have hx_pos : 0 < a / Real.sqrt (T : ℝ) := by positivity
  have hTailIci :
      (μ {ω | a / Real.sqrt (T : ℝ) ≤ Y ω}).toReal ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    simpa [MeasureTheory.Measure.real_def, Y] using
      (ProbabilityTheory.HasLaw.standardNormal_tail_bounds
        (P := μ) (X := Y) hY hx_pos).2
  have hTailSubset :
      {ω | a < B T ω} ⊆ {ω | a / Real.sqrt (T : ℝ) ≤ Y ω} := by
    intro ω hω
    have hScaled : a / Real.sqrt (T : ℝ) < Y ω := by
      simpa [Y] using (div_lt_div_of_pos_right hω hsqrtT_pos)
    exact hScaled.le
  have hTailIoi :
      (μ {ω | a < B T ω}).toReal ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    exact
      (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hTailSubset)).trans hTailIci
  have hExplicit :
      2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) =
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
    -- Proof comment: the explicit Gaussian algebra is isolated in the dedicated scaling helper so
    -- the probabilistic argument only consumes the resulting closed form.
    exact gaussianTailUpperBound_scaledThreshold ha hT
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ E) (by positivity)).2 ?_
  calc
    (μ E).toReal = 2 * (μ {ω | a < B T ω}).toReal := by
      rw [hRun, ENNReal.toReal_mul]
      norm_num
    _ ≤ 2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) := by
          gcongr
    _ = (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := hExplicit

/-- Helper for Theorem 22.1: the `n`th geometric upper block uses the threshold
`α * √(2 τₙ log log τₙ)`. -/
private def geometricUpperBlockThreshold (α : NNReal) (n : ℕ) : ℝ :=
  let τ : ℕ → NNReal := geometricMesh α
  (α : ℝ) * lilNormalizer (τ n)

/-- Helper for Theorem 22.1: this is the explicit reflection-principle upper bound attached to the
`n`th geometric upper block. -/
private def geometricUpperBlockUpperBound (α : NNReal) (n : ℕ) : ℝ :=
  let τ : ℕ → NNReal := geometricMesh α
  let threshold := geometricUpperBlockThreshold α n
  ((2 * Real.sqrt (((τ (n + 1) : NNReal) : ℝ)) / Real.sqrt (2 * Real.pi)) *
      (1 / threshold)) *
    Real.exp (-(threshold ^ 2) / (2 * (((τ (n + 1) : NNReal) : ℝ))))

/-- Helper for Theorem 22.1: the geometric upper-block threshold is positive once the mesh time
lies beyond `exp (exp 1)`. -/
private lemma geometricUpperBlockThreshold_pos_of_expExp_one_lt
    {α : NNReal} (hα : 1 < (α : ℝ)) {n : ℕ}
    (hnLarge : Real.exp (Real.exp 1) < (((geometricMesh α) n : NNReal) : ℝ)) :
    0 < geometricUpperBlockThreshold α n := by
  let τ : ℕ → NNReal := geometricMesh α
  have hMeshLarge : Real.exp 1 < ((τ n : NNReal) : ℝ) := by
    exact lt_trans (by simpa using (Real.one_lt_exp_iff.2 (Real.exp_pos 1))) hnLarge
  dsimp [geometricUpperBlockThreshold]
  exact mul_pos (lt_trans zero_lt_one hα) (lilNormalizer_pos_of_exp_one_lt hMeshLarge)

/-- Helper for Theorem 22.1: on the large-time tail `τₙ > exp (exp 1)`, the explicit
reflection-principle majorant on the `n`th geometric block has the canonical profile
`(√π √α √(log log τₙ))⁻¹ * (log τₙ)^(-α)`. -/
private lemma geometricUpperBlockUpperBound_eq_profile
    {α : NNReal} (hα : 1 < (α : ℝ)) {n : ℕ}
    (hnLarge : Real.exp (Real.exp 1) < (((geometricMesh α) n : NNReal) : ℝ)) :
    geometricUpperBlockUpperBound α n =
      (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) *
          Real.sqrt (Real.log (Real.log ((((geometricMesh α) n : NNReal) : ℝ)))))) *
        (Real.log ((((geometricMesh α) n : NNReal) : ℝ))) ^ (-(α : ℝ)) := by
  let τ : ℕ → NNReal := geometricMesh α
  let s : ℝ := ((τ n : NNReal) : ℝ)
  have hα_pos : 0 < (α : ℝ) := lt_trans zero_lt_one hα
  have hs_pos : 0 < s := by
    dsimp [s, τ, geometricMesh]
    simpa using (pow_pos hα_pos n : 0 < (α : ℝ) ^ n)
  have hlog_gt_exp : Real.exp 1 < Real.log s := by
    simpa [s] using (Real.log_lt_log (Real.exp_pos (Real.exp 1)) hnLarge)
  have hlog_pos : 0 < Real.log s := lt_trans (Real.exp_pos 1) hlog_gt_exp
  have hloglog_gt_one : 1 < Real.log (Real.log s) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hlog_gt_exp)
  have hloglog_pos : 0 < Real.log (Real.log s) := lt_trans zero_lt_one hloglog_gt_one
  have hsqrt_two_pi :
      Real.sqrt (2 * Real.pi) = Real.sqrt (2 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by positivity) Real.pi]
  have hsqrt_inner :
      Real.sqrt (2 * s * Real.log (Real.log s)) =
        Real.sqrt (2 : ℝ) * Real.sqrt s * Real.sqrt (Real.log (Real.log s)) := by
    calc
      Real.sqrt (2 * s * Real.log (Real.log s))
          = Real.sqrt (2 * s) * Real.sqrt (Real.log (Real.log s)) := by
              rw [show 2 * s * Real.log (Real.log s) =
                  (2 * s) * Real.log (Real.log s) by ring]
              rw [Real.sqrt_mul (show 0 ≤ 2 * s by positivity) (Real.log (Real.log s))]
      _ = (Real.sqrt (2 : ℝ) * Real.sqrt s) * Real.sqrt (Real.log (Real.log s)) := by
            rw [show 2 * s = (2 : ℝ) * s by ring]
            rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by positivity) s]
      _ = Real.sqrt (2 : ℝ) * Real.sqrt s * Real.sqrt (Real.log (Real.log s)) := by ring
  have hMeshSucc :
      (((τ (n + 1) : NNReal) : ℝ)) = (α : ℝ) * s := by
    dsimp [τ, s, geometricMesh]
    rw [pow_succ]
    ring
  have hPrefactor :
      ((2 * Real.sqrt (((τ (n + 1) : NNReal) : ℝ)) / Real.sqrt (2 * Real.pi)) *
          (1 / geometricUpperBlockThreshold α n)) =
        1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) * Real.sqrt (Real.log (Real.log s))) := by
    -- Proof comment: expand the geometric successor and split both square roots so all mesh-scale
    -- terms cancel except the canonical `√π √α √(log log s)` denominator.
    rw [hMeshSucc, geometricUpperBlockThreshold, lilNormalizer]
    dsimp [τ, s]
    rw [Real.sqrt_mul (show 0 ≤ (α : ℝ) by positivity) s]
    rw [hsqrt_two_pi, hsqrt_inner]
    field_simp [show (α : ℝ) ≠ 0 by linarith, show Real.sqrt Real.pi ≠ 0 by positivity,
      show Real.sqrt (α : ℝ) ≠ 0 by positivity, show Real.sqrt (2 : ℝ) ≠ 0 by positivity,
      show Real.sqrt s ≠ 0 by positivity, show Real.sqrt (Real.log (Real.log s)) ≠ 0 by
        positivity]
    rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity), Real.sq_sqrt hα_pos.le]
    -- Proof comment: the remaining mismatch is only the local alias `s = τ n`, after which the
    -- final cancellation is a one-line field simplification.
    simp only [s, τ]
    field_simp [show Real.sqrt (Real.log (Real.log ↑(geometricMesh α n))) ≠ 0 by positivity]
  have hExponentArg :
      -((geometricUpperBlockThreshold α n) ^ 2) / (2 * (((τ (n + 1) : NNReal) : ℝ))) =
        -(α : ℝ) * Real.log (Real.log s) := by
    -- Proof comment: the quadratic Brownian threshold contributes exactly the factor
    -- `-α log log s` once `τ (n + 1) = α s` is substituted.
    rw [hMeshSucc]
    simp [geometricUpperBlockThreshold, lilNormalizer, τ, s, pow_two,
      Real.sq_sqrt (show 0 ≤ 2 * s * Real.log (Real.log s) by positivity)]
    field_simp [show (α : ℝ) ≠ 0 by linarith, hs_pos.ne']
    rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity), Real.sq_sqrt hs_pos.le,
      Real.sq_sqrt hloglog_pos.le]
    -- Proof comment: the only remaining work is to rewrite the alias `s = τ n` and normalize the
    -- scalar factors.
    simp only [s, τ]
    field_simp [show (((geometricMesh α n : NNReal) : ℝ)) ≠ 0 by positivity]
  have hExp :
      Real.exp (-(geometricUpperBlockThreshold α n ^ 2) / (2 * (((τ (n + 1) : NNReal) : ℝ)))) =
        (Real.log s) ^ (-(α : ℝ)) := by
    -- Proof comment: `exp (-α log log s)` is the same as `(log s)^(-α)` because `log s > 0`.
    rw [hExponentArg, mul_comm, Real.exp_mul, Real.exp_log hlog_pos]
  -- Proof comment: combine the simplified prefactor and exponential term into the stable
  -- deterministic profile used for the p-series comparison.
  calc
    geometricUpperBlockUpperBound α n
        = ((2 * Real.sqrt (((τ (n + 1) : NNReal) : ℝ)) / Real.sqrt (2 * Real.pi)) *
            (1 / geometricUpperBlockThreshold α n)) *
          Real.exp
            (-(geometricUpperBlockThreshold α n ^ 2) /
              (2 * (((τ (n + 1) : NNReal) : ℝ)))) := by
              rfl
    _ =
        (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) *
            Real.sqrt (Real.log (Real.log s)))) *
          (Real.log s) ^ (-(α : ℝ)) := by
            rw [hPrefactor, hExp]
    _ = (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) *
            Real.sqrt (Real.log (Real.log ((((geometricMesh α) n : NNReal) : ℝ)))))) *
          (Real.log ((((geometricMesh α) n : NNReal) : ℝ))) ^ (-(α : ℝ)) := by
            simp [s, τ]

/-- Helper for Theorem 22.1: once the geometric mesh time `τₙ` is large enough, the explicit
reflection-principle upper bound on the `n`th block is controlled by a constant multiple of
`n ^ (-α)`. -/
private lemma geometricUpperBlockUpperBound_le_rpow
    {α : NNReal} (hα : 1 < (α : ℝ)) {n : ℕ}
    (hnLarge : Real.exp (Real.exp 1) < (((geometricMesh α) n : NNReal) : ℝ))
    (hnPos : 1 ≤ n) :
    let C : ℝ :=
      (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ))) * (Real.log (α : ℝ)) ^ (-(α : ℝ))
    geometricUpperBlockUpperBound α n ≤ C * (n : ℝ) ^ (-(α : ℝ)) := by
  let C : ℝ :=
    (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ))) * (Real.log (α : ℝ)) ^ (-(α : ℝ))
  let s : ℝ := (((geometricMesh α) n : NNReal) : ℝ)
  have hα_pos : 0 < (α : ℝ) := lt_trans zero_lt_one hα
  have hlogα_pos : 0 < Real.log (α : ℝ) := Real.log_pos hα
  have hs_pos : 0 < s := by
    dsimp [s, geometricMesh]
    simpa using (pow_pos hα_pos n : 0 < (α : ℝ) ^ n)
  have hloglog_gt_one : 1 < Real.log (Real.log s) := by
    have hlog_gt_exp : Real.exp 1 < Real.log s := by
      simpa [s] using (Real.log_lt_log (Real.exp_pos (Real.exp 1)) hnLarge)
    simpa using (Real.log_lt_log (Real.exp_pos 1) hlog_gt_exp)
  have hsqrt_loglog_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log s)) := by
    exact (Real.one_le_sqrt).2 hloglog_gt_one.le
  have hDenom_nonneg : 0 ≤ Real.sqrt Real.pi * Real.sqrt (α : ℝ) := by positivity
  have hDenom_pos :
      0 < Real.sqrt Real.pi * Real.sqrt (α : ℝ) * Real.sqrt (Real.log (Real.log s)) := by
    positivity
  have hProfileCoeff :
      1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) * Real.sqrt (Real.log (Real.log s))) ≤
        1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ)) := by
    have hBase_pos : 0 < Real.sqrt Real.pi * Real.sqrt (α : ℝ) := by
      positivity
    have hMul_le :
        Real.sqrt Real.pi * Real.sqrt (α : ℝ) ≤
          Real.sqrt Real.pi * Real.sqrt (α : ℝ) * Real.sqrt (Real.log (Real.log s)) := by
      nlinarith [hsqrt_loglog_ge_one, hDenom_nonneg]
    exact one_div_le_one_div_of_le hBase_pos hMul_le
  have hLogMesh :
      Real.log s = (n : ℝ) * Real.log (α : ℝ) := by
    calc
      Real.log s = Real.log ((α : ℝ) ^ (n : ℝ)) := by
            simp [s, geometricMesh, Real.rpow_natCast]
      _ = (n : ℝ) * Real.log (α : ℝ) := by rw [Real.log_rpow hα_pos]
  have hRpow :
      (Real.log s) ^ (-(α : ℝ)) =
        (Real.log (α : ℝ)) ^ (-(α : ℝ)) * (n : ℝ) ^ (-(α : ℝ)) := by
    rw [hLogMesh, show (n : ℝ) * Real.log (α : ℝ) = Real.log (α : ℝ) * (n : ℝ) by ring]
    rw [Real.mul_rpow hlogα_pos.le (show 0 ≤ (n : ℝ) by positivity)]
  have hLogMesh_pos : 0 < Real.log s := by
    rw [hLogMesh]
    positivity
  calc
    geometricUpperBlockUpperBound α n
        = (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ) *
            Real.sqrt (Real.log (Real.log s)))) * (Real.log s) ^ (-(α : ℝ)) := by
              simpa [s] using geometricUpperBlockUpperBound_eq_profile (α := α) hα hnLarge
    _ ≤ (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ))) * (Real.log s) ^ (-(α : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hProfileCoeff (Real.rpow_nonneg hLogMesh_pos.le _)
    _ = C * (n : ℝ) ^ (-(α : ℝ)) := by
          dsimp [C]
          rw [hRpow]
          ac_rfl

/-- Helper for Theorem 22.1: the reflection-principle upper bound on each geometric block is
eventually dominated by a constant multiple of `n ^ (-α)`. -/
private lemma geometricUpperBlockMeasureReal_eventually_le_rpow
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      (μ (geometricUpperBlock B α n)).toReal ≤ C * (n : ℝ) ^ (-(α : ℝ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let C : ℝ :=
    (1 / (Real.sqrt Real.pi * Real.sqrt (α : ℝ))) * (Real.log (α : ℝ)) ^ (-(α : ℝ))
  refine ⟨C, ?_, ?_⟩
  · have hlogα_pos : 0 < Real.log (α : ℝ) := Real.log_pos hα
    dsimp [C]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hlogα_pos _)
  · let τ : ℕ → NNReal := geometricMesh α
    have hτ_tendsto :
        Tendsto (fun n : ℕ ↦ ((τ n : NNReal) : ℝ)) atTop atTop := by
      simpa [τ, geometricMesh] using
        (tendsto_pow_atTop_atTop_of_one_lt hα :
          Tendsto (fun n : ℕ ↦ (α : ℝ) ^ n) atTop atTop)
    have hEventuallyLarge :
        ∀ᶠ n : ℕ in atTop, Real.exp (Real.exp 1) < ((τ n : NNReal) : ℝ) := by
      exact hτ_tendsto.eventually_gt_atTop (Real.exp (Real.exp 1))
    filter_upwards [hEventuallyLarge, Ici_mem_atTop (1 : ℕ)] with n hnLarge hnPos
    have hThresholdPos :
        0 < geometricUpperBlockThreshold α n :=
      geometricUpperBlockThreshold_pos_of_expExp_one_lt (α := α) hα hnLarge
    have hTimePos : 0 < τ (n + 1) := by
      dsimp [τ, geometricMesh]
      exact pow_pos (lt_trans zero_lt_one hα) (n + 1)
    have hSubset :
        geometricUpperBlock B α n ⊆
          {ω | ∃ t ∈ Set.Icc (0 : NNReal) (τ (n + 1)), geometricUpperBlockThreshold α n < B t ω} := by
      intro ω hω
      rcases hω with ⟨t, ht, htB⟩
      exact ⟨t, ⟨le_trans (show (0 : NNReal) ≤ τ n by positivity) ht.1, ht.2⟩, htB⟩
    have hReflect :
        μ (geometricUpperBlock B α n) ≤ ENNReal.ofReal (geometricUpperBlockUpperBound α n) := by
      refine le_trans (measure_mono hSubset) ?_
      simpa [geometricUpperBlockUpperBound, geometricUpperBlockThreshold, τ] using
        reflectionPrincipleRunningMaximum_bound (B := B) hB
          (a := geometricUpperBlockThreshold α n) hThresholdPos (T := τ (n + 1)) hTimePos
    have hMass_le_profile :
        (μ (geometricUpperBlock B α n)).toReal ≤ geometricUpperBlockUpperBound α n := by
      have hUpperNonneg : 0 ≤ geometricUpperBlockUpperBound α n := by
        have hlog_gt_exp :
            Real.exp 1 < Real.log ((((τ n : NNReal) : ℝ))) := by
          simpa using (Real.log_lt_log (Real.exp_pos (Real.exp 1)) hnLarge)
        have hLogMesh_pos : 0 < Real.log ((((τ n : NNReal) : ℝ))) := by
          exact lt_trans (Real.exp_pos 1) hlog_gt_exp
        rw [geometricUpperBlockUpperBound_eq_profile (α := α) hα hnLarge]
        apply mul_nonneg
        · positivity
        · exact Real.rpow_nonneg hLogMesh_pos.le _
      have hReflect_toReal :
          (μ (geometricUpperBlock B α n)).toReal ≤
            (ENNReal.ofReal (geometricUpperBlockUpperBound α n)).toReal := by
        exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hReflect
      simpa [ENNReal.toReal_ofReal hUpperNonneg] using hReflect_toReal
    exact hMass_le_profile.trans <|
      by
        simpa [C, τ] using
          geometricUpperBlockUpperBound_le_rpow (α := α) hα hnLarge hnPos

/-- Helper for Theorem 22.1: the geometric upper-block events have summable real masses for every
mesh ratio `α > 1`. -/
lemma summable_geometricUpperBlock_measureReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B α n)).toReal) := by
  rcases geometricUpperBlockMeasureReal_eventually_le_rpow (B := B) hB hα with
    ⟨C, hC_pos, hTail⟩
  rcases Filter.eventually_atTop.1 hTail with ⟨N, hN⟩
  have hSeries :
      Summable (fun n : ℕ ↦ C * (n : ℝ) ^ (-(α : ℝ))) := by
    refine (Real.summable_nat_rpow.mpr ?_).mul_left C
    linarith
  have hSeriesShift :
      Summable (fun n : ℕ ↦ C * (n + N : ℝ) ^ (-(α : ℝ))) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      ((_root_.summable_nat_add_iff N).2 hSeries)
  have hShift :
      Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B α (n + N))).toReal) := by
    refine Summable.of_nonneg_of_le (fun n ↦ ENNReal.toReal_nonneg) ?_ hSeriesShift
    intro n
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      hN (n + N) (Nat.le_add_left N n)
  exact (_root_.summable_nat_add_iff N).1 hShift

/-- Helper for Theorem 22.1: summable geometric upper-block masses force the normalized Brownian
coordinates to stay eventually below the mesh ratio `α` almost surely. -/
lemma ae_eventually_lilRatio_le_of_geometricUpperBlockSummable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ))
    (hSummable : Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B α n)).toReal)) :
    ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio B ω t ≤ (α : ℝ) := by
  let τ : ℕ → NNReal := geometricMesh α
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hAvoid :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ geometricUpperBlock B α n :=
    ae_eventually_notMem_of_summable_measureReal μ hSummable
  have hτ_tendsto : Tendsto (fun n : ℕ ↦ ((τ n : NNReal) : ℝ)) atTop atTop := by
    simpa [τ, geometricMesh] using
      (tendsto_pow_atTop_atTop_of_one_lt hα : Tendsto (fun n : ℕ ↦ (α : ℝ) ^ n) atTop atTop)
  have hEventuallyLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp 1 < ((τ n : NNReal) : ℝ) := by
    exact hτ_tendsto.eventually_gt_atTop (Real.exp 1)
  filter_upwards [hAvoid] with ω hAvoidω
  rcases Filter.eventually_atTop.1 hAvoidω with ⟨N₀, hN₀⟩
  rcases Filter.eventually_atTop.1 hEventuallyLarge with ⟨N₁, hN₁⟩
  let N := max N₀ N₁
  refine Filter.eventually_atTop.2 ⟨τ N, ?_⟩
  intro t ht
  rcases exists_mem_geometricBlock hα ht with ⟨n, hNn, htBlock⟩
  have hN₀n : N₀ ≤ n := le_trans (le_max_left _ _) hNn
  have hN₁n : N₁ ≤ n := le_trans (le_max_right _ _) hNn
  have hnLarge : Real.exp 1 < ((τ n : NNReal) : ℝ) := hN₁ n hN₁n
  have htLarge : Real.exp 1 < (t : ℝ) := lt_of_lt_of_le hnLarge (by exact_mod_cast htBlock.1)
  have hMeshBound :
      B t ω ≤ (α : ℝ) * lilNormalizer (τ n) := by
    -- Proof comment: outside the bad event on the containing geometric block, the Brownian value
    -- at `t` cannot exceed the block threshold.
    refine le_of_not_gt ?_
    intro hgt
    have hMem : ω ∈ geometricUpperBlock B α n := by
      simpa [geometricUpperBlock] using
        (show ∃ s ∈ Set.Icc (τ n) (τ (n + 1)), (α : ℝ) * lilNormalizer (τ n) < B s ω from
          ⟨t, htBlock, hgt⟩)
    exact (hN₀ n hN₀n) hMem
  have hNormalizerMono :
      lilNormalizer (τ n) ≤ lilNormalizer t :=
    lilNormalizer_le_of_le_of_exp_one_lt hnLarge htBlock.1
  have hScaled :
      (α : ℝ) * lilNormalizer (τ n) ≤ (α : ℝ) * lilNormalizer t := by
    gcongr
  have hValueBound :
      B t ω ≤ (α : ℝ) * lilNormalizer t :=
    hMeshBound.trans hScaled
  have hNormalizerPos : 0 < lilNormalizer t :=
    lilNormalizer_pos_of_exp_one_lt htLarge
  -- Proof comment: divide the samplewise upper bound by the positive normalizer to obtain the
  -- eventual `lilRatio` control.
  simpa [lilRatio] using (div_le_iff₀ hNormalizerPos).2 hValueBound

/-- Helper for Theorem 22.1: the lower-half geometric increment events are measurable and
independent once the geometric mesh is fixed. -/
private lemma geometricIncrementEvent_eq_preimage
    {B : NNReal → Ω → ℝ} {α : NNReal} (n : ℕ) :
    let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
    let τ : ℕ → NNReal := geometricMesh α
    let Y : Ω → ℝ := fun ω ↦ B (τ (n + 1)) ω - B (τ n) ω
    geometricIncrementEvent B α n = Y ⁻¹' Set.Ici ((1 / β) * lilNormalizer (τ (n + 1))) := by
  -- Proof comment: `geometricIncrementEvent` is definitionally the threshold preimage of the
  -- geometric increment random variable.
  rfl

/-- Helper for Theorem 22.1: the successive geometric-mesh gap is exactly `τ (n + 1) / β`,
where `β = α / (α - 1)`. -/
private lemma geometricMesh_succ_sub_eq_div_beta
    {α : NNReal} (hα : 1 < (α : ℝ)) (n : ℕ) :
    let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
    let τ : ℕ → NNReal := geometricMesh α
    (((τ (n + 1) : NNReal) : ℝ) - (τ n : ℝ)) = ((τ (n + 1) : ℝ)) / β := by
  -- Proof comment: expand `τ (n + 1) = α * τ n` and then simplify the rational coefficient.
  change (α : ℝ) ^ (n + 1) - (α : ℝ) ^ n =
    (α : ℝ) ^ (n + 1) / ((α : ℝ) / ((α : ℝ) - 1))
  rw [pow_succ]
  field_simp [show (α : ℝ) ≠ 0 by linarith, show (α : ℝ) - 1 ≠ 0 by linarith]

/-- Helper for Theorem 22.1: on the large-time tail `τₙ₊₁ > exp 1`, the geometric increment
threshold on the normalized Brownian increment scale matches the original LIL threshold after
multiplying by the mesh-gap square root. -/
private lemma geometricIncrementThreshold_mul_sqrt_diff_eq
    {α : NNReal} (hα : 1 < (α : ℝ)) (n : ℕ)
    (hnLarge : Real.exp 1 < ((((geometricMesh α) (n + 1) : NNReal) : ℝ))) :
    let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
    let τ : ℕ → NNReal := geometricMesh α
    let diff : NNReal := τ (n + 1) - τ n
    let x : ℝ := Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
    x * Real.sqrt (diff : ℝ) = (1 / β) * lilNormalizer (τ (n + 1)) := by
  let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
  let τ : ℕ → NNReal := geometricMesh α
  let diff : NNReal := τ (n + 1) - τ n
  let x : ℝ := Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact div_pos (lt_trans zero_lt_one hα) (sub_pos.mpr hα)
  have hτ_pos : 0 < ((τ (n + 1) : NNReal) : ℝ) := by
    dsimp [τ, geometricMesh]
    simpa using (pow_pos (lt_trans zero_lt_one hα) (n + 1) : 0 < (α : ℝ) ^ (n + 1))
  have hlog_gt_one : 1 < Real.log ((τ (n + 1) : ℝ)) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hnLarge)
  have hloglog_pos : 0 < Real.log (Real.log ((τ (n + 1) : ℝ))) := Real.log_pos hlog_gt_one
  have hdiff_eq :
      (diff : ℝ) = ((τ (n + 1) : ℝ)) / β := by
    have hτ_le : τ n ≤ τ (n + 1) := by
      exact (geometricMesh_monotone hα) (Nat.le_succ n)
    rw [NNReal.coe_sub hτ_le]
    simpa [β, τ] using geometricMesh_succ_sub_eq_div_beta (α := α) hα n
  have hCore :
      ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ)))) * ((τ (n + 1) : ℝ) / β) =
        (1 / β) ^ 2 * (2 * ((τ (n + 1) : ℝ)) * Real.log (Real.log ((τ (n + 1) : ℝ)))) := by
    field_simp [show β ≠ 0 by linarith]
  -- Proof comment: rewrite the mesh gap as `τ (n + 1) / β`, then combine the two square roots
  -- into the single LIL normalizer with the prefactor `1 / β`.
  calc
    x * Real.sqrt (diff : ℝ)
        = Real.sqrt
            (((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ)))) *
              (((τ (n + 1) : ℝ) / β))) := by
                rw [show x = Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ)))) by rfl,
                  hdiff_eq]
                rw [← Real.sqrt_mul
                  (show 0 ≤ (2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))) by positivity)
                  (((τ (n + 1) : ℝ) / β))]
    _ = Real.sqrt
          ((1 / β) ^ 2 * (2 * ((τ (n + 1) : ℝ)) *
            Real.log (Real.log ((τ (n + 1) : ℝ))))) := by rw [hCore]
    _ = Real.sqrt ((1 / β) ^ 2) *
          Real.sqrt
            (2 * ((τ (n + 1) : ℝ)) * Real.log (Real.log ((τ (n + 1) : ℝ)))) := by
              rw [Real.sqrt_mul (show 0 ≤ (1 / β) ^ 2 by positivity)
                (2 * ((τ (n + 1) : ℝ)) * Real.log (Real.log ((τ (n + 1) : ℝ))))]
    _ = (1 / β) * lilNormalizer (τ (n + 1)) := by
          rw [Real.sqrt_sq (show 0 ≤ 1 / β by positivity), lilNormalizer]

lemma geometricIncrementEvents_measurable_iIndepSet
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    (∀ n, MeasurableSet (geometricIncrementEvent B α n)) ∧
      iIndepSet (geometricIncrementEvent B α) μ := by
  let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
  let τ : ℕ → NNReal := geometricMesh α
  let Y : ℕ → Ω → ℝ := fun n ω ↦ B (τ (n + 1)) ω - B (τ n) ω
  have hτ_mono : Monotone τ := by
    simpa [τ] using geometricMesh_monotone hα
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact ((hB.stronglyMeasurable (τ (n + 1))).measurable).sub
      ((hB.stronglyMeasurable (τ n)).measurable)
  have hY_indep : iIndepFun Y μ := by
    -- Proof comment: consecutive increments along the monotone geometric mesh inherit
    -- independence from the Brownian independent-increments axiom.
    simpa [Y, τ, add_assoc, add_left_comm, add_comm] using
      hB.indepIncrements.nat (t := τ) hτ_mono
  constructor
  · intro n
    -- Proof comment: each increment event is a closed-ray preimage under the measurable increment
    -- map `Y n`.
    rw [show geometricIncrementEvent B α n =
        (Y n) ⁻¹' Set.Ici ((1 / β) * lilNormalizer (τ (n + 1))) by
          simpa [β, τ, Y] using geometricIncrementEvent_eq_preimage (B := B) (α := α) n]
    exact (hY_meas n) measurableSet_Ici
  · -- Proof comment: the full event family is the threshold-preimage family of the independent
    -- coordinates `Y n`, so independence follows from the generic preimage lemma.
    rw [show geometricIncrementEvent B α =
        fun n ↦ (Y n) ⁻¹' Set.Ici ((1 / β) * lilNormalizer (τ (n + 1))) by
          funext n
          simpa [β, τ, Y] using geometricIncrementEvent_eq_preimage (B := B) (α := α) n]
    exact
      iIndepSet_preimage_of_iIndepFun (μ := μ) (Y := Y) hY_meas hY_indep
        (s := fun n ↦ Set.Ici ((1 / β) * lilNormalizer (τ (n + 1))))
        (fun _ ↦ measurableSet_Ici)

/-- Helper for Theorem 22.1: once the lower-half geometric increment events have an eventual
harmonic lower bound on their real masses, they occur infinitely often almost surely. -/
lemma geometricIncrementEvents_force_frequently_of_eventually_inv_le_measureReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ))
    (hLower :
      ∀ᶠ n : ℕ in atTop, (1 / (n + 1 : ℝ)) ≤ μ.real (geometricIncrementEvent B α n)) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ geometricIncrementEvent B α n := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  rcases geometricIncrementEvents_measurable_iIndepSet (B := B) hB hα with ⟨hMeas, hIndep⟩
  have hNotSummable :
      ¬ Summable (fun n : ℕ ↦ μ.real (geometricIncrementEvent B α n)) := by
    intro hSummable
    rcases Filter.eventually_atTop.1 hLower with ⟨N, hN⟩
    have hShiftMass :
        Summable (fun n : ℕ ↦ μ.real (geometricIncrementEvent B α (n + N))) := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        ((_root_.summable_nat_add_iff N).2 hSummable)
    have hShiftHarm :
        Summable (fun n : ℕ ↦ 1 / (n + (N + 1) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hShiftMass
      intro n
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        hN (n + N) (Nat.le_add_left N n)
    have hShiftNot : ¬ Summable (fun n : ℕ ↦ 1 / (n + (N + 1) : ℝ)) := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) (N + 1)).1)
          Real.not_summable_one_div_natCast
    exact hShiftNot hShiftHarm
  have hMem :
      ∀ᵐ ω ∂μ, ω ∈ Filter.limsup (geometricIncrementEvent B α) atTop :=
    ae_mem_limsup_of_notSummable_measureReal μ hMeas hIndep hNotSummable
  simpa [Filter.mem_limsup_iff_frequently_mem] using hMem

/-- Helper for Theorem 22.1: once the upper-half geometric block events are summable in real
mass, they are eventually avoided almost surely. -/
lemma ae_eventually_notMem_geometricUpperBlocks_of_summable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal}
    (hSummable : Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B α n)).toReal)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ geometricUpperBlock B α n := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: this is exactly the first Borel--Cantelli wrapper consumed by the upper
  -- geometric-grid argument.
  exact ae_eventually_notMem_of_summable_measureReal μ hSummable

/-- Helper for Theorem 22.1: the geometric-grid reflection-principle and first-Borel-Cantelli
argument yields the almost-sure upper bound `limsup ≤ 1 + 1 / (m + 1)`. -/
lemma ae_limsup_le_one_add_invSucc
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (m : ℕ) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop ≤ 1 + 1 / (m + 1 : ℝ) := by
  let α : NNReal := 1 + 1 / (m + 1 : NNReal)
  have hα : 1 < (α : ℝ) := by
    change 1 < 1 + 1 / (m + 1 : ℝ)
    have hrecip_pos : 0 < (1 / (m + 1 : ℝ)) := by positivity
    linarith
  have hSummable :
      Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B α n)).toReal) :=
    summable_geometricUpperBlock_measureReal (B := B) hB hα
  have hSummableNeg :
      Summable (fun n : ℕ ↦ (μ (geometricUpperBlock (fun t ω ↦ -B t ω) α n)).toReal) := by
    exact summable_geometricUpperBlock_measureReal (B := fun t ω ↦ -B t ω)
      (neg_isBrownianMotion hB) hα
  have hEventually :
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio B ω t ≤ (α : ℝ) :=
    ae_eventually_lilRatio_le_of_geometricUpperBlockSummable (B := B) hB hα hSummable
  have hEventuallyNeg :
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio (fun s ω ↦ -B s ω) ω t ≤ (α : ℝ) :=
    ae_eventually_lilRatio_le_of_geometricUpperBlockSummable
      (B := fun s ω ↦ -B s ω) (neg_isBrownianMotion hB) hα hSummableNeg
  -- Proof comment: the first Borel--Cantelli upper argument already yields an eventual bound by
  -- the chosen mesh ratio `α = 1 + 1 / (m + 1)`, and `limsup` respects eventual upper bounds.
  filter_upwards [hEventually, hEventuallyNeg] with ω hω hωNeg
  have hCobounded :
      atTop.IsCoboundedUnder (· ≤ ·) (fun t : NNReal ↦ lilRatio B ω t) := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := -(α : ℝ))
    have hEventuallyLower : ∀ᶠ t : NNReal in atTop, -(α : ℝ) ≤ lilRatio B ω t := by
      filter_upwards [hωNeg] with t ht
      have hEq :
          lilRatio (fun s ω ↦ -B s ω) ω t = -lilRatio B ω t := by
        simp [lilRatio, div_eq_mul_inv]
      have hneg : -lilRatio B ω t ≤ (α : ℝ) := by
        simpa [hEq] using ht
      linarith
    exact hEventuallyLower.frequently
  simpa [lilRatio, α] using (Filter.limsup_le_of_le hCobounded hω)

/-- Helper for Theorem 22.1: the fixed geometric ratio `2` already gives an almost-sure eventual
pointwise upper bound `lilRatio ≤ 2`. -/
private lemma ae_eventually_lilRatio_le_two
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio B ω t ≤ (2 : ℝ) := by
  have hSummable :
      Summable (fun n : ℕ ↦ (μ (geometricUpperBlock B (2 : NNReal) n)).toReal) :=
    summable_geometricUpperBlock_measureReal (B := B) hB (α := 2) (by norm_num)
  -- Proof comment: specialize the already completed upper-side geometric-block argument to the
  -- textbook ratio `α = 2`.
  exact ae_eventually_lilRatio_le_of_geometricUpperBlockSummable (B := B) hB (α := 2)
    (by norm_num) hSummable

/-- Helper for Theorem 22.1: on a fixed geometric mesh, a frequent lower bound along the mesh
already forces the same lower bound for the full `atTop` limsup. -/
lemma geometricMeshFrequently_le_limsup
    {ω : Ω} {B : NNReal → Ω → ℝ} {α : NNReal} {c C : ℝ} (hα : 1 < (α : ℝ))
    (hUpper : ∀ᶠ t in atTop, lilRatio B ω t ≤ C)
    (hFreqMesh : ∃ᶠ n in atTop, c ≤ lilRatio B ω (geometricMesh α (n + 1))) :
    c ≤ limsup (fun t : NNReal ↦ lilRatio B ω t) atTop := by
  let τ : ℕ → NNReal := fun n ↦ geometricMesh α (n + 1)
  let v : ℕ → ℝ := fun n ↦ lilRatio B ω (τ n)
  have hτ_tendsto : Tendsto τ atTop atTop := by
    have hαNN : (1 : NNReal) < α := by
      exact_mod_cast hα
    simpa [τ, geometricMesh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((tendsto_pow_atTop_atTop_of_one_lt hαNN :
        Tendsto (fun n : ℕ ↦ α ^ n) atTop atTop)).comp (Filter.tendsto_add_atTop_nat 1)
  have hUpperMesh : ∀ᶠ n : ℕ in atTop, v n ≤ C := by
    -- Proof comment: the eventual upper bound on the full path restricts along the geometric
    -- subsequence because the mesh itself tends to `∞`.
    simpa [v, τ] using hτ_tendsto.eventually hUpper
  have hBoundedMesh : atTop.IsBoundedUnder (· ≤ ·) v := by
    exact isBoundedUnder_of_eventually_le hUpperMesh
  have hCoboundedMesh : atTop.IsCoboundedUnder (· ≤ ·) v := by
    exact Filter.IsCoboundedUnder.of_frequently_ge hFreqMesh
  have hSubseq :
      c ≤ limsup (fun t : NNReal ↦ lilRatio B ω t) (Filter.map τ atTop) := by
    have hSubseqBase : c ≤ limsup v atTop := by
      exact Filter.le_limsup_of_frequently_le hFreqMesh hBoundedMesh
    simpa [v, τ, limsup_comp] using hSubseqBase
  have hBoundedFull : atTop.IsBoundedUnder (· ≤ ·) (fun t : NNReal ↦ lilRatio B ω t) := by
    exact isBoundedUnder_of_eventually_le hUpper
  have hCoboundedSubseq :
      (Filter.map τ atTop).IsCoboundedUnder (· ≤ ·) (fun t : NNReal ↦ lilRatio B ω t) := by
    simpa [v, τ] using hCoboundedMesh
  -- Proof comment: compare the subsequence limsup to the ambient `atTop` limsup using the mesh
  -- tendsto statement.
  exact le_trans hSubseq <|
    Filter.limsup_le_limsup_of_le hτ_tendsto hCoboundedSubseq hBoundedFull

/-- Helper for Theorem 22.1: a frequent family of large geometric increments together with an
eventual upper bound on the negated process forces frequent lower bounds on the mesh values of the
LIL ratio. -/
lemma frequently_ge_lilRatio_geometricMesh_of_geometricIncrement
    {ω : Ω} {B : NNReal → Ω → ℝ} {α : NNReal} (hα : 1 < (α : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hNegUpper : ∀ᶠ t in atTop, lilRatio (fun s ω ↦ -B s ω) ω t ≤ C)
    (hFreq : ∃ᶠ n in atTop, ω ∈ geometricIncrementEvent B α n) :
    ∃ᶠ n in atTop,
      (((α : ℝ) - 1) / (α : ℝ)) - C / Real.sqrt (α : ℝ) ≤
        lilRatio B ω (geometricMesh α (n + 1)) := by
  let τ : ℕ → NNReal := geometricMesh α
  have hαNN : (1 : NNReal) < α := by exact_mod_cast hα
  have hτ_tendsto : Tendsto τ atTop atTop := by
    simpa [τ, geometricMesh] using tendsto_pow_atTop_atTop_of_one_lt hαNN
  have hτ_tendstoReal :
      Tendsto (fun n : ℕ ↦ ((τ n : NNReal) : ℝ)) atTop atTop := by
    simpa [τ, geometricMesh] using
      (tendsto_pow_atTop_atTop_of_one_lt hα : Tendsto (fun n : ℕ ↦ (α : ℝ) ^ n) atTop atTop)
  have hNegUpperMesh :
      ∀ᶠ n : ℕ in atTop, lilRatio (fun s ω ↦ -B s ω) ω (τ n) ≤ C := by
    -- Proof comment: specialize the eventual upper bound on `-B` to the geometric mesh times.
    exact hτ_tendsto.eventually hNegUpper
  have hNormalizerRatio :
      ∀ᶠ n : ℕ in atTop,
        lilNormalizer (τ n) ≤ (1 / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1)) := by
    -- Proof comment: the deterministic mesh-to-mesh normalizer comparison was isolated earlier.
    simpa [τ] using eventually_geometricNormalizer_ratio_le_invSqrt (α := α) hα
  have hMeshLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp 1 < ((τ n : NNReal) : ℝ) := by
    -- Proof comment: past a tail, every mesh time is large enough for the LIL normalizer to be
    -- positive.
    exact hτ_tendstoReal.eventually_gt_atTop (Real.exp 1)
  have hτ_mono : Monotone τ := by
    simpa [τ] using geometricMesh_monotone hα
  have hOneDivBeta :
      (1 / (((α : ℝ) / ((α : ℝ) - 1))) : ℝ) = (((α : ℝ) - 1) / (α : ℝ)) := by
    field_simp [show (α : ℝ) ≠ 0 by linarith, show (α : ℝ) - 1 ≠ 0 by linarith]
  refine (hFreq.and_eventually (hNegUpperMesh.and (hNormalizerRatio.and hMeshLarge))).mono ?_
  intro n hn
  rcases hn with ⟨hIncr, hNegRatio, hNormRatio, hLarge⟩
  have hτ_le : τ n ≤ τ (n + 1) := hτ_mono (Nat.le_succ n)
  have hLargeNext : Real.exp 1 < ((τ (n + 1) : NNReal) : ℝ) := by
    exact lt_of_lt_of_le hLarge (by exact_mod_cast hτ_le)
  have hNormPos : 0 < lilNormalizer (τ n) :=
    lilNormalizer_pos_of_exp_one_lt hLarge
  have hNormNextPos : 0 < lilNormalizer (τ (n + 1)) :=
    lilNormalizer_pos_of_exp_one_lt hLargeNext
  have hNegValue :
      -B (τ n) ω ≤ C * lilNormalizer (τ n) := by
    -- Proof comment: convert the eventual upper bound on `-B` at time `τ n` back to a lower
    -- bound on `B (τ n)`.
    simpa [lilRatio, mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ hNormPos).1 hNegRatio
  have hScaledNorm :
      C * lilNormalizer (τ n) ≤
        (C / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1)) := by
    -- Proof comment: transport the previous-time normalizer to the next mesh point using the
    -- deterministic `1 / √α` comparison.
    calc
      C * lilNormalizer (τ n) ≤ C * ((1 / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1))) := by
        exact mul_le_mul_of_nonneg_left hNormRatio hC
      _ = (C / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1)) := by
        ring
  have hPrevLower :
      -((C / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1))) ≤ B (τ n) ω := by
    -- Proof comment: the previous mesh value is bounded below by the negated upper control for
    -- `-B`, now expressed in the next mesh normalizer.
    have hPrevBase : -(C * lilNormalizer (τ n)) ≤ B (τ n) ω := by
      linarith
    have hPrevScaled :
        -((C / Real.sqrt (α : ℝ)) * lilNormalizer (τ (n + 1))) ≤ -(C * lilNormalizer (τ n)) := by
      linarith
    exact le_trans hPrevScaled hPrevBase
  have hIncrement :
      (((α : ℝ) - 1) / (α : ℝ)) * lilNormalizer (τ (n + 1)) ≤
        B (τ (n + 1)) ω - B (τ n) ω := by
    -- Proof comment: rewrite the geometric increment event with the simpler coefficient
    -- `(α - 1) / α`.
    simpa [geometricIncrementEvent, τ, hOneDivBeta] using hIncr
  have hValueLower :
      ((((α : ℝ) - 1) / (α : ℝ)) - C / Real.sqrt (α : ℝ)) *
          lilNormalizer (τ (n + 1)) ≤
        B (τ (n + 1)) ω := by
    -- Proof comment: add the increment lower bound and the previous-point lower bound.
    nlinarith
  -- Proof comment: divide by the positive next-step normalizer to obtain the lower bound on the
  -- LIL ratio at `τ (n + 1)`.
  simpa [lilRatio] using (le_div_iff₀ hNormNextPos).2 hValueLower

/-- Helper for Theorem 22.1: after normalizing a geometric Brownian increment to variance `1`,
Lemma 22.2 gives an eventual Mills lower bound for the increment-event masses. -/
private lemma eventually_geometricIncrementEvent_measureReal_ge_millsLower
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : NNReal} (hα : 1 < (α : ℝ)) :
    let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
    let τ : ℕ → NNReal := geometricMesh α
    let x : ℕ → ℝ := fun n ↦ Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
    ∀ᶠ n in atTop, gaussianPDFReal 0 1 (x n) / (x n + 1 / x n) ≤
      μ.real (geometricIncrementEvent B α n) := by
  let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
  let τ : ℕ → NNReal := geometricMesh α
  let x : ℕ → ℝ := fun n ↦ Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact div_pos (lt_trans zero_lt_one hα) (sub_pos.mpr hα)
  have hτ_mono : Monotone τ := by
    simpa [τ] using geometricMesh_monotone hα
  have hτ_tendsto :
      Tendsto (fun n : ℕ ↦ ((τ (n + 1) : NNReal) : ℝ)) atTop atTop := by
    -- Proof comment: the shifted geometric mesh still tends to `∞`.
    simpa [τ, geometricMesh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((tendsto_pow_atTop_atTop_of_one_lt hα :
        Tendsto (fun n : ℕ ↦ (α : ℝ) ^ n) atTop atTop)).comp (Filter.tendsto_add_atTop_nat 1)
  have hEventuallyLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp 1 < ((τ (n + 1) : NNReal) : ℝ) := by
    -- Proof comment: on this tail the iterated-logarithm threshold is strictly positive.
    exact hτ_tendsto.eventually_gt_atTop (Real.exp 1)
  filter_upwards [hEventuallyLarge] with n hnLarge
  let diff : NNReal := τ (n + 1) - τ n
  let Y : Ω → ℝ := fun ω ↦ (B (τ (n + 1)) ω - B (τ n) ω) / Real.sqrt (diff : ℝ)
  have hτ_le : τ n ≤ τ (n + 1) := hτ_mono (Nat.le_succ n)
  have hdiff_real : (diff : ℝ) = ((τ (n + 1) : ℝ) - (τ n : ℝ)) := by
    simp [diff, NNReal.coe_sub hτ_le]
  have hdiff_eq :
      (diff : ℝ) = ((τ (n + 1) : ℝ)) / β := by
    rw [hdiff_real]
    simpa [β, τ] using geometricMesh_succ_sub_eq_div_beta (α := α) hα n
  have hdiff_pos : 0 < (diff : ℝ) := by
    rw [hdiff_eq]
    have hτ_pos : 0 < ((τ (n + 1) : NNReal) : ℝ) := by
      simpa [τ, geometricMesh] using
        (pow_pos (lt_trans zero_lt_one hα) (n + 1) : 0 < (α : ℝ) ^ (n + 1))
    exact div_pos hτ_pos hβ_pos
  have hsqrt_diff_pos : 0 < Real.sqrt (diff : ℝ) := Real.sqrt_pos.2 hdiff_pos
  have hlog_gt_one : 1 < Real.log ((τ (n + 1) : ℝ)) := by
    simpa using (Real.log_lt_log (Real.exp_pos 1) hnLarge)
  have hloglog_pos : 0 < Real.log (Real.log ((τ (n + 1) : ℝ))) := Real.log_pos hlog_gt_one
  have hx_pos : 0 < x n := by
    dsimp [x]
    exact Real.sqrt_pos.2 (by positivity)
  have hIncrement :
      HasLaw (fun ω ↦ B (τ (n + 1)) ω - B (τ n) ω) (gaussianReal 0 diff) μ :=
    brownianIncrement_hasLaw_ofBrownianMotion hB hτ_le
  have hScale :
      HasLaw
        (fun z : ℝ ↦ (Real.sqrt (diff : ℝ))⁻¹ * z)
        (gaussianReal 0 1)
        (gaussianReal 0 diff) := by
    let c : ℝ := (Real.sqrt (diff : ℝ))⁻¹
    let d : NNReal := ⟨c ^ 2, sq_nonneg c⟩
    have hmap :
        (gaussianReal 0 diff).map (fun z : ℝ ↦ c * z) =
          gaussianReal 0 1 := by
      have hmap0 :
          (gaussianReal 0 diff).map (c * ·) = gaussianReal 0 (d * diff) := by
        simpa [d] using (gaussianReal_map_const_mul (μ := 0) (v := diff) c)
      have hvar : d * diff = 1 := by
        ext
        simp [c, d, NNReal.coe_mul, hdiff_pos.ne', Real.sq_sqrt hdiff_pos.le]
      rw [hvar] at hmap0
      simpa [c] using hmap0
    refine ⟨?_, hmap⟩
    fun_prop
  have hScaled : HasLaw Y (gaussianReal 0 1) μ := by
    simpa [Y, Function.comp, div_eq_mul_inv, mul_comm] using hScale.comp hIncrement
  have hThreshold :
      x n * Real.sqrt (diff : ℝ) = (1 / β) * lilNormalizer (τ (n + 1)) := by
    -- Proof comment: reuse the dedicated threshold-transport bridge to avoid repeating the
    -- geometric-grid square-root algebra here.
    simpa [β, τ, diff, x] using
      geometricIncrementThreshold_mul_sqrt_diff_eq (α := α) hα n hnLarge
  have hEvent :
      Y ⁻¹' Set.Ici (x n) = geometricIncrementEvent B α n := by
    ext ω
    constructor
    · intro hω
      have hω' :
          x n * Real.sqrt (diff : ℝ) ≤ B (τ (n + 1)) ω - B (τ n) ω := by
        exact (le_div_iff₀ hsqrt_diff_pos).1 hω
      simpa [Y, geometricIncrementEvent, β, τ, hThreshold] using hω'
    · intro hω
      have hω' :
          (1 / β) * lilNormalizer (τ (n + 1)) ≤ B (τ (n + 1)) ω - B (τ n) ω := by
        simpa [geometricIncrementEvent, β, τ] using hω
      have :
          x n * Real.sqrt (diff : ℝ) ≤ B (τ (n + 1)) ω - B (τ n) ω := by
        simpa [hThreshold] using hω'
      exact (le_div_iff₀ hsqrt_diff_pos).2 this
  -- Proof comment: once the increment is normalized to variance `1`, Lemma 22.2 applies
  -- directly to the preimage of the closed ray `Set.Ici (x n)`.
  simpa [x, hEvent] using
    (HasLaw.standardNormal_tail_bounds (P := μ) (X := Y) hScaled hx_pos).1

/-- Helper for Theorem 22.1: on the coarse mesh `α = 16 (m + 1)^2`, the Mills lower profile of
the standard-normal threshold eventually dominates the harmonic term `1 / (n + 1)`. -/
private lemma eventually_invSucc_le_millsLower_coarseMesh (m : ℕ) :
    let α : NNReal := 16 * (m + 1 : NNReal) ^ 2
    let β : ℝ := (α : ℝ) / ((α : ℝ) - 1)
    let τ : ℕ → NNReal := geometricMesh α
    let x : ℕ → ℝ := fun n ↦ Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
    ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) ≤ gaussianPDFReal 0 1 (x n) / (x n + 1 / x n) := by
  let α : NNReal := 16 * (m + 1 : NNReal) ^ 2
  let αR : ℝ := (α : ℝ)
  let β : ℝ := αR / (αR - 1)
  let τ : ℕ → NNReal := geometricMesh α
  let x : ℕ → ℝ := fun n ↦ Real.sqrt ((2 / β) * Real.log (Real.log ((τ (n + 1) : ℝ))))
  let y : ℕ → ℝ := fun n ↦ (n + 1 : ℝ) * Real.log αR
  let s : ℝ := 1 / (2 * αR)
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * Real.sqrt (2 / β) *
    (Real.log αR) ^ (1 / β + s)
  have hα : 1 < αR := by
    dsimp [α, αR]
    change 1 < 16 * (m + 1 : ℝ) ^ 2
    have hm_one_le : 1 ≤ (m + 1 : ℝ) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have hsq_one_le : 1 ≤ (m + 1 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hα_pos : 0 < αR := lt_trans zero_lt_one hα
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact div_pos hα_pos (sub_pos.mpr hα)
  have hlogα_pos : 0 < Real.log αR := Real.log_pos hα
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hPowerBalance : 1 - (1 / β + s) = s := by
    dsimp [β, s]
    field_simp [show αR ≠ 0 by linarith, show αR - 1 ≠ 0 by linarith]
    ring
  have hLittleReal :
      (fun t : ℝ ↦ Real.log t) =o[atTop] fun t ↦ t ^ (2 * s) := by
    simpa using (isLittleO_log_rpow_atTop (r := 2 * s) (by positivity))
  have hY_tendsto : Tendsto y atTop atTop := by
    -- Proof comment: `y n = (n + 1) log α` is a positive constant multiple of the shifted naturals.
    simpa [y, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc, mul_comm] using
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)).const_mul_atTop hlogα_pos
  have hYVeryLarge :
      ∀ᶠ n : ℕ in atTop, Real.exp (β / 2) < y n := by
    exact hY_tendsto.eventually_gt_atTop (Real.exp (β / 2))
  have hLittleNat :
      (fun n : ℕ ↦ Real.log (y n)) =o[atTop] fun n ↦ (y n) ^ (2 * s) := by
    simpa [y] using hLittleReal.comp_tendsto hY_tendsto
  have hLogBound :
      ∀ᶠ n : ℕ in atTop, Real.log (y n) ≤ (y n) ^ (2 * s) := by
    filter_upwards [hLittleNat.eventuallyLE, hYVeryLarge] with n hn hnLarge
    have hy_pos : 0 < y n := lt_trans (Real.exp_pos (β / 2)) hnLarge
    have hlog_nonneg : 0 ≤ Real.log (y n) := by
      have hy_one_le : 1 ≤ y n := by
        exact le_trans (Real.one_lt_exp_iff.2 (by positivity)).le hnLarge.le
      exact Real.log_nonneg hy_one_le
    have hpow_nonneg : 0 ≤ (y n) ^ (2 * s) := Real.rpow_nonneg hy_pos.le _
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg, abs_of_nonneg hpow_nonneg] using hn
  have hPowLarge :
      ∀ᶠ n : ℕ in atTop, D ≤ (n + 1 : ℝ) ^ s := by
    -- Proof comment: the positive power `(n + 1)^s` tends to `∞`, so it eventually absorbs all
    -- constants coming from the Mills lower profile.
    have hPowTendsto :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) ^ s) atTop atTop := by
      convert
        (tendsto_rpow_atTop hs_pos).comp
          (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)) using 1
      funext n
      simp [Nat.cast_add, Nat.cast_one]
    exact hPowTendsto.eventually_ge_atTop D
  filter_upwards [hYVeryLarge, hLogBound, hPowLarge] with n hnLarge hLogBoundN hPowLargeN
  have hy_pos : 0 < y n := lt_trans (Real.exp_pos (β / 2)) hnLarge
  have hy_nonneg : 0 ≤ y n := hy_pos.le
  have hlogy_gt_half : β / 2 < Real.log (y n) := by
    simpa using (Real.log_lt_log (Real.exp_pos (β / 2)) hnLarge)
  have hlogy_nonneg : 0 ≤ Real.log (y n) := by
    exact le_trans (by positivity : 0 ≤ β / 2) hlogy_gt_half.le
  have hlogy_pos : 0 < Real.log (y n) := by
    have hhalf_pos : 0 < β / 2 := by positivity
    exact lt_trans hhalf_pos hlogy_gt_half
  have hx_def : x n = Real.sqrt ((2 / β) * Real.log (y n)) := by
    have hmesh :
        Real.log ((geometricMesh α (n + 1) : NNReal) : ℝ) = y n := by
      rw [show Real.log ((geometricMesh α (n + 1) : NNReal) : ℝ) = (n + 1 : ℝ) * Real.log αR by
        rw [geometricMesh, NNReal.coe_pow, ← Real.rpow_natCast, Real.log_rpow hα_pos,
          Nat.cast_add, Nat.cast_one]]
    dsimp [x]
    rw [hmesh]
  have hx_pos : 0 < x n := by
    rw [hx_def]
    exact Real.sqrt_pos.2 (mul_pos (by positivity) hlogy_pos)
  have hx_ge_one : 1 ≤ x n := by
    rw [hx_def]
    have hInside_ge_one : 1 ≤ (2 / β) * Real.log (y n) := by
      have hInside_gt_one : 1 < (2 * Real.log (y n)) / β := by
        rw [one_lt_div_iff]
        left
        exact ⟨hβ_pos, by linarith⟩
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInside_gt_one.le
    exact (Real.one_le_sqrt).2 hInside_ge_one
  have hsqrtLogBound : Real.sqrt (Real.log (y n)) ≤ (y n) ^ s := by
    calc
      Real.sqrt (Real.log (y n)) ≤ Real.sqrt ((y n) ^ (2 * s)) := Real.sqrt_le_sqrt hLogBoundN
      _ = (y n) ^ s := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy_nonneg]
          ring_nf
  have hx_upper : x n ≤ Real.sqrt (2 / β) * (y n) ^ s := by
    rw [hx_def]
    calc
      Real.sqrt ((2 / β) * Real.log (y n))
          = Real.sqrt (2 / β) * Real.sqrt (Real.log (y n)) := by
              rw [Real.sqrt_mul (show 0 ≤ 2 / β by positivity) (Real.log (y n))]
      _ ≤ Real.sqrt (2 / β) * (y n) ^ s := by
            exact mul_le_mul_of_nonneg_left hsqrtLogBound (by positivity)
  have hDenom_le : x n + 1 / x n ≤ 2 * x n := by
    have hInv_le : 1 / x n ≤ x n := by
      refine (div_le_iff₀ hx_pos).2 ?_
      nlinarith [hx_ge_one]
    linarith
  have hTail_ge_half :
      gaussianPDFReal 0 1 (x n) / (2 * x n) ≤
        gaussianPDFReal 0 1 (x n) / (x n + 1 / x n) := by
    have hInvDen : 1 / (2 * x n) ≤ 1 / (x n + 1 / x n) := by
      exact one_div_le_one_div_of_le (by positivity) hDenom_le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hInvDen (gaussianPDFReal_nonneg 0 1 (x n))
  have hInvX :
      1 / (2 * Real.sqrt (2 / β) * (y n) ^ s) ≤ 1 / (2 * x n) := by
    have hDenomBound : 2 * x n ≤ 2 * Real.sqrt (2 / β) * (y n) ^ s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hx_upper (show 0 ≤ (2 : ℝ) by positivity)
    exact one_div_le_one_div_of_le (by positivity) hDenomBound
  have hGauss :
      gaussianPDFReal 0 1 (x n) =
        (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x n) ^ 2 / 2) := by
    simp [gaussianPDFReal_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hExp :
      Real.exp (-(x n) ^ 2 / 2) = (y n) ^ (-(1 / β)) := by
    rw [hx_def, Real.sq_sqrt (by positivity)]
    have hExpArg :
        -((2 / β) * Real.log (y n)) / 2 = -(1 / β) * Real.log (y n) := by
      field_simp [show β ≠ 0 by linarith]
    rw [hExpArg, mul_comm, Real.exp_mul, Real.exp_log hy_pos]
  have hProfile :
      (1 / Real.sqrt (2 * Real.pi)) * (y n) ^ (-(1 / β)) *
          (1 / (2 * Real.sqrt (2 / β) * (y n) ^ s))
        ≤ gaussianPDFReal 0 1 (x n) / (x n + 1 / x n) := by
    calc
      (1 / Real.sqrt (2 * Real.pi)) * (y n) ^ (-(1 / β)) *
          (1 / (2 * Real.sqrt (2 / β) * (y n) ^ s))
          ≤ (1 / Real.sqrt (2 * Real.pi)) * (y n) ^ (-(1 / β)) * (1 / (2 * x n)) := by
              gcongr
      _ = gaussianPDFReal 0 1 (x n) / (2 * x n) := by
          rw [hGauss, hExp]
          ring
      _ ≤ gaussianPDFReal 0 1 (x n) / (x n + 1 / x n) := hTail_ge_half
  have hGoalMul :
      1 ≤
        ((1 / Real.sqrt (2 * Real.pi)) * (y n) ^ (-(1 / β)) *
            (1 / (2 * Real.sqrt (2 / β) * (y n) ^ s))) * (n + 1 : ℝ) := by
    have hD_pos : 0 < D := by
      dsimp [D]
      positivity
    have hConst :
        1 ≤ (n + 1 : ℝ) ^ s / D := by
      rw [le_div_iff₀ hD_pos]
      simpa using hPowLargeN
    -- Proof comment: rewrite the explicit Mills profile on the mesh to the power `(n + 1)^s / D`.
    calc
      1 ≤ (n + 1 : ℝ) ^ s / D := hConst
      _ =
          ((1 / Real.sqrt (2 * Real.pi)) * (y n) ^ (-(1 / β)) *
              (1 / (2 * Real.sqrt (2 / β) * (y n) ^ s))) * (n + 1 : ℝ) := by
            have hk_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
            have hk_pos : 0 < (n + 1 : ℝ) := by positivity
            have hNatPower :
                (n + 1 : ℝ) ^ s * (n + 1 : ℝ) ^ s =
                  (n + 1 : ℝ) ^ (1 - 1 / β) := by
              calc
                (n + 1 : ℝ) ^ s * (n + 1 : ℝ) ^ s = (n + 1 : ℝ) ^ (s + s) := by
                  rw [← Real.rpow_add hk_pos]
                _ = (n + 1 : ℝ) ^ (1 - 1 / β) := by
                  congr 1
                  linarith [hPowerBalance]
            have hNatPower' :
                (n + 1 : ℝ) * (n + 1 : ℝ) ^ (-(1 / β)) =
                  (n + 1 : ℝ) ^ (1 - 1 / β) := by
              calc
                (n + 1 : ℝ) * (n + 1 : ℝ) ^ (-(1 / β)) =
                    (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (-(1 / β)) := by
                      rw [Real.rpow_one]
                _ = (n + 1 : ℝ) ^ (1 - 1 / β) := by
                  rw [← Real.rpow_add hk_pos]
                  ring_nf
            have hLogPower :
                Real.log αR ^ (1 / β + s) * Real.log αR ^ (-(1 / β)) =
                  Real.log αR ^ s := by
              calc
                Real.log αR ^ (1 / β + s) * Real.log αR ^ (-(1 / β)) =
                    Real.log αR ^ ((1 / β + s) + -(1 / β)) := by
                      rw [← Real.rpow_add hlogα_pos]
                _ = Real.log αR ^ s := by
                  congr 1
                  ring
            have hLogExponent :
                Real.log αR ^ ((1 + β * s) / β) = Real.log αR ^ (1 / β + s) := by
              congr 1
              field_simp [show β ≠ 0 by linarith]
            dsimp [D, y]
            field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 by positivity,
              show Real.sqrt (2 / β) ≠ 0 by positivity,
              show Real.log αR ^ (1 / β + s) ≠ 0 by positivity,
              show ((n + 1 : ℝ) * Real.log αR) ^ s ≠ 0 by positivity,
              show (n + 1 : ℝ) ≠ 0 by positivity]
            rw [Real.mul_rpow hk_nonneg hlogα_pos.le, Real.mul_rpow hk_nonneg hlogα_pos.le]
            rw [hLogExponent]
            calc
              (n + 1 : ℝ) ^ s * ((n + 1 : ℝ) ^ s * Real.log αR ^ s)
                  = ((n + 1 : ℝ) ^ s * (n + 1 : ℝ) ^ s) * Real.log αR ^ s := by ring
              _ = (n + 1 : ℝ) ^ (1 - 1 / β) * Real.log αR ^ s := by rw [hNatPower]
              _ =
                  ((n + 1 : ℝ) * (n + 1 : ℝ) ^ (-(1 / β))) *
                    (Real.log αR ^ (1 / β + s) * Real.log αR ^ (-(1 / β))) := by
                      rw [hNatPower', hLogPower]
              _ =
                  (n + 1 : ℝ) *
                    (Real.log αR ^ (1 / β + s) *
                      ((n + 1 : ℝ) ^ (-(1 / β)) * Real.log αR ^ (-(1 / β)))) := by
                      calc
                        (n + 1 : ℝ) * (n + 1 : ℝ) ^ (-(1 / β)) *
                            (Real.log αR ^ (1 / β + s) * Real.log αR ^ (-(1 / β))) =
                            (n + 1 : ℝ) *
                              ((n + 1 : ℝ) ^ (-(1 / β)) *
                                (Real.log αR ^ (1 / β + s) * Real.log αR ^ (-(1 / β)))) := by
                                  rw [mul_assoc]
                        _ = (n + 1 : ℝ) *
                              (Real.log αR ^ (1 / β + s) *
                                ((n + 1 : ℝ) ^ (-(1 / β)) * Real.log αR ^ (-(1 / β)))) := by
                                  congr 1
                                  ac_rfl
              _ =
                  (n + 1 : ℝ) * Real.log αR ^ (1 / β + s) *
                    ((n + 1 : ℝ) ^ (-(1 / β)) * Real.log αR ^ (-(1 / β))) := by
                      rw [mul_assoc]
  have hProfileMul :
      1 ≤ (gaussianPDFReal 0 1 (x n) / (x n + 1 / x n)) * (n + 1 : ℝ) := by
    exact le_trans hGoalMul (by gcongr)
  -- Proof comment: convert the lower bound on the product with `(n + 1)` back to the desired
  -- harmonic lower bound.
  exact (div_le_iff₀ (show 0 < (n + 1 : ℝ) by positivity)).2 hProfileMul

/-- Helper for Theorem 22.1: the Brownian increment events on the coarse geometric mesh have an
eventual harmonic lower bound on their real masses. -/
private lemma eventually_invSucc_le_measureReal_geometricIncrementEvent
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (m : ℕ) :
    let α : NNReal := 16 * (m + 1 : NNReal) ^ 2
    ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) ≤ μ.real (geometricIncrementEvent B α n) := by
  let α : NNReal := 16 * (m + 1 : NNReal) ^ 2
  have hα : 1 < (α : ℝ) := by
    change 1 < 16 * (m + 1 : ℝ) ^ 2
    have hm_one_le : 1 ≤ (m + 1 : ℝ) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have hsq_one_le : 1 ≤ (m + 1 : ℝ) ^ 2 := by nlinarith
    nlinarith
  -- Proof comment: the lower-mass input is the composition of the probabilistic Mills lower
  -- bound and the deterministic coarse-mesh comparison.
  filter_upwards [eventually_invSucc_le_millsLower_coarseMesh m,
    eventually_geometricIncrementEvent_measureReal_ge_millsLower (B := B) hB hα] with n hn1 hn2
  exact le_trans hn1 hn2

/-- Helper for Theorem 22.1: the textbook coarse mesh `α = 16 (m + 1)^2` makes the deterministic
mesh lower bound dominate the target constant `1 - 1 / (m + 1)`. -/
private lemma one_sub_invSucc_le_geometricLowerConstant (m : ℕ) :
    1 - 1 / (m + 1 : ℝ) ≤
      ((((16 * (m + 1 : NNReal) ^ 2 : NNReal) : ℝ) - 1) /
          ((16 * (m + 1 : NNReal) ^ 2 : NNReal) : ℝ)) -
        2 / Real.sqrt ((16 * (m + 1 : NNReal) ^ 2 : NNReal) : ℝ) := by
  have hk_pos : 0 < (m + 1 : ℝ) := by positivity
  have hk_nonneg : 0 ≤ (m + 1 : ℝ) := by positivity
  have hsqrt :
      Real.sqrt ((16 * (m + 1 : NNReal) ^ 2 : NNReal) : ℝ) = 4 * (m + 1 : ℝ) := by
    change Real.sqrt (16 * (m + 1 : ℝ) ^ 2) = 4 * (m + 1 : ℝ)
    rw [show 16 * (m + 1 : ℝ) ^ 2 = (4 * (m + 1 : ℝ)) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  -- Proof comment: after identifying `√(16 (m + 1)^2) = 4 (m + 1)`, the remaining estimate is a
  -- straightforward reciprocal comparison.
  rw [hsqrt]
  have htwo :
      (2 : ℝ) / (4 * (m + 1 : ℝ)) = 1 / (2 * (m + 1 : ℝ)) := by
    field_simp [show (m + 1 : ℝ) ≠ 0 by positivity]
    ring
  rw [htwo]
  have haux :
      0 ≤ (8 * (m + 1 : ℝ) - 1) / (16 * (m + 1 : ℝ) ^ 2) := by
    have hnum : 0 ≤ 8 * (m + 1 : ℝ) - 1 := by
      nlinarith [hk_pos]
    have hden : 0 ≤ 16 * (m + 1 : ℝ) ^ 2 := by positivity
    exact div_nonneg hnum hden
  have hdiff :
      ((((16 * (m + 1 : ℝ) ^ 2) - 1) / (16 * (m + 1 : ℝ) ^ 2)) - 1 / (2 * (m + 1 : ℝ))) -
          (1 - 1 / (m + 1 : ℝ)) =
        (8 * (m + 1 : ℝ) - 1) / (16 * (m + 1 : ℝ) ^ 2) := by
    field_simp [show (16 * (m + 1 : ℝ) ^ 2) ≠ 0 by positivity, show (m + 1 : ℝ) ≠ 0 by positivity]
    ring
  have hdiff_nonneg :
      0 ≤
        ((((16 * (m + 1 : ℝ) ^ 2) - 1) / (16 * (m + 1 : ℝ) ^ 2)) - 1 / (2 * (m + 1 : ℝ))) -
          (1 - 1 / (m + 1 : ℝ)) := by
    rw [hdiff]
    exact haux
  exact sub_nonneg.mp hdiff_nonneg

/-- Helper for Theorem 22.1: the geometric-grid increment construction and second
Borel-Cantelli argument yield the almost-sure lower bound `1 - 1 / (m + 1) ≤ limsup`. -/
lemma ae_limsup_ge_one_sub_invSucc
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (m : ℕ) :
    ∀ᵐ ω ∂μ,
      1 - 1 / (m + 1 : ℝ) ≤
        limsup
          (fun t : NNReal ↦
            B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
          atTop := by
  -- Route correction: the lower half cannot be closed by local symmetry alone; it needs the
  -- independent geometric increments together with the already-isolated negative Brownian bridge
  -- and the geometric normalizer transport lemma proved just above.
  let α : NNReal := 16 * (m + 1 : NNReal) ^ 2
  have hα : 1 < (α : ℝ) := by
    change 1 < 16 * (m + 1 : ℝ) ^ 2
    have hm_one_le : 1 ≤ (m + 1 : ℝ) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have hsq_one_le : 1 ≤ (m + 1 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hUpperB :
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio B ω t ≤ (2 : ℝ) := by
    -- Proof comment: reuse the fixed-ratio upper-side bound for the original Brownian motion.
    exact ae_eventually_lilRatio_le_two (B := B) hB
  have hUpperNeg :
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, lilRatio (fun s ω ↦ -B s ω) ω t ≤ (2 : ℝ) := by
    -- Proof comment: apply the same fixed-ratio upper control to the negated Brownian motion so
    -- that earlier mesh values can be controlled from below.
    have hNegB : IsBrownianMotion μ (fun s ω ↦ -B s ω) := neg_isBrownianMotion hB
    exact ae_eventually_lilRatio_le_two (B := fun s ω ↦ -B s ω) hNegB
  have hFreq :
      ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ geometricIncrementEvent B α n := by
    have hLowerMass :
        ∀ᶠ n : ℕ in atTop, (1 / (n + 1 : ℝ)) ≤ μ.real (geometricIncrementEvent B α n) := by
      -- Proof comment: the new lower-mass helper isolates the probabilistic normalization and the
      -- coarse-mesh asymptotic comparison from the rest of the lower-limsup argument.
      simpa [α] using
        eventually_invSucc_le_measureReal_geometricIncrementEvent (B := B) hB m
    exact geometricIncrementEvents_force_frequently_of_eventually_inv_le_measureReal
      (B := B) hB hα hLowerMass
  filter_upwards [hUpperB, hUpperNeg, hFreq] with ω hUpperBω hUpperNegω hFreqω
  have hFreqMesh :
      ∃ᶠ n in atTop,
        (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤
          lilRatio B ω (geometricMesh α (n + 1)) := by
    -- Proof comment: each frequent large increment, together with the eventual upper control on
    -- `-B`, forces a large normalized value at the next mesh point.
    exact frequently_ge_lilRatio_geometricMesh_of_geometricIncrement
      (B := B) (ω := ω) (α := α) hα (C := 2) (by positivity) hUpperNegω hFreqω
  have hLimsup :
      (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) ≤
        limsup (fun t : NNReal ↦ lilRatio B ω t) atTop := by
    -- Proof comment: frequent lower bounds on the geometric mesh already control the ambient
    -- limsup once the full path is eventually bounded above.
    exact geometricMeshFrequently_le_limsup (B := B) (ω := ω) (α := α)
      (c := (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ))
      (C := 2) hα hUpperBω hFreqMesh
  have hArithmetic :
      1 - 1 / (m + 1 : ℝ) ≤
        (((α : ℝ) - 1) / (α : ℝ)) - 2 / Real.sqrt (α : ℝ) := by
    -- Proof comment: the chosen coarse mesh ratio `α = 16 (m + 1)^2` makes the deterministic
    -- mesh lower bound at least `1 - 1 / (m + 1)`.
    simpa [α] using one_sub_invSucc_le_geometricLowerConstant m
  exact le_trans hArithmetic (by simpa [lilRatio] using hLimsup)

/- Theorem 22.1 is the `core/canonical` Brownian-motion owner for the global law of the iterated
logarithm. The proof is organized as a countable squeeze: a family of almost-sure upper bounds
and a family of almost-sure lower bounds are intersected with `ae_all_iff`, then a deterministic
reciprocal-gap lemma forces the samplewise limsup to equal `1`. -/

-- Proof sketch: isolate the countable upper family `limsup ≤ 1 + 1 / (m + 1)` and the countable
-- lower family `1 - 1 / (m + 1) ≤ limsup`, intersect them on a single almost-sure event, and
-- squeeze the samplewise limsup to `1` by the deterministic reciprocal-gap lemma above.
/-- Theorem 22.1: Law of the iterated logarithm for Brownian motion. For every Brownian motion
`B`, the normalized coordinates `B t / √(2 t log log t)` have almost-sure `limsup` equal to `1`
along `t → ∞`. -/
theorem ae_limsup_div_sqrt_two_mul_t_log_log_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
        atTop = 1 := by
  -- Proof comment: once the upper and lower countable approximation families are both available,
  -- intersect them with `ae_all_iff` and close the samplewise squeeze by
  -- `eq_one_of_forall_invSucc_bounds`.
  have hUpper :
      ∀ᵐ ω ∂μ,
        ∀ m : ℕ,
          limsup
              (fun t : NNReal ↦
                B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
              atTop
            ≤ 1 + 1 / (m + 1 : ℝ) := by
    -- Proof comment: collect the countable upper approximation family onto one almost-sure set.
    exact ae_all_iff.2 (fun m ↦ ae_limsup_le_one_add_invSucc (B := B) hB m)
  have hLower :
      ∀ᵐ ω ∂μ,
        ∀ m : ℕ,
          1 - 1 / (m + 1 : ℝ) ≤
            limsup
              (fun t : NNReal ↦
                B t ω / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log (t : ℝ))))
              atTop := by
    -- Proof comment: collect the countable lower approximation family onto one almost-sure set.
    exact ae_all_iff.2 (fun m ↦ ae_limsup_ge_one_sub_invSucc (B := B) hB m)
  -- Proof comment: on the intersection of the two full-measure sets, every reciprocal bound holds
  -- simultaneously, so the deterministic squeeze lemma identifies the limsup.
  filter_upwards [hUpper, hLower] with ω hUpperω hLowerω
  exact eq_one_of_forall_invSucc_bounds hUpperω hLowerω

end IsBrownianMotion

end ProbabilityTheory
