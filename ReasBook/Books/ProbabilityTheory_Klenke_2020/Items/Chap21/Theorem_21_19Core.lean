/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 21.19: choosing the scaling factor `√T` makes the Brownian time-change
equal to `T`. -/
private lemma brownianScalingTime_sqrt (T : NNReal) :
    ProbabilityTheory.brownianScalingTime (Real.sqrt (T : ℝ)) = T := by
  -- Proof comment: `brownianScalingTime` is the square of the scaling factor, viewed in `NNReal`.
  ext
  simp [ProbabilityTheory.brownianScalingTime, Real.sq_sqrt]

/-- Helper for Theorem 21.19: every positive-time Brownian marginal assigns zero mass to a fixed
terminal value. -/
private lemma brownianTerminal_value_measure_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (x : ℝ) {t : NNReal} (ht : 0 < t) :
    μ {ω | B t ω = x} = 0 := by
  let hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht
  have hMeas : Measurable (B t) := (hB.stronglyMeasurable t).measurable
  -- Proof comment: push the singleton event through the Gaussian marginal and use atomlessness.
  calc
    μ {ω | B t ω = x} = μ.map (B t) ({x} : Set ℝ) := by
      symm
      rw [Measure.map_apply hMeas (MeasurableSet.singleton x)]
      rfl
    _ = gaussianReal 0 t ({x} : Set ℝ) := by
      rw [hLaw.map_eq]
    _ = 0 := by
      exact (noAtoms_gaussianReal (ne_of_gt ht)).measure_singleton x

/-- Helper for Theorem 21.19: for positive times, the closed terminal Brownian tail agrees with
the strict one. -/
private lemma brownianTerminal_closedTail_eq_openTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (x : ℝ) {t : NNReal} (ht : 0 < t) :
    μ {ω | x ≤ B t ω} = μ {ω | x < B t ω} := by
  let A : Set Ω := {ω | x ≤ B t ω}
  let S : Set Ω := {ω | B t ω = x}
  have hS_meas : MeasurableSet S := by
    simpa [S] using
      measurableSet_eq_fun ((hB.stronglyMeasurable t).measurable) measurable_const
  have hsplit : μ (A ∩ S) + μ (A \ S) = μ A := by
    simpa using measure_inter_add_diff (μ := μ) A hS_meas
  have hInter : A ∩ S = S := by
    ext ω
    constructor
    · intro hω
      exact hω.2
    · intro hω
      exact ⟨hω.symm.le, hω⟩
  have hDiff : A \ S = {ω | x < B t ω} := by
    ext ω
    constructor
    · rintro ⟨hωA, hωS⟩
      dsimp [A, S] at hωA hωS ⊢
      exact lt_of_le_of_ne hωA (by
        intro hEq
        exact hωS hEq.symm)
    · intro hω
      dsimp [A, S] at hω ⊢
      exact ⟨hω.le, ne_of_gt hω⟩
  have hS_zero : μ S = 0 := by
    simpa [S] using brownianTerminal_value_measure_eq_zero (hB := hB) x ht
  -- Proof comment: split the closed tail into the strict part and the null boundary singleton.
  calc
    μ A = μ (A ∩ S) + μ (A \ S) := by
      symm
      exact hsplit
    _ = μ S + μ {ω | x < B t ω} := by rw [hInter, hDiff]
    _ = μ {ω | x < B t ω} := by simp [hS_zero]

/-- Helper for Theorem 21.19: on continuous Brownian paths, hitting level `b > 0` by time `T`
is equivalent to the closed running maximum reaching at least `b` on `[0, T]`. -/
private lemma hitUpperBeforeTime_event_ae_eq_runningMaxClosed
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T} =ᵐ[μ]
      ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) := by
  -- Proof comment: on every continuous Brownian sample path, `hittingAfter ≤ T` is equivalent to
  -- an exact hit of the level `b` inside `[0, T]`; continuity and `B 0 = 0 < b` then turn the
  -- closed running-maximum condition into the same event.
  filter_upwards [hB.continuous_paths] with ω hω
  apply propext
  constructor
  · intro hHit
    classical
    let hitSet : Set NNReal := {t : NNReal | B t ω = b}
    have hHit_ne_top : hittingAfter B ({b} : Set ℝ) 0 ω ≠ ⊤ := by
      have hT_ne_top : ((T : NNReal) : ENNReal) ≠ ⊤ := by simp
      exact ne_top_of_le_ne_top hT_ne_top hHit
    have hHitSet_nonempty : hitSet.Nonempty := by
      by_contra hEmpty
      have hTop : hittingAfter B ({b} : Set ℝ) 0 ω = ⊤ := by
        rw [hittingAfter_eq_top_iff]
        intro t ht0 ht_mem
        exact hEmpty ⟨t, by simpa [hitSet] using ht_mem⟩
      exact hHit_ne_top hTop
    have hHitSet_closed : IsClosed hitSet := by
      simpa [hitSet, processPath] using (isClosed_singleton.preimage hω)
    have hHitSet_bddBelow : BddBelow hitSet := by
      refine ⟨0, ?_⟩
      intro t ht_mem
      positivity
    have hInf_mem : sInf hitSet ∈ hitSet :=
      hHitSet_closed.csInf_mem hHitSet_nonempty hHitSet_bddBelow
    have hInf_le : sInf hitSet ≤ T := by
      have hExistsEq : ∃ j : NNReal, B j ω = b := hHitSet_nonempty
      have hHitProp :
          (if ∃ j : NNReal, B j ω = b then ((sInf hitSet : NNReal) : ENNReal) else ⊤) ≤
            (T : ENNReal) := by
        simpa [hittingAfter_def, hitSet] using hHit
      have hHit' : ((sInf hitSet : NNReal) : ENNReal) ≤ (T : ENNReal) := by
        simpa [hExistsEq] using hHitProp
      exact ENNReal.coe_le_coe.mp hHit'
    exact ⟨sInf hitSet, ⟨by positivity, hInf_le⟩, by simpa [hitSet] using hInf_mem.ge⟩
  · rintro ⟨t, ht, ht_ge⟩
    by_cases ht_eq : B t ω = b
    · exact (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
        (ω := ω) ht.1 (by simp [ht_eq])).trans (by exact_mod_cast ht.2)
    · have hb_mem : b ∈ Set.Icc (B 0 ω) (B t ω) := by
        refine ⟨?_, ht_ge⟩
        simpa [hB.zero] using hb.le
      obtain ⟨s, hsIcc, hs_eq⟩ :=
        (intermediate_value_Icc
          (a := (0 : NNReal))
          (b := t)
          ht.1
          hω.continuousOn) hb_mem
      exact
        (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
          (ω := ω) hsIcc.1 (by simpa [processPath] using hs_eq)).trans <|
          by
            exact_mod_cast hsIcc.2.trans ht.2

/-- Helper for Theorem 21.19: adjoining the terminal cutoff preserves the almost-sure bridge
between the hitting-time event and the closed running-maximum event. -/
private lemma hitUpperBeforeTime_terminalBelow_event_ae_eq_runningMaxClosed
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T ∧ B T ω ≤ y} =ᵐ[μ]
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) ∩
        {ω | B T ω ≤ y}) : Set Ω) := by
  -- Proof comment: intersect the almost-sure hitting-time/running-maximum bridge with the common
  -- terminal cutoff event `B T ≤ y`.
  filter_upwards [hitUpperBeforeTime_event_ae_eq_runningMaxClosed (μ := μ) (B := B) hB hb
      (T := T)] with ω hω
  apply propext
  constructor
  · intro hω'
    exact ⟨hω.mp hω'.1, hω'.2⟩
  · rintro ⟨hRun, hTerm⟩
    exact ⟨hω.mpr hRun, hTerm⟩

/-- Helper for Theorem 21.19: Brownian scaling transports the closed level-and-terminal slice on
`[0, T]` to the unit-time slice for the scaled Brownian motion. -/
private lemma scaledClosedRunningMaximum_terminalBelow_event_eq
    {B : NNReal → Ω → ℝ} {b y : ℝ} {T : NNReal} (hT : 0 < T) :
    ((({ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ B s ω} : Set Ω) ∩
      {ω | B T ω ≤ y}) : Set Ω) =
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) 1,
            b / Real.sqrt (T : ℝ) ≤
              brownianScaling B (Real.sqrt (T : ℝ)) t ω} : Set Ω) ∩
        {ω | brownianScaling B (Real.sqrt (T : ℝ)) 1 ω ≤ y / Real.sqrt (T : ℝ)}) : Set Ω) := by
  -- TODO: rewrite the closed level-and-terminal slice under the Brownian scaling map with factor
  -- `√T`, using the explicit inverse time-change `s ↦ s / T`.
  sorry

/-- Helper for Theorem 21.19: the unit-time reflected slice identity is the remaining imported
support theorem needed by the arbitrary-horizon scaling argument. -/
private lemma unitHitUpperBeforeOne_terminalBelow_measure_eq_reflectedTail_core_local
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) (hyb : y < b) :
    μ {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y} =
      μ {ω | 2 * b - y ≤ B 1 ω} := by
  -- TODO: this is exactly the theorem-local `UnitSlice` owner result. The current environment
  -- lacks the corresponding built `.olean`, so the support theorem cannot be imported for
  -- validation in this proof pass.
  sorry

/-- Helper for Theorem 21.19: transport the unit-time reflected slice identity to an arbitrary
positive horizon `T`. -/
private lemma hitUpperBeforeTime_terminalBelow_eq_reflectedTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) {T : NNReal} (hT : 0 < T) (hyb : y < b) :
    μ {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T ∧ B T ω ≤ y} =
      μ {ω | 2 * b - y ≤ B T ω} := by
  -- TODO: combine the AE bridge, the scaling set equality, and the unit-time reflected slice
  -- theorem to transport the reflection identity from horizon `1` to horizon `T`.
  sorry

/-- Helper for Theorem 21.19: the strict running-maximum event is the increasing union of the
closed running-maximum events at the nearby levels `a + (n + 2)⁻¹`. -/
private lemma strictRunningMaximumEvent_eq_iUnion_closedLevels
    {B : NNReal → Ω → ℝ} {a : ℝ} (T : NNReal) :
    ({ω | ∃ s ∈ Set.Icc (0 : NNReal) T, a < B s ω} : Set Ω) =
      ⋃ n : ℕ, {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, a + (n + 2 : ℝ)⁻¹ ≤ B s ω} := by
  -- TODO: approximate the strict barrier `a` from above by the decreasing levels
  -- `a + (n + 2)⁻¹`, keeping the original witness time `s`.
  sorry

/-- Helper for Theorem 21.19: the strict terminal upper tail is the increasing union of the
nearby closed upper tails. -/
private lemma strictTerminalEvent_eq_iUnion_closedLevels
    {B : NNReal → Ω → ℝ} (a : ℝ) (T : NNReal) :
    ({ω | a < B T ω} : Set Ω) =
      ⋃ n : ℕ, {ω | a + (n + 2 : ℝ)⁻¹ ≤ B T ω} := by
  -- TODO: identify the strict terminal tail with the increasing union of nearby closed tails.
  sorry

/-- Helper for Theorem 21.19: the closed running-maximum event on `[0, T]` has probability
`2 * P[b ≤ B_T]`. -/
private lemma closedRunningMaximum_eq_two_mul_terminalClosedTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} (hb : 0 < b) {T : NNReal} (hT : 0 < T) :
    μ {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ B s ω} =
      2 * μ {ω | b ≤ B T ω} := by
  -- TODO: split the closed running-maximum event by the measurable terminal tail, identify the
  -- lower branch with a monotone union of reflected slices, and use the terminal no-atom lemma to
  -- replace the open tail by the closed tail.
  sorry

/-- Theorem 21.19: for Brownian motion, the strict running maximum on `[0, T]` has probability
`2 * P[B T > a]`. -/
theorem runningMaximum_eq_two_mul_brownianTerminalTail
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    μ {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, a < B s ω} =
      2 * μ {ω | a < B T ω} := by
  -- Route correction: first prove the closed-level reflection identity, then obtain the strict
  -- event by the monotone union over the nearby closed levels `a + (n + 2)⁻¹`.
  -- TODO: finish the monotone-union assembly from the preceding closed-level helper.
  sorry

end ProbabilityTheory
