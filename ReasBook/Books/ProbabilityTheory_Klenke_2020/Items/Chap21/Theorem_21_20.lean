/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.BrownianStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19Core

open MeasureTheory ProbabilityTheory Filter

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The last zero time of a real-valued path on `[0, ∞)` before the horizon `T`. -/
def pathLastZeroBefore (f : NNReal → ℝ) (T : NNReal) : NNReal :=
  sSup ({t : NNReal | t ≤ T ∧ f t = 0} : Set NNReal)

/-- The last zero time of the sample path `t ↦ B t ω` before the horizon `T`. -/
def lastZeroBefore (B : NNReal → Ω → ℝ) (T : NNReal) : Ω → NNReal :=
  fun ω ↦ pathLastZeroBefore (fun t ↦ B t ω) T

omit [MeasurableSpace Ω] in
/-- Evaluating `lastZeroBefore B T` at `ω` rewrites it as the pathwise supremum of zero times. -/
theorem lastZeroBefore_apply (B : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    lastZeroBefore B T ω = pathLastZeroBefore (fun t ↦ B t ω) T := by
  rfl

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: the pathwise last zero before `T` never exceeds the horizon `T`. -/
theorem pathLastZeroBefore_le_horizon (f : NNReal → ℝ) (T : NNReal) :
    pathLastZeroBefore f T ≤ T := by
  -- Proof comment: every zero time contributing to the defining supremum already lies below `T`.
  change sSup ({t : NNReal | t ≤ T ∧ f t = 0} : Set NNReal) ≤ T
  refine (csSup_le_iff' ?_).2 ?_
  · exact ⟨T, fun t ht ↦ ht.1⟩
  intro t ht
  exact ht.1

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: the pathwise last zero before `T` is at most `t` exactly when the
path avoids `0` on the tail interval `Set.Ioc t T`. -/
theorem pathLastZeroBefore_le_iff (f : NNReal → ℝ) {t T : NNReal} (ht : t ≤ T) :
    pathLastZeroBefore f T ≤ t ↔ ∀ s ∈ Set.Ioc t T, f s ≠ 0 := by
  constructor
  · intro hsup s hs hsZero
    -- Proof comment: a zero strictly after `t` would belong to the defining zero-time set and
    -- force the supremum above `t`.
    have hsMem : s ∈ ({u : NNReal | u ≤ T ∧ f u = 0} : Set NNReal) := ⟨hs.2, hsZero⟩
    have hsLe : s ≤ pathLastZeroBefore f T := by
      exact le_csSup ⟨T, fun u hu ↦ hu.1⟩ hsMem
    exact (not_le_of_gt hs.1) (le_trans hsLe hsup)
  · intro hAvoid
    -- Proof comment: every zero time contributing to the supremum must lie at or before `t`,
    -- because zeros in the tail interval are excluded by hypothesis.
    change sSup ({u : NNReal | u ≤ T ∧ f u = 0} : Set NNReal) ≤ t
    refine (csSup_le_iff' ?_).2 ?_
    · exact ⟨T, fun s hs ↦ hs.1⟩
    intro s hs
    by_cases hst : s ≤ t
    · exact hst
    · have hts : t < s := lt_of_not_ge hst
      have hsIoc : s ∈ Set.Ioc t T := ⟨hts, hs.1⟩
      exact False.elim ((hAvoid s hsIoc) hs.2)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: the event `{lastZeroBefore B T ≤ t}` is the tail zero-avoidance
event on `Set.Ioc t T`. -/
theorem lastZeroBefore_preimage_Iic_eq_tailZeroAvoidance
    (B : NNReal → Ω → ℝ) {t T : NNReal} (ht : t ≤ T) :
    ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic t) =
      {ω | ∀ s ∈ Set.Ioc t T, B s ω ≠ 0} := by
  ext ω
  constructor
  · intro hω
    -- Proof comment: rewrite the event through the pathwise supremum description and apply the
    -- pathwise bridge to tail zero-avoidance.
    change ((lastZeroBefore B T ω : NNReal) : ℝ) ≤ t at hω
    rw [lastZeroBefore_apply] at hω
    exact (pathLastZeroBefore_le_iff (fun s ↦ B s ω) ht).mp (by exact_mod_cast hω)
  · intro hω
    -- Proof comment: the same bridge turns tail zero-avoidance back into the pathwise supremum
    -- inequality, which is then recast in the real-valued event language.
    change ((lastZeroBefore B T ω : NNReal) : ℝ) ≤ t
    rw [lastZeroBefore_apply]
    exact_mod_cast (pathLastZeroBefore_le_iff (fun s ↦ B s ω) ht).mpr hω

/-- Helper for Theorem 21.20: coordinatewise measurability makes a process adapted to its
natural filtration. -/
theorem adapted_processFiltration_of_measurable
    {β : Type*} [MeasurableSpace β] {X : NNReal → Ω → β}
    (hX_meas : ∀ t : NNReal, Measurable (X t)) :
    Adapted (processFiltration X) X := by
  intro t
  -- Proof comment: the time-`t` coordinate is one of the generators of `processFiltration X t`.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX_meas t)) <| by
    refine le_iSup_of_le t ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Theorem 21.20: pointwise negation preserves Brownian motion. -/
theorem neg_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (fun t ω ↦ -B t ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the time-zero value stays `0` after negation.
    funext ω
    simp [hB.zero]
  · -- Proof comment: independent increments are preserved under the measurable map `x ↦ -x`.
    simpa using hB.indepIncrements.neg
  · -- Proof comment: the increment of `-B` is the negation of the matching increment of `B`.
    intro r s t
    convert (hB.stationaryIncrements r s t).comp measurable_neg using 1
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under negation.
    simpa using ProbabilityTheory.gaussianReal_neg (hB.gaussian_marginal ht)
  · -- Proof comment: pointwise negation preserves continuity of each sample path.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.neg

/-- Helper for Theorem 21.20: choosing the Brownian scaling factor `√T` recovers the horizon `T`
as the scaled time parameter. -/
theorem brownianScalingTime_sqrt (T : NNReal) :
    ProbabilityTheory.brownianScalingTime (Real.sqrt (T : ℝ)) = T := by
  -- Proof comment: `brownianScalingTime` records the square of the scaling factor as an
  -- `NNReal`, and squaring `√T` returns `T`.
  ext
  simp [ProbabilityTheory.brownianScalingTime, Real.sq_sqrt]

/-- Helper for Theorem 21.20: at a positive level, the closed running-maximum event has the same
probability as the strict running-maximum event. -/
theorem shiftedIncrement_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    IsBrownianMotion μ (fun u ω ↦ B (t + u) ω - B t ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the recentered process starts from `0` at time `u = 0`.
    funext ω
    simp
  · -- Proof comment: increment blocks of the shifted process are just translated increment
    -- blocks of the original Brownian motion.
    intro n times hmono
    have htranslated :
        ∀ i j, i ≤ j → (fun k ↦ t + times k) i ≤ (fun k ↦ t + times k) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (hmono hij) t
    simpa [add_assoc] using hB.indepIncrements n (fun k ↦ t + times k) htranslated
  · -- Proof comment: stationary increments are invariant under deterministic time translation.
    intro u s r
    simpa [add_assoc, add_left_comm, add_comm] using hB.stationaryIncrements (t + u) s r
  · intro u hu
    -- Proof comment: the shifted time-`u` value is distributed like the original increment
    -- `B u - B 0`, and `B 0 = 0`.
    let X : Ω → ℝ := fun ω ↦ B (t + u) ω - B t ω
    let Y : Ω → ℝ := fun ω ↦ B (u + 0) ω - B 0 ω
    have hStat : IdentDistrib X Y μ μ := by
      simpa [X, Y, add_comm, add_left_comm, add_assoc] using hB.stationaryIncrements 0 u t
    have hYLaw : HasLaw Y (gaussianReal 0 u) μ := by
      have hLaw : HasLaw (B u) (gaussianReal 0 u) μ := hB.gaussian_marginal hu
      simpa [Y, hB.zero] using hLaw
    exact hStat.symm.hasLaw hYLaw
  · -- Proof comment: translating time and subtracting a constant preserve path continuity.
    filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun s : NNReal ↦ B (t + s) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Theorem 21.20: on the interior branch, the tail-zero event rewrites to the shifted
increment process started from the anchor value `B t ω`. -/
theorem tailZeroAvoidance_eq_shiftedIncrementAvoidance
    (B : NNReal → Ω → ℝ) {t T : NNReal} (ht : t ≤ T) :
    {ω | ∀ s ∈ Set.Ioc t T, B s ω ≠ 0} =
      {ω | ∀ u ∈ Set.Ioc 0 (T - t), B t ω + (B (t + u) ω - B t ω) ≠ 0} := by
  ext ω
  constructor
  · intro hω u hu
    -- Proof comment: reindex the tail interval by the shifted parameter `u = s - t`.
    have htu : t + u ∈ Set.Ioc t T := by
      refine ⟨?_, ?_⟩
      · simpa using add_lt_add_left hu.1 t
      · calc
          t + u ≤ t + (T - t) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hu.2 t
          _ = T := by
            simpa [add_assoc, add_left_comm, add_comm] using (tsub_add_cancel_of_le ht)
    simpa [sub_eq_add_neg, add_assoc] using hω (t + u) htu
  · intro hω s hs
    -- Proof comment: conversely, every tail time `s` is `t + (s - t)` with `s - t ∈ (0, T - t]`.
    have hu : s - t ∈ Set.Ioc 0 (T - t) := by
      refine ⟨?_, ?_⟩
      · exact tsub_pos_of_lt hs.1
      · have hs' : s ≤ T - t + t := by
          simpa [tsub_add_cancel_of_le ht, add_assoc, add_left_comm, add_comm] using hs.2
        simpa [add_comm, add_left_comm, add_assoc] using hs'
    have hst : t + (s - t) = s := by
      exact add_tsub_cancel_of_le hs.1.le
    simpa [hst, sub_eq_add_neg, add_assoc] using hω (s - t) hu

/-- Helper for Theorem 21.20: a nondegenerate Gaussian marginal has no jump at a deterministic
threshold, so the closed and open lower tails have the same real-valued mass. -/
theorem gaussianReal_closedTail_eq_openTail
    {m : ℝ} {δ : NNReal} (hδ : 0 < δ) (a : ℝ) :
    (gaussianReal m δ).real (Set.Iic a) = (gaussianReal m δ).real (Set.Iio a) := by
  let ν : Measure ℝ := gaussianReal m δ
  have hUnion : Set.Iic a = Set.Iio a ∪ ({a} : Set ℝ) := by
    ext x
    simp
  have hDisjoint : Disjoint (Set.Iio a) ({a} : Set ℝ) := by
    refine Set.disjoint_left.2 ?_
    intro x hxLeft hxEq
    exact hxLeft.ne (by simpa using hxEq)
  have hSingleton : ν.real ({a} : Set ℝ) = 0 := by
    -- Proof comment: positive-variance Gaussian laws are atomless, so the threshold singleton
    -- carries no mass.
    simpa [ν, Measure.real_def] using
      congrArg ENNReal.toReal ((noAtoms_gaussianReal (ne_of_gt hδ)).measure_singleton a)
  -- Proof comment: split the closed tail into the open tail plus the null singleton endpoint.
  calc
    ν.real (Set.Iic a) = ν.real (Set.Iio a ∪ ({a} : Set ℝ)) := by rw [hUnion]
    _ = ν.real (Set.Iio a) + ν.real ({a} : Set ℝ) := by
          exact
            MeasureTheory.measureReal_union hDisjoint
              (show MeasurableSet ({a} : Set ℝ) by exact MeasurableSet.singleton a)
    _ = ν.real (Set.Iio a) := by rw [hSingleton]; ring

/-- Helper for Theorem 21.20: the two centered Gaussian closed tails at `a` and `-a`
complement each other. -/
theorem centeredGaussian_closedTail_reflect
    {δ : NNReal} (hδ : 0 < δ) (a : ℝ) :
    (gaussianReal 0 δ).real (Set.Iic a) =
      1 - (gaussianReal 0 δ).real (Set.Iic (-a)) := by
  let ν : Measure ℝ := gaussianReal 0 δ
  have hTailSymm :
      ν.real (Set.Ioi a) = ν.real (Set.Iio (-a)) := by
    have hSymm : ν.map (fun x : ℝ ↦ -x) = ν := by
      simpa [ν] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := δ)
    -- Proof comment: negate the right tail and use symmetry of the centered Gaussian law.
    calc
      ν.real (Set.Ioi a) = (ν.map (fun x : ℝ ↦ -x)).real (Set.Ioi a) := by rw [hSymm]
      _ = ν.real (Set.Iio (-a)) := by
            rw [Measure.real_def, Measure.map_apply measurable_neg measurableSet_Ioi]
            have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ioi a = Set.Iio (-a) := by
              ext x
              simp
            rw [hpre, Measure.real_def]
  have hCompl :
      ν.real (Set.Iic a) = 1 - ν.real (Set.Ioi a) := by
    -- Proof comment: the right-open tail is the complement of the closed lower tail.
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub (μ := ν) (s := Set.Ioi a) measurableSet_Ioi)
  calc
    ν.real (Set.Iic a) = 1 - ν.real (Set.Ioi a) := hCompl
    _ = 1 - ν.real (Set.Iio (-a)) := by rw [hTailSymm]
    _ = 1 - ν.real (Set.Iic (-a)) := by
          rw [← gaussianReal_closedTail_eq_openTail (m := 0) (δ := δ) hδ (-a)]

/-- Helper for Theorem 21.20: the centered Gaussian mass of the symmetric closed interval
`[-a, a]` is exactly the lower-boundary reflection expression. -/
theorem centeredGaussian_interval_real_eq_lowerBoundaryCdf
    {δ : NNReal} (hδ : 0 < δ) {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 δ).real (Set.Icc (-a) a) =
      1 - 2 * (gaussianReal 0 δ).real (Set.Iic (-a)) := by
  let ν : Measure ℝ := gaussianReal 0 δ
  have hSplit :
      ν.real (Set.Iic a) = ν.real (Set.Iio (-a)) + ν.real (Set.Icc (-a) a) := by
    have hUnion : Set.Iic a = Set.Iio (-a) ∪ Set.Icc (-a) a := by
      ext x
      constructor
      · intro hx
        by_cases hxLeft : x < -a
        · exact Or.inl hxLeft
        · exact Or.inr ⟨le_of_not_gt hxLeft, hx⟩
      · intro hx
        rcases hx with hxLeft | hxMid
        · have hxLeft' : x < -a := hxLeft
          have hneg_lt : -a < a := by
            linarith
          exact le_of_lt (lt_trans hxLeft' hneg_lt)
        · exact hxMid.2
    have hDisjoint : Disjoint (Set.Iio (-a)) (Set.Icc (-a) a) := by
      refine Set.disjoint_left.2 ?_
      intro x hxLeft hxMid
      have hxLeft' : x < -a := hxLeft
      exact not_le_of_gt hxLeft' hxMid.1
    -- Proof comment: decompose the left half-line at the reflected threshold `-a`.
    calc
      ν.real (Set.Iic a) = ν.real (Set.Iio (-a) ∪ Set.Icc (-a) a) := by rw [hUnion]
      _ = ν.real (Set.Iio (-a)) + ν.real (Set.Icc (-a) a) := by
            exact MeasureTheory.measureReal_union hDisjoint measurableSet_Icc
  have hReflect :
      ν.real (Set.Iic a) = 1 - ν.real (Set.Iic (-a)) :=
    centeredGaussian_closedTail_reflect (δ := δ) hδ a
  -- Proof comment: combine the strip decomposition with the reflected-tail identity.
  calc
    ν.real (Set.Icc (-a) a) = ν.real (Set.Iic a) - ν.real (Set.Iio (-a)) := by
          linarith [hSplit]
    _ = ν.real (Set.Iic a) - ν.real (Set.Iic (-a)) := by
          rw [← gaussianReal_closedTail_eq_openTail (m := 0) (δ := δ) hδ (-a)]
    _ = 1 - 2 * ν.real (Set.Iic (-a)) := by
          linarith [hReflect]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: on a continuous path started below `b`, an exact hit of `b` on
`[0, T]` is equivalent to strict hits of every lower level `b - b / (n + 2)`. -/
theorem continuous_exists_eq_level_iff_forall_strictLowerLevels
    {f : NNReal → ℝ} (hcont : Continuous f) (hf0 : f 0 = 0)
    {b : ℝ} (hb : 0 < b) {T : NNReal} :
    (∃ s ∈ Set.Icc (0 : NNReal) T, f s = b) ↔
      ∀ n : ℕ, ∃ s ∈ Set.Icc (0 : NNReal) T, b - b / (n + 2 : ℝ) < f s := by
  constructor
  · rintro ⟨s, hs, hsEq⟩ n
    -- Proof comment: the same hitting time for level `b` also lies above every lower threshold.
    refine ⟨s, hs, ?_⟩
    have hfrac : 0 < b / (n + 2 : ℝ) := by positivity
    linarith
  · intro hLower
    -- Proof comment: a continuous path that crosses every lower level attains a maximum at least
    -- `b`, and the intermediate value theorem then recovers an exact hit of `b`.
    obtain ⟨smax, hsmax_mem, hsmax_max⟩ :=
      isCompact_Icc.exists_isMaxOn
        ⟨0, Set.mem_Icc.2 ⟨le_rfl, by simp⟩⟩ hcont.continuousOn
    have hmax_ge : b ≤ f smax := by
      by_contra hlt
      have hgap : 0 < b - f smax := sub_pos.mpr (lt_of_not_ge hlt)
      have hratio : 0 < (b - f smax) / b := by positivity
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hratio
      have hsmall : (1 : ℝ) / (n + 2 : ℝ) < (b - f smax) / b := by
        have hmono : (1 : ℝ) / (n + 2 : ℝ) ≤ (1 : ℝ) / (n + 1 : ℝ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · norm_num
        exact lt_of_le_of_lt hmono hn
      rcases hLower n with ⟨s, hs_mem, hs_lt⟩
      have hs_le : f s ≤ f smax := hsmax_max hs_mem
      have hfrac : b / (n + 2 : ℝ) < b - f smax := by
        field_simp [hb.ne'] at hsmall ⊢
        nlinarith
      have hupper : b - b / (n + 2 : ℝ) < f smax := lt_of_lt_of_le hs_lt hs_le
      linarith
    have hlevel : b ∈ Set.Icc (f 0) (f smax) := by
      refine ⟨?_, hmax_ge⟩
      simpa [hf0] using hb.le
    obtain ⟨s, hsIcc, hsEq⟩ :=
      intermediate_value_Icc hsmax_mem.1 hcont.continuousOn hlevel
    exact ⟨s, ⟨hsIcc.1, hsIcc.2.trans hsmax_mem.2⟩, hsEq⟩

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: a closed tail `{b ≤ x}` is the decreasing intersection of the
strict lower tails `{b - b / (n + 2) < x}`. -/
theorem closedTail_iff_forall_strictLowerLevels
    {b x : ℝ} (hb : 0 < b) :
    b ≤ x ↔ ∀ n : ℕ, b - b / (n + 2 : ℝ) < x := by
  constructor
  · intro hx n
    -- Proof comment: every strict lower level still lies below a point in the closed tail.
    have hfrac : 0 < b / (n + 2 : ℝ) := by positivity
    linarith
  · intro hLower
    -- Proof comment: if `x < b`, choose a lower level already above `x` to contradict the
    -- assumed strict lower-tail membership.
    by_contra hx
    have hgap : 0 < b - x := sub_pos.mpr (lt_of_not_ge hx)
    have hratio : 0 < (b - x) / b := by positivity
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hratio
    have hsmall : (1 : ℝ) / (n + 2 : ℝ) < (b - x) / b := by
      have hmono : (1 : ℝ) / (n + 2 : ℝ) ≤ (1 : ℝ) / (n + 1 : ℝ) := by
        apply one_div_le_one_div_of_le
        · positivity
        · norm_num
      exact lt_of_le_of_lt hmono hn
    have hfrac : b / (n + 2 : ℝ) < b - x := by
      field_simp [hb.ne'] at hsmall ⊢
      nlinarith
    have hlt : b - b / (n + 2 : ℝ) < x := hLower n
    linarith

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: on a continuous path started at `0`, reaching `b` by time `T` is
equivalent to hitting each strict lower level at some nonnegative rational time before `T`. -/
theorem continuous_exists_upperCrossing_iff_forall_nnrat_strictLowerLevels
    {f : NNReal → ℝ} (hcont : Continuous f) (hf0 : f 0 = 0)
    {b : ℝ} (hb : 0 < b) {T : NNReal} :
    (∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ f s) ↔
      ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧
        b - b / (n + 2 : ℝ) < f (q : NNReal) := by
  constructor
  · intro hHit n
    have hEq : ∃ s ∈ Set.Icc (0 : NNReal) T, f s = b := by
      rcases hHit with ⟨s, hs, hsLevel⟩
      have hlevel : b ∈ Set.Icc (f 0) (f s) := by
        refine ⟨?_, hsLevel⟩
        simpa [hf0] using hb.le
      obtain ⟨t, htIcc, htEq⟩ :=
        intermediate_value_Icc hs.1 hcont.continuousOn hlevel
      exact ⟨t, ⟨htIcc.1, htIcc.2.trans hs.2⟩, htEq⟩
    rcases
        (continuous_exists_eq_level_iff_forall_strictLowerLevels
          (f := f) hcont hf0 hb).mp hEq n with ⟨s, hs, hsLt⟩
    have hs_ne_zero : s ≠ 0 := by
      intro hs_zero
      have hthreshold_pos : 0 < b - b / (n + 2 : ℝ) := by
        have hden_pos : 0 < (n + 2 : ℝ) := by positivity
        have hn_nonneg : (0 : ℝ) ≤ n := by positivity
        have hden_gt_one : (1 : ℝ) < (n + 2 : ℝ) := by
          linarith
        have hfrac_lt : b / (n + 2 : ℝ) < b := by
          have hmul : b < b * (n + 2 : ℝ) := by
            nlinarith [hb, hden_gt_one]
          exact (div_lt_iff₀ hden_pos).2 hmul
        linarith
      have : b - b / (n + 2 : ℝ) < 0 := by
        simpa [hs_zero, hf0] using hsLt
      linarith
    have hs_pos : 0 < s := bot_lt_iff_ne_bot.mpr hs_ne_zero
    let U : Set NNReal := {t : NNReal | b - b / (n + 2 : ℝ) < f t}
    have hU_open : IsOpen U := by
      simpa [U] using (isOpen_Ioi.preimage hcont)
    have hsU : s ∈ U := by
      simpa [U] using hsLt
    have hUNhds : U ∈ nhds s := hU_open.mem_nhds hsU
    rcases
        (mem_nhds_iff_exists_Ioo_subset'
          (show ∃ l : NNReal, l < s from ⟨0, hs_pos⟩)
          (show ∃ r : NNReal, s < r from
            ⟨s + 1, by simpa using lt_add_of_pos_right s zero_lt_one⟩)).1 hUNhds with
      ⟨l, r, hlr, hIoo⟩
    obtain ⟨q, hql, hqs⟩ := exists_rat_btwn
      (show (l : ℝ) < (s : ℝ) by exact_mod_cast hlr.1)
    have hq_nonneg : 0 ≤ q := by
      have h0le_l : (0 : ℝ) ≤ (l : ℝ) := by
        exact_mod_cast (show 0 ≤ l by simp)
      exact Rat.cast_nonneg.mp (le_trans h0le_l hql.le)
    let qnn : ℚ≥0 := ⟨q, hq_nonneg⟩
    have hql_nn : l < (qnn : NNReal) := by
      exact_mod_cast hql
    have hqs_nn : (qnn : NNReal) < s := by
      exact_mod_cast hqs
    have hqU : (qnn : NNReal) ∈ U := by
      exact hIoo ⟨hql_nn, lt_trans hqs_nn hlr.2⟩
    refine ⟨qnn, hqs_nn.le.trans hs.2, ?_⟩
    simpa [U] using hqU
  · intro hApprox
    have hLower :
        ∀ n : ℕ, ∃ s ∈ Set.Icc (0 : NNReal) T, b - b / (n + 2 : ℝ) < f s := by
      intro n
      rcases hApprox n with ⟨q, hqT, hqLt⟩
      exact ⟨(q : NNReal), ⟨by simp, hqT⟩, hqLt⟩
    rcases
        (continuous_exists_eq_level_iff_forall_strictLowerLevels
          (f := f) hcont hf0 hb).mpr hLower with ⟨s, hs, hsEq⟩
    exact ⟨s, hs, hsEq.ge⟩

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: on a continuous path, a strict upper crossing before `T` already
occurs at some nonnegative rational time before `T`. -/
theorem continuous_exists_strictUpperCrossing_iff_exists_nnrat
    {f : NNReal → ℝ} (hcont : Continuous f) {a : ℝ} {T : NNReal} :
    (∃ s ∈ Set.Icc (0 : NNReal) T, a < f s) ↔
      ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧ a < f (q : NNReal) := by
  constructor
  · rintro ⟨s, hsIcc, hslt⟩
    by_cases hs0 : s = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa [hs0] using hsIcc.2
      · simpa [hs0] using hslt
    · have hs_pos : 0 < s := bot_lt_iff_ne_bot.mpr hs0
      let U : Set NNReal := {t : NNReal | a < f t}
      have hU_open : IsOpen U := by
        simpa [U] using (isOpen_Ioi.preimage hcont)
      have hsU : s ∈ U := by
        simpa [U] using hslt
      have hUNhds : U ∈ nhds s := hU_open.mem_nhds hsU
      rcases
          (mem_nhds_iff_exists_Ioo_subset'
            (show ∃ l : NNReal, l < s from ⟨0, hs_pos⟩)
            (show ∃ r : NNReal, s < r from
              ⟨s + 1, by simpa using lt_add_of_pos_right s zero_lt_one⟩)).1 hUNhds with
        ⟨l, r, hlr, hIoo⟩
      obtain ⟨q, hql, hqs⟩ := exists_rat_btwn
        (show (l : ℝ) < (s : ℝ) by exact_mod_cast hlr.1)
      have hq_nonneg : 0 ≤ q := by
        have h0le_l : (0 : ℝ) ≤ (l : ℝ) := by
          exact_mod_cast (show 0 ≤ l by simp)
        exact Rat.cast_nonneg.mp (le_trans h0le_l hql.le)
      let qnn : ℚ≥0 := ⟨q, hq_nonneg⟩
      have hql_nn : l < (qnn : NNReal) := by
        exact_mod_cast hql
      have hqs_nn : (qnn : NNReal) < s := by
        exact_mod_cast hqs
      have hqU : (qnn : NNReal) ∈ U := by
        exact hIoo ⟨hql_nn, lt_trans hqs_nn hlr.2⟩
      refine ⟨qnn, hqs_nn.le.trans hsIcc.2, ?_⟩
      simpa [U] using hqU
  · rintro ⟨q, hqT, hq⟩
    exact ⟨q, ⟨by simp, hqT⟩, by simpa using hq⟩

/-- Helper for Theorem 21.20: subtracting the random start value from a Brownian motion started at
`0` produces an exact Brownian motion. -/
private theorem startedAtZero_sub_start_isBrownianMotionBridge
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotionStartedAt μ W 0) :
    IsBrownianMotion μ (fun t ω ↦ W t ω - W 0 ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting the common time-zero anchor makes the corrected process vanish
    -- identically at time `0`.
    funext ω
    simp
  · -- Proof comment: the random anchor cancels inside every increment, so independence is
    -- unchanged.
    intro n times hmono
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hW.indepIncrements n times hmono
  · -- Proof comment: the same cancellation turns the corrected increments into the original
    -- stationary-increment family.
    intro r s t
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hW.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: at positive times the corrected process is exactly the increment over
    -- `[0, t]`.
    simpa using
      startedAtZeroIncrement_hasLaw (hX := hW) (s := (0 : NNReal)) (t := t)
        (show 0 ≤ t by simp)
  · -- Proof comment: subtracting the constant initial value preserves continuity of each sample
    -- path.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 21.20: if two sample paths agree pointwise at one sample, then their
singleton hitting times agree at that sample. -/
private lemma hittingAfter_eq_of_pointwise_eq
    {u v : NNReal → Ω → ℝ} {S : Set ℝ} {n : NNReal} {ω : Ω}
    (hω : ∀ k : NNReal, u k ω = v k ω) :
    hittingAfter u S n ω = hittingAfter v S n ω := by
  by_cases hu : ∃ j : NNReal, n ≤ j ∧ u j ω ∈ S
  · have hv : ∃ j : NNReal, n ≤ j ∧ v j ω ∈ S := by
      rcases hu with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    have hset :
        {j : NNReal | n ≤ j ∧ u j ω ∈ S} =
          {j : NNReal | n ≤ j ∧ v j ω ∈ S} := by
      ext i
      constructor
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
    -- Proof comment: once the time-index hit sets agree, the defining `sInf` formula for
    -- `hittingAfter` is identical on both sides.
    simp [hittingAfter_def, hu, hv, hset]
  · have hv : ¬ ∃ j : NNReal, n ≤ j ∧ v j ω ∈ S := by
      intro hv
      apply hu
      rcases hv with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    -- Proof comment: if neither path ever hits the set, both hitting times are `⊤`.
    simp [hittingAfter_def, hu, hv]

/-- Helper for Theorem 21.20: on continuous Brownian paths, hitting a positive level `b` by time
`T` is equivalent to the closed running maximum reaching at least `b` on `[0, T]`. -/
private lemma hitUpperBeforeTime_event_ae_eq_runningMaxClosed
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T} =ᵐ[μ]
      ({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) := by
  -- Proof comment: on every continuous sample path, `hittingAfter ≤ T` means the level `b` is
  -- hit inside `[0, T]`, and continuity upgrades the exact hit to the closed running-maximum
  -- event.
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
    · -- Proof comment: an exact hit at the witness time immediately bounds `hittingAfter`.
      exact (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
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
      -- Proof comment: if the terminal witness only reaches `b` weakly, the intermediate value
      -- theorem recovers an exact hit earlier on the same path segment.
      exact
        (hittingAfter_le_of_mem (u := B) (s := ({b} : Set ℝ)) (n := (0 : NNReal))
          (ω := ω) hsIcc.1 (by simpa [processPath] using hs_eq)).trans <|
          by
            exact_mod_cast hsIcc.2.trans ht.2

/-- Helper for Theorem 21.20: adjoining the terminal cutoff preserves the almost-sure bridge
between the hit-by-time event and the closed running-maximum event. -/
private lemma hitUpperBeforeTime_terminalBelow_event_ae_eq_runningMaxClosed
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) {T : NNReal} :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ T ∧ B T ω ≤ y} =ᵐ[μ]
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) T, b ≤ B t ω} : Set Ω) ∩
        {ω | B T ω ≤ y}) : Set Ω) := by
  -- Proof comment: intersect the hit-by-time/running-maximum bridge with the shared terminal
  -- cutoff event.
  filter_upwards [hitUpperBeforeTime_event_ae_eq_runningMaxClosed (μ := μ) (B := B) hB hb
      (T := T)] with ω hω
  apply propext
  constructor
  · intro hω'
    exact ⟨hω.mp hω'.1, hω'.2⟩
  · rintro ⟨hRun, hTerm⟩
    exact ⟨hω.mpr hRun, hTerm⟩

/-- Helper for Theorem 21.20: Brownian scaling transports the closed upper-hit slice on `[0, T]`
to the corresponding unit-time slice. -/
private lemma scaledClosedRunningMaximum_terminalBelow_event_eq
    {B : NNReal → Ω → ℝ} {b y : ℝ} {T : NNReal} (hT : 0 < T) :
    ((({ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ B s ω} : Set Ω) ∩
      {ω | B T ω ≤ y}) : Set Ω) =
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) 1,
            b / Real.sqrt (T : ℝ) ≤
              brownianScaling B (Real.sqrt (T : ℝ)) t ω} : Set Ω) ∩
        {ω | brownianScaling B (Real.sqrt (T : ℝ)) 1 ω ≤ y / Real.sqrt (T : ℝ)}) : Set Ω) := by
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hSqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨s, hsIcc, hsLevel⟩, hTerm⟩
    refine ⟨?_, ?_⟩
    · refine ⟨s / T, ?_, ?_⟩
      · -- Proof comment: divide the original witness time by the positive horizon `T` to move it
        -- into the normalized interval `[0, 1]`.
        refine ⟨by positivity, ?_⟩
        exact (div_le_iff₀ hT).2 (by simpa using hsIcc.2)
      · -- Proof comment: after rewriting the scaled process at time `s / T`, the barrier
        -- inequality is just the original inequality divided by the positive factor `√T`.
        rw [brownianScaling_apply, brownianScalingTime_sqrt]
        rw [mul_div_cancel₀ _ (ne_of_gt hT)]
        simpa [div_eq_mul_inv, mul_comm] using
          (div_le_div_of_nonneg_right hsLevel hSqrt.le)
    · -- Proof comment: the terminal cutoff transports by the same positive division after
      -- evaluating the scaled process at unit time.
      rw [brownianScaling_apply, brownianScalingTime_sqrt]
      simpa [div_eq_mul_inv, mul_comm] using
        (div_le_div_of_nonneg_right hTerm hSqrt.le)
  · rintro ⟨⟨t, htIcc, htLevel⟩, hTerm⟩
    refine ⟨?_, ?_⟩
    · refine ⟨T * t, ?_, ?_⟩
      · -- Proof comment: multiply the normalized witness time by `T` to recover a witness in the
        -- original interval `[0, T]`.
        refine ⟨by positivity, ?_⟩
        have hmul : T * t ≤ T * 1 := by
          simpa using mul_le_mul_of_nonneg_left htIcc.2 T.2
        simpa using hmul
      · -- Proof comment: once the scaled inequality is rewritten as a common positive division by
        -- `√T`, cancel that denominator to recover the original barrier inequality.
        have htLevel' : b / Real.sqrt (T : ℝ) ≤ B (T * t) ω / Real.sqrt (T : ℝ) := by
          simpa [brownianScaling_apply, brownianScalingTime_sqrt, div_eq_mul_inv, mul_comm]
            using htLevel
        exact (div_le_div_iff_of_pos_right hSqrt).mp htLevel'
    · -- Proof comment: the terminal cutoff is recovered by the same denominator cancellation at
      -- unit time.
      have hTerm' : B T ω / Real.sqrt (T : ℝ) ≤ y / Real.sqrt (T : ℝ) := by
        simpa [brownianScaling_apply, brownianScalingTime_sqrt, div_eq_mul_inv, mul_comm]
          using hTerm
      exact (div_le_div_iff_of_pos_right hSqrt).mp hTerm'

/-- Helper for Theorem 21.20: subtracting the random start value from a Brownian motion started at
`0` produces an exact Brownian motion with pointwise zero start. -/
lemma isBrownianMotionStartedAt_sub_const
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ B t ω - x) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting a constant preserves strong measurability of each time slice.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: the shifted start event is exactly the original start event at `x`.
    have hpreimage :
        (fun ω ↦ B 0 ω - x) ⁻¹' ({0} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro h
        change B 0 ω - x = 0 at h
        change B 0 ω = x
        linarith
      · intro h
        have hx : B 0 ω = x := by
          simpa using h
        change B 0 ω - x = 0
        simp [hx]
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: subtracting the same constant from every time slice does not change any
    -- increment.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: the same cancellation leaves the stationary-increment law unchanged.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: transport the Gaussian marginal by subtracting the start point.
    simpa using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) x
  · -- Proof comment: continuity of sample paths is preserved by subtracting a constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 21.20: Brownian increments started at `x` have the centered Gaussian law
with variance equal to their time lag. -/
lemma brownianStartedAtIncrement_hasLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hIdent :
      IdentDistrib
        (fun ω ↦ B (((t - s) + s) + 0) ω - B (s + 0) ω)
        (fun ω ↦ B ((t - s) + 0) ω - B 0 ω)
        μ μ :=
    hB.stationaryIncrements ((0 : NNReal)) (t - s) s
  have hZeroAe : B 0 =ᵐ[μ] fun _ ↦ x :=
    brownianStart_ae_eq_const_of_measurable (hB.stronglyMeasurable 0).measurable hB
  have hBase :
      HasLaw (fun ω ↦ B ((t - s) + 0) ω - B 0 ω) (gaussianReal 0 (t - s)) μ := by
    -- Proof comment: rewrite the anchored increment as `B (t - s) - x` and transport the
    -- prescribed `gaussianReal x (t - s)` law by subtracting the start point.
    have hShifted :
        HasLaw (fun ω ↦ B ((t - s) + 0) ω - x) (gaussianReal 0 (t - s)) μ := by
      by_cases hlag : t - s = 0
      · have hts : t = s := by
          exact le_antisymm (show t ≤ s from (tsub_eq_zero_iff_le).mp hlag) hst
        subst hts
        have hZeroSubAe : (fun ω ↦ B 0 ω - x) =ᵐ[μ] fun _ : Ω ↦ (0 : ℝ) := by
          filter_upwards [hZeroAe] with ω hω
          simp [hω]
        have hZeroLaw : HasLaw (fun ω ↦ B 0 ω - x) (gaussianReal 0 0) μ := by
          refine
            { aemeasurable := by
                simpa using
                  (((hB.stronglyMeasurable 0).measurable.sub measurable_const).aemeasurable)
              map_eq := ?_ }
          calc
            μ.map (fun ω ↦ B 0 ω - x) = μ.map (fun _ : Ω ↦ (0 : ℝ)) := Measure.map_congr hZeroSubAe
            _ = gaussianReal 0 0 := by
                  simp [gaussianReal_zero_var]
        simpa using hZeroLaw
      · have hlag_pos : 0 < t - s := by
          exact bot_lt_iff_ne_bot.mpr hlag
        simpa [add_comm] using ProbabilityTheory.gaussianReal_sub_const
          (hB.gaussian_marginal hlag_pos) x
    refine hShifted.congr ?_
    filter_upwards [hZeroAe] with ω hω
    simp [hω]
  -- Proof comment: stationary increments move the anchored law on `[0, t - s]` to the interval
  -- `[s, t]`.
  simpa [tsub_add_cancel_of_le hst] using hIdent.symm.hasLaw hBase

/-- Helper for Theorem 21.20: finite future Brownian increment vectors are independent of finite
history tuples ending at the anchor time. -/
lemma brownianFutureIncrementVector_indep_historyTuple
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x)
    {m n : ℕ} (hist : Fin (m + 1) → NNReal) (hhist : StrictMono hist)
    (times : Fin n → NNReal) :
    IndepFun
      (fun ω i ↦ B (hist (Fin.last m) + times i) ω - B (hist (Fin.last m)) ω)
      (fun ω j ↦ B (hist j) ω)
      μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Z : NNReal → Ω → ℝ := fun t ω ↦ B t ω - x
  have hZ : IsBrownianMotionStartedAt μ Z 0 :=
    isBrownianMotionStartedAt_sub_const hB
  have hGaussian : IsGaussianProcess Z μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hZ
  let s : NNReal := hist (Fin.last m)
  let futureIncrements : Fin n → Ω → ℝ := fun i ω ↦ Z (s + times i) ω - Z s ω
  let historyVector : Fin (m + 1) → Ω → ℝ := fun j ω ↦ Z (hist j) ω
  have hJoint :
      IsGaussianProcess
        (Sum.elim
          (fun i : Fin n ↦ futureIncrements i)
          (fun j : Fin (m + 1) ↦ historyVector j))
        μ := by
    -- Proof comment: each future increment and each history coordinate is a continuous linear
    -- image of finitely many coordinates of the centered Brownian process `Z`.
    refine hGaussian.of_isGaussianProcess ?_
    intro u
    cases u with
    | inl i =>
        let ti : NNReal := s + times i
        let I : Finset NNReal := {ti, s}
        have hti : ti ∈ I := by simp [I]
        have hs : s ∈ I := by simp [I]
        refine ⟨I, ?_, ?_⟩
        · refine
            { toFun := fun y ↦ y ⟨ti, hti⟩ - y ⟨s, hs⟩
              map_add' := by
                intro y z
                change y ⟨ti, hti⟩ + z ⟨ti, hti⟩ - (y ⟨s, hs⟩ + z ⟨s, hs⟩) =
                  (y ⟨ti, hti⟩ - y ⟨s, hs⟩) + (z ⟨ti, hti⟩ - z ⟨s, hs⟩)
                ring
              map_smul' := by
                intro c y
                change c * y ⟨ti, hti⟩ - c * y ⟨s, hs⟩ =
                  c * (y ⟨ti, hti⟩ - y ⟨s, hs⟩)
                ring
              cont := by
                fun_prop }
        · intro ω
          simp [futureIncrements, Z, ti, s]
    | inr j =>
        let I : Finset NNReal := {hist j}
        have hj : hist j ∈ I := by simp [I]
        refine ⟨I, ?_, ?_⟩
        · refine
            { toFun := fun y ↦ y ⟨hist j, hj⟩
              map_add' := by
                intro y z
                rfl
              map_smul' := by
                intro c y
                rfl
              cont := by
                fun_prop }
        · intro ω
          simp [historyVector, Z, I]
  have hIndepCentered :
      IndepFun (fun ω i ↦ futureIncrements i ω) (fun ω j ↦ historyVector j ω) μ := by
    -- Proof comment: for the centered Brownian process `Z`, every future increment is
    -- uncorrelated with every history coordinate up to the anchor time `s`.
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hJoint ?_ ?_ ?_
    · intro i
      exact
        ((hZ.stronglyMeasurable (s + times i)).aemeasurable.sub
          (hZ.stronglyMeasurable s).aemeasurable)
    · intro j
      exact (hZ.stronglyMeasurable (hist j)).aemeasurable
    · intro i j
      have hs_mem : MemLp (Z s) 2 μ := (hGaussian.hasGaussianLaw_eval s).memLp_two
      have hsi_mem : MemLp (Z (s + times i)) 2 μ :=
        (hGaussian.hasGaussianLaw_eval (s + times i)).memLp_two
      have hj_mem : MemLp (Z (hist j)) 2 μ :=
        (hGaussian.hasGaussianLaw_eval (hist j)).memLp_two
      have hj_le_s : hist j ≤ s := hhist.monotone (Fin.le_last j)
      have hj_le_si : hist j ≤ s + times i := by
        exact le_trans hj_le_s (by simp [s])
      have hcov_future :
          cov[Z (s + times i), Z (hist j); μ] = ((hist j : NNReal) : ℝ) := by
        simpa [inf_eq_right.mpr hj_le_si] using
          startedAtZero_covariance_eq hZ (s + times i) (hist j)
      have hcov_anchor :
          cov[Z s, Z (hist j); μ] = ((hist j : NNReal) : ℝ) := by
        simpa [inf_eq_right.mpr hj_le_s] using startedAtZero_covariance_eq hZ s (hist j)
      rw [covariance_fun_sub_left hsi_mem hs_mem hj_mem, hcov_future, hcov_anchor]
      ring
  have hTranslateHistory :
      Measurable (fun y : Fin (m + 1) → ℝ ↦ fun j : Fin (m + 1) ↦ y j + x) := by
    -- Proof comment: translating the centered history tuple by the deterministic start value is
    -- coordinatewise measurable.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact (measurable_pi_apply j).add measurable_const
  -- Proof comment: translating the centered history tuple back to the original Brownian history
  -- leaves the future increment vector unchanged.
  refine (hIndepCentered.comp measurable_id hTranslateHistory).congr ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦ by
      ext i
      simp [futureIncrements, Z, s]
  · exact Filter.Eventually.of_forall fun ω ↦ by
      ext j
      simp [historyVector, Z]

/-- Helper for Theorem 21.20: subtracting the random start value from a Brownian motion started at
`0` produces an exact Brownian motion with pointwise zero start. -/
theorem startedAtZero_sub_start_isBrownianMotion
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotionStartedAt μ W 0) :
    IsBrownianMotion μ (fun t ω ↦ W t ω - W 0 ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting the common time-zero anchor makes the corrected process vanish
    -- identically at time `0`.
    funext ω
    simp
  · -- Proof comment: the random anchor cancels inside every increment, so independence is
    -- unchanged.
    intro n times hmono
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hW.indepIncrements n times hmono
  · -- Proof comment: the same cancellation turns the corrected increments into the original
    -- stationary-increment family.
    intro r s t
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hW.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: at positive times the corrected process is exactly the increment over
    -- `[0, t]`.
    simpa using
      startedAtZeroIncrement_hasLaw (hX := hW) (s := (0 : NNReal)) (t := t)
        (show 0 ≤ t by simp)
  · -- Proof comment: subtracting the constant initial value preserves continuity of each sample
    -- path.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 21.20: pointwise negation preserves Brownian motion started at `0`. -/
theorem neg_isBrownianMotionStartedAtZero
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotionStartedAt μ W 0) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ -W t ω) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: each time slice stays strongly measurable after pointwise negation.
    intro t
    exact (hW.stronglyMeasurable t).neg
  · -- Proof comment: the event `{ -W 0 = 0 }` is exactly `{ W 0 = 0 }`.
    have hpreimage : (fun ω ↦ -W 0 ω) ⁻¹' ({0} : Set ℝ) = W 0 ⁻¹' ({0} : Set ℝ) := by
      ext ω
      simp
    rw [hpreimage]
    exact hW.start
  · -- Proof comment: independent increments are preserved by the measurable map `z ↦ -z`.
    intro n t ht
    simpa using hW.indepIncrements.neg n t ht
  · -- Proof comment: every increment of `-W` is the negation of the matching increment of `W`.
    intro r s t
    convert (hW.stationaryIncrements r s t).comp measurable_neg using 1
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under negation.
    simpa using ProbabilityTheory.gaussianReal_neg (hW.gaussian_marginal ht)
  · -- Proof comment: pointwise negation preserves continuity of each sample path.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.neg

/-- Helper for Theorem 21.20: survival below an upper barrier is expressed by the terminal
Gaussian lower-tail probability. -/
theorem startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotionStartedAt μ W 0)
    {b : ℝ} {T : NNReal} (hb : 0 < b) (hT : 0 < T) :
    μ.real {ω | T < hittingAfter W ({b} : Set ℝ) 0 ω} =
      2 * μ.real {ω | W T ω ≤ b} - 1 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω - W 0 ω
  let A : Set Ω := {ω | hittingAfter W ({b} : Set ℝ) 0 ω ≤ T}
  let AX : Set Ω := {ω | hittingAfter X ({b} : Set ℝ) 0 ω ≤ T}
  let R : Set Ω := {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b ≤ X s ω}
  let RApprox : Set Ω :=
    ⋂ n : ℕ,
      ⋃ q : {q : ℚ≥0 // (q : NNReal) ≤ T},
        {ω | b - b / (n + 2 : ℝ) < X (q : NNReal) ω}
  let S : Set Ω := {ω | T < hittingAfter W ({b} : Set ℝ) 0 ω}
  let L : Set Ω := {ω | W T ω ≤ b}
  let LX : Set Ω := {ω | X T ω ≤ b}
  have hX : IsBrownianMotion μ X := startedAtZero_sub_start_isBrownianMotion hW
  have hStartAe : W 0 =ᵐ[μ] fun _ ↦ (0 : ℝ) :=
    brownianStart_ae_eq_const_of_measurable (hW.stronglyMeasurable 0).measurable hW
  have hHitAe : A =ᵐ[μ] AX := by
    -- Proof comment: on the almost-sure start event `W 0 = 0`, the corrected process `X`
    -- agrees pointwise with `W`, so the hit-by-time events coincide.
    filter_upwards [hStartAe] with ω hω
    apply propext
    have hHitEq :
        hittingAfter W ({b} : Set ℝ) 0 ω =
          hittingAfter X ({b} : Set ℝ) 0 ω := by
      apply hittingAfter_eq_of_pointwise_eq
      intro s
      simp [X, hω]
    constructor <;> intro h
    · change hittingAfter W ({b} : Set ℝ) 0 ω ≤ T at h
      change hittingAfter X ({b} : Set ℝ) 0 ω ≤ T
      simpa [hHitEq] using h
    · change hittingAfter X ({b} : Set ℝ) 0 ω ≤ T at h
      change hittingAfter W ({b} : Set ℝ) 0 ω ≤ T
      simpa [hHitEq] using h
  have hTermAe : L =ᵐ[μ] LX := by
    -- Proof comment: the same almost-sure start event identifies the terminal-value cutoffs.
    filter_upwards [hStartAe] with ω hω
    apply propext
    constructor <;> intro h
    · change W T ω ≤ b at h
      change W T ω - W 0 ω ≤ b
      simpa [hω] using h
    · change W T ω - W 0 ω ≤ b at h
      change W T ω ≤ b
      simpa [hω] using h
  have hHitRunAe : AX =ᵐ[μ] R := by
    exact hitUpperBeforeTime_event_ae_eq_runningMaxClosed (μ := μ) (B := X) hX hb (T := T)
  have hRunApproxAe : R =ᵐ[μ] RApprox := by
    -- Proof comment: on continuous exact Brownian paths, the closed upper-hit event is exactly
    -- the countable rational approximation from the strict lower levels.
    filter_upwards [hX.continuous_paths] with ω hω
    apply propext
    have hcont : Continuous (fun s : NNReal ↦ X s ω) := by
      simpa [HasAlmostSurelyContinuousPaths, processPath] using hω
    constructor
    · intro hMem
      have hLevels :
          ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧
            b - b / (n + 2 : ℝ) < X (q : NNReal) ω := by
        exact
          (continuous_exists_upperCrossing_iff_forall_nnrat_strictLowerLevels
            (f := fun s : NNReal ↦ X s ω) hcont (by simp [X]) (hb := hb) (T := T)).mp
            (by simpa [R] using hMem)
      refine Set.mem_iInter.mpr ?_
      intro n
      rcases hLevels n with ⟨q, hqT, hq⟩
      exact Set.mem_iUnion.mpr ⟨⟨q, hqT⟩, by simpa using hq⟩
    · intro hMem
      have hLevels :
          ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ T ∧
            b - b / (n + 2 : ℝ) < X (q : NNReal) ω := by
        intro n
        rcases Set.mem_iUnion.mp (Set.mem_iInter.mp hMem n) with ⟨q, hq⟩
        exact ⟨q, q.2, by simpa using hq⟩
      exact
        (continuous_exists_upperCrossing_iff_forall_nnrat_strictLowerLevels
          (f := fun s : NNReal ↦ X s ω) hcont (by simp [X]) (hb := hb) (T := T)).mpr
          hLevels
  have hRunApproxMeas : MeasurableSet RApprox := by
    refine MeasurableSet.iInter ?_
    intro n
    refine MeasurableSet.iUnion ?_
    intro q
    change MeasurableSet ((X (q : NNReal)) ⁻¹' Set.Ioi (b - b / (n + 2 : ℝ)))
    exact (hX.stronglyMeasurable (q : NNReal)).measurable measurableSet_Ioi
  have hSurvAe : S =ᵐ[μ] RApproxᶜ := by
    -- Proof comment: the survival event is the complement of the closed running-maximum event
    -- after transporting through the exact Brownian correction and the rational approximation.
    filter_upwards [hHitAe, hHitRunAe, hRunApproxAe] with ω hA hR hApprox
    apply propext
    constructor
    · intro hSurv hMem
      have hAmem : A ω := hA.mpr <| hR.mpr <| hApprox.mpr hMem
      exact (not_le_of_gt hSurv) hAmem
    · intro hNoApprox
      have hAnot : ¬ A ω := by
        intro hAmem
        exact hNoApprox (hApprox.mp <| hR.mp <| hA.mp hAmem)
      exact lt_of_not_ge hAnot
  have hUpperClosed :
      μ.real {ω | b ≤ X T ω} = 1 - μ.real LX := by
    have hXT_meas : Measurable (X T) := (hX.stronglyMeasurable T).measurable
    have hXLaw : HasLaw (X T) (gaussianReal 0 T) μ := hX.gaussian_marginal hT
    -- Proof comment: the centered Gaussian terminal law has no atom at `b`, so the closed upper
    -- tail is the complement of the closed lower tail.
    calc
      μ.real {ω | b ≤ X T ω} = (μ.map (X T)).real (Set.Ici b) := by
        change (μ ((X T) ⁻¹' Set.Ici b)).toReal = ((μ.map (X T)) (Set.Ici b)).toReal
        rw [Measure.map_apply hXT_meas measurableSet_Ici]
      _ = (gaussianReal 0 T).real (Set.Ici b) := by
        rw [hXLaw.map_eq]
      _ = 1 - (gaussianReal 0 T).real (Set.Iio b) := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := gaussianReal 0 T)
            (s := Set.Iio b) measurableSet_Iio)
      _ = 1 - (gaussianReal 0 T).real (Set.Iic b) := by
        rw [gaussianReal_closedTail_eq_openTail (m := 0) (δ := T) hT b]
      _ = 1 - (μ.map (X T)).real (Set.Iic b) := by
        rw [hXLaw.map_eq]
      _ = 1 - μ.real LX := by
        change 1 - ((μ.map (X T)) (Set.Iic b)).toReal =
          1 - (μ ((X T) ⁻¹' Set.Iic b)).toReal
        rw [Measure.map_apply hXT_meas measurableSet_Iic]
  let RRow : ℕ → Set Ω := fun n ↦
    ⋃ q : {q : ℚ≥0 // (q : NNReal) ≤ T},
      {ω | b - b / (n + 2 : ℝ) < X (q : NNReal) ω}
  let V : ℕ → Set Ω := fun n ↦
    {ω | b - b / (n + 2 : ℝ) < X T ω}
  have hRRow_meas : ∀ n : ℕ, MeasurableSet (RRow n) := by
    intro n
    refine MeasurableSet.iUnion ?_
    intro q
    change MeasurableSet ((X (q : NNReal)) ⁻¹' Set.Ioi (b - b / (n + 2 : ℝ)))
    exact (hX.stronglyMeasurable (q : NNReal)).measurable measurableSet_Ioi
  have hV_meas : ∀ n : ℕ, MeasurableSet (V n) := by
    intro n
    change MeasurableSet ((X T) ⁻¹' Set.Ioi (b - b / (n + 2 : ℝ)))
    exact (hX.stronglyMeasurable T).measurable measurableSet_Ioi
  have hRRow_anti : Antitone RRow := by
    intro n m hnm ω hω
    rcases Set.mem_iUnion.mp hω with ⟨q, hqω⟩
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    have hden : (n + 2 : ℝ) ≤ (m + 2 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 2
    have honeDiv :
        (1 : ℝ) / (m + 2 : ℝ) ≤ (1 : ℝ) / (n + 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden
    have hfrac :
        b / (m + 2 : ℝ) ≤ b / (n + 2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left honeDiv hb.le
    dsimp [RRow] at hqω ⊢
    linarith
  have hV_anti : Antitone V := by
    intro n m hnm ω hω
    have hden : (n + 2 : ℝ) ≤ (m + 2 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 2
    have honeDiv :
        (1 : ℝ) / (m + 2 : ℝ) ≤ (1 : ℝ) / (n + 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden
    have hfrac :
        b / (m + 2 : ℝ) ≤ b / (n + 2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left honeDiv hb.le
    dsimp [V] at hω ⊢
    linarith
  have hRRowAe :
      ∀ n : ℕ,
        RRow n =ᵐ[μ]
          {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b - b / (n + 2 : ℝ) < X s ω} := by
    intro n
    filter_upwards [hX.continuous_paths] with ω hω
    have hcont : Continuous (fun s : NNReal ↦ X s ω) := by
      simpa [HasAlmostSurelyContinuousPaths, processPath] using hω
    apply propext
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨q, hqω⟩
      exact ⟨(q : NNReal), ⟨by simp, q.2⟩, by simpa using hqω⟩
    · intro hω
      rcases
          (continuous_exists_strictUpperCrossing_iff_exists_nnrat
            (f := fun s : NNReal ↦ X s ω) hcont
            (a := b - b / (n + 2 : ℝ)) (T := T)).mp hω with
        ⟨q, hqT, hqω⟩
      exact Set.mem_iUnion.mpr ⟨⟨q, hqT⟩, by simpa using hqω⟩
  have hRRowMass :
      ∀ n : ℕ, μ.real (RRow n) = 2 * μ.real (V n) := by
    intro n
    have hden_pos : 0 < (n + 2 : ℝ) := by positivity
    have hden_gt_one : (1 : ℝ) < (n + 2 : ℝ) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      linarith
    have hfrac_lt : b / (n + 2 : ℝ) < b := by
      exact (div_lt_iff₀ hden_pos).2 (by nlinarith [hb, hden_gt_one])
    have hlevel_pos : 0 < b - b / (n + 2 : ℝ) := by
      linarith
    calc
      μ.real (RRow n) =
          μ.real {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b - b / (n + 2 : ℝ) < X s ω} := by
            exact MeasureTheory.measureReal_congr (hRRowAe n)
      _ = 2 * μ.real (V n) := by
            simpa [Measure.real_def, V] using
              congrArg ENNReal.toReal
                (reflectionPrincipleForBrownianMotion (hB := hX)
                  (a := b - b / (n + 2 : ℝ)) hlevel_pos hT)
  have hRRowMassENN :
      ∀ n : ℕ, μ (RRow n) = 2 * μ (V n) := by
    intro n
    calc
      μ (RRow n) =
          μ {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, b - b / (n + 2 : ℝ) < X s ω} := by
            exact measure_congr (hRRowAe n)
      _ = 2 * μ (V n) := by
            exact reflectionPrincipleForBrownianMotion (hB := hX)
              (a := b - b / (n + 2 : ℝ))
              (by
                have hden_pos : 0 < (n + 2 : ℝ) := by positivity
                have hden_gt_one : (1 : ℝ) < (n + 2 : ℝ) := by
                  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
                  linarith
                have hfrac_lt : b / (n + 2 : ℝ) < b := by
                  exact (div_lt_iff₀ hden_pos).2 (by nlinarith [hb, hden_gt_one])
                linarith)
              hT
  have hVInter :
      (⋂ n : ℕ, V n) = {ω | b ≤ X T ω} := by
    ext ω
    constructor
    · intro hω
      by_contra hlt
      have hlt' : X T ω < b := by
        simpa using hlt
      have hgap : 0 < b - X T ω := sub_pos.mpr hlt'
      have hratio : 0 < (b - X T ω) / b := by positivity
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hratio
      have hsmall : (1 : ℝ) / (n + 2 : ℝ) < (b - X T ω) / b := by
        have hmono :
            (1 : ℝ) / (n + 2 : ℝ) ≤ (1 : ℝ) / (n + 1 : ℝ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · norm_num
        exact lt_of_le_of_lt hmono hn
      have hfrac : b / (n + 2 : ℝ) < b - X T ω := by
        field_simp [hb.ne'] at hsmall ⊢
        nlinarith
      have hrow : b - b / (n + 2 : ℝ) < X T ω := Set.mem_iInter.mp hω n
      linarith
    · intro hω
      refine Set.mem_iInter.mpr ?_
      intro n
      dsimp [V]
      have hfrac : 0 < b / (n + 2 : ℝ) := by positivity
      have hω' : b ≤ X T ω := by simpa using hω
      linarith
  have hRunApproxMass :
      μ.real RApprox = 2 * μ.real {ω | b ≤ X T ω} := by
    -- Proof comment: each rational row is a strict running-maximum event, so Theorem 21.19
    -- applies rowwise and the decreasing intersection limits to the closed terminal tail.
    have hMassENN : μ RApprox = 2 * μ {ω | b ≤ X T ω} := by
      calc
        μ RApprox = μ (⋂ n : ℕ, RRow n) := by rfl
        _ = ⨅ n : ℕ, μ (RRow n) := by
              rw [hRRow_anti.measure_iInter (fun n ↦ (hRRow_meas n).nullMeasurableSet)]
              exact ⟨0, measure_ne_top μ (RRow 0)⟩
        _ = ⨅ n : ℕ, 2 * μ (V n) := by
              congr with n
              exact hRRowMassENN n
        _ = 2 * ⨅ n : ℕ, μ (V n) := by
              rw [← ENNReal.mul_iInf_of_ne (f := fun n : ℕ ↦ μ (V n)) (by norm_num) (by simp)]
        _ = 2 * μ (⋂ n : ℕ, V n) := by
              rw [← hV_anti.measure_iInter (fun n ↦ (hV_meas n).nullMeasurableSet)]
              exact ⟨0, measure_ne_top μ (V 0)⟩
        _ = 2 * μ {ω | b ≤ X T ω} := by rw [hVInter]
    simpa [Measure.real_def] using congrArg ENNReal.toReal hMassENN
  have hCompl :
      μ.real S = 1 - μ.real RApprox := by
    -- Proof comment: the measurable rational approximation makes the complement step available.
    calc
      μ.real S = μ.real (RApproxᶜ) := by
        exact MeasureTheory.measureReal_congr hSurvAe
      _ = 1 - μ.real RApprox := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := μ) (s := RApprox) hRunApproxMeas)
  calc
    μ.real {ω | T < hittingAfter W ({b} : Set ℝ) 0 ω} = 1 - μ.real RApprox := hCompl
    _ = 1 - (2 * μ.real {ω | b ≤ X T ω}) := by rw [hRunApproxMass]
    _ = 1 - (2 * (1 - μ.real LX)) := by rw [hUpperClosed]
    _ = 2 * μ.real LX - 1 := by ring
    _ = 2 * μ.real L - 1 := by
          rw [MeasureTheory.measureReal_congr hTermAe.symm]

/-- Helper for Theorem 21.20: survival above a lower barrier is the sign-symmetric companion of
the upper-barrier boundary-CDF formula. -/
theorem startedAtZero_survivalAboveLowerBarrier_eq_boundaryCdf
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotionStartedAt μ W 0)
    {b : ℝ} {T : NNReal} (hb : 0 < b) (hT : 0 < T) :
    μ.real {ω | T < hittingAfter W ({-b} : Set ℝ) 0 ω} =
      1 - 2 * μ.real {ω | W T ω ≤ -b} := by
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -W t ω
  have hBneg : IsBrownianMotionStartedAt μ Bneg 0 :=
    neg_isBrownianMotionStartedAtZero hW
  have hEventEq :
      {ω | T < hittingAfter W ({-b} : Set ℝ) 0 ω} =
        {ω | T < hittingAfter Bneg ({b} : Set ℝ) 0 ω} := by
    -- Proof comment: negating the path swaps the lower barrier `-b` with the upper barrier `b`.
    ext ω
    classical
    have hHit :
        hittingAfter Bneg ({b} : Set ℝ) 0 ω =
          hittingAfter W ({-b} : Set ℝ) 0 ω := by
      rw [hittingAfter_def, hittingAfter_def]
      simp only [Bneg, Set.mem_singleton_iff, zero_le, true_and]
      have hExists :
          (∃ j : NNReal, -W j ω = b) ↔
            ∃ j : NNReal, W j ω = -b := by
        constructor
        · rintro ⟨j, hj⟩
          exact ⟨j, by linarith⟩
        · rintro ⟨j, hj⟩
          exact ⟨j, by linarith⟩
      have hSet :
          {i : NNReal | -W i ω = b} =
            {i : NNReal | W i ω = -b} := by
        ext i
        constructor
        · intro hi
          have hEq : -W i ω = b := by simpa using hi
          change W i ω = -b
          linarith
        · intro hi
          have hEq : W i ω = -b := by simpa using hi
          change -W i ω = b
          linarith
      by_cases h : ∃ j : NNReal, -W j ω = b
      · have h' : ∃ j : NNReal, W j ω = -b := hExists.mp h
        rw [if_pos h, if_pos h']
        have hsInf :
            (sInf {i : NNReal | -W i ω = b} : NNReal) =
              sInf {i : NNReal | W i ω = -b} := by
          simpa using congrArg (fun s : Set NNReal ↦ (sInf s : NNReal)) hSet
        exact_mod_cast hsInf
      · have h' : ¬ ∃ j : NNReal, W j ω = -b := by
          exact mt hExists.mpr h
        rw [if_neg h, if_neg h']
    simpa [hHit]
  have hTerminalEq :
      μ.real {ω | Bneg T ω ≤ b} = μ.real {ω | -b ≤ W T ω} := by
    -- Proof comment: the terminal inequality for `-W` is exactly the reflected upper-tail event
    -- for `W`.
    apply MeasureTheory.measureReal_congr
    filter_upwards with ω
    apply propext
    constructor
    · intro h
      change -W T ω ≤ b at h
      change -b ≤ W T ω
      linarith
    · intro h
      change -b ≤ W T ω at h
      change -W T ω ≤ b
      linarith
  have hUpperClosed :
      μ.real {ω | -b ≤ W T ω} = 1 - μ.real {ω | W T ω ≤ -b} := by
    have hWT_meas : Measurable (W T) := (hW.stronglyMeasurable T).measurable
    have hWLaw : HasLaw (W T) (gaussianReal 0 T) μ := hW.gaussian_marginal hT
    -- Proof comment: the centered Gaussian terminal law has no atom at `-b`, so the upper
    -- closed tail complements the lower closed tail there as well.
    calc
      μ.real {ω | -b ≤ W T ω} = (μ.map (W T)).real (Set.Ici (-b)) := by
        change (μ ((W T) ⁻¹' Set.Ici (-b))).toReal = ((μ.map (W T)) (Set.Ici (-b))).toReal
        rw [Measure.map_apply hWT_meas measurableSet_Ici]
      _ = (gaussianReal 0 T).real (Set.Ici (-b)) := by
        rw [hWLaw.map_eq]
      _ = 1 - (gaussianReal 0 T).real (Set.Iio (-b)) := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := gaussianReal 0 T)
            (s := Set.Iio (-b)) measurableSet_Iio)
      _ = 1 - (gaussianReal 0 T).real (Set.Iic (-b)) := by
        rw [gaussianReal_closedTail_eq_openTail (m := 0) (δ := T) hT (-b)]
      _ = 1 - (μ.map (W T)).real (Set.Iic (-b)) := by
        rw [hWLaw.map_eq]
      _ = 1 - μ.real {ω | W T ω ≤ -b} := by
        change 1 - ((μ.map (W T)) (Set.Iic (-b))).toReal =
          1 - (μ ((W T) ⁻¹' Set.Iic (-b))).toReal
        rw [Measure.map_apply hWT_meas measurableSet_Iic]
  calc
    μ.real {ω | T < hittingAfter W ({-b} : Set ℝ) 0 ω}
        = μ.real {ω | T < hittingAfter Bneg ({b} : Set ℝ) 0 ω} := by
            rw [hEventEq]
    _ = 2 * μ.real {ω | Bneg T ω ≤ b} - 1 := by
          exact startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf hBneg hb hT
    _ = 2 * μ.real {ω | -b ≤ W T ω} - 1 := by
          rw [hTerminalEq]
    _ = 2 * (1 - μ.real {ω | W T ω ≤ -b}) - 1 := by
          rw [hUpperClosed]
    _ = 1 - 2 * μ.real {ω | W T ω ≤ -b} := by
          ring

/-- Helper for Theorem 21.20: hitting `0` for the translated process `u ↦ x + W u` is exactly
hitting `-x` for `W`. -/
theorem translatedZeroHittingEvent_eq_singletonHit
    (W : NNReal → Ω → ℝ) {x : ℝ} {δ : NNReal} :
    {ω | δ < hittingAfter (fun u ω ↦ x + W u ω) ({0} : Set ℝ) 0 ω} =
      {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
  ext ω
  classical
  have hHit :
      hittingAfter (fun u ω' ↦ x + W u ω') ({0} : Set ℝ) 0 ω =
        hittingAfter W ({-x} : Set ℝ) 0 ω := by
    rw [hittingAfter_def, hittingAfter_def]
    simp only [Set.mem_singleton_iff, zero_le, true_and]
    have hExists :
        (∃ j : NNReal, x + W j ω = 0) ↔
          ∃ j : NNReal, W j ω = -x := by
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        linarith
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        linarith
    have hSet :
        {i : NNReal | x + W i ω = 0} =
          {i : NNReal | W i ω = -x} := by
      ext i
      constructor
      · intro hi
        have hEq : x + W i ω = 0 := by simpa using hi
        change W i ω = -x
        linarith
      · intro hi
        have hEq : W i ω = -x := by simpa using hi
        change x + W i ω = 0
        linarith
    by_cases h : ∃ j : NNReal, x + W j ω = 0
    · have h' : ∃ j : NNReal, W j ω = -x := hExists.mp h
      rw [if_pos h, if_pos h']
      have hsInf :
          (sInf {i : NNReal | x + W i ω = 0} : NNReal) =
            sInf {i : NNReal | W i ω = -x} := by
        simpa using congrArg (fun s : Set NNReal ↦ (sInf s : NNReal)) hSet
      exact_mod_cast hsInf
    · have h' : ¬∃ j : NNReal, W j ω = -x := by
        exact mt hExists.mpr h
      rw [if_neg h, if_neg h']
  -- Proof comment: once the translated and centered hitting times agree pointwise, the event
  -- `{δ < τ}` agrees pointwise as well.
  simpa [hHit]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.20: on a continuous path started away from `0`, surviving strictly past
time `δ` before the first zero is equivalent to avoiding `0` on `(0, δ]`. -/
private theorem continuous_lt_hittingAfter_zero_iff
    {f : NNReal → ℝ} (hcont : Continuous f) (hf0 : f 0 ≠ 0) (δ : NNReal) :
    δ < hittingAfter (fun u (_ : Unit) ↦ f u) ({0} : Set ℝ) 0 () ↔
      ∀ u ∈ Set.Ioc 0 δ, f u ≠ 0 := by
  classical
  let X : NNReal → Unit → ℝ := fun u _ ↦ f u
  let hitSet : Set NNReal := {u : NNReal | f u = 0}
  constructor
  · intro hδ u hu
    -- Proof comment: any zero inside `(0, δ]` would force the first hitting time to be at most
    -- that parameter, contradicting `δ < τ`.
    have hu_lt : (u : WithTop NNReal) < hittingAfter X ({0} : Set ℝ) 0 () :=
      lt_of_le_of_lt (by exact_mod_cast hu.2) hδ
    exact
      notMem_of_lt_hittingAfter
        (u := X) (s := ({0} : Set ℝ)) (n := (0 : NNReal))
        (ω := ()) (k := u) hu_lt hu.1.le
  · intro hAvoid
    -- Route correction: the old route tried to use the discrete `hittingAfter_le_iff` API.
    -- Here we instead recover the first hit from continuity of the closed zero set.
    by_cases htop : hittingAfter X ({0} : Set ℝ) 0 () = ⊤
    · rw [htop]
      exact (WithTop.coe_lt_top (a := δ))
    · by_contra hlt
      have hτ_le : hittingAfter X ({0} : Set ℝ) 0 () ≤ (δ : WithTop NNReal) := not_lt.mp hlt
      have hExists :
          ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j () ∈ ({0} : Set ℝ) := by
        simpa [X, ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] using htop
      have hτ_eq :
          hittingAfter X ({0} : Set ℝ) 0 () =
            ((sInf hitSet : NNReal) : WithTop NNReal) := by
        have hSet :
            {i : NNReal | (0 : NNReal) ≤ i ∧ X i () ∈ ({0} : Set ℝ)} = hitSet := by
          ext u
          simp [X, hitSet]
        change
          (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j () ∈ ({0} : Set ℝ) then
              ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ X i () ∈ ({0} : Set ℝ)} : NNReal) :
                WithTop NNReal)
            else ⊤) = ((sInf hitSet : NNReal) : WithTop NNReal)
        rw [if_pos hExists, hSet]
      have hClosed : IsClosed hitSet := by
        simpa [hitSet] using (isClosed_singleton.preimage hcont)
      have hNonempty : hitSet.Nonempty := by
        rcases hExists with ⟨j, -, hj⟩
        exact ⟨j, by simpa [hitSet] using hj⟩
      have hBddBelow : BddBelow hitSet := by
        refine ⟨0, ?_⟩
        intro u hu
        positivity
      have hInf_mem : sInf hitSet ∈ hitSet :=
        hClosed.csInf_mem hNonempty hBddBelow
      have hInf_le : sInf hitSet ≤ δ := by
        rw [hτ_eq] at hτ_le
        exact_mod_cast hτ_le
      have hInf_ne_zero : sInf hitSet ≠ 0 := by
        intro hzero
        exact hf0 (by simpa [hitSet, hzero] using hInf_mem)
      have hInf_Ioc : sInf hitSet ∈ Set.Ioc 0 δ := ⟨pos_iff_ne_zero.mpr hInf_ne_zero, hInf_le⟩
      exact (hAvoid (sInf hitSet) hInf_Ioc) (by simpa [hitSet] using hInf_mem)

/-- Helper for Theorem 21.20: away from the zero anchor, the translated zero-hit event matches the
tail zero-avoidance event on `(0, δ]` almost surely. -/
theorem translatedZeroHittingEvent_eq_tailZeroAvoidance
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : x ≠ 0) {δ : NNReal} :
    {ω | δ < hittingAfter (fun u ω ↦ x + W u ω) ({0} : Set ℝ) 0 ω} =ᵐ[μ]
      {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} := by
  -- Route correction: the discrete `hittingAfter_le_iff` route is the wrong normal form here.
  -- We instead apply the pathwise continuity lemma on the almost-sure continuity event.
  filter_upwards [hW.continuous_paths] with ω hω
  have hcontW : Continuous (fun u : NNReal ↦ W u ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω
  have hcontTranslated : Continuous (fun u : NNReal ↦ x + W u ω) :=
    continuous_const.add hcontW
  have hstart : x + W 0 ω ≠ 0 := by
    simpa [hW.zero] using hx
  simpa using
    (continuous_lt_hittingAfter_zero_iff
      (f := fun u : NNReal ↦ x + W u ω) hcontTranslated hstart δ)

/-- Helper for Theorem 21.20: a positive anchored tail-zero event has the reflected lower-barrier
survival probability. -/
theorem positiveAnchorTailZeroAvoidance_real_eq_lowerBoundaryCdf
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : 0 < x) {δ : NNReal} (hδ : 0 < δ) :
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =
      1 - 2 * μ.real {ω | W δ ω ≤ -x} := by
  have hStarted : IsBrownianMotionStartedAt μ W 0 := inferInstance
  have hEventAe :
      {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =ᵐ[μ]
        {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
    -- Proof comment: normalize the translated zero-avoidance event to the centered hitting-time
    -- event that the reflected survival theorem already controls.
    refine (translatedZeroHittingEvent_eq_tailZeroAvoidance (hW := hW) (x := x)
        (hx := ne_of_gt hx) (δ := δ)).symm.trans ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa using congrArg (fun s : Set Ω ↦ ω ∈ s)
        (translatedZeroHittingEvent_eq_singletonHit (W := W) (x := x) (δ := δ))
  -- Proof comment: after the event normalization, the lower-barrier survival formula gives the
  -- exact boundary CDF.
  calc
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0}
        = μ.real {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
            exact MeasureTheory.measureReal_congr hEventAe
    _ = 1 - 2 * μ.real {ω | W δ ω ≤ -x} := by
          exact startedAtZero_survivalAboveLowerBarrier_eq_boundaryCdf hStarted hx hδ

/-- Helper for Theorem 21.20: a negative anchored tail-zero event has the reflected upper-barrier
survival probability. -/
theorem negativeAnchorTailZeroAvoidance_real_eq_upperBoundaryCdf
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : x < 0) {δ : NNReal} (hδ : 0 < δ) :
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =
      2 * μ.real {ω | W δ ω ≤ -x} - 1 := by
  have hStarted : IsBrownianMotionStartedAt μ W 0 := inferInstance
  have hx' : 0 < -x := by linarith
  have hEventAe :
      {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =ᵐ[μ]
        {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
    -- Proof comment: the translated zero-avoidance event becomes survival below the upper
    -- barrier `-x` once the translated hitting-time is rewritten back to the centered path.
    refine (translatedZeroHittingEvent_eq_tailZeroAvoidance (hW := hW) (x := x)
        (hx := ne_of_lt hx) (δ := δ)).symm.trans ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa using congrArg (fun s : Set Ω ↦ ω ∈ s)
        (translatedZeroHittingEvent_eq_singletonHit (W := W) (x := x) (δ := δ))
  -- Proof comment: now apply the upper-barrier survival formula at the positive level `-x`.
  calc
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0}
        = μ.real {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
            exact MeasureTheory.measureReal_congr hEventAe
    _ = 2 * μ.real {ω | W δ ω ≤ -x} - 1 := by
          exact startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf hStarted hx' hδ

/-- Helper for Theorem 21.20: Brownian motion almost surely is not nonpositive on the whole
interval `[0, T]`. -/
private theorem brownianNonpositiveTail_real_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  letI : IsBrownianMotion μ B := hB
  let hStarted : IsBrownianMotionStartedAt μ B 0 := inferInstance
  let ν : Measure ℝ := gaussianReal 0 T
  let c : ℕ → ℝ := fun n ↦ (n + 2 : ℝ)⁻¹
  let stayBelow : ℕ → Set Ω := fun n ↦ {ω | T < hittingAfter B ({c n} : Set ℝ) 0 ω}
  let windows : ℕ → Set ℝ := fun n ↦ Set.Icc (-(c n)) (c n)
  have hLaw : HasLaw (B T) ν μ := hStarted.gaussian_marginal hT
  have hMass :
      ∀ n : ℕ, μ.real (stayBelow n) = ν.real (windows n) := by
    intro n
    have hc_pos : 0 < c n := by
      dsimp [c]
      positivity
    have hTail :
        μ.real {ω | B T ω ≤ c n} = ν.real (Set.Iic (c n)) := by
      have hTailENN : μ ((B T) ⁻¹' Set.Iic (c n)) = ν (Set.Iic (c n)) := by
        rw [← Measure.map_apply (hB.stronglyMeasurable T).measurable measurableSet_Iic]
        exact congrArg (fun ρ : Measure ℝ => ρ (Set.Iic (c n))) hLaw.map_eq
      simpa [Measure.real_def] using congrArg ENNReal.toReal hTailENN
    have hReflect : ν.real (Set.Iic (c n)) = 1 - ν.real (Set.Iic (-(c n))) :=
      centeredGaussian_closedTail_reflect (δ := T) hT (c n)
    have hInterval :
        ν.real (windows n) = 1 - 2 * ν.real (Set.Iic (-(c n))) :=
      centeredGaussian_interval_real_eq_lowerBoundaryCdf (δ := T) hT (a := c n) hc_pos
    calc
      μ.real (stayBelow n) = 2 * μ.real {ω | B T ω ≤ c n} - 1 := by
        simpa [stayBelow, c] using
          startedAtZero_survivalBelowUpperBarrier_eq_boundaryCdf
            hStarted (b := c n) hc_pos hT
      _ = 2 * ν.real (Set.Iic (c n)) - 1 := by
            rw [hTail]
      _ = ν.real (windows n) := by
            linarith [hReflect, hInterval]
  have hBound :
      ∀ n : ℕ, μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} ≤ ν.real (windows n) := by
    intro n
    have hsubset :
        ({ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} ∩ {ω | Continuous (processPath B ω)}) ⊆ stayBelow n := by
      intro ω hω
      rcases hω with ⟨hω, hcont⟩
      have hcontB : Continuous (fun u : NNReal ↦ B u ω) := by
        simpa [processPath] using hcont
      have hAvoid :
          ∀ u ∈ Set.Ioc 0 T, c n - B u ω ≠ 0 := by
        intro u hu huEq
        have huNonpos : B u ω ≤ 0 := hω u ⟨hu.1.le, hu.2⟩
        have huPos : 0 < B u ω := by
          have huEq' : B u ω = c n := by
            simpa [eq_comm] using (sub_eq_zero.mp huEq)
          rw [huEq']
          dsimp [c]
          positivity
        exact (not_lt_of_ge huNonpos) huPos
      have hStart : c n - B 0 ω ≠ 0 := by
        have hc_pos : 0 < c n := by
          dsimp [c]
          positivity
        simpa [hB.zero] using (ne_of_gt hc_pos)
      have hHitEq :
          hittingAfter (fun u (_ : Unit) ↦ c n - B u ω) ({0} : Set ℝ) 0 () =
            hittingAfter B ({c n} : Set ℝ) 0 ω := by
        change
          hittingAfter (fun u (_ : Unit) ↦ c n - B u ω) ({0} : Set ℝ) 0 () =
            hittingAfter (fun u (_ : Unit) ↦ B u ω) ({c n} : Set ℝ) 0 ()
        rw [MeasureTheory.hittingAfter_def, MeasureTheory.hittingAfter_def]
        have hExists :
            (∃ j : NNReal, 0 ≤ j ∧ c n - B j ω ∈ ({0} : Set ℝ)) ↔
              ∃ j : NNReal, 0 ≤ j ∧ B j ω ∈ ({c n} : Set ℝ) := by
          constructor
          · rintro ⟨j, hj0, hj⟩
            refine ⟨j, hj0, ?_⟩
            change B j ω = c n
            have hEq : c n - B j ω = 0 := by simpa using hj
            linarith
          · rintro ⟨j, hj0, hj⟩
            refine ⟨j, hj0, ?_⟩
            change c n - B j ω ∈ ({0} : Set ℝ)
            have hEq : B j ω = c n := by simpa using hj
            simp [Set.mem_singleton_iff, hEq]
        have hSet :
            {i : NNReal | 0 ≤ i ∧ c n - B i ω ∈ ({0} : Set ℝ)} =
              {i : NNReal | 0 ≤ i ∧ B i ω ∈ ({c n} : Set ℝ)} := by
          ext i
          constructor
          · intro hi
            refine ⟨hi.1, ?_⟩
            change B i ω = c n
            have hEq : c n - B i ω = 0 := by simpa using hi.2
            linarith
          · intro hi
            refine ⟨hi.1, ?_⟩
            change c n - B i ω ∈ ({0} : Set ℝ)
            have hEq : B i ω = c n := by simpa using hi.2
            simp [Set.mem_singleton_iff, hEq]
        by_cases h :
            ∃ j : NNReal, 0 ≤ j ∧ c n - B j ω ∈ ({0} : Set ℝ)
        · have h' : ∃ j : NNReal, 0 ≤ j ∧ B j ω ∈ ({c n} : Set ℝ) := hExists.mp h
          rw [if_pos h, if_pos h']
          have hsInf :
              (sInf {i : NNReal | 0 ≤ i ∧ c n - B i ω ∈ ({0} : Set ℝ)} : NNReal) =
                sInf {i : NNReal | 0 ≤ i ∧ B i ω ∈ ({c n} : Set ℝ)} := by
            simpa using congrArg (fun s : Set NNReal ↦ (sInf s : NNReal)) hSet
          simpa using congrArg (fun t : NNReal ↦ ((t : WithTop NNReal))) hsInf
        · have h' : ¬∃ j : NNReal, 0 ≤ j ∧ B j ω ∈ ({c n} : Set ℝ) := by
            intro h'
            exact h (hExists.mpr h')
          rw [if_neg h, if_neg h']
      have hStay :
          T < hittingAfter (fun u (_ : Unit) ↦ c n - B u ω) ({0} : Set ℝ) 0 () := by
        exact
          (continuous_lt_hittingAfter_zero_iff
            (f := fun u ↦ c n - B u ω) (continuous_const.sub hcontB) hStart T).2 hAvoid
      rwa [hHitEq] at hStay
    have hcongr :
        ({ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} : Set Ω) =ᵐ[μ]
          Set.inter ({ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} : Set Ω)
            {ω | Continuous (processPath B ω)} := by
      filter_upwards [hB.continuous_paths] with ω hcont
      apply propext
      constructor
      · intro hω
        exact ⟨hω, hcont⟩
      · intro hω
        exact hω.1
    calc
      μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} =
          μ.real (Set.inter ({ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} : Set Ω)
            {ω | Continuous (processPath B ω)}) := by
            exact MeasureTheory.measureReal_congr hcongr
      _ ≤ μ.real (stayBelow n) := by
            exact MeasureTheory.measureReal_mono hsubset (measure_ne_top μ _)
      _ = ν.real (windows n) := hMass n
  have hWindows_anti : Antitone windows := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by
      exact_mod_cast hmn
    have hmn'' : (m + 2 : ℝ) ≤ n + 2 := by
      linarith
    have hc_le : c n ≤ c m := by
      dsimp [c]
      have hm_pos : 0 < (m + 2 : ℝ) := by positivity
      simpa using one_div_le_one_div_of_le hm_pos hmn''
    refine Set.Icc_subset_Icc ?_ hc_le
    linarith
  have hWindows_inter :
      (⋂ n : ℕ, windows n) = ({0} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      by_contra hx_ne
      have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
      obtain ⟨n, hn_raw⟩ := exists_nat_one_div_lt hx_abs_pos
      have hn : ((n + 1 : ℝ)⁻¹) < |x| := by
        simpa [one_div] using hn_raw
      have hstep : c n < (n + 1 : ℝ)⁻¹ := by
        dsimp [c]
        have hn_pos : (0 : ℝ) < n + 1 := by
          positivity
        have hn_lt : (n + 1 : ℝ) < n + 2 := by
          linarith
        simpa using one_div_lt_one_div_of_lt hn_pos hn_lt
      have hx_mem : x ∈ windows n := (Set.mem_iInter.1 hx) n
      have hx_abs_le : |x| ≤ c n := by
        exact abs_le.2 ⟨by linarith [hx_mem.1], hx_mem.2⟩
      exact (not_lt_of_ge hx_abs_le) (lt_trans hstep hn)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      refine Set.mem_iInter.2 ?_
      intro i
      change -(c i) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ c i
      have hci_nonneg : 0 ≤ c i := by
        dsimp [c]
        positivity
      constructor
      · linarith
      · exact hci_nonneg
  have hWindows_tendsto :
      Tendsto (fun n : ℕ ↦ ν (windows n)) atTop (nhds (ν (⋂ n : ℕ, windows n))) := by
    exact
      tendsto_measure_iInter_atTop
        (μ := ν)
        (s := windows)
        (fun n ↦ measurableSet_Icc.nullMeasurableSet)
        hWindows_anti
        ⟨0, measure_ne_top ν _⟩
  have hSingleton : ν (⋂ n : ℕ, windows n) = 0 := by
    simpa [ν, hWindows_inter] using
      (noAtoms_gaussianReal (ne_of_gt hT)).measure_singleton (0 : ℝ)
  have hWindows_real_tendsto :
      Tendsto (fun n : ℕ ↦ ν.real (windows n)) atTop (nhds (0 : ℝ)) := by
    have hWindows_tendsto_zero : Tendsto (fun n : ℕ ↦ ν (windows n)) atTop (nhds 0) := by
      simpa [hSingleton] using hWindows_tendsto
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hWindows_tendsto_zero
  by_contra hzero
  have hpos : 0 < μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} := by
    have hnonneg : 0 ≤ μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} := by
      positivity
    exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
  have hEventually :
      ∀ᶠ n : ℕ in atTop, ν.real (windows n) < μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} := by
    exact hWindows_real_tendsto.eventually (Iio_mem_nhds hpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  have hlt :
      μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} <
        μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} := by
    exact lt_of_le_of_lt (hBound N) (hN N le_rfl)
  exact (lt_irrefl _ hlt)

/-- Helper for Theorem 21.20: a Brownian path started at `0` almost surely does not stay strictly
negative on the whole tail interval `(0, T]`. -/
private theorem brownianStrictNegativeTail_real_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0} = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let nonpos : Set Ω := {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0}
  have hsubset :
      {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0} ⊆ nonpos := by
    intro ω hω s hsIcc
    rcases lt_or_eq_of_le hsIcc.1 with hs0 | rfl
    · exact (hω s ⟨hs0, hsIcc.2⟩).le
    · simpa [hB.zero]
  have hle : μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0} ≤ 0 := by
    calc
      μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0} ≤ μ.real nonpos := by
        exact MeasureTheory.measureReal_mono hsubset (measure_ne_top μ _)
      _ = 0 := brownianNonpositiveTail_real_eq_zero hB hT
  exact le_antisymm hle (by positivity)

/-- Helper for Theorem 21.20: the zero-time tail-zero event has probability `0`. -/
private theorem brownianTailZeroAvoidance_zeroBranch_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} = 0 := by
  let posTail : Set Ω := {ω | ∀ s ∈ Set.Ioc 0 T, 0 < B s ω}
  let negTail : Set Ω := {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0}
  have hBneg : IsBrownianMotion μ (fun t ω ↦ -B t ω) := neg_isBrownianMotion hB
  have hPosEq :
      μ.real posTail = μ.real {ω | ∀ s ∈ Set.Ioc 0 T, -B s ω < 0} := by
    apply MeasureTheory.measureReal_congr
    filter_upwards with ω
    apply propext
    constructor
    · intro hω s hs
      linarith [hω s hs]
    · intro hω s hs
      linarith [hω s hs]
  have hPosZero : μ.real posTail = 0 := by
    calc
      μ.real posTail = μ.real {ω | ∀ s ∈ Set.Ioc 0 T, -B s ω < 0} := hPosEq
      _ = 0 := by
            simpa using brownianStrictNegativeTail_real_eq_zero
              (B := fun t ω ↦ -B t ω) hBneg hT
  have hNegZero : μ.real negTail = 0 := brownianStrictNegativeTail_real_eq_zero hB hT
  have hSplitAe :
      {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} =ᵐ[μ] ((posTail ∪ negTail : Set Ω)) := by
    filter_upwards [hB.continuous_paths] with ω hcont
    apply propext
    constructor
    · intro hω
      have hTnz : B T ω ≠ 0 := hω T ⟨hT, le_rfl⟩
      rcases lt_or_gt_of_ne hTnz with hTneg | hTpos
      · right
        intro s hs
        by_contra hsNotNeg
        have hsNonneg : 0 ≤ B s ω := le_of_not_gt hsNotNeg
        have hzero_mem : (0 : ℝ) ∈ Set.uIcc (B s ω) (B T ω) := by
          rw [Set.mem_uIcc]
          exact Or.inr ⟨hTneg.le, hsNonneg⟩
        obtain ⟨u, huSeg, huZero⟩ :=
          intermediate_value_uIcc
            (a := s)
            (b := T)
            (f := fun r : NNReal ↦ B r ω)
            hcont.continuousOn
            hzero_mem
        have huIcc : u ∈ Set.Icc s T := by
          simpa [Set.uIcc_of_le hs.2] using huSeg
        exact hω u ⟨lt_of_lt_of_le hs.1 huIcc.1, huIcc.2⟩ huZero
      · left
        intro s hs
        by_contra hsNotPos
        have hsNonpos : B s ω ≤ 0 := le_of_not_gt hsNotPos
        have hzero_mem : (0 : ℝ) ∈ Set.uIcc (B s ω) (B T ω) := by
          rw [Set.mem_uIcc]
          exact Or.inl ⟨hsNonpos, hTpos.le⟩
        obtain ⟨u, huSeg, huZero⟩ :=
          intermediate_value_uIcc
            (a := s)
            (b := T)
            (f := fun r : NNReal ↦ B r ω)
            hcont.continuousOn
            hzero_mem
        have huIcc : u ∈ Set.Icc s T := by
          simpa [Set.uIcc_of_le hs.2] using huSeg
        exact hω u ⟨lt_of_lt_of_le hs.1 huIcc.1, huIcc.2⟩ huZero
    · intro hω s hs
      rcases hω with hPos | hNeg
      · exact (hPos s hs).ne'
      · exact (hNeg s hs).ne
  have hle : μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} ≤ 0 := by
    calc
      μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} = μ.real (posTail ∪ negTail) := by
        exact MeasureTheory.measureReal_congr hSplitAe
      _ ≤ μ.real posTail + μ.real negTail := by
        exact MeasureTheory.measureReal_union_le _ _
      _ = 0 := by
        rw [hPosZero, hNegZero]
        ring
  exact le_antisymm hle (by positivity)

/-- Helper for Theorem 21.20: for a deterministic anchor `x`, Brownian tail zero-avoidance on
`(0, δ]` matches the symmetric Gaussian interval mass at time `δ`. -/
theorem deterministicAnchorTailZeroAvoidance_real_eq_gaussianIntervalMass
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} {δ : NNReal} (hδ : 0 < δ) :
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =
      (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hReflect :
        (gaussianReal 0 δ).real (Set.Iic (-x)) =
          1 - (gaussianReal 0 δ).real (Set.Iic x) :=
      by simpa using centeredGaussian_closedTail_reflect (δ := δ) hδ (-x)
    have hTailLaw :
        μ.real {ω | W δ ω ≤ -x} = (gaussianReal 0 δ).real (Set.Iic (-x)) := by
      have hTailENN :
          μ ((W δ) ⁻¹' Set.Iic (-x)) = (gaussianReal 0 δ) (Set.Iic (-x)) := by
        rw [← Measure.map_apply (hW.stronglyMeasurable δ).measurable measurableSet_Iic]
        exact congrArg (fun ν : Measure ℝ => ν (Set.Iic (-x))) (hW.gaussian_marginal hδ).map_eq
      simpa [Measure.real_def] using congrArg ENNReal.toReal hTailENN
    -- Proof comment: for a negative anchor, rewrite the upper-barrier survival formula through
    -- Gaussian symmetry and then match it with the symmetric interval identity at `a = -x`.
    calc
      μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0}
          = 2 * μ.real {ω | W δ ω ≤ -x} - 1 := by
              exact negativeAnchorTailZeroAvoidance_real_eq_upperBoundaryCdf hW hx hδ
      _ = 2 * (gaussianReal 0 δ).real (Set.Iic (-x)) - 1 := by rw [hTailLaw]
      _ = 1 - 2 * (gaussianReal 0 δ).real (Set.Iic x) := by
            linarith
      _ = (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
            simpa [abs_of_neg hx] using
              (centeredGaussian_interval_real_eq_lowerBoundaryCdf
                (δ := δ) hδ (a := -x) (by linarith : 0 < -x)).symm
  · have hRightZero :
        (gaussianReal 0 δ).real (Set.Icc (-|(0 : ℝ)|) |(0 : ℝ)|) = 0 := by
      have hSingleton :
          (gaussianReal 0 δ).real ({(0 : ℝ)} : Set ℝ) = 0 := by
        simpa [Measure.real_def] using
          congrArg ENNReal.toReal ((noAtoms_gaussianReal (ne_of_gt hδ)).measure_singleton 0)
      simpa using hSingleton
    have hZeroBranch :
        μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, W u ω ≠ 0} = 0 := by
      exact brownianTailZeroAvoidance_zeroBranch_eq_zero hW hδ
    -- Proof comment: the zero-anchor branch is exactly the tail-zero event already shown to have
    -- probability `0` for Brownian motion started at `0`.
    calc
      μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, (0 : ℝ) + W u ω ≠ 0} = 0 := by
        simpa using hZeroBranch
      _ = (gaussianReal 0 δ).real (Set.Icc (-|(0 : ℝ)|) |(0 : ℝ)|) := by
            rw [hRightZero]
  · -- Proof comment: for a positive anchor, the lower-barrier survival formula already matches
    -- the symmetric Gaussian interval identity at `a = x`.
    have hTailLaw :
        μ.real {ω | W δ ω ≤ -x} = (gaussianReal 0 δ).real (Set.Iic (-x)) := by
      have hTailENN :
          μ ((W δ) ⁻¹' Set.Iic (-x)) = (gaussianReal 0 δ) (Set.Iic (-x)) := by
        rw [← Measure.map_apply (hW.stronglyMeasurable δ).measurable measurableSet_Iic]
        exact congrArg (fun ν : Measure ℝ => ν (Set.Iic (-x))) (hW.gaussian_marginal hδ).map_eq
      simpa [Measure.real_def] using congrArg ENNReal.toReal hTailENN
    calc
      μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0}
          = 1 - 2 * μ.real {ω | W δ ω ≤ -x} := by
              exact positiveAnchorTailZeroAvoidance_real_eq_lowerBoundaryCdf hW hx hδ
      _ = 1 - 2 * (gaussianReal 0 δ).real (Set.Iic (-x)) := by
            rw [hTailLaw]
      _ = (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
            simpa [abs_of_pos hx] using
              (centeredGaussian_interval_real_eq_lowerBoundaryCdf
                (δ := δ) hδ (a := x) hx).symm

namespace IsBrownianMotion

/-- Helper for Theorem 21.20: Brownian motion almost surely is not nonpositive on the whole
interval `[0, T]`. -/
private theorem nonpositiveTail_real_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Icc 0 T, B s ω ≤ 0} = 0 := by
  exact brownianNonpositiveTail_real_eq_zero hB hT

/-- Helper for Theorem 21.20: a Brownian path started at `0` almost surely does not stay strictly
negative on the whole tail interval `(0, T]`. -/
theorem strictNegativeTail_real_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω < 0} = 0 := by
  exact brownianStrictNegativeTail_real_eq_zero hB hT

/-- Helper for Theorem 21.20: the zero-time tail-zero event has probability `0`. -/
theorem tailZeroAvoidance_zeroBranch_eq_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T : NNReal} (hT : 0 < T) :
    μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} = 0 := by
  exact brownianTailZeroAvoidance_zeroBranch_eq_zero hB hT

/-- Helper for Theorem 21.20: a Brownian value and the following terminal increment form the
expected independent Gaussian pair. -/
theorem timeValue_increment_hasLaw_prodGaussians
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {t T : NNReal} (ht : t ≤ T) :
    HasLaw (fun ω ↦ (B t ω, B T ω - B t ω))
      ((gaussianReal 0 t).prod (gaussianReal 0 (T - t))) μ := by
  let X : Ω → ℝ := B t
  let Y : Ω → ℝ := fun ω ↦ B T ω - B t ω
  letI : IsBrownianMotion μ B := hB
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hStarted : IsBrownianMotionStartedAt μ B 0 := inferInstance
  have hXlaw : HasLaw X (gaussianReal 0 t) μ := by
    -- Proof comment: view the anchor value `B t` as the increment over `[0, t]`.
    simpa [X, hB.zero] using
      brownianStartedAtIncrement_hasLaw (hB := hStarted) (s := (0 : NNReal)) (t := t) (by simp)
  have hYlaw : HasLaw Y (gaussianReal 0 (T - t)) μ := by
    -- Proof comment: the terminal increment over `[t, T]` has the centered Gaussian law with
    -- variance `T - t`.
    simpa [Y] using brownianStartedAtIncrement_hasLaw (hB := hStarted) (s := t) (t := T) ht
  have hIndep : X ⟂ᵢ[μ] Y := by
    let times : Fin 1 → NNReal := fun _ ↦ T - t
    have hhist : StrictMono (fun _ : Fin 1 ↦ t) := by
      intro i j hij
      fin_cases i
      fin_cases j
      cases hij
    have hVec :
        IndepFun
          (fun ω ↦ fun _ : Fin 1 ↦ B t ω)
          (fun ω ↦ fun _ : Fin 1 ↦ B (t + (T - t)) ω - B t ω)
          μ := by
      -- Proof comment: the one-step future increment vector is independent of the singleton
      -- history vector at time `t`.
      simpa [times] using
        (brownianFutureIncrementVector_indep_historyTuple
          (hB := hStarted) (hist := fun _ : Fin 1 ↦ t) hhist times).symm
    have hScalar :
        (fun ω ↦ (fun _ : Fin 1 ↦ B t ω) 0) ⟂ᵢ[μ]
          (fun ω ↦ (fun _ : Fin 1 ↦ B (t + (T - t)) ω - B t ω) 0) := by
      exact IndepFun.comp hVec (measurable_pi_apply 0) (measurable_pi_apply 0)
    have hFutureEq :
        (fun ω ↦ (fun _ : Fin 1 ↦ B (t + (T - t)) ω - B t ω) 0) =ᵐ[μ] Y := by
      have htime : t + (T - t) = T := by
        simpa [add_comm] using (tsub_add_cancel_of_le ht)
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp [Y, htime]
    -- Proof comment: evaluate both singleton vectors at their unique coordinate to recover the
    -- scalar anchor value and the scalar terminal increment.
    exact hScalar.congr (Filter.Eventually.of_forall fun _ ↦ rfl) hFutureEq
  have hMap :
      μ.map (fun ω ↦ (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      (μ := μ) (f := X) (g := Y) hXlaw.aemeasurable hYlaw.aemeasurable).1 hIndep
  -- Proof comment: combine the product factorization from independence with the two Gaussian
  -- marginal laws to obtain the joint law of the Brownian anchor and terminal increment.
  refine
    { aemeasurable := hXlaw.aemeasurable.prodMk hYlaw.aemeasurable
      map_eq := ?_ }
  simpa [X, Y] using
    calc
      μ.map (fun ω ↦ (X ω, Y ω)) = (μ.map X).prod (μ.map Y) := hMap
      _ = ((gaussianReal 0 t).prod (gaussianReal 0 (T - t))) := by
            rw [hXlaw.map_eq, hYlaw.map_eq]

/-- Helper for Theorem 21.20: the endpoint comparison event is exactly the cone event under the
Gaussian pair `(B t, B T - B t)`. -/
theorem absEndpointComparison_real_eq_prodGaussianConeMass
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {t T : NNReal} (ht : t ≤ T) :
    μ.real {ω | |B T ω - B t ω| ≤ |B t ω|} =
      (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
        {p : ℝ × ℝ | |p.2| ≤ |p.1|}) := by
  let f : Ω → ℝ × ℝ := fun ω ↦ (B t ω, B T ω - B t ω)
  let s : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.2| ≤ |p.1|}
  have hf : Measurable f := by
    -- Proof comment: both coordinates are deterministic-time Brownian evaluations, hence
    -- measurable, so the pair map is measurable as well.
    refine (hB.stronglyMeasurable t).measurable.prodMk ?_
    exact (hB.stronglyMeasurable T).measurable.sub (hB.stronglyMeasurable t).measurable
  have hs : MeasurableSet s := by
    -- Proof comment: the cone event is a closed inequality between continuous coordinate norms.
    simpa [s, Real.norm_eq_abs] using
      (isClosed_le continuous_snd.norm continuous_fst.norm).measurableSet
  have hLaw := timeValue_increment_hasLaw_prodGaussians (hB := hB) ht
  have hpre : f ⁻¹' s = {ω | |B T ω - B t ω| ≤ |B t ω|} := by
    ext ω
    rfl
  -- Proof comment: rewrite the event as a preimage under the Gaussian pair map and then use the
  -- joint law from the previous helper.
  calc
    μ.real {ω | |B T ω - B t ω| ≤ |B t ω|} = μ.real (f ⁻¹' s) := by rw [hpre.symm]
    _ = (μ.map f).real s := by
          rw [MeasureTheory.map_measureReal_apply (μ := μ) (f := f) hf hs]
    _ = (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real s) := by
          rw [hLaw.map_eq]
    _ = (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
          {p : ℝ × ℝ | |p.2| ≤ |p.1|}) := by
          rfl

/-- Helper for Theorem 21.20: the anchor value `B t` is independent of the whole shifted future
increment process `u ↦ B (t + u) - B t`. -/
theorem timeValue_indep_shiftedIncrementProcess
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (t : NNReal) :
    IndepFun (B t) (fun ω ↦ fun u : NNReal ↦ B (t + u) ω - B t ω) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  letI : IsBrownianMotion μ B := hB
  have hBtMeas : Measurable (B t) := (hB.stronglyMeasurable t).measurable
  have hIncMeas :
      ∀ u : NNReal, Measurable (fun ω ↦ B (t + u) ω - B t ω) := by
    intro u
    exact ((hB.stronglyMeasurable (t + u)).measurable.sub (hB.stronglyMeasurable t).measurable)
  refine IndepFun.indepFun_process hBtMeas hIncMeas ?_
  intro J
  let times : Fin J.card → NNReal := fun i ↦ J.orderEmbOfFin rfl i
  have hhist : StrictMono (fun _ : Fin 1 ↦ t) := by
    intro i j hij
    fin_cases i
    fin_cases j
    cases hij
  have hVec :
      IndepFun
        (fun ω ↦ fun _ : Fin 1 ↦ B t ω)
        (fun ω ↦ fun i : Fin J.card ↦ B (t + times i) ω - B t ω)
        μ := by
    -- Proof comment: the finite history/future bridge applied to the single history time `t`
    -- gives independence of `B t` from every finite future increment vector.
    simpa [times] using
      (brownianFutureIncrementVector_indep_historyTuple
        (hB := (inferInstance : IsBrownianMotionStartedAt μ B 0))
        (hist := fun _ : Fin 1 ↦ t) hhist times).symm
  let evalZero : (Fin 1 → ℝ) → ℝ := fun z ↦ z 0
  have hEvalZero : Measurable evalZero := measurable_pi_apply 0
  have hScalar :
      IndepFun
        (B t)
        (fun ω ↦ fun i : Fin J.card ↦ B (t + times i) ω - B t ω)
        μ := by
    -- Proof comment: evaluate the singleton history vector at its only coordinate to recover
    -- the scalar anchor value `B t`.
    refine (hVec.comp hEvalZero measurable_id).congr ?_ ?_
    · exact Filter.Eventually.of_forall fun ω ↦ by
        simp [evalZero]
    · exact Filter.Eventually.of_forall fun ω ↦ by
        ext i
        rfl
  let reindex : (Fin J.card → ℝ) → J → ℝ := fun z u ↦ z ((J.orderIsoOfFin rfl).symm u)
  have hReindexMeas : Measurable reindex := by
    -- Proof comment: reindexing the ordered tuple back to the original finite set `J` is
    -- coordinatewise evaluation at deterministic indices.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact measurable_pi_apply ((J.orderIsoOfFin rfl).symm u)
  have hReindexed :
      IndepFun
        (B t)
        (fun ω ↦ reindex (fun i : Fin J.card ↦ B (t + times i) ω - B t ω))
        μ :=
    hScalar.comp measurable_id hReindexMeas
  have hReindexEq :
      (fun ω ↦ reindex (fun i : Fin J.card ↦ B (t + times i) ω - B t ω)) =
        (fun ω (u : J) ↦ B (t + u.1) ω - B t ω) := by
    funext ω u
    let ku : J := u
    have hindex :
        J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm ku) = u.1 := by
      change (((J.orderIsoOfFin rfl) ((J.orderIsoOfFin rfl).symm ku) : J) : NNReal) = u.1
      simpa [ku] using
        congrArg (fun v : J ↦ (v : NNReal)) ((J.orderIsoOfFin rfl).apply_symm_apply ku)
    simpa [reindex, times] using congrArg (fun r : NNReal ↦ B (t + r) ω - B t ω) hindex
  -- Proof comment: undo the deterministic reindexing to recover the original `J`-indexed family
  -- of shifted future increments.
  simpa [hReindexEq] using hReindexed

/-- Helper for Theorem 21.20: the joint law of the anchor value and the shifted future increment
process factors as the product of their marginals. -/
theorem timeValue_shiftedIncrementProcess_map_eq_prod
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (t : NNReal) :
    μ.map (fun ω ↦ (B t ω, fun u : NNReal ↦ B (t + u) ω - B t ω)) =
      (μ.map (B t)).prod (μ.map fun ω ↦ fun u : NNReal ↦ B (t + u) ω - B t ω) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let g : Ω → NNReal → ℝ := fun ω u ↦ B (t + u) ω - B t ω
  have hBtAemeas : AEMeasurable (B t) μ := (hB.stronglyMeasurable t).measurable.aemeasurable
  have hgMeas : Measurable g := by
    -- Proof comment: coordinatewise deterministic-time measurability gives measurability of the
    -- shifted increment path map into the product path space.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact ((hB.stronglyMeasurable (t + u)).measurable.sub (hB.stronglyMeasurable t).measurable)
  have hIndep : IndepFun (B t) g μ := by
    simpa [g] using timeValue_indep_shiftedIncrementProcess (hB := hB) t
  -- Proof comment: independence of the anchor value and the full shifted increment path is
  -- exactly the product-factorization criterion for their joint pushforward law.
  exact
    (indepFun_iff_map_prod_eq_prod_map_map hBtAemeas hgMeas.aemeasurable).1 hIndep

/-- Helper for Theorem 21.20: negating the path turns the singleton target `{c}` into `{-c}` at
the level of hitting times. -/
theorem negSingletonHittingEvent_eq_singletonHit
    (W : NNReal → Ω → ℝ) {c : ℝ} {δ : NNReal} :
    {ω | δ < hittingAfter (fun u ω ↦ -W u ω) ({c} : Set ℝ) 0 ω} =
      {ω | δ < hittingAfter W ({-c} : Set ℝ) 0 ω} := by
  ext ω
  classical
  have hHit :
      hittingAfter (fun u ω' ↦ -W u ω') ({c} : Set ℝ) 0 ω =
        hittingAfter W ({-c} : Set ℝ) 0 ω := by
    rw [hittingAfter_def, hittingAfter_def]
    simp only [Set.mem_singleton_iff, zero_le, true_and]
    have hExists :
        (∃ j : NNReal, -W j ω = c) ↔
          ∃ j : NNReal, W j ω = -c := by
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        linarith
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        linarith
    have hSet :
        {i : NNReal | -W i ω = c} =
          {i : NNReal | W i ω = -c} := by
      ext i
      constructor
      · intro hi
        have hEq : -W i ω = c := by simpa using hi
        change W i ω = -c
        linarith
      · intro hi
        have hEq : W i ω = -c := by simpa using hi
        change -W i ω = c
        linarith
    by_cases h : ∃ j : NNReal, -W j ω = c
    · have h' : ∃ j : NNReal, W j ω = -c := hExists.mp h
      rw [if_pos h, if_pos h']
      have hsInf :
          (sInf {i : NNReal | -W i ω = c} : NNReal) =
            sInf {i : NNReal | W i ω = -c} := by
        simpa using congrArg (fun s : Set NNReal ↦ (sInf s : NNReal)) hSet
      exact_mod_cast hsInf
    · have h' : ¬∃ j : NNReal, W j ω = -c := by
        exact mt hExists.mpr h
      rw [if_neg h, if_neg h']
  -- Proof comment: once the two singleton hitting times agree pathwise, the strict-survival
  -- events at horizon `δ` agree pathwise as well.
  simpa [hHit]

/-- Helper for Theorem 21.20: a positive deterministic anchor avoids zero on `(0, δ]` almost
surely exactly when the centered Brownian path survives above the lower barrier `-x` until time
`δ`. -/
theorem positiveAnchorTailZeroAvoidance_eq_lowerBarrierSurvival
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : 0 < x) {δ : NNReal} :
    {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =ᵐ[μ]
      {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
  -- Proof comment: first replace the translated zero-hit event by the almost-sure tail
  -- zero-avoidance event, then rewrite the translated singleton hitting time back to `W`.
  refine (translatedZeroHittingEvent_eq_tailZeroAvoidance (hW := hW) (x := x)
      (hx := ne_of_gt hx) (δ := δ)).symm.trans ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa using congrArg (fun s : Set Ω ↦ ω ∈ s)
      (translatedZeroHittingEvent_eq_singletonHit (W := W) (x := x) (δ := δ))

/-- Helper for Theorem 21.20: a negative deterministic anchor avoids zero on `(0, δ]` almost
surely exactly when the centered Brownian path survives below the upper barrier `-x` until time
`δ`. -/
theorem negativeAnchorTailZeroAvoidance_eq_upperBarrierSurvival
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} (hx : x < 0) {δ : NNReal} :
    {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} =ᵐ[μ]
      {ω | δ < hittingAfter W ({-x} : Set ℝ) 0 ω} := by
  -- Proof comment: this is the same translated zero-hit bridge as in the positive-anchor case;
  -- the sign only changes the singleton target from `0` to `-x`.
  refine (translatedZeroHittingEvent_eq_tailZeroAvoidance (hW := hW) (x := x)
      (hx := ne_of_lt hx) (δ := δ)).symm.trans ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa using congrArg (fun s : Set Ω ↦ ω ∈ s)
      (translatedZeroHittingEvent_eq_singletonHit (W := W) (x := x) (δ := δ))

/-- Helper for Theorem 21.20: the compact tails `[1 / (m + 1), δ]` are indexed by this positive
lower cutoff. -/
def tailCompactionFloor (m : ℕ) : NNReal :=
  ((m + 1 : NNReal)⁻¹)

/-- Helper for Theorem 21.20: this measurable rational surrogate encodes tail zero-avoidance by
uniform positive lower bounds on each compact tail `[1 / (m + 1), δ]`. -/
def tailZeroAvoidanceRatPair (δ : NNReal) : Set (ℝ × (NNReal → ℝ)) :=
  ⋂ m : ℕ, ⋃ n : ℕ, ⋂ q : ℚ≥0,
    if hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ then
      {p | (tailCompactionFloor n : ℝ) ≤ |p.1 + p.2 (q : NNReal)|}
    else
      Set.univ

/-- Helper for Theorem 21.20: the rational compact-tail surrogate is measurable on the product
path space. -/
theorem measurableSet_tailZeroAvoidanceRatPair (δ : NNReal) :
    MeasurableSet (tailZeroAvoidanceRatPair δ) := by
  let sectionEvent : ℕ → ℕ → ℚ≥0 → Set (ℝ × (NNReal → ℝ)) :=
    fun m n q ↦
      if hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ then
        {p | (tailCompactionFloor n : ℝ) ≤ |p.1 + p.2 (q : NNReal)|}
      else
        Set.univ
  let lowerApproxEvent : ℕ → Set (ℝ × (NNReal → ℝ)) :=
    fun m ↦ ⋃ n : ℕ, ⋂ q : ℚ≥0, sectionEvent m n q
  let pathEvent : Set (ℝ × (NNReal → ℝ)) := ⋂ m : ℕ, lowerApproxEvent m
  have hSectionMeas : ∀ m n q, MeasurableSet (sectionEvent m n q) := by
    intro m n q
    have hEval :
        Measurable (fun p : ℝ × (NNReal → ℝ) ↦ p.1 + p.2 (q : NNReal)) := by
      exact measurable_fst.add ((measurable_pi_apply (q : NNReal)).comp measurable_snd)
    by_cases hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ
    · -- Proof comment: each active rational section is a closed lower-bound inequality on one
      -- path coordinate.
      simpa [sectionEvent, hq] using
        measurableSet_le
          (f := fun _ : ℝ × (NNReal → ℝ) ↦ (tailCompactionFloor n : ℝ))
          (g := fun p : ℝ × (NNReal → ℝ) ↦ |p.1 + p.2 (q : NNReal)|)
          measurable_const hEval.abs
    · simpa [sectionEvent, hq] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℝ × (NNReal → ℝ))))
  have hLowerApproxMeas : ∀ m, MeasurableSet (lowerApproxEvent m) := by
    intro m
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ hSectionMeas m n q
  have hPathMeas : MeasurableSet pathEvent := by
    exact MeasurableSet.iInter hLowerApproxMeas
  -- Proof comment: the surrogate is already written as the countable intersection/union/intersection
  -- used in the measurable section analysis above.
  simpa [tailZeroAvoidanceRatPair, sectionEvent, lowerApproxEvent, pathEvent] using hPathMeas

/-- Helper for Theorem 21.20: on continuous paths, the rational compact-tail surrogate is exactly
the tail zero-avoidance event on `(0, δ]`. -/
theorem continuousTailZeroAvoidance_iff_mem_tailZeroAvoidanceRatPair
    {f : NNReal → ℝ} (hcont : Continuous f) {x : ℝ} {δ : NNReal} :
    (x, f) ∈ tailZeroAvoidanceRatPair δ ↔ ∀ u ∈ Set.Ioc 0 δ, x + f u ≠ 0 := by
  constructor
  · intro hRat u hu huZero
    have hRat' :
        ∀ m : ℕ, ∃ n : ℕ, ∀ q : ℚ≥0,
          if hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ then
            (tailCompactionFloor n : ℝ) ≤ |x + f (q : NNReal)|
          else
            True := by
      simpa [tailZeroAvoidanceRatPair] using hRat
    obtain ⟨m, hm_lt⟩ := exists_nat_one_div_lt (show 0 < (u : ℝ) by exact_mod_cast hu.1)
    have hm_lt_u : tailCompactionFloor m < u := by
      simpa [tailCompactionFloor] using hm_lt
    rcases hRat' m with ⟨n, hn⟩
    let ε : ℝ := (tailCompactionFloor n : ℝ)
    have hε_pos : 0 < ε := by
      dsimp [ε, tailCompactionFloor]
      positivity
    let U : Set NNReal := {v | |x + f v| < ε}
    have hU_open : IsOpen U := by
      -- Proof comment: continuity turns the small-absolute-value condition into an open
      -- neighborhood of the alleged zero.
      simpa [U] using (isOpen_Iio.preimage ((continuous_const.add hcont).abs))
    have huU : u ∈ U := by
      simpa [U, ε, huZero] using hε_pos
    have hUNhds : U ∈ nhds u := hU_open.mem_nhds huU
    rcases
        (mem_nhds_iff_exists_Ioo_subset'
          (show ∃ l : NNReal, l < u from ⟨tailCompactionFloor m, hm_lt_u⟩)
          (show ∃ r : NNReal, u < r from
            ⟨u + 1, by simpa using lt_add_of_pos_right u zero_lt_one⟩)).1 hUNhds with
      ⟨l, r, hlr, hIoo⟩
    have hmax_lt_u : max l (tailCompactionFloor m) < u := max_lt hlr.1 hm_lt_u
    obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn (show ((max l (tailCompactionFloor m) : NNReal)
        : ℝ) < (u : ℝ) by exact_mod_cast hmax_lt_u)
    have hq_nonneg : 0 ≤ q := by
      have hq_nonneg_real : (0 : ℝ) ≤ q := by
        have hmax_nonneg : (0 : ℝ) ≤ ((max l (tailCompactionFloor m) : NNReal) : ℝ) := by
          positivity
        exact le_trans hmax_nonneg hqLower.le
      exact Rat.cast_nonneg.mp hq_nonneg_real
    let qnn : ℚ≥0 := ⟨q, Rat.cast_nonneg.mp hq_nonneg⟩
    have hqLower_nn : max l (tailCompactionFloor m) < (qnn : NNReal) := by
      exact_mod_cast hqLower
    have hqUpper_nn : (qnn : NNReal) < u := by
      exact_mod_cast hqUpper
    have hqU : (qnn : NNReal) ∈ U := by
      have hql : l < (qnn : NNReal) := lt_of_le_of_lt (le_max_left _ _) hqLower_nn
      exact hIoo ⟨hql, lt_trans hqUpper_nn hlr.2⟩
    have hqFloor : tailCompactionFloor m ≤ (qnn : NNReal) := by
      exact le_trans (le_max_right _ _) hqLower_nn.le
    have hqδ : (qnn : NNReal) ≤ δ := le_trans hqUpper_nn.le hu.2
    have hLower : ε ≤ |x + f (qnn : NNReal)| := by
      simpa [ε, hqFloor, hqδ] using hn qnn
    have hUpper : |x + f (qnn : NNReal)| < ε := by
      simpa [U, ε] using hqU
    exact (not_le_of_gt hUpper) hLower
  · intro hAvoid
    have hRat' :
        ∀ m : ℕ, ∃ n : ℕ, ∀ q : ℚ≥0,
          if hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ then
            (tailCompactionFloor n : ℝ) ≤ |x + f (q : NNReal)|
          else
            True := by
      intro m
      by_cases hTail : δ < tailCompactionFloor m
      · refine ⟨0, ?_⟩
        intro q
        by_cases hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ
        · exact False.elim ((not_le_of_gt hTail) (le_trans hq.1 hq.2))
        · simp [hq]
      · have hmδ : tailCompactionFloor m ≤ δ := le_of_not_gt hTail
        let s : Set NNReal := Set.Icc (tailCompactionFloor m) δ
        let g : NNReal → ℝ := fun u ↦ |x + f u|
        have hg_cont : Continuous g := (continuous_const.add hcont).abs
        obtain ⟨z, hzMem, hzMin⟩ :=
          isCompact_Icc.exists_isMinOn
            ⟨tailCompactionFloor m, Set.mem_Icc.2 ⟨le_rfl, hmδ⟩⟩ hg_cont.continuousOn
        have hz_pos : 0 < g z := by
          have hfloor_pos : 0 < tailCompactionFloor m := by
            dsimp [tailCompactionFloor]
            positivity
          have hz_tail : z ∈ Set.Ioc 0 δ := by
            exact ⟨lt_of_lt_of_le hfloor_pos hzMem.1, hzMem.2⟩
          dsimp [g]
          exact abs_pos.mpr (hAvoid z hz_tail)
        obtain ⟨n, hn_raw⟩ := exists_nat_one_div_lt hz_pos
        refine ⟨n, ?_⟩
        intro q
        by_cases hq : tailCompactionFloor m ≤ (q : NNReal) ∧ (q : NNReal) ≤ δ
        · have hqMem : (q : NNReal) ∈ s := hq
          have hz_le : g z ≤ g (q : NNReal) := hzMin hqMem
          have hFloorLe : (tailCompactionFloor n : ℝ) ≤ g z := by
            simpa [g, tailCompactionFloor] using (le_of_lt hn_raw)
          simpa [g, hq] using le_trans hFloorLe hz_le
        · simp [hq]
    simpa [tailZeroAvoidanceRatPair] using hRat'

/-- Helper for Theorem 21.20: the fixed-anchor row of the measurable rational-path surrogate has
the same mass as the deterministic tail zero-avoidance event, hence the Gaussian interval mass. -/
theorem processPathTailZeroAvoidance_row_real_eq_intervalMass
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} {δ : NNReal} (hδ : 0 < δ) :
    ((μ.map (processPath W)).real (Prod.mk x ⁻¹' tailZeroAvoidanceRatPair δ)) =
      (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
  have hPathMeas : Measurable (processPath W) := by
    -- Proof comment: deterministic-time evaluations generate measurability of the full path map.
    refine measurable_pi_lambda _ fun u ↦ ?_
    simpa [processPath] using (hW.stronglyMeasurable u).measurable
  have hRowMeas :
      MeasurableSet (Prod.mk x ⁻¹' tailZeroAvoidanceRatPair δ) := by
    exact measurable_prodMk_left (measurableSet_tailZeroAvoidanceRatPair δ)
  have hRowAe :
      (processPath W) ⁻¹' (Prod.mk x ⁻¹' tailZeroAvoidanceRatPair δ) =ᵐ[μ]
        {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} := by
    -- Proof comment: continuity of the Brownian sample path upgrades the rational compact-tail
    -- surrogate back to the original tail zero-avoidance condition.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [processPath] using
      (continuousTailZeroAvoidance_iff_mem_tailZeroAvoidanceRatPair
        (f := fun u ↦ W u ω) hω (x := x) (δ := δ))
  calc
    ((μ.map (processPath W)).real (Prod.mk x ⁻¹' tailZeroAvoidanceRatPair δ)) =
        μ.real ((processPath W) ⁻¹' (Prod.mk x ⁻¹' tailZeroAvoidanceRatPair δ)) := by
          rw [MeasureTheory.map_measureReal_apply
            (μ := μ) (f := processPath W) hPathMeas hRowMeas]
    _ = μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, x + W u ω ≠ 0} := by
          exact MeasureTheory.measureReal_congr hRowAe
    _ = (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
          exact deterministicAnchorTailZeroAvoidance_real_eq_gaussianIntervalMass (hW := hW) hδ

/-- Helper for Theorem 21.20: under the path-law pushforward `μ.map (processPath W)`, the endpoint
row `{p | |p δ| ≤ |x|}` has the centered Gaussian interval mass at time `δ`. -/
theorem processPathEndpointComparison_row_real_eq_intervalMass
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {x : ℝ} {δ : NNReal} (hδ : 0 < δ) :
    ((μ.map (processPath W)).real {p : NNReal → ℝ | |p δ| ≤ |x|}) =
      (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
  have hPathMeas : Measurable (processPath W) := by
    -- Proof comment: the full path map is measurable because every deterministic-time coordinate
    -- `ω ↦ W u ω` is measurable.
    refine measurable_pi_lambda _ fun u ↦ ?_
    simpa [processPath] using (hW.stronglyMeasurable u).measurable
  have hRowMeas :
      MeasurableSet {p : NNReal → ℝ | |p δ| ≤ |x|} := by
    -- Proof comment: the row set is the inverse image of a closed half-line under the measurable
    -- endpoint-evaluation map `p ↦ |p δ|`.
    simpa [Real.norm_eq_abs] using
      measurableSet_le (f := fun p : NNReal → ℝ ↦ ‖p δ‖)
        (g := fun _ : NNReal → ℝ ↦ ‖x‖)
        (measurable_pi_apply δ).norm measurable_const
  have hRowPreimage :
      (processPath W) ⁻¹' {p : NNReal → ℝ | |p δ| ≤ |x|} =
        {ω | |W δ ω| ≤ |x|} := by
    -- Proof comment: evaluating the pushed-forward path at time `δ` recovers the original
    -- Brownian value `W δ`.
    ext ω
    simp [processPath]
  have hEndpointPreimage :
      (W δ) ⁻¹' Set.Icc (-|x|) |x| = {ω | |W δ ω| ≤ |x|} := by
    -- Proof comment: the absolute-value comparison is exactly membership in the symmetric
    -- interval `[-|x|, |x|]`.
    ext ω
    simp [abs_le]
  -- Proof comment: rewrite the path-row event through evaluation at time `δ`, then use the
  -- Gaussian marginal law of `W δ`.
  calc
    ((μ.map (processPath W)).real {p : NNReal → ℝ | |p δ| ≤ |x|}) =
        μ.real {ω | |W δ ω| ≤ |x|} := by
          rw [← hRowPreimage, MeasureTheory.map_measureReal_apply
            (μ := μ) (f := processPath W) hPathMeas hRowMeas]
    _ = (μ.map (W δ)).real (Set.Icc (-|x|) |x|) := by
          rw [← hEndpointPreimage, MeasureTheory.map_measureReal_apply
            (μ := μ) (f := W δ) (hW.stronglyMeasurable δ).measurable measurableSet_Icc]
    _ = (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
          rw [(hW.gaussian_marginal hδ).map_eq]

/-- Helper for Theorem 21.20: the real mass of a measurable product event is the integral of its
rowwise real masses. -/
theorem prod_real_eq_integral_sectionReal
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν]
    {s : Set (α × β)}
    (hs : MeasurableSet s) :
    (μ.prod ν).real s = ∫ x, ν.real (Prod.mk x ⁻¹' s) ∂μ := by
  -- Proof comment: `Measure.prod_apply` expresses the product mass as a row `lintegral`, and
  -- `integral_toReal` converts that `ENNReal` integral into the displayed real integral.
  rw [Measure.real_def, Measure.prod_apply hs]
  have hfinite : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ⊤ := by
    exact Filter.Eventually.of_forall fun x ↦ measure_lt_top ν _
  exact (integral_toReal (measurable_measure_prodMk_left hs).aemeasurable hfinite).symm

/-- Helper for Theorem 21.20: if the anchor `A` is independent of the whole shifted Brownian path,
then integrating the deterministic-anchor row formula identifies tail zero-avoidance with the
endpoint comparison event. -/
theorem independentAnchorTailZeroAvoidance_real_eq_endpointComparison
    {μ : Measure Ω} {A : Ω → ℝ} (hA : Measurable A)
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {δ : NNReal} (hδ : 0 < δ)
    (hProd :
      μ.map (fun ω ↦ (A ω, processPath W ω)) =
        (μ.map A).prod (μ.map (processPath W))) :
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, A ω + W u ω ≠ 0} =
      μ.real {ω | |W δ ω| ≤ |A ω|} := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let tailPair : Set (ℝ × (NNReal → ℝ)) := tailZeroAvoidanceRatPair δ
  let endpointPair : Set (ℝ × (NNReal → ℝ)) := {q | |q.2 δ| ≤ |q.1|}
  have hPathMeas : Measurable (processPath W) := by
    -- Proof comment: coordinatewise Brownian measurability again promotes to measurability of the
    -- full path map.
    refine measurable_pi_lambda _ fun u ↦ ?_
    simpa [processPath] using (hW.stronglyMeasurable u).measurable
  have hPairMeas : Measurable (fun ω ↦ (A ω, processPath W ω)) := hA.prodMk hPathMeas
  have hTailPairMeas : MeasurableSet tailPair := measurableSet_tailZeroAvoidanceRatPair δ
  have hEndpointPairMeas : MeasurableSet endpointPair := by
    -- Proof comment: the product event only depends on the anchor coordinate and the terminal
    -- path value `p δ`, so it is a closed inequality between measurable maps.
    simpa [endpointPair, Real.norm_eq_abs] using
      measurableSet_le
        (f := fun q : ℝ × (NNReal → ℝ) ↦ ‖q.2 δ‖)
        (g := fun q : ℝ × (NNReal → ℝ) ↦ ‖q.1‖)
        (((measurable_pi_apply δ).comp measurable_snd).norm) measurable_fst.norm
  have hEndpointPairPreimage :
      (fun ω ↦ (A ω, processPath W ω)) ⁻¹' endpointPair =
        {ω | |W δ ω| ≤ |A ω|} := by
    -- Proof comment: the product event pulls back to the original endpoint comparison event by
    -- evaluating the path coordinate at time `δ`.
    ext ω
    simp [endpointPair, processPath]
  have hTailPairAe :
      (fun ω ↦ (A ω, processPath W ω)) ⁻¹' tailPair =ᵐ[μ]
        {ω | ∀ u ∈ Set.Ioc 0 δ, A ω + W u ω ≠ 0} := by
    -- Route correction: replace the nonmeasurable raw path-space tail event by the countable
    -- rational compact-tail surrogate and only then invoke continuity almost surely.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [tailPair, processPath] using
      (continuousTailZeroAvoidance_iff_mem_tailZeroAvoidanceRatPair
        (f := fun u ↦ W u ω) hω (x := A ω) (δ := δ))
  have hEndpointPairReal :
      μ.real {ω | |W δ ω| ≤ |A ω|} =
        ((μ.map A).prod (μ.map (processPath W))).real endpointPair := by
    -- Proof comment: the product factorization already normalizes the right-hand side into a
    -- measurable event on `ℝ × (NNReal → ℝ)`.
    calc
      μ.real {ω | |W δ ω| ≤ |A ω|} =
          (μ.map (fun ω ↦ (A ω, processPath W ω))).real endpointPair := by
            rw [← hEndpointPairPreimage, MeasureTheory.map_measureReal_apply
              (μ := μ) (f := fun ω ↦ (A ω, processPath W ω)) hPairMeas hEndpointPairMeas]
      _ = ((μ.map A).prod (μ.map (processPath W))).real endpointPair := by
            rw [hProd]
  have hTailPairReal :
      μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, A ω + W u ω ≠ 0} =
        ((μ.map A).prod (μ.map (processPath W))).real tailPair := by
    -- Proof comment: the same product factorization rewrites the left-hand side once the
    -- continuity bridge has replaced it by the measurable rational surrogate.
    calc
      μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, A ω + W u ω ≠ 0} =
          μ.real ((fun ω ↦ (A ω, processPath W ω)) ⁻¹' tailPair) := by
            exact (MeasureTheory.measureReal_congr hTailPairAe).symm
      _ = (μ.map (fun ω ↦ (A ω, processPath W ω))).real tailPair := by
            rw [MeasureTheory.map_measureReal_apply
              (μ := μ) (f := fun ω ↦ (A ω, processPath W ω)) hPairMeas hTailPairMeas]
      _ = ((μ.map A).prod (μ.map (processPath W))).real tailPair := by
            rw [hProd]
  have hEndpointRow :
      ∀ x : ℝ,
        ((μ.map (processPath W)).real {p : NNReal → ℝ | |p δ| ≤ |x|}) =
          (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) := by
    -- Proof comment: each fixed endpoint section already matches the Gaussian interval mass.
    intro x
    exact processPathEndpointComparison_row_real_eq_intervalMass (hW := hW) (x := x) hδ
  have hTailIntegral :
      ((μ.map A).prod (μ.map (processPath W))).real tailPair =
        ∫ x, (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) ∂(μ.map A) := by
    -- Proof comment: the left product event is now a measurable set, so Fubini reduces it to the
    -- already identified fixed-anchor rows.
    calc
      ((μ.map A).prod (μ.map (processPath W))).real tailPair =
          ∫ x, ((μ.map (processPath W)).real (Prod.mk x ⁻¹' tailPair)) ∂(μ.map A) := by
            exact prod_real_eq_integral_sectionReal (μ := μ.map A) (ν := μ.map (processPath W))
              hTailPairMeas
      _ = ∫ x, (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) ∂(μ.map A) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x ↦
              processPathTailZeroAvoidance_row_real_eq_intervalMass (hW := hW) (x := x) hδ
  have hEndpointIntegral :
      μ.real {ω | |W δ ω| ≤ |A ω|} =
        ∫ x, (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) ∂(μ.map A) := by
    -- Proof comment: the endpoint comparison product event has the same row masses, so it shares
    -- the same anchor integral.
    calc
      μ.real {ω | |W δ ω| ≤ |A ω|} =
          ((μ.map A).prod (μ.map (processPath W))).real endpointPair := hEndpointPairReal
      _ = ∫ x, ((μ.map (processPath W)).real (Prod.mk x ⁻¹' endpointPair)) ∂(μ.map A) := by
            exact prod_real_eq_integral_sectionReal (μ := μ.map A) (ν := μ.map (processPath W))
              hEndpointPairMeas
      _ = ∫ x, (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) ∂(μ.map A) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x ↦ by
              simpa [endpointPair] using hEndpointRow x
  -- Proof comment: both the tail-zero event and the endpoint event are now identified with the
  -- same anchor integral, so the conditioning bridge closes by transitivity.
  calc
    μ.real {ω | ∀ u ∈ Set.Ioc 0 δ, A ω + W u ω ≠ 0} =
        ((μ.map A).prod (μ.map (processPath W))).real tailPair := hTailPairReal
    _ = ∫ x, (gaussianReal 0 δ).real (Set.Icc (-|x|) |x|) ∂(μ.map A) := hTailIntegral
    _ = μ.real {ω | |W δ ω| ≤ |A ω|} := hEndpointIntegral.symm

local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Helper for Theorem 21.20: the weighted Box-Muller cone is measured through this explicit
three-interval window in the angular coordinate. -/
def boxMullerAngleWindow (α : ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) (α / (2 * Real.pi)) ∪
    Set.Icc (1 / 2 - α / (2 * Real.pi)) (1 / 2 + α / (2 * Real.pi)) ∪
    Set.Icc (1 - α / (2 * Real.pi)) 1

/-- Helper for Theorem 21.20: scaling a standard Gaussian pair by the square-root variances
normalizes the cone mass to the standard product law. -/
theorem prodGaussianConeMass_eq_standardConeMass
    {t T : NNReal} (ht_pos : 0 < t) (htT : t < T) :
    (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
      {p : ℝ × ℝ | |p.2| ≤ |p.1|}) =
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).real
        {p : ℝ × ℝ |
          Real.sqrt ((T - t : NNReal) : ℝ) * |p.2| ≤ Real.sqrt (t : ℝ) * |p.1|}) := by
  let a : ℝ := Real.sqrt (t : ℝ)
  let b : ℝ := Real.sqrt ((T - t : NNReal) : ℝ)
  let f : ℝ × ℝ → ℝ × ℝ := fun p ↦ (a * p.1, b * p.2)
  let s : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.2| ≤ |p.1|}
  let s' : Set (ℝ × ℝ) := {p : ℝ × ℝ | b * |p.2| ≤ a * |p.1|}
  have ha_pos : 0 < a := by
    -- Proof comment: the time variance `t` is positive on the interior branch, so its square root
    -- is a positive scaling factor.
    exact Real.sqrt_pos.2 (by exact_mod_cast ht_pos)
  have hb_pos : 0 < b := by
    -- Proof comment: the complementary variance `T - t` is also positive on the interior branch.
    exact Real.sqrt_pos.2 (by exact_mod_cast (tsub_pos_of_lt htT))
  have hf : Measurable f := by
    -- Proof comment: the diagonal scaling map is coordinatewise measurable.
    fun_prop
  have hs : MeasurableSet s := by
    -- Proof comment: the unweighted cone is a closed inequality between the two coordinate norms.
    simpa [s, Real.norm_eq_abs] using
      (isClosed_le continuous_snd.norm continuous_fst.norm).measurableSet
  have hmapLeft : (gaussianReal 0 1).map (a * ·) = gaussianReal 0 t := by
    -- Proof comment: `gaussianReal_map_const_mul` transports the first standard Gaussian to
    -- variance `t`.
    simpa [a, Real.sq_sqrt, ht_pos.le] using
      (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) a)
  have hmapRight : (gaussianReal 0 1).map (b * ·) = gaussianReal 0 (T - t) := by
    -- Proof comment: the same scaling formula transports the second coordinate to variance
    -- `T - t`.
    simpa [b, Real.sq_sqrt, (tsub_pos_of_lt htT).le] using
      (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) b)
  have hmap :
      (gaussianReal 0 t).prod (gaussianReal 0 (T - t)) =
        Measure.map f ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    -- Proof comment: after matching both one-dimensional marginals, the product law is exactly
    -- the pushforward of the standard Gaussian pair by the diagonal scaling map.
    calc
      (gaussianReal 0 t).prod (gaussianReal 0 (T - t)) =
          ((gaussianReal 0 1).map (a * ·)).prod ((gaussianReal 0 1).map (b * ·)) := by
            rw [hmapLeft, hmapRight]
      _ = Measure.map (Prod.map (a * ·) (b * ·))
            ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            exact Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
              (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
      _ = Measure.map f ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rfl
  have hpre : f ⁻¹' s = s' := by
    -- Proof comment: pulling the cone back through the diagonal scaling replaces `|y| ≤ |x|` by
    -- the weighted inequality `b |y| ≤ a |x|`.
    ext p
    simp [f, s, s', abs_mul, abs_of_pos ha_pos, abs_of_pos hb_pos, mul_assoc]
  -- Proof comment: rewrite the cone mass through the diagonal pushforward and the explicit
  -- preimage calculation.
  calc
    (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
        {p : ℝ × ℝ | |p.2| ≤ |p.1|}) =
        (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real s) := by
            rfl
    _ = (Measure.map f ((gaussianReal 0 1).prod (gaussianReal 0 1))).real s := by
          rw [hmap]
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).real (f ⁻¹' s)) := by
          rw [MeasureTheory.map_measureReal_apply
            (μ := ((gaussianReal 0 1).prod (gaussianReal 0 1))) (f := f) hf hs]
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).real s') := by
          rw [hpre]
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).real
          {p : ℝ × ℝ |
            Real.sqrt ((T - t : NNReal) : ℝ) * |p.2| ≤ Real.sqrt (t : ℝ) * |p.1|}) := by
          rfl

/-- Helper for Theorem 21.20: on the open unit interval, the Box-Muller cone inequality is
equivalent to the same weighted inequality on the angular sine/cosine terms after canceling the
strictly positive radial factor. -/
theorem boxMullerCone_mem_iff_weightedTrigInequality
    {a b u v : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    boxMullerPair u v ∈ {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|} ↔
      a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| := by
  let r : ℝ := Real.sqrt (-2 * Real.log u)
  have hr_pos : 0 < r := by
    -- Proof comment: the Box-Muller radius is strictly positive on `u ∈ (0,1)` because
    -- `log u < 0` there.
    refine Real.sqrt_pos.2 ?_
    nlinarith [Real.log_neg hu.1 hu.2]
  constructor
  · intro hCone
    -- Proof comment: rewrite the cone event through the explicit Box-Muller coordinates and
    -- cancel the common positive radial factor.
    have hScaledAbs :
        (a * |Real.sin (2 * Real.pi * v)|) * |r| ≤
          (b * |Real.cos (2 * Real.pi * v)|) * |r| := by
      simpa [boxMullerPair, r, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hCone
    have hScaled :
        (a * |Real.sin (2 * Real.pi * v)|) * r ≤
          (b * |Real.cos (2 * Real.pi * v)|) * r := by
      simpa [abs_of_nonneg hr_pos.le] using hScaledAbs
    exact (mul_le_mul_iff_of_pos_right hr_pos).mp hScaled
  · intro hTrig
    -- Proof comment: multiply the angular inequality back by the positive radius to recover the
    -- original cone comparison.
    have hScaled :
        (a * |Real.sin (2 * Real.pi * v)|) * r ≤
          (b * |Real.cos (2 * Real.pi * v)|) * r :=
      (mul_le_mul_iff_of_pos_right hr_pos).2 hTrig
    have hScaledAbs :
        (a * |Real.sin (2 * Real.pi * v)|) * |r| ≤
          (b * |Real.cos (2 * Real.pi * v)|) * |r| := by
      simpa [abs_of_nonneg hr_pos.le] using hScaled
    simpa [boxMullerPair, r, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hScaledAbs

/-- Helper for Theorem 21.20: the arctangent ratio attached to positive weights lies in the
principal interval `(0, π / 2)`. -/
theorem arctanRatio_mem_Ioo_piDivTwo
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.arctan (b / a) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  constructor
  · -- Proof comment: positive weights give a positive ratio, hence a positive arctangent.
    exact Real.arctan_pos.2 (div_pos hb ha)
  · -- Proof comment: every real arctangent stays strictly below `π / 2`.
    exact Real.arctan_lt_pi_div_two _

/-- Helper for Theorem 21.20: on the principal interval `[0, π / 2)`, the weighted trigonometric
inequality is exactly the arctangent angle bound. -/
private theorem weightedTrigInequality_nonneg_iff_le_arctan
    {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < Real.pi / 2) :
    a * Real.sin θ ≤ b * Real.cos θ ↔ θ ≤ Real.arctan (b / a) := by
  have hcos_pos : 0 < Real.cos θ := by
    -- Proof comment: on `[0, π / 2)`, the cosine term is strictly positive, so division is safe.
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt⟩
  constructor
  · intro h
    -- Proof comment: divide by the positive cosine and then by the positive weight `a` to obtain
    -- the tangent bound.
    have hDiv : (a * Real.sin θ) / Real.cos θ ≤ b := by
      exact (div_le_iff₀ hcos_pos).2 h
    have hTan : a * Real.tan θ ≤ b := by
      simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hDiv
    have hTanLe : Real.tan θ ≤ b / a := by
      exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using hTan)
    have hArctan :
        Real.arctan (Real.tan θ) ≤ Real.arctan (b / a) := Real.arctan_mono hTanLe
    simpa [Real.arctan_tan (by linarith) hθ_lt] using hArctan
  · intro h
    -- Proof comment: convert the arctangent bound back to a tangent bound, then clear the same
    -- positive factors in reverse.
    have hArctan :
        Real.arctan (Real.tan θ) ≤ Real.arctan (b / a) := by
      simpa [Real.arctan_tan (by linarith) hθ_lt] using h
    have hTanLe : Real.tan θ ≤ b / a := Real.arctan_le_arctan_iff.mp hArctan
    have hTan : a * Real.tan θ ≤ b := by
      have hMul : Real.tan θ * a ≤ b := (le_div_iff₀ ha).mp hTanLe
      simpa [mul_comm] using hMul
    have hDiv : (a * Real.sin θ) / Real.cos θ ≤ b := by
      simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hTan
    exact (div_le_iff₀ hcos_pos).mp hDiv

/-- Helper for Theorem 21.20: on the interior unit square and away from the quarter-turn
singularities, the Box-Muller weighted cone depends only on the angular coordinate and equals the
explicit three-interval window. -/
theorem boxMullerCone_mem_angleWindow_iff
    {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (hvQuarter : v ≠ 1 / 4) (hvThreeQuarter : v ≠ 3 / 4) :
    boxMullerPair u v ∈ {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|} ↔
      v ∈ boxMullerAngleWindow (Real.arctan (b / a)) := by
  let α : ℝ := Real.arctan (b / a)
  let β : ℝ := α / (2 * Real.pi)
  have hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := arctanRatio_mem_Ioo_piDivTwo ha hb
  have hβ_nonneg : 0 ≤ β := by
    -- Proof comment: the angle window radius is nonnegative because `α ∈ (0, π / 2)`.
    positivity
  have hβ_lt_quarter : β < 1 / 4 := by
    -- Proof comment: dividing `α < π / 2` by `2π` places the window radius below one quarter.
    have h : α / (2 * Real.pi) < (Real.pi / 2) / (2 * Real.pi) := by
      exact div_lt_div_of_pos_right hα.2 (by positivity : 0 < 2 * Real.pi)
    have hquarter : (Real.pi / 2) / (2 * Real.pi) = (1 / 4 : ℝ) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa [β, hquarter] using h
  -- Route correction: the raw Box-Muller cone is first reduced to the angular inequality, and
  -- each quarter of `(0, 1)` is then normalized to the principal interval `[0, π / 2)`.
  rw [boxMullerCone_mem_iff_weightedTrigInequality (a := a) (b := b) hu]
  rcases le_or_gt v (1 / 4 : ℝ) with hv_le_quarter | hv_gt_quarter
  · have hv_lt_quarter : v < 1 / 4 := lt_of_le_of_ne hv_le_quarter hvQuarter
    have hθ_nonneg : 0 ≤ 2 * Real.pi * v := by
      nlinarith [Real.pi_pos, hv.1]
    have hθ_lt : 2 * Real.pi * v < Real.pi / 2 := by
      nlinarith [Real.pi_pos, hv_lt_quarter]
    have hsin_nonneg : 0 ≤ Real.sin (2 * Real.pi * v) := by
      exact Real.sin_nonneg_of_mem_Icc ⟨hθ_nonneg, by linarith [hθ_lt]⟩
    have hcos_pos : 0 < Real.cos (2 * Real.pi * v) := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt⟩
    have hTrig :
        a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
          2 * Real.pi * v ≤ α := by
      -- Proof comment: on the first quarter, both trigonometric factors have their principal
      -- signs, so the absolute values disappear directly.
      calc
        a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
            a * Real.sin (2 * Real.pi * v) ≤ b * Real.cos (2 * Real.pi * v) := by
              simpa [abs_of_nonneg hsin_nonneg, abs_of_pos hcos_pos]
        _ ↔ 2 * Real.pi * v ≤ α := by
              simpa [α] using
                weightedTrigInequality_nonneg_iff_le_arctan
                  (a := a) (b := b) (θ := 2 * Real.pi * v) ha hb hθ_nonneg hθ_lt
    have hScaled :
        2 * Real.pi * v ≤ α ↔ v ∈ Set.Icc (0 : ℝ) β := by
      have hTwoPiPos : 0 < 2 * Real.pi := by
        positivity
      constructor
      · intro hθ
        have hvβ : v ≤ β := by
          dsimp [β]
          have hθ' : v * (2 * Real.pi) ≤ α := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hθ
          exact (le_div_iff₀ hTwoPiPos).2 hθ'
        exact ⟨hv.1.le, hvβ⟩
      · intro hvβ
        have hMul := mul_le_mul_of_nonneg_right hvβ.2 hTwoPiPos.le
        have hMul' : v * (2 * Real.pi) ≤ α := by
          calc
            v * (2 * Real.pi) ≤ β * (2 * Real.pi) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
            _ = α := by
              dsimp [β]
              field_simp [Real.pi_ne_zero]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hMul'
    have hWindow :
        v ∈ boxMullerAngleWindow α ↔ v ∈ Set.Icc (0 : ℝ) β := by
      have hWindowForm :
          v ∈ boxMullerAngleWindow α ↔
            (0 ≤ v ∧ v ≤ β) ∨
              (1 / 2 - β ≤ v ∧ v ≤ 1 / 2 + β) ∨
              (1 - β ≤ v ∧ v ≤ 1) := by
        simp [boxMullerAngleWindow, β, Set.mem_union, Set.mem_Icc, or_assoc]
      rw [hWindowForm]
      constructor
      · intro hvw
        rcases hvw with hvw | hvw | hvw
        · simpa [β] using hvw
        · exfalso
          linarith [hvw.1, hv_lt_quarter, hβ_lt_quarter]
        · exfalso
          linarith [hvw.1, hv_lt_quarter, hβ_lt_quarter]
      · intro hvβ
        exact Or.inl hvβ
    exact hTrig.trans (hScaled.trans hWindow.symm)
  · rcases le_or_gt v (1 / 2 : ℝ) with hv_le_half | hv_gt_half
    · let θ : ℝ := Real.pi - 2 * Real.pi * v
      have hθ_nonneg : 0 ≤ θ := by
        dsimp [θ]
        nlinarith [Real.pi_pos, hv_le_half]
      have hθ_lt : θ < Real.pi / 2 := by
        dsimp [θ]
        nlinarith [Real.pi_pos, hv_gt_quarter]
      have hsin_nonneg : 0 ≤ Real.sin θ := by
        exact Real.sin_nonneg_of_mem_Icc ⟨hθ_nonneg, by linarith [hθ_lt]⟩
      have hcos_pos : 0 < Real.cos θ := by
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt⟩
      have hSinEq : Real.sin (2 * Real.pi * v) = Real.sin θ := by
        dsimp [θ]
        rw [Real.sin_pi_sub]
      have hCosEq : Real.cos (2 * Real.pi * v) = -Real.cos θ := by
        have htmp : Real.cos θ = -Real.cos (2 * Real.pi * v) := by
          dsimp [θ]
          simpa using (Real.cos_pi_sub (2 * Real.pi * v))
        linarith
      have hTrig :
          a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
            θ ≤ α := by
        -- Proof comment: reflect the second quarter across `π / 2`, reducing it to the same
        -- principal-angle comparison as in the first quarter.
        calc
          a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
              a * Real.sin θ ≤ b * Real.cos θ := by
                rw [hSinEq, hCosEq]
                simp [abs_of_nonneg hsin_nonneg, abs_of_pos hcos_pos]
          _ ↔ θ ≤ α := by
                simpa [α] using
                  weightedTrigInequality_nonneg_iff_le_arctan
                    (a := a) (b := b) (θ := θ) ha hb hθ_nonneg hθ_lt
      have hScaled : θ ≤ α ↔ 1 / 2 - β ≤ v := by
        have hTwoPiPos : 0 < 2 * Real.pi := by positivity
        constructor
        · intro hθ
          have hMul : (1 / 2 - v) * (2 * Real.pi) ≤ α := by
            dsimp [θ] at hθ ⊢
            nlinarith [hθ]
          have hDiv : 1 / 2 - v ≤ α / (2 * Real.pi) := (le_div_iff₀ hTwoPiPos).2 hMul
          dsimp [β]
          linarith
        · intro hvβ
          have hDiv : 1 / 2 - v ≤ α / (2 * Real.pi) := by
            dsimp [β] at hvβ
            linarith
          have hMul : (1 / 2 - v) * (2 * Real.pi) ≤ α := (le_div_iff₀ hTwoPiPos).1 hDiv
          dsimp [θ]
          nlinarith [hMul]
      have hWindow :
          v ∈ boxMullerAngleWindow α ↔ 1 / 2 - β ≤ v := by
        have hWindowForm :
            v ∈ boxMullerAngleWindow α ↔
              (0 ≤ v ∧ v ≤ β) ∨
                (1 / 2 - β ≤ v ∧ v ≤ 1 / 2 + β) ∨
                (1 - β ≤ v ∧ v ≤ 1) := by
          simp [boxMullerAngleWindow, β, Set.mem_union, Set.mem_Icc, or_assoc]
        rw [hWindowForm]
        constructor
        · intro hvw
          rcases hvw with hvw | hvw | hvw
          · exfalso
            linarith [hvw.2, hv_gt_quarter, hβ_lt_quarter]
          · exact hvw.1
          · exfalso
            linarith [hvw.1, hv_le_half, hβ_lt_quarter]
        · intro hvβ
          have hvUpper : v ≤ 1 / 2 + β := by
            linarith [hv_le_half, hβ_nonneg]
          exact Or.inr <| Or.inl ⟨hvβ, hvUpper⟩
      exact hTrig.trans (hScaled.trans hWindow.symm)
    · rcases le_or_gt v (3 / 4 : ℝ) with hv_le_threeQuarter | hv_gt_threeQuarter
      · have hv_lt_threeQuarter : v < 3 / 4 := lt_of_le_of_ne hv_le_threeQuarter hvThreeQuarter
        let θ : ℝ := 2 * Real.pi * v - Real.pi
        have hθ_nonneg : 0 ≤ θ := by
          dsimp [θ]
          nlinarith [Real.pi_pos, hv_gt_half]
        have hθ_lt : θ < Real.pi / 2 := by
          dsimp [θ]
          nlinarith [Real.pi_pos, hv_lt_threeQuarter]
        have hsin_nonneg : 0 ≤ Real.sin θ := by
          exact Real.sin_nonneg_of_mem_Icc ⟨hθ_nonneg, by linarith [hθ_lt]⟩
        have hcos_pos : 0 < Real.cos θ := by
          exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt⟩
        have hSinEq : Real.sin (2 * Real.pi * v) = -Real.sin θ := by
          have htmp : Real.sin θ = -Real.sin (2 * Real.pi * v) := by
            dsimp [θ]
            simpa using (Real.sin_sub_pi (2 * Real.pi * v))
          linarith
        have hCosEq : Real.cos (2 * Real.pi * v) = -Real.cos θ := by
          have htmp : Real.cos θ = -Real.cos (2 * Real.pi * v) := by
            dsimp [θ]
            simp
          linarith
        have hTrig :
            a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
              θ ≤ α := by
          -- Proof comment: after subtracting `π`, the third quarter has the same principal-angle
          -- form, with both sine and cosine merely picking up a common sign.
          calc
            a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
                a * Real.sin θ ≤ b * Real.cos θ := by
                  rw [hSinEq, hCosEq]
                  simp [abs_of_nonneg hsin_nonneg, abs_of_pos hcos_pos]
            _ ↔ θ ≤ α := by
                  simpa [α] using
                    weightedTrigInequality_nonneg_iff_le_arctan
                      (a := a) (b := b) (θ := θ) ha hb hθ_nonneg hθ_lt
        have hScaled : θ ≤ α ↔ v ≤ 1 / 2 + β := by
          have hTwoPiPos : 0 < 2 * Real.pi := by positivity
          constructor
          · intro hθ
            have hMul : (v - 1 / 2) * (2 * Real.pi) ≤ α := by
              dsimp [θ] at hθ ⊢
              nlinarith [hθ]
            have hDiv : v - 1 / 2 ≤ α / (2 * Real.pi) := (le_div_iff₀ hTwoPiPos).2 hMul
            dsimp [β]
            linarith
          · intro hvβ
            have hDiv : v - 1 / 2 ≤ α / (2 * Real.pi) := by
              dsimp [β] at hvβ
              linarith
            have hMul : (v - 1 / 2) * (2 * Real.pi) ≤ α := (le_div_iff₀ hTwoPiPos).1 hDiv
            dsimp [θ]
            nlinarith [hMul]
        have hWindow :
            v ∈ boxMullerAngleWindow α ↔ v ≤ 1 / 2 + β := by
          have hWindowForm :
              v ∈ boxMullerAngleWindow α ↔
                (0 ≤ v ∧ v ≤ β) ∨
                  (1 / 2 - β ≤ v ∧ v ≤ 1 / 2 + β) ∨
                  (1 - β ≤ v ∧ v ≤ 1) := by
            simp [boxMullerAngleWindow, β, Set.mem_union, Set.mem_Icc, or_assoc]
          rw [hWindowForm]
          constructor
          · intro hvw
            rcases hvw with hvw | hvw | hvw
            · exfalso
              linarith [hvw.2, hv_gt_half, hβ_lt_quarter]
            · exact hvw.2
            · exfalso
              linarith [hvw.1, hv_lt_threeQuarter, hβ_lt_quarter]
          · intro hvβ
            have hvLower : 1 / 2 - β ≤ v := by
              linarith [hv_gt_half, hβ_nonneg]
            exact Or.inr <| Or.inl ⟨hvLower, hvβ⟩
        exact hTrig.trans (hScaled.trans hWindow.symm)
      · let θ : ℝ := 2 * Real.pi - 2 * Real.pi * v
        have hθ_nonneg : 0 ≤ θ := by
          dsimp [θ]
          nlinarith [Real.pi_pos, hv.2]
        have hθ_lt : θ < Real.pi / 2 := by
          dsimp [θ]
          nlinarith [Real.pi_pos, hv_gt_threeQuarter]
        have hsin_nonneg : 0 ≤ Real.sin θ := by
          exact Real.sin_nonneg_of_mem_Icc ⟨hθ_nonneg, by linarith [hθ_lt]⟩
        have hcos_pos : 0 < Real.cos θ := by
          exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt⟩
        have hSinEq : Real.sin (2 * Real.pi * v) = -Real.sin θ := by
          have htmp : Real.sin θ = -Real.sin (2 * Real.pi * v) := by
            dsimp [θ]
            simp
          linarith
        have hCosEq : Real.cos (2 * Real.pi * v) = Real.cos θ := by
          have htmp : Real.cos θ = Real.cos (2 * Real.pi * v) := by
            dsimp [θ]
            simp
          linarith
        have hTrig :
            a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
              θ ≤ α := by
          -- Proof comment: reflect the fourth quarter across `2π`; only the sine changes sign,
          -- so the same principal-angle comparison closes the branch.
          calc
            a * |Real.sin (2 * Real.pi * v)| ≤ b * |Real.cos (2 * Real.pi * v)| ↔
                a * Real.sin θ ≤ b * Real.cos θ := by
                  rw [hSinEq, hCosEq]
                  simp [abs_of_nonneg hsin_nonneg, abs_of_pos hcos_pos]
            _ ↔ θ ≤ α := by
                  simpa [α] using
                    weightedTrigInequality_nonneg_iff_le_arctan
                      (a := a) (b := b) (θ := θ) ha hb hθ_nonneg hθ_lt
        have hScaled : θ ≤ α ↔ 1 - β ≤ v := by
          have hTwoPiPos : 0 < 2 * Real.pi := by positivity
          constructor
          · intro hθ
            have hMul : (1 - v) * (2 * Real.pi) ≤ α := by
              dsimp [θ] at hθ ⊢
              nlinarith [hθ]
            have hDiv : 1 - v ≤ α / (2 * Real.pi) := (le_div_iff₀ hTwoPiPos).2 hMul
            dsimp [β]
            linarith
          · intro hvβ
            have hDiv : 1 - v ≤ α / (2 * Real.pi) := by
              dsimp [β] at hvβ
              linarith
            have hMul : (1 - v) * (2 * Real.pi) ≤ α := (le_div_iff₀ hTwoPiPos).1 hDiv
            dsimp [θ]
            nlinarith [hMul]
        have hWindow :
            v ∈ boxMullerAngleWindow α ↔ 1 - β ≤ v := by
          have hWindowForm :
              v ∈ boxMullerAngleWindow α ↔
                (0 ≤ v ∧ v ≤ β) ∨
                  (1 / 2 - β ≤ v ∧ v ≤ 1 / 2 + β) ∨
                  (1 - β ≤ v ∧ v ≤ 1) := by
            simp [boxMullerAngleWindow, β, Set.mem_union, Set.mem_Icc, or_assoc]
          rw [hWindowForm]
          constructor
          · intro hvw
            rcases hvw with hvw | hvw | hvw
            · exfalso
              linarith [hvw.2, hv_gt_threeQuarter, hβ_lt_quarter]
            · exfalso
              linarith [hvw.2, hv_gt_threeQuarter, hβ_lt_quarter]
            · exact hvw.1
          · intro hvβ
            exact Or.inr <| Or.inr ⟨hvβ, hv.2.le⟩
        exact hTrig.trans (hScaled.trans hWindow.symm)

/-- Helper for Theorem 21.20: under the unit-square product measure, the weighted Box-Muller cone
is almost everywhere the cylinder cut out by the explicit angle window. -/
theorem boxMullerConePreimage_ae_eq_angleWindow
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2) ⁻¹'
        {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|} =ᵐ[
          (unitIntervalVolume).prod unitIntervalVolume]
      (Set.univ ×ˢ boxMullerAngleWindow (Real.arctan (b / a))) := by
  have hFstLaw :
      HasLaw Prod.fst unitIntervalVolume ((unitIntervalVolume).prod unitIntervalVolume) :=
    (measurePreserving_fst (μ := unitIntervalVolume) (ν := unitIntervalVolume)).hasLaw
  have hSndLaw :
      HasLaw Prod.snd unitIntervalVolume ((unitIntervalVolume).prod unitIntervalVolume) :=
    (measurePreserving_snd (μ := unitIntervalVolume) (ν := unitIntervalVolume)).hasLaw
  have hIccAe : ∀ᵐ x : ℝ ∂unitIntervalVolume, x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc]
      with x hx
    exact hx
  have hZeroAe : ∀ᵐ x : ℝ ∂unitIntervalVolume, x ≠ 0 := by
    rw [ae_iff]
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) ({x : ℝ | x ≠ 0}ᶜ) = 0
    have hset : ({x : ℝ | x ≠ 0}ᶜ) = ({0} : Set ℝ) := by
      ext x
      simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    simp
  have hOneAe : ∀ᵐ x : ℝ ∂unitIntervalVolume, x ≠ 1 := by
    rw [ae_iff]
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) ({x : ℝ | x ≠ 1}ᶜ) = 0
    have hset : ({x : ℝ | x ≠ 1}ᶜ) = ({1} : Set ℝ) := by
      ext x
      simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton (1 : ℝ))]
    simp
  have hQuarterAe : ∀ᵐ x : ℝ ∂unitIntervalVolume, x ≠ 1 / 4 := by
    rw [ae_iff]
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) ({x : ℝ | x ≠ 1 / 4}ᶜ) = 0
    have hset : ({x : ℝ | x ≠ 1 / 4}ᶜ) = ({1 / 4} : Set ℝ) := by
      ext x
      simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton (1 / 4 : ℝ))]
    have hinter :
        ({(1 / 4 : ℝ)} : Set ℝ) ∩ Set.Icc (0 : ℝ) 1 = ({1 / 4} : Set ℝ) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        subst hx
        norm_num
    rw [hinter]
    simp
  have hThreeQuarterAe : ∀ᵐ x : ℝ ∂unitIntervalVolume, x ≠ 3 / 4 := by
    rw [ae_iff]
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) ({x : ℝ | x ≠ 3 / 4}ᶜ) = 0
    have hset : ({x : ℝ | x ≠ 3 / 4}ᶜ) = ({3 / 4} : Set ℝ) := by
      ext x
      simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton (3 / 4 : ℝ))]
    have hinter :
        ({(3 / 4 : ℝ)} : Set ℝ) ∩ Set.Icc (0 : ℝ) 1 = ({3 / 4} : Set ℝ) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        subst hx
        norm_num
    rw [hinter]
    simp
  have hFstIcc :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume),
        q.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.fst ((unitIntervalVolume).prod unitIntervalVolume),
          x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [hFstLaw.map_eq] using hIccAe
    exact
      (ae_map_iff (measurePreserving_fst (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable measurableSet_Icc).1 hMap
  have hFstZero :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.1 ≠ 0 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.fst ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 0 := by
      simpa [hFstLaw.map_eq] using hZeroAe
    exact
      (ae_map_iff (measurePreserving_fst (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (0 : ℝ)).compl)).1 hMap
  have hFstOne :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.1 ≠ 1 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.fst ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 1 := by
      simpa [hFstLaw.map_eq] using hOneAe
    exact
      (ae_map_iff (measurePreserving_fst (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (1 : ℝ)).compl)).1 hMap
  have hSndIcc :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume),
        q.2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.snd ((unitIntervalVolume).prod unitIntervalVolume),
          x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [hSndLaw.map_eq] using hIccAe
    exact
      (ae_map_iff (measurePreserving_snd (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable measurableSet_Icc).1 hMap
  have hSndZero :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.2 ≠ 0 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.snd ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 0 := by
      simpa [hSndLaw.map_eq] using hZeroAe
    exact
      (ae_map_iff (measurePreserving_snd (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (0 : ℝ)).compl)).1 hMap
  have hSndOne :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.2 ≠ 1 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.snd ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 1 := by
      simpa [hSndLaw.map_eq] using hOneAe
    exact
      (ae_map_iff (measurePreserving_snd (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (1 : ℝ)).compl)).1 hMap
  have hSndQuarter :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.2 ≠ 1 / 4 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.snd ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 1 / 4 :=
      by simpa [hSndLaw.map_eq] using hQuarterAe
    exact
      (ae_map_iff (measurePreserving_snd (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (1 / 4 : ℝ)).compl)).1
        hMap
  have hSndThreeQuarter :
      ∀ᵐ q : ℝ × ℝ ∂((unitIntervalVolume).prod unitIntervalVolume), q.2 ≠ 3 / 4 := by
    have hMap :
        ∀ᵐ x : ℝ ∂Measure.map Prod.snd ((unitIntervalVolume).prod unitIntervalVolume), x ≠ 3 / 4 :=
      by simpa [hSndLaw.map_eq] using hThreeQuarterAe
    exact
      (ae_map_iff (measurePreserving_snd (μ := unitIntervalVolume)
        (ν := unitIntervalVolume)).aemeasurable ((measurableSet_singleton (3 / 4 : ℝ)).compl)).1
        hMap
  -- Proof comment: away from the boundary and the two quarter-turn singularities, the pointwise
  -- angular classification from `boxMullerCone_mem_angleWindow_iff` applies directly.
  filter_upwards
      [hFstIcc, hFstZero, hFstOne, hSndIcc, hSndZero, hSndOne, hSndQuarter, hSndThreeQuarter]
      with q hq1Icc hq10 hq11 hq2Icc hq20 hq21 hq24 hq234
  have hu : q.1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hq1Icc.1 (Ne.symm hq10),
    lt_of_le_of_ne hq1Icc.2 hq11⟩
  have hv : q.2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hq2Icc.1 (Ne.symm hq20),
    lt_of_le_of_ne hq2Icc.2 hq21⟩
  apply propext
  constructor
  · intro hqMem
    have hCone :
        boxMullerPair q.1 q.2 ∈ {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|} := by
      simpa [Set.mem_preimage] using hqMem
    have hAngle :=
      (boxMullerCone_mem_angleWindow_iff
        (a := a) (b := b) (u := q.1) (v := q.2) ha hb hu hv hq24 hq234).mp hCone
    exact ⟨by simp, hAngle⟩
  · intro hqMem
    have hAngle : q.2 ∈ boxMullerAngleWindow (Real.arctan (b / a)) := by
      have hPair : q.1 ∈ (Set.univ : Set ℝ) ∧ q.2 ∈ boxMullerAngleWindow (Real.arctan (b / a)) :=
        hqMem
      exact hPair.2
    have hCone :=
      (boxMullerCone_mem_angleWindow_iff
        (a := a) (b := b) (u := q.1) (v := q.2) ha hb hu hv hq24 hq234).mpr hAngle
    simpa [Set.mem_preimage] using hCone

/-- Helper for Theorem 21.20: the unit-interval angle window has the expected Lebesgue mass
`(2 / π) * α`. -/
theorem unitIntervalAngleWindow_real_eq_arctan
    {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_lt : α < Real.pi / 2) :
    (unitIntervalVolume : Measure ℝ).real (boxMullerAngleWindow α) =
      (2 / Real.pi) * α := by
  let β : ℝ := α / (2 * Real.pi)
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    positivity
  have hβ_lt_quarter : β < 1 / 4 := by
    have h : α / (2 * Real.pi) < (Real.pi / 2) / (2 * Real.pi) := by
      exact div_lt_div_of_pos_right hα_lt (by positivity : 0 < 2 * Real.pi)
    have hquarter : (Real.pi / 2) / (2 * Real.pi) = (1 / 4 : ℝ) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa [β, hquarter] using h
  have hβ_le_half : β ≤ 1 / 2 := by
    linarith
  let I₀ : Set ℝ := Set.Icc 0 β
  let I₁ : Set ℝ := Set.Icc (1 / 2 - β) (1 / 2 + β)
  let I₂ : Set ℝ := Set.Icc (1 - β) 1
  have hI₀_subset : I₀ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by linarith [hβ_le_half])⟩
  have hI₁_subset : I₁ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1, hβ_le_half], by linarith [hx.2, hβ_le_half]⟩
  have hI₂_subset : I₂ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1, hβ_le_half], hx.2⟩
  have hI₀ :
      (unitIntervalVolume : Measure ℝ).real I₀ = β := by
    have hRestrict := measureReal_restrict_apply (μ := volume) (s := Set.Icc (0 : ℝ) 1)
      (t := I₀) (by simp [I₀])
    -- Proof comment: each component interval sits inside `[0,1]`, so restricting Lebesgue
    -- measure to the unit interval does not change its mass.
    calc
      (unitIntervalVolume : Measure ℝ).real I₀ = volume.real I₀ := by
        simpa [Set.inter_eq_left.mpr hI₀_subset] using hRestrict
      _ = β - 0 := by
        simpa [I₀] using (Real.volume_real_Icc_of_le hβ_nonneg)
      _ = β := by
        ring
  have hI₁ :
      (unitIntervalVolume : Measure ℝ).real I₁ = 2 * β := by
    have hRestrict := measureReal_restrict_apply (μ := volume) (s := Set.Icc (0 : ℝ) 1)
      (t := I₁) (by simp [I₁])
    -- Proof comment: the middle interval has length `2β`.
    calc
      (unitIntervalVolume : Measure ℝ).real I₁ = volume.real I₁ := by
        simpa [Set.inter_eq_left.mpr hI₁_subset] using hRestrict
      _ = (1 / 2 + β) - (1 / 2 - β) := by
        simpa [I₁] using
          (Real.volume_real_Icc_of_le (by linarith : 1 / 2 - β ≤ 1 / 2 + β))
      _ = 2 * β := by
        ring
  have hI₂ :
      (unitIntervalVolume : Measure ℝ).real I₂ = β := by
    have hRestrict := measureReal_restrict_apply (μ := volume) (s := Set.Icc (0 : ℝ) 1)
      (t := I₂) (by simp [I₂])
    -- Proof comment: the right interval is the reflected copy of the left interval and has the
    -- same length `β`.
    calc
      (unitIntervalVolume : Measure ℝ).real I₂ = volume.real I₂ := by
        simpa [Set.inter_eq_left.mpr hI₂_subset] using hRestrict
      _ = 1 - (1 - β) := by
        simpa [I₂] using (Real.volume_real_Icc_of_le (by linarith : 1 - β ≤ 1))
      _ = β := by
        ring
  have hSep₀₁ : β < 1 / 2 - β := by
    linarith
  have hSep₁₂ : 1 / 2 + β < 1 - β := by
    linarith
  have hDisjoint₀₁ : Disjoint I₀ I₁ := by
    refine Set.disjoint_left.2 ?_
    intro x hx₀ hx₁
    exact (not_le_of_gt hSep₀₁) (le_trans hx₁.1 hx₀.2)
  have hDisjointUnion₂ : Disjoint (I₀ ∪ I₁) I₂ := by
    refine Set.disjoint_left.2 ?_
    intro x hx hx₂
    rcases hx with hx₀ | hx₁
    · have : β < 1 - β := by
        linarith
      exact (not_le_of_gt this) (le_trans hx₂.1 hx₀.2)
    · exact (not_le_of_gt hSep₁₂) (le_trans hx₂.1 hx₁.2)
  -- Proof comment: for `α < π / 2`, the three intervals are disjoint and their lengths add up to
  -- `4β = (2 / π) α`.
  calc
    (unitIntervalVolume : Measure ℝ).real (boxMullerAngleWindow α)
        = (unitIntervalVolume : Measure ℝ).real ((I₀ ∪ I₁) ∪ I₂) := by
            simp [boxMullerAngleWindow, I₀, I₁, I₂, β]
    _ = (unitIntervalVolume : Measure ℝ).real (I₀ ∪ I₁) +
          (unitIntervalVolume : Measure ℝ).real I₂ := by
            exact MeasureTheory.measureReal_union hDisjointUnion₂ (by simp [I₂])
    _ = ((unitIntervalVolume : Measure ℝ).real I₀ +
          (unitIntervalVolume : Measure ℝ).real I₁) +
          (unitIntervalVolume : Measure ℝ).real I₂ := by
            congr 1
            exact MeasureTheory.measureReal_union hDisjoint₀₁ (by simp [I₁])
    _ = 4 * β := by
          rw [hI₀, hI₁, hI₂]
          ring
    _ = (2 / Real.pi) * α := by
          dsimp [β]
          field_simp [Real.pi_ne_zero]
          ring

/-- Helper for Theorem 21.20: the standard Gaussian cone mass is the arctangent ratio coming from
the Box-Muller angle window. -/
theorem standardGaussianConeMass_eq_arctanRatio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|}) =
      (2 / Real.pi) * Real.arctan (b / a) := by
  letI : IsProbabilityMeasure unitIntervalVolume := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    norm_num [Real.volume_Icc]
  let s : Set (ℝ × ℝ) := {p : ℝ × ℝ | a * |p.2| ≤ b * |p.1|}
  let α : ℝ := Real.arctan (b / a)
  have hs : MeasurableSet s := by
    -- Proof comment: the weighted cone is a closed inequality between continuous weighted norms.
    simpa [s, Real.norm_eq_abs] using
      (isClosed_le (continuous_const.mul continuous_snd.norm)
        (continuous_const.mul continuous_fst.norm)).measurableSet
  have hAngleMeas : MeasurableSet (boxMullerAngleWindow α) := by
    -- Proof comment: the angle window is a finite union of closed intervals.
    simp [boxMullerAngleWindow, α]
  have hBoxMeas : Measurable (fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2) := by
    -- Proof comment: the deterministic Box-Muller map is measurable on the square.
    fun_prop
  have hFstLaw :
      HasLaw Prod.fst unitIntervalVolume ((unitIntervalVolume).prod unitIntervalVolume) :=
    (measurePreserving_fst (μ := unitIntervalVolume) (ν := unitIntervalVolume)).hasLaw
  have hSndLaw :
      HasLaw Prod.snd unitIntervalVolume ((unitIntervalVolume).prod unitIntervalVolume) :=
    (measurePreserving_snd (μ := unitIntervalVolume) (ν := unitIntervalVolume)).hasLaw
  have hIndep : Prod.fst ⟂ᵢ[((unitIntervalVolume).prod unitIntervalVolume)] Prod.snd := by
    -- Proof comment: the two coordinate projections are independent under a product measure.
    simpa using
      (indepFun_prod (μ := unitIntervalVolume) (ν := unitIntervalVolume)
        (X := fun x : ℝ ↦ x) (Y := fun y : ℝ ↦ y) measurable_id measurable_id)
  have hJoint :
      HasLaw (fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))
        ((unitIntervalVolume).prod unitIntervalVolume) := by
    -- Proof comment: apply the existing Box-Muller law to the two coordinate projections of the
    -- unit-square product measure.
    simpa using
      (boxMullerPair_hasLaw (P := ((unitIntervalVolume).prod unitIntervalVolume))
        (U := Prod.fst) (V := Prod.snd) hFstLaw hSndLaw hIndep)
  have hSection :
      ((Set.univ : Set ℝ) ×ˢ boxMullerAngleWindow α) =
        (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' boxMullerAngleWindow α := by
    ext q
    simp
  have hα_nonneg : 0 ≤ α := by
    -- Proof comment: the ratio `b / a` is positive, hence so is its arctangent.
    exact Real.arctan_nonneg.2 (by positivity)
  have hα_lt : α < Real.pi / 2 := by
    -- Proof comment: every real arctangent lies strictly below `π / 2`.
    exact Real.arctan_lt_pi_div_two _
  -- Proof comment: transport the cone event through the Box-Muller pushforward, replace its
  -- preimage by the angle window almost everywhere, then evaluate the remaining one-dimensional
  -- mass on the second coordinate.
  calc
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).real s) =
        (((unitIntervalVolume).prod unitIntervalVolume).map
          (fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2)).real s := by
            rw [hJoint.map_eq]
    _ = (((unitIntervalVolume).prod unitIntervalVolume).real
          ((fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2) ⁻¹' s)) := by
            rw [MeasureTheory.map_measureReal_apply
              (μ := ((unitIntervalVolume).prod unitIntervalVolume))
              (f := fun q : ℝ × ℝ ↦ boxMullerPair q.1 q.2) hBoxMeas hs]
    _ = (((unitIntervalVolume).prod unitIntervalVolume).real
          (Set.univ ×ˢ boxMullerAngleWindow α)) := by
            exact
              MeasureTheory.measureReal_congr
                (boxMullerConePreimage_ae_eq_angleWindow (a := a) (b := b) ha hb)
    _ = (((unitIntervalVolume).prod unitIntervalVolume).real
          (Prod.snd ⁻¹' boxMullerAngleWindow α)) := by
            rw [hSection]
    _ = (unitIntervalVolume : Measure ℝ).real (boxMullerAngleWindow α) := by
          rw [← MeasureTheory.map_measureReal_apply
            (μ := ((unitIntervalVolume).prod unitIntervalVolume))
            (f := Prod.snd) measurable_snd hAngleMeas]
          rw [(measurePreserving_snd (μ := unitIntervalVolume) (ν := unitIntervalVolume)).map_eq]
    _ = (2 / Real.pi) * α := by
          exact unitIntervalAngleWindow_real_eq_arctan hα_nonneg hα_lt
    _ = (2 / Real.pi) * Real.arctan (b / a) := by
          rfl

/-- Helper for Theorem 21.20: the arctangent ratio from the normalized Gaussian cone is exactly
the arcsine expression in the theorem statement. -/
theorem arctanSqrtInteriorRatio_eq_arcsinSqrtRatio
    {t T : NNReal} (ht_pos : 0 < t) (htT : t < T) :
    Real.arctan (Real.sqrt (t : ℝ) / Real.sqrt ((T - t : NNReal) : ℝ)) =
      Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
  have hT_pos : 0 < T := lt_trans ht_pos htT
  have hT_real_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT_pos
  have hsub_real_pos : 0 < ((T - t : NNReal) : ℝ) := by
    exact_mod_cast (tsub_pos_of_lt htT)
  have hsqrtRatio_mem :
      Real.sqrt ((t : ℝ) / (T : ℝ)) ∈ Set.Ioo (-(1 : ℝ)) 1 := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: the square root is nonnegative, so it certainly lies above `-1`.
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((t : ℝ) / (T : ℝ)) := Real.sqrt_nonneg _
      linarith
    · -- Proof comment: because `t < T`, the normalized ratio `t / T` lies in `(0,1)`, hence its
      -- square root is also strictly below `1`.
      have hratio_lt : (t : ℝ) / (T : ℝ) < 1 := by
        exact (div_lt_one hT_real_pos).2 (by exact_mod_cast htT)
      have hratio_nonneg : 0 ≤ (t : ℝ) / (T : ℝ) := by
        positivity
      have hsq_lt : (Real.sqrt ((t : ℝ) / (T : ℝ))) ^ 2 < 1 := by
        rw [Real.sq_sqrt hratio_nonneg]
        exact hratio_lt
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((t : ℝ) / (T : ℝ)) := Real.sqrt_nonneg _
      nlinarith
  -- Proof comment: use the canonical `arcsin_eq_arctan` interface, then normalize both square
  -- roots with the common factor `√T`.
  rw [Real.arcsin_eq_arctan hsqrtRatio_mem]
  have hratio_nonneg : 0 ≤ (t : ℝ) / (T : ℝ) := by
    positivity
  rw [Real.sq_sqrt hratio_nonneg]
  have hsqrt_div_t :
      Real.sqrt ((t : ℝ) / (T : ℝ)) = Real.sqrt (t : ℝ) / Real.sqrt (T : ℝ) := by
    exact Real.sqrt_div' (t : ℝ) (show 0 ≤ (T : ℝ) by positivity)
  have hsub_nonneg : 0 ≤ ((T - t : NNReal) : ℝ) := by
    positivity
  have hsqrt_div_sub :
      Real.sqrt (1 - (t : ℝ) / (T : ℝ)) =
        Real.sqrt ((T - t : NNReal) : ℝ) / Real.sqrt (T : ℝ) := by
    have hrewrite : 1 - (t : ℝ) / (T : ℝ) = ((T - t : NNReal) : ℝ) / (T : ℝ) := by
      rw [NNReal.coe_sub htT.le]
      field_simp [ne_of_gt hT_real_pos]
    rw [hrewrite]
    exact Real.sqrt_div' ((T - t : NNReal) : ℝ) (show 0 ≤ (T : ℝ) by positivity)
  rw [hsqrt_div_t, hsqrt_div_sub]
  field_simp [ne_of_gt hT_real_pos, ne_of_gt hsub_real_pos]

/-- Helper for Theorem 21.20: the remaining Gaussian cone mass is expected to evaluate to the
arcsine expression from Lévy's law. -/
theorem prodGaussianConeMass_eq_arcsine
    {t T : NNReal} (ht_pos : 0 < t) (htT : t < T) :
    (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
      {p : ℝ × ℝ | |p.2| ≤ |p.1|}) =
      (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
  have hsub_real_pos : 0 < ((T - t : NNReal) : ℝ) := by
    exact_mod_cast (tsub_pos_of_lt htT)
  -- Proof comment: the remaining cone mass route is now a short calc chain through the scaled
  -- standard Gaussian cone and the normalized `arctan` expression.
  calc
    (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
        {p : ℝ × ℝ | |p.2| ≤ |p.1|}) =
        (((gaussianReal 0 1).prod (gaussianReal 0 1)).real
          {p : ℝ × ℝ |
            Real.sqrt ((T - t : NNReal) : ℝ) * |p.2| ≤
              Real.sqrt (t : ℝ) * |p.1|}) := by
            exact prodGaussianConeMass_eq_standardConeMass ht_pos htT
    _ = (2 / Real.pi) *
          Real.arctan (Real.sqrt (t : ℝ) / Real.sqrt ((T - t : NNReal) : ℝ)) := by
            exact
              standardGaussianConeMass_eq_arctanRatio
                (a := Real.sqrt ((T - t : NNReal) : ℝ))
                (b := Real.sqrt (t : ℝ))
                (ha := Real.sqrt_pos.2 hsub_real_pos)
                (hb := Real.sqrt_pos.2 (by exact_mod_cast ht_pos))
    _ = (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
          rw [arctanSqrtInteriorRatio_eq_arcsinSqrtRatio ht_pos htT]

/-- Helper for Theorem 21.20: the event-probability form of Lévy's arcsine law. -/
theorem lastZeroBefore_eventProbability_eq_arcsine
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T t : NNReal} (hT : 0 < T) (ht : t ≤ T) :
    μ.real ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic t) =
      (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht0 : t = 0
  · subst ht0
    -- Proof comment: the zero-time branch is exactly the Brownian tail-zero event on `(0, T]`,
    -- which was already shown to be null.
    calc
      μ.real ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic (0 : NNReal)) =
          μ.real {ω | ∀ s ∈ Set.Ioc 0 T, B s ω ≠ 0} := by
            rw [lastZeroBefore_preimage_Iic_eq_tailZeroAvoidance (B := B) (t := 0) (T := T)
              (by simp)]
      _ = 0 := by
            exact tailZeroAvoidance_zeroBranch_eq_zero (hB := hB) hT
      _ = (2 / Real.pi) * Real.arcsin (Real.sqrt (((0 : NNReal) : ℝ) / (T : ℝ))) := by
            have hT_ne : (T : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hT)
            simp [Real.arcsin_zero]
  · by_cases hEq : t = T
    · subst hEq
      have hEvent :
          ((fun ω ↦ (lastZeroBefore B t ω : ℝ)) ⁻¹' Set.Iic t) = Set.univ := by
        rw [lastZeroBefore_preimage_Iic_eq_tailZeroAvoidance (B := B) (t := t) (T := t) le_rfl]
        ext ω
        simp
      -- Proof comment: at the full horizon `T`, the event is all of `Ω`, so its mass is `1`.
      calc
        μ.real ((fun ω ↦ (lastZeroBefore B t ω : ℝ)) ⁻¹' Set.Iic t) = μ.real Set.univ := by
              rw [hEvent]
        _ = 1 := by
              simp [Measure.real_def]
        _ = (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (t : ℝ))) := by
              have hT_ne : (t : ℝ) ≠ 0 := by
                exact_mod_cast (ne_of_gt hT)
              have hratio : (t : ℝ) / (t : ℝ) = 1 := by
                field_simp [hT_ne]
              rw [hratio]
              simp [Real.arcsin_one, Real.pi_ne_zero]
    · have ht_pos : 0 < t := lt_of_le_of_ne (by simp) (Ne.symm ht0)
      have htT : t < T := lt_of_le_of_ne ht hEq
      let W : NNReal → Ω → ℝ := fun u ω ↦ B (t + u) ω - B t ω
      have hW : IsBrownianMotion μ W := shiftedIncrement_isBrownianMotion hB t
      have hProd :
          μ.map (fun ω ↦ (B t ω, processPath W ω)) =
            (μ.map (B t)).prod (μ.map (processPath W)) := by
        -- Proof comment: the present Brownian value is independent of the whole shifted future
        -- increment path.
        simpa [W, processPath] using timeValue_shiftedIncrementProcess_map_eq_prod (hB := hB) t
      have hEndpoint :
          μ.real {ω | |W (T - t) ω| ≤ |B t ω|} =
            μ.real {ω | |B T ω - B t ω| ≤ |B t ω|} := by
        have hSet :
            {ω | |W (T - t) ω| ≤ |B t ω|} =
              {ω | |B T ω - B t ω| ≤ |B t ω|} := by
          ext ω
          have htime : t + (T - t) = T := by
            simpa [add_comm] using (tsub_add_cancel_of_le ht)
          simp [W, htime]
        rw [hSet]
      -- Proof comment: on the strict interior branch, the last-zero event passes through the
      -- shifted increment conditioning bridge and then through the Gaussian cone computation.
      calc
        μ.real ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic t) =
            μ.real {ω | ∀ s ∈ Set.Ioc t T, B s ω ≠ 0} := by
              rw [lastZeroBefore_preimage_Iic_eq_tailZeroAvoidance (B := B) ht]
        _ = μ.real
              {ω | ∀ u ∈ Set.Ioc 0 (T - t), B t ω + (B (t + u) ω - B t ω) ≠ 0} := by
              rw [tailZeroAvoidance_eq_shiftedIncrementAvoidance (B := B) ht]
        _ = μ.real {ω | |W (T - t) ω| ≤ |B t ω|} := by
              simpa [W] using
                (independentAnchorTailZeroAvoidance_real_eq_endpointComparison
                  (μ := μ) (A := B t) ((hB.stronglyMeasurable t).measurable)
                  (hW := hW) (δ := T - t) (hδ := tsub_pos_of_lt htT) hProd)
        _ = μ.real {ω | |B T ω - B t ω| ≤ |B t ω|} := hEndpoint
        _ = (((gaussianReal 0 t).prod (gaussianReal 0 (T - t))).real
              {p : ℝ × ℝ | |p.2| ≤ |p.1|}) := by
                exact absEndpointComparison_real_eq_prodGaussianConeMass (hB := hB) ht
        _ = (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
              exact prodGaussianConeMass_eq_arcsine ht_pos htT

/-- Theorem 21.20: Lévy's arcsine law identifies the distribution function of the last zero of a
Brownian path before time `T`. -/
theorem lastZeroBefore_real_preimage_Iic_eq_arcsineLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T t : NNReal} (hT : 0 < T) (ht : t ≤ T) :
    μ.real ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic t) =
      (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := by
  simpa using lastZeroBefore_eventProbability_eq_arcsine hB hT ht

end IsBrownianMotion

end ProbabilityTheory
