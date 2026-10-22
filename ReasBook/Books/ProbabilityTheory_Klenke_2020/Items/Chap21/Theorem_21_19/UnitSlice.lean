/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_14

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Helper for Theorem 21.19: the future part of the time-inverted path, recentered at time `1`,
is the Brownian motion that drives the unit-slice reflection package. -/
private def shiftedTimeInversion
    (B : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun u ω ↦ ProbabilityTheory.timeInversion B (1 + u) ω - ProbabilityTheory.timeInversion B 1 ω

/-- Helper for Theorem 21.19: a closed running-maximum event on `[0,1]` is exactly the
corresponding affine-boundary event for the time-inverted Brownian path. -/
private lemma closedUnitRunningMaximum_eq_timeInversionAffineEvent
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} (hb : 0 < b) :
    {ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, b ≤ B t ω} =
      {ω | ∃ u : NNReal,
        b ≤ ProbabilityTheory.timeInversion B (1 + u) ω - b * (u : ℝ)} := by
  ext ω
  constructor
  · rintro ⟨t, ht, hbt⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      have : b ≤ 0 := by simpa [ht0, hB.zero] using hbt
      exact (not_le_of_gt hb) this
    let u : NNReal := t⁻¹ - 1
    refine ⟨u, ?_⟩
    have h1le : (1 : NNReal) ≤ t⁻¹ := one_le_inv_of_le_one ht.2
    have hu : 1 + u = t⁻¹ := by
      dsimp [u]
      rw [add_comm]
      exact tsub_add_cancel_of_le h1le
    have hu_real : (u : ℝ) = (t⁻¹ : ℝ) - 1 := by
      dsimp [u]
      rw [NNReal.coe_sub h1le]
      norm_num
    -- Proof comment: substitute `u = t⁻¹ - 1` and rewrite the affine event as
    -- `b + t⁻¹ * (B t - b)`, which is at least `b` because `b ≤ B t`.
    rw [hu, ProbabilityTheory.timeInversion_apply]
    simp [inv_ne_zero ht0]
    rw [show (t⁻¹)⁻¹ = t by simpa [ht0] using inv_inv t, hu_real]
    have hnonneg : 0 ≤ (t⁻¹ : ℝ) * (B t ω - b) := by
      refine mul_nonneg ?_ (sub_nonneg.mpr hbt)
      positivity
    linarith
  · rintro ⟨u, hu⟩
    let t : NNReal := (1 + u)⁻¹
    refine ⟨t, ?_, ?_⟩
    have h1u_ne : (1 + u : NNReal) ≠ 0 := by positivity
    constructor
    · positivity
    · dsimp [t]
      exact inv_le_one_of_one_le (by simp)
    -- Proof comment: the affine event is exactly `((1 + u) : ℝ) * (B t - b) ≥ 0`, so dividing
    -- by the positive factor `1 + u` recovers the closed Brownian threshold `b ≤ B t`.
    have hrewrite :
        b ≤ ((1 + u : NNReal) : ℝ) * B t ω - b * (u : ℝ) := by
      simpa [ProbabilityTheory.timeInversion_apply, t, h1u_ne] using hu
    have hmul_nonneg : 0 ≤ ((1 + u : NNReal) : ℝ) * (B t ω - b) := by
      linarith
    have hsub_nonneg : 0 ≤ B t ω - b := by
      exact nonneg_of_mul_nonneg_left hmul_nonneg (by positivity : 0 < ((1 + u : NNReal) : ℝ))
    linarith

/-- Helper for Theorem 21.19: recentering the time-inverted Brownian path at the anchor time
`1` preserves the Brownian-motion structure. -/
private lemma shiftedTimeInversion_isBrownian
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (shiftedTimeInversion B) := by
  let X : NNReal → Ω → ℝ := ProbabilityTheory.timeInversion B
  have hX : IsBrownianMotion μ X := ProbabilityTheory.IsBrownianMotion.timeInversion hB
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the shifted process starts from `0` by subtracting the anchor value `X 1`.
    funext ω
    simp [shiftedTimeInversion, X]
  · -- Proof comment: increments of the shifted process are literal increments of `X` on the
    -- translated time mesh, so independence is inherited from `X`.
    intro n t ht
    have hTranslated :
        ∀ i j, i ≤ j → (fun i ↦ 1 + t i) i ≤ (fun i ↦ 1 + t i) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) 1
    simpa [shiftedTimeInversion, X, add_assoc] using
      hX.indepIncrements n (fun i ↦ 1 + t i) hTranslated
  · -- Proof comment: the deterministic shift by `1` does not change stationary increments.
    intro u s t
    simpa [shiftedTimeInversion, X, add_assoc, add_left_comm, add_comm] using
      hX.stationaryIncrements (1 + u) s t
  · intro t ht
    -- Proof comment: the recentered shifted marginal is the Brownian increment of `X` over
    -- `[1, 1 + t]`, hence a centered Gaussian with variance `t`.
    have hId :
        IdentDistrib
          (fun ω ↦ X (1 + t) ω - X 1 ω)
          (fun ω ↦ X t ω - X 0 ω)
          μ μ := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hX.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := 1)
    have hLaw0 : HasLaw (fun ω ↦ X t ω - X 0 ω) (gaussianReal 0 t) μ := by
      simpa [hX.zero] using hX.gaussian_marginal ht
    simpa [shiftedTimeInversion, X] using hId.symm.hasLaw hLaw0
  · -- Proof comment: translate the continuous `X`-paths by `1` and subtract the anchor value.
    filter_upwards [hX.continuous_paths] with ω hω
    have hshift : Continuous (fun t : NNReal ↦ X (1 + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [shiftedTimeInversion, X, HasAlmostSurelyContinuousPaths, processPath] using
      hshift.sub continuous_const

/-- Helper for Theorem 21.19: the closed affine event for the time-inverted Brownian path
splits almost surely into an immediate-anchor branch and the lower-anchor exact-hit branch for the
shifted future process. -/
private lemma closedUnitAffineEvent_ae_eq_anchorSplit
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b : ℝ} :
    {ω | ∃ u : NNReal,
      b ≤ ProbabilityTheory.timeInversion B (1 + u) ω - b * (u : ℝ)} =ᵐ[μ]
      ((({ω | b ≤ ProbabilityTheory.timeInversion B 1 ω} : Set Ω) ∪
        {ω | ProbabilityTheory.timeInversion B 1 ω < b ∧
          ∃ t : NNReal,
            shiftedTimeInversion B t ω - b * (t : ℝ) =
              b - ProbabilityTheory.timeInversion B 1 ω}) : Set Ω) := by
  let X : NNReal → Ω → ℝ := ProbabilityTheory.timeInversion B
  let Y : NNReal → Ω → ℝ := shiftedTimeInversion B
  have hY : IsBrownianMotion μ Y := by
    simpa [Y] using shiftedTimeInversion_isBrownian (hB := hB)
  filter_upwards [hY.continuous_paths] with ω hωcont
  have hcontDrift : Continuous (fun t : NNReal ↦ Y t ω - b * (t : ℝ)) := by
    -- Proof comment: the drifted future path is a continuous translate of the Brownian path.
    exact hωcont.sub (continuous_const.mul continuous_subtype_val)
  constructor
  · intro hω
    by_cases hAnchor : b ≤ X 1 ω
    · -- Proof comment: when the anchor already lies above `b`, the affine event holds at `u = 0`.
      exact Or.inl hAnchor
    · have hAnchor_lt : X 1 ω < b := lt_of_not_ge hAnchor
      rcases hω with ⟨u, hu⟩
      have hthreshold : b - X 1 ω ≤ Y u ω - b * (u : ℝ) := by
        -- Proof comment: subtract the anchor value from the affine inequality to isolate the
        -- shifted future process against the positive-slope boundary.
        dsimp [X, Y, shiftedTimeInversion] at hu ⊢
        linarith
      have hstart : Y 0 ω - b * ((0 : NNReal) : ℝ) < b - X 1 ω := by
        -- Proof comment: on the lower-anchor branch the drifted future path starts strictly below
        -- the target boundary level.
        simpa [X, Y, shiftedTimeInversion] using sub_pos.mpr hAnchor_lt
      have hlevel :
          b - X 1 ω ∈
            Set.Icc
              ((fun t : NNReal ↦ Y t ω - b * (t : ℝ)) 0)
              ((fun t : NNReal ↦ Y t ω - b * (t : ℝ)) u) := by
        exact ⟨le_of_lt hstart, hthreshold⟩
      obtain ⟨t, htIcc, ht_eq⟩ :=
        (intermediate_value_Icc (a := (0 : NNReal)) (b := u) (show (0 : NNReal) ≤ u by positivity)
          hcontDrift.continuousOn) hlevel
      -- Proof comment: the intermediate-value witness is already the exact lower-anchor hit.
      exact Or.inr ⟨hAnchor_lt, ⟨t, ht_eq⟩⟩
  · intro hω
    rcases hω with hAnchor | ⟨hAnchor_lt, t, ht_eq⟩
    · -- Proof comment: the anchor-above branch closes the affine event at `u = 0`.
      exact ⟨0, by simpa [X] using hAnchor⟩
    · refine ⟨t, ?_⟩
      -- Proof comment: add the anchor value back to the hitting-time equality to recover the
      -- original closed affine event.
      dsimp [X, Y, shiftedTimeInversion] at ht_eq ⊢
      linarith

/-- Helper for Theorem 21.19: on the unit interval, the hit-slice event is almost surely the
closed running-maximum event with the same terminal cutoff. -/
private lemma hitUpperBeforeOne_terminalBelow_event_ae_eq_runningMaxClosed
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y} =ᵐ[μ]
      ((({ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, b ≤ B t ω} : Set Ω) ∩
        {ω | B 1 ω ≤ y}) : Set Ω) := by
  filter_upwards [hB.continuous_paths] with ω hωcont
  have hcont : Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hωcont
  have hzero : B 0 ω = 0 := by
    simpa using congrFun hB.zero ω
  constructor
  · intro hω
    have hτ_le : brownianLevelHittingTime B b ω ≤ 1 := by
      simpa [brownianLevelHittingTime_eq_hittingAfter] using hω.1
    have hτ_ne : brownianLevelHittingTime B b ω ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hτ_le (by simp))
    have hhit :
        B (brownianLevelHittingTime B b ω).untopA ω = b := by
      -- Proof comment: continuity lets us recover the exact level at the first finite hit.
      simpa [stoppedValue] using
        brownianLevelHittingTime_stoppedValue_eq_level
          (B := B) (b := b) (ω := ω) hcont hτ_ne
    have hτ_le_one : (brownianLevelHittingTime B b ω).untopA ≤ 1 := by
      exact (WithTop.untopA_le_iff (x := brownianLevelHittingTime B b ω) (hx := hτ_ne)).1 hτ_le
    refine ⟨?_, hω.2⟩
    refine ⟨(brownianLevelHittingTime B b ω).untopA, ⟨by positivity, hτ_le_one⟩, ?_⟩
    linarith
  · rintro ⟨⟨t, htIcc, hbt⟩, hterm⟩
    have hlevel : b ∈ Set.Icc (B 0 ω) (B t ω) := by
      refine ⟨?_, hbt⟩
      simpa [hzero] using hb.le
    obtain ⟨s, hsIcc, hs_eq⟩ :=
      (intermediate_value_Icc (a := (0 : NNReal)) (b := t) htIcc.1 hcont.continuousOn) hlevel
    have hτ_le_s : brownianLevelHittingTime B b ω ≤ s := by
      exact brownianLevelHittingTime_le_of_eq (B := B) (b := b) (ω := ω) hs_eq
    have hτ_le_one : brownianLevelHittingTime B b ω ≤ 1 := by
      exact le_trans hτ_le_s (by exact_mod_cast hsIcc.2)
    refine ⟨?_, hterm⟩
    simpa [brownianLevelHittingTime_eq_hittingAfter] using hτ_le_one

/-- Helper for Theorem 21.19: after unit-time normalization, the positive-barrier hit slice is
almost surely the anchor-section event for the shifted time-inverted Brownian path. -/
private lemma unitHitUpperBeforeOne_terminalBelow_ae_eq_anchorSection
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) (hyb : y < b) :
    {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y} =ᵐ[μ]
      {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
        ∃ t : NNReal,
          shiftedTimeInversion B t ω - b * (t : ℝ) =
            b - ProbabilityTheory.timeInversion B 1 ω} := by
  let A : Set Ω := {ω | ∃ t ∈ Set.Icc (0 : NNReal) 1, b ≤ B t ω}
  let E : Set Ω := {ω | ∃ u : NNReal,
    b ≤ ProbabilityTheory.timeInversion B (1 + u) ω - b * (u : ℝ)}
  let C : Set Ω := {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y}
  let H : Set Ω := {ω | ProbabilityTheory.timeInversion B 1 ω < b ∧
    ∃ t : NNReal,
      shiftedTimeInversion B t ω - b * (t : ℝ) =
        b - ProbabilityTheory.timeInversion B 1 ω}
  have hHit :
      {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y} =ᵐ[μ]
        ((A ∩ {ω | B 1 ω ≤ y} : Set Ω)) :=
    hitUpperBeforeOne_terminalBelow_event_ae_eq_runningMaxClosed (hB := hB) (b := b) (y := y) hb
  have hAffine :
      (A ∩ {ω | B 1 ω ≤ y} : Set Ω) = (E ∩ C : Set Ω) := by
    ext ω
    constructor
    · rintro ⟨hA, hTerm⟩
      refine ⟨?_, ?_⟩
      · exact (congrArg (fun s : Set Ω => ω ∈ s)
          (closedUnitRunningMaximum_eq_timeInversionAffineEvent (hB := hB) (b := b) hb)).mp hA
      · simpa [C, ProbabilityTheory.timeInversion_apply] using hTerm
    · rintro ⟨hE, hTerm⟩
      refine ⟨?_, ?_⟩
      · exact (congrArg (fun s : Set Ω => ω ∈ s)
          (closedUnitRunningMaximum_eq_timeInversionAffineEvent (hB := hB) (b := b) hb)).mpr hE
      · simpa [C, ProbabilityTheory.timeInversion_apply] using hTerm
  have hSplit :
      (E ∩ C : Set Ω) =ᵐ[μ] (((({ω | b ≤ ProbabilityTheory.timeInversion B 1 ω} : Set Ω) ∪ H) ∩ C : Set Ω)) := by
    filter_upwards [closedUnitAffineEvent_ae_eq_anchorSplit (hB := hB) (b := b)] with ω hω
    constructor <;> intro h
    · exact ⟨hω.mp h.1, h.2⟩
    · exact ⟨hω.mpr h.1, h.2⟩
  have hFinal :
      (((({ω | b ≤ ProbabilityTheory.timeInversion B 1 ω} : Set Ω) ∪ H) ∩ C : Set Ω)) =
        {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
          ∃ t : NNReal,
            shiftedTimeInversion B t ω - b * (t : ℝ) =
              b - ProbabilityTheory.timeInversion B 1 ω} := by
    ext ω
    constructor
    · rintro ⟨hBranch, hTerm⟩
      rcases hBranch with hAnchor | hLower
      · exact False.elim ((not_lt_of_ge hAnchor) (lt_of_le_of_lt hTerm hyb))
      · exact ⟨hTerm, hLower.2⟩
    · rintro ⟨hTerm, hHitPath⟩
      refine ⟨Or.inr ?_, hTerm⟩
      exact ⟨lt_of_le_of_lt hTerm hyb, hHitPath⟩
  refine hHit.trans ?_
  refine (Filter.EventuallyEq.of_eq hAffine).trans ?_
  exact hSplit.trans (Filter.EventuallyEq.of_eq hFinal)

/-- Helper for Theorem 21.19: each rational future coordinate of the shifted time inversion has
zero covariance with the anchor `X 1`. -/
private lemma shiftedTimeInversion_covAnchor_eq_zero
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (q : ℚ≥0) :
    cov[fun ω ↦ shiftedTimeInversion B (q : NNReal) ω,
      fun ω ↦ ProbabilityTheory.timeInversion B 1 ω; μ] = 0 := by
  let X : NNReal → Ω → ℝ := ProbabilityTheory.timeInversion B
  have hX : IsBrownianMotion μ X := ProbabilityTheory.IsBrownianMotion.timeInversion hB
  let tq : NNReal := 1 + (q : NNReal)
  have htq_mem : ProbabilityTheory.MemLp (X tq) 2 μ :=
    ProbabilityTheory.brownianEval_memLp_two hX tq
  have h1_mem : ProbabilityTheory.MemLp (X 1) 2 μ :=
    ProbabilityTheory.brownianEval_memLp_two hX 1
  change cov[X tq - fun ω ↦ X 1 ω, X 1; μ] = 0
  rw [covariance_sub_left htq_mem h1_mem h1_mem]
  have hcov_tq : cov[X tq, X 1; μ] = 1 := by
    simpa [tq, inf_eq_right.mpr (by simp : (1 : NNReal) ≤ 1 + (q : NNReal))] using
      IsBrownianMotion.covariance_eq hX tq 1
  have hcov_one : cov[X 1, X 1; μ] = 1 := by
    simpa using IsBrownianMotion.covariance_eq hX 1 1
  rw [hcov_tq, hcov_one]
  ring

/-- Helper for Theorem 21.19: the full rational future path of the shifted time inversion is
independent of the anchor value at time `1`. -/
private lemma shiftedTimeInversionRatPath_indepAnchor
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IndepFun
      (fun ω q : ℚ≥0 ↦ shiftedTimeInversion B (q : NNReal) ω)
      (fun ω ↦ ProbabilityTheory.timeInversion B 1 ω)
      μ := by
  let X : ℚ≥0 → Ω → ℝ := fun q ω ↦ shiftedTimeInversion B (q : NNReal) ω
  let Y : Unit → Ω → ℝ := fun _ ω ↦ ProbabilityTheory.timeInversion B 1 ω
  have hTimeInv : IsBrownianMotion μ (ProbabilityTheory.timeInversion B) :=
    ProbabilityTheory.IsBrownianMotion.timeInversion hB
  have hShift : IsBrownianMotion μ (shiftedTimeInversion B) :=
    shiftedTimeInversion_isBrownian hB
  have hJoint :
      IsGaussianProcess (Sum.elim X Y) μ := by
    let hGaussian : IsGaussianProcess (ProbabilityTheory.timeInversion B) μ :=
      IsBrownianMotion.isGaussianProcess hTimeInv
    refine hGaussian.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl q =>
        let tq : NNReal := 1 + (q : NNReal)
        let I : Finset NNReal := {tq, 1}
        have htq : tq ∈ I := by simp [I]
        have h1 : (1 : NNReal) ∈ I := by simp [I]
        refine ⟨I, ?_, ?_⟩
        · refine
            { toFun := fun x ↦ x ⟨tq, htq⟩ - x ⟨1, h1⟩
              map_add' := by
                intro x y
                change x ⟨tq, htq⟩ + y ⟨tq, htq⟩ - (x ⟨1, h1⟩ + y ⟨1, h1⟩) =
                  (x ⟨tq, htq⟩ - x ⟨1, h1⟩) + (y ⟨tq, htq⟩ - y ⟨1, h1⟩)
                ring
              map_smul' := by
                intro c x
                change c * x ⟨tq, htq⟩ - c * x ⟨1, h1⟩ =
                  c * (x ⟨tq, htq⟩ - x ⟨1, h1⟩)
                ring
              cont := by
                fun_prop }
        · -- Proof comment: each rational future coordinate is the difference between the
          -- time-inverted Brownian path at `1 + q` and the anchor at `1`.
          intro ω
          simp [X, shiftedTimeInversion, tq]
    | inr u =>
        let I : Finset NNReal := {1}
        have h1 : (1 : NNReal) ∈ I := by simp [I]
        refine ⟨I, ?_, ?_⟩
        · refine
            { toFun := fun x ↦ x ⟨1, h1⟩
              map_add' := by
                intro x y
                rfl
              map_smul' := by
                intro c x
                rfl
              cont := by
                fun_prop }
        · -- Proof comment: the unit-indexed side of the joint family is just the scalar anchor.
          intro ω
          cases u
          simp [I, Y]
  have hIndepFamily : IndepFun (fun ω i ↦ X i ω) (fun ω u ↦ Y u ω) μ := by
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hJoint ?_ ?_ ?_
    · intro q
      exact (hShift.stronglyMeasurable (q : NNReal)).aemeasurable
    · intro u
      cases u
      exact (hTimeInv.stronglyMeasurable 1).aemeasurable
    · intro q u
      cases u
      simpa [X, Y] using shiftedTimeInversion_covAnchor_eq_zero (hB := hB) q
  -- Proof comment: evaluate the independent `Unit`-indexed family at `()` to recover `X 1`.
  simpa [X, Y] using
    hIndepFamily.comp measurable_id (by
      simpa using measurable_pi_apply ())

/-- Helper for Theorem 21.19: on continuous Brownian paths, hitting a positive-slope affine
boundary in finite time is equivalent to realizing the boundary at some deterministic time. -/
private lemma brownianAffineBoundaryFiniteHitEvent_ae_eq_exists_hit
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {a c : ℝ} :
    {ω | brownianAffineBoundaryHittingTime B a c ω < ⊤} =ᵐ[μ]
      {ω | ∃ t : NNReal, B t ω - a * (t : ℝ) = c} := by
  filter_upwards [hB.continuous_paths] with ω hωcont
  constructor
  · intro hω
    refine ⟨(brownianAffineBoundaryHittingTime B a c ω).untopA, ?_⟩
    -- Proof comment: on a continuous path, the owner API evaluates the drifted path at the
    -- finite hitting time itself.
    exact
      driftedBrownian_value_eq_boundary_at_hittingTime
        (B := B) (a := a) (b := c) hωcont hω
  · rintro ⟨t, ht_eq⟩
    have hle :
        brownianAffineBoundaryHittingTime B a c ω ≤ t := by
      -- Proof comment: any deterministic boundary hit witnesses finiteness of the affine hitting
      -- time and bounds it from above.
      simpa [brownianAffineBoundaryHittingTime_eq_hittingAfter, Set.mem_singleton_iff, ht_eq] using
        (hittingAfter_le_of_mem
          (u := fun s ω ↦ B s ω - a * (s : ℝ))
          (s := ({c} : Set ℝ))
          (n := (0 : NNReal))
          (ω := ω)
          (by simp)
          (by simpa [Set.mem_singleton_iff, ht_eq]))
    exact lt_of_le_of_lt hle (by simp)

/-- Helper for Theorem 21.19: the finite-hit probability for a positive-slope affine boundary is
`exp (-2 * c * a)`. -/
private lemma brownianAffineBoundary_hit_prob_eq_exp
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    μ {ω | ∃ t : NNReal, B t ω - a * (t : ℝ) = c} =
      ENNReal.ofReal (Real.exp (-2 * c * a)) := by
  have hHitEvent :
      μ {ω | ∃ t : NNReal, B t ω - a * (t : ℝ) = c} =
        μ {ω | brownianAffineBoundaryHittingTime B a c ω < ⊤} := by
    -- Proof comment: replace the existential event by the canonical affine-boundary owner event.
    rw [measure_congr (brownianAffineBoundaryFiniteHitEvent_ae_eq_exists_hit
      (hB := hB) (a := a) (c := c)).symm]
  calc
    μ {ω | ∃ t : NNReal, B t ω - a * (t : ℝ) = c}
        = μ {ω | brownianAffineBoundaryHittingTime B a c ω < ⊤} := hHitEvent
    _ = ENNReal.ofReal (min 1 (Real.exp (-2 * c * a))) := by
          simpa using
            brownianAffineBoundaryHittingTime_lt_top_prob
              (μ := μ) (B := B) hB (a := a) (b := c) hc
    _ = ENNReal.ofReal (Real.exp (-2 * c * a)) := by
          congr 1
          rw [min_eq_right]
          have hnonpos : -2 * c * a ≤ 0 := by
            nlinarith [ha, hc]
          simpa using Real.exp_le_one_iff.mpr hnonpos

/-- Helper for Theorem 21.19: a continuous path started below a level `c` hits `c` exactly when
bounded rational times approximate the level from below arbitrarily well. -/
private lemma affineLevelHit_iff_existsNatRatLowerApprox
    {f : NNReal → ℝ} {c : ℝ} (hcont : Continuous f) (h0 : f 0 < c) :
    (∃ t : NNReal, f t = c) ↔
      ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0, (q : ℝ) ≤ N ∧ c - (m + 1 : ℝ)⁻¹ ≤ f (q : NNReal) := by
  constructor
  · rintro ⟨t, ht⟩
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      have : c < c := by simpa [ht0, ht] using h0
      exact lt_irrefl _ this
    have ht_pos : 0 < (t : ℝ) := by
      exact_mod_cast NNReal.pos_iff_ne_zero.mpr ht_ne_zero
    refine ⟨Nat.ceil (t : ℝ), ?_⟩
    intro m
    have hεpos : 0 < (m + 1 : ℝ)⁻¹ := by positivity
    rcases (Metric.continuousAt_iff.mp hcont.continuousAt) _ hεpos with ⟨δ, hδpos, hδ⟩
    let η : ℝ := min (δ / 2) (t / 2)
    have hηpos : 0 < η := by
      dsimp [η]
      positivity
    obtain ⟨r, hr_left, hr_right⟩ : ∃ r : ℚ, t - η < r ∧ r < t := by
      exact exists_rat_btwn (by linarith)
    have hr_pos : 0 < (r : ℝ) := by
      nlinarith
    let q : ℚ≥0 := ⟨r, hr_pos.le⟩
    have hq_le_N : (q : ℝ) ≤ Nat.ceil (t : ℝ) := by
      exact le_trans hr_right.le (Nat.le_ceil (t : ℝ))
    have hq_close_real : |((q : NNReal) : ℝ) - t| < δ := by
      rw [abs_of_nonpos]
      · nlinarith
      · exact sub_nonpos.mpr hr_right.le
    have hq_close : dist (q : NNReal) t < δ := by
      simpa [NNReal.dist_eq] using hq_close_real
    have hq_value : |f (q : NNReal) - c| < (m + 1 : ℝ)⁻¹ := by
      simpa [Real.dist_eq, ht] using hδ hq_close
    refine ⟨q, hq_le_N, ?_⟩
    have hq_lower : -((m + 1 : ℝ)⁻¹) < f (q : NNReal) - c := (abs_lt.mp hq_value).1
    linarith
  · rintro ⟨N, hN⟩
    by_contra hhit
    have hlt : ∀ s ∈ Set.Icc (0 : NNReal) N, f s < c := by
      intro s hs
      by_contra hs_not_lt
      have hsc : c ≤ f s := le_of_not_gt hs_not_lt
      have hsgt : c < f s := by
        have hs_ne : f s ≠ c := by
          intro hs_eq
          exact hhit ⟨s, hs_eq⟩
        exact lt_of_le_of_ne hsc hs_ne.symm
      have hlevel : c ∈ Set.Icc (f 0) (f s) := ⟨le_of_lt h0, le_of_lt hsgt⟩
      obtain ⟨t, -, ht_eq⟩ :=
        (intermediate_value_Icc (a := (0 : NNReal)) (b := s) hs.1 hcont.continuousOn) hlevel
      exact hhit ⟨t, ht_eq⟩
    have hgap : ∀ s ∈ Set.Icc (0 : NNReal) N, 0 < c - f s := by
      intro s hs
      linarith [hlt s hs]
    obtain ⟨ε, hεpos, hεbound⟩ :=
      isCompact_Icc.exists_forall_le'
        (f := fun s : NNReal ↦ c - f s)
        (hf := (continuous_const.sub hcont).continuousOn)
        (a := (0 : ℝ))
        hgap
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hεpos
    rcases hN m with ⟨q, hqN, hqApprox⟩
    have hq_mem : (q : NNReal) ∈ Set.Icc (0 : NNReal) N := by
      constructor
      · positivity
      · exact_mod_cast hqN
    have hqGap : ε ≤ c - f (q : NNReal) := hεbound (q : NNReal) hq_mem
    linarith

/-- Helper for Theorem 21.19: the lower-anchor exact-hit branch is represented by a measurable
event on the anchor value and the rational future path. -/
private def lowerAnchorRatPathEvent (b : ℝ) : Set (ℝ × (ℚ≥0 → ℝ)) :=
  {p |
    p.1 < b ∧
      ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
        (q : ℝ) ≤ N ∧ b - p.1 - (m + 1 : ℝ)⁻¹ ≤ p.2 q - b * (q : ℝ)}

/-- Helper for Theorem 21.19: the rational lower-approximation normal form of the lower-anchor
branch is measurable on `ℝ × (ℚ≥0 → ℝ)`. -/
private lemma measurableSet_lowerAnchorRatPathEvent (b : ℝ) :
    MeasurableSet (lowerAnchorRatPathEvent b) := by
  let anchorEvent : Set (ℝ × (ℚ≥0 → ℝ)) := {p | p.1 < b}
  let sectionEvent : ℕ → ℕ → ℚ≥0 → Set (ℝ × (ℚ≥0 → ℝ)) := fun N m q ↦
    {p |
      (q : ℝ) ≤ N ∧ b - p.1 - (m + 1 : ℝ)⁻¹ ≤ p.2 q - b * (q : ℝ)}
  let lowerApproxEvent : ℕ → ℕ → Set (ℝ × (ℚ≥0 → ℝ)) := fun N m ↦
    ⋃ q : ℚ≥0, sectionEvent N m q
  let pathEvent : ℕ → Set (ℝ × (ℚ≥0 → ℝ)) := fun N ↦
    ⋂ m : ℕ, lowerApproxEvent N m
  have hAnchorMeas : MeasurableSet anchorEvent := by
    simpa [anchorEvent] using measurableSet_lt measurable_fst measurable_const
  have hSectionMeas : ∀ N m q, MeasurableSet (sectionEvent N m q) := by
    intro N m q
    by_cases hqN : (q : ℝ) ≤ N
    · have hLeft :
          Measurable (fun p : ℝ × (ℚ≥0 → ℝ) ↦ b - p.1 - (m + 1 : ℝ)⁻¹) := by
        fun_prop
      have hRight :
          Measurable (fun p : ℝ × (ℚ≥0 → ℝ) ↦ p.2 q - b * (q : ℝ)) := by
        fun_prop
      simpa [sectionEvent, hqN] using measurableSet_le hLeft hRight
    · simpa [sectionEvent, hqN] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set (ℝ × (ℚ≥0 → ℝ))))
  have hLowerApproxMeas : ∀ N m, MeasurableSet (lowerApproxEvent N m) := by
    intro N m
    exact MeasurableSet.iUnion fun q ↦ hSectionMeas N m q
  have hPathMeas : ∀ N, MeasurableSet (pathEvent N) := by
    intro N
    exact MeasurableSet.iInter fun m ↦ hLowerApproxMeas N m
  -- Proof comment: after separating the anchor coordinate, the remaining quantifiers become
  -- countable `iUnion/iInter` over rational-time inequalities.
  simpa [lowerAnchorRatPathEvent, anchorEvent, sectionEvent, lowerApproxEvent, pathEvent,
    Set.setOf_forall, Set.setOf_exists] using
    hAnchorMeas.inter (MeasurableSet.iUnion hPathMeas)

/-- Helper for Theorem 21.19: the lower-anchor exact-hit branch is almost surely the preimage of
the measurable rational-path event under the anchor/future-path pair map. -/
private lemma lowerAnchorBranch_ae_eq_ratPathPreimage
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} :
    {ω | ProbabilityTheory.timeInversion B 1 ω < b ∧
      ∃ t : NNReal,
        shiftedTimeInversion B t ω - b * (t : ℝ) =
          b - ProbabilityTheory.timeInversion B 1 ω} =ᵐ[μ]
      ((fun ω ↦
          (ProbabilityTheory.timeInversion B 1 ω,
            fun q : ℚ≥0 ↦ shiftedTimeInversion B (q : NNReal) ω)) ⁻¹'
        lowerAnchorRatPathEvent b) := by
  let X : NNReal → Ω → ℝ := ProbabilityTheory.timeInversion B
  let Y : NNReal → Ω → ℝ := shiftedTimeInversion B
  have hY : IsBrownianMotion μ Y := by
    simpa [Y] using shiftedTimeInversion_isBrownian (hB := hB)
  filter_upwards [hY.continuous_paths] with ω hωcont
  have hcontDrift : Continuous (fun t : NNReal ↦ Y t ω - b * (t : ℝ)) := by
    exact hωcont.sub (continuous_const.mul continuous_subtype_val)
  constructor
  · rintro ⟨hxb, t, ht⟩
    have h0 :
        (fun s : NNReal ↦ Y s ω - b * (s : ℝ)) 0 < b - X 1 ω := by
      simpa [X, Y, shiftedTimeInversion] using sub_pos.mpr hxb
    have hApprox :
        ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
          (q : ℝ) ≤ N ∧
            b - X 1 ω - (m + 1 : ℝ)⁻¹ ≤ Y (q : NNReal) ω - b * (q : ℝ) := by
      simpa [Y] using
        (affineLevelHit_iff_existsNatRatLowerApprox
          (f := fun s : NNReal ↦ Y s ω - b * (s : ℝ))
          (c := b - X 1 ω) hcontDrift h0).mp ⟨t, ht⟩
    simpa [X, Y, lowerAnchorRatPathEvent] using ⟨hxb, hApprox⟩
  · intro hω
    have hx :
        X 1 ω < b ∧
          ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
            (q : ℝ) ≤ N ∧
              b - X 1 ω - (m + 1 : ℝ)⁻¹ ≤ Y (q : NNReal) ω - b * (q : ℝ) := by
      simpa [X, Y, lowerAnchorRatPathEvent] using hω
    rcases hx with ⟨hxb, hApprox⟩
    have h0 :
        (fun s : NNReal ↦ Y s ω - b * (s : ℝ)) 0 < b - X 1 ω := by
      simpa [X, Y, shiftedTimeInversion] using sub_pos.mpr hxb
    refine ⟨hxb, ?_⟩
    simpa [Y] using
      (affineLevelHit_iff_existsNatRatLowerApprox
        (f := fun s : NNReal ↦ Y s ω - b * (s : ℝ))
        (c := b - X 1 ω) hcontDrift h0).mpr hApprox

/-- Helper for Theorem 21.19: fixing the anchor coordinate `x < b` rewrites the lower-anchor
section back to the affine-boundary hit event for the shifted future process. -/
private lemma lowerAnchorSectionPreimage_ae_eq_hitEvent
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b x : ℝ} (hx : x < b) :
    ((fun ω q : ℚ≥0 ↦ shiftedTimeInversion B (q : NNReal) ω) ⁻¹'
      (Prod.mk x ⁻¹' lowerAnchorRatPathEvent b)) =ᵐ[μ]
      {ω | ∃ t : NNReal, shiftedTimeInversion B t ω - b * (t : ℝ) = b - x} := by
  let Y : NNReal → Ω → ℝ := shiftedTimeInversion B
  have hY : IsBrownianMotion μ Y := by
    simpa [Y] using shiftedTimeInversion_isBrownian (hB := hB)
  filter_upwards [hY.continuous_paths] with ω hωcont
  have hcontDrift : Continuous (fun t : NNReal ↦ Y t ω - b * (t : ℝ)) := by
    -- Proof comment: fixing the anchor leaves only the continuous drifted future path.
    exact hωcont.sub (continuous_const.mul continuous_subtype_val)
  have h0 :
      (fun s : NNReal ↦ Y s ω - b * (s : ℝ)) 0 < b - x := by
    -- Proof comment: at time `0` the shifted future path is `0`, so the anchor gap is `b - x`.
    simpa [Y, shiftedTimeInversion] using sub_pos.mpr hx
  constructor
  · intro hω
    have hApprox :
        ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
          (q : ℝ) ≤ N ∧ b - x - (m + 1 : ℝ)⁻¹ ≤ Y (q : NNReal) ω - b * (q : ℝ) := by
      simpa [Y, lowerAnchorRatPathEvent, hx] using hω
    -- Proof comment: the rational lower approximations close exactly the affine hit because the
    -- drifted path is continuous and starts below the target level.
    simpa [Y] using
      (affineLevelHit_iff_existsNatRatLowerApprox
        (f := fun s : NNReal ↦ Y s ω - b * (s : ℝ))
        (c := b - x) hcontDrift h0).mpr hApprox
  · intro hω
    have hApprox :
        ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
          (q : ℝ) ≤ N ∧ b - x - (m + 1 : ℝ)⁻¹ ≤ Y (q : NNReal) ω - b * (q : ℝ) := by
      -- Proof comment: an exact hit yields the same rational lower-approximation normal form.
      simpa [Y] using
        (affineLevelHit_iff_existsNatRatLowerApprox
          (f := fun s : NNReal ↦ Y s ω - b * (s : ℝ))
          (c := b - x) hcontDrift h0).mp hω
    simpa [Y, lowerAnchorRatPathEvent, hx] using hApprox

/-- Helper for Theorem 21.19: each fixed-anchor section of the measurable rational-path event
has mass `exp (-2 * b * (b - x))` when `x < b`, and is empty otherwise. -/
private lemma lowerAnchorSectionMeasure_eq_exp
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b x : ℝ} (hb : 0 < b) :
    (μ.map (fun ω q : ℚ≥0 ↦ shiftedTimeInversion B (q : NNReal) ω))
      (Prod.mk x ⁻¹' lowerAnchorRatPathEvent b) =
        if x < b then ENNReal.ofReal (Real.exp (-2 * b * (b - x))) else 0 := by
  let R : Ω → (ℚ≥0 → ℝ) := fun ω q ↦ shiftedTimeInversion B (q : NNReal) ω
  let Y : NNReal → Ω → ℝ := shiftedTimeInversion B
  have hY : IsBrownianMotion μ Y := by
    simpa [Y] using shiftedTimeInversion_isBrownian (hB := hB)
  have hRMeas : Measurable R := by
    -- Proof comment: the rational future-path map is measurable coordinatewise.
    refine measurable_pi_lambda _ fun q ↦ ?_
    simpa [R, Y] using (hY.stronglyMeasurable (q : NNReal)).measurable
  have hSectionMeas : MeasurableSet (Prod.mk x ⁻¹' lowerAnchorRatPathEvent b) :=
    measurable_prodMk_left (measurableSet_lowerAnchorRatPathEvent b)
  by_cases hx : x < b
  · have hbx : 0 < b - x := by linarith
    rw [Measure.map_apply hRMeas hSectionMeas]
    -- Proof comment: rewrite the fixed-anchor section back to the affine-hit event, then invoke
    -- the affine-boundary probability formula.
    rw [measure_congr
      (lowerAnchorSectionPreimage_ae_eq_hitEvent (hB := hB) (b := b) (x := x) hx)]
    simpa [R, Y] using
      brownianAffineBoundary_hit_prob_eq_exp (hB := hY) (a := b) (c := b - x) hb hbx
  · rw [Measure.map_apply hRMeas hSectionMeas]
    have hempty : Prod.mk x ⁻¹' lowerAnchorRatPathEvent b = ∅ := by
      ext f
      simp [lowerAnchorRatPathEvent, hx]
    simp [hempty, hx]

/-- Helper for Theorem 21.19: intersecting the lower-anchor branch with the cutoff
`timeInversion B 1 ≤ y` turns its probability into a truncated Gaussian weighted integral. -/
private lemma lowerAnchorBranchBelow_measure_eq_anchorIntegral
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) (hyb : y < b) :
    μ {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
      ∃ t : NNReal,
        shiftedTimeInversion B t ω - b * (t : ℝ) =
          b - ProbabilityTheory.timeInversion B 1 ω} =
      ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x)))
        ∂(μ.map fun ω ↦ ProbabilityTheory.timeInversion B 1 ω) := by
  let X : Ω → ℝ := fun ω ↦ ProbabilityTheory.timeInversion B 1 ω
  let R : Ω → (ℚ≥0 → ℝ) := fun ω q ↦ shiftedTimeInversion B (q : NNReal) ω
  let S : Set (ℝ × (ℚ≥0 → ℝ)) := lowerAnchorRatPathEvent b ∩ (Set.Iic y ×ˢ Set.univ)
  have hTimeInv : IsBrownianMotion μ (ProbabilityTheory.timeInversion B) :=
    ProbabilityTheory.IsBrownianMotion.timeInversion hB
  have hXMeas : Measurable X := by
    simpa [X] using (hTimeInv.stronglyMeasurable 1).measurable
  have hRMeas : Measurable R := by
    have hShift : IsBrownianMotion μ (shiftedTimeInversion B) := shiftedTimeInversion_isBrownian hB
    refine measurable_pi_lambda _ fun q ↦ ?_
    simpa [R] using (hShift.stronglyMeasurable (q : NNReal)).measurable
  have hPairMeas : Measurable (fun ω ↦ (X ω, R ω)) := hXMeas.prodMk hRMeas
  have hProd :
      μ.map (fun ω ↦ (X ω, R ω)) = (μ.map X).prod (μ.map R) := by
    -- Proof comment: the anchor and the whole rational future path are independent, so their
    -- joint law factors as the product of the marginals.
    simpa [X, R] using
      (indepFun_iff_map_prod_eq_prod_map_map hXMeas.aemeasurable hRMeas.aemeasurable).mp
        (shiftedTimeInversionRatPath_indepAnchor (hB := hB)).symm
  have hEventAe :
      {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
        ∃ t : NNReal,
          shiftedTimeInversion B t ω - b * (t : ℝ) =
            b - ProbabilityTheory.timeInversion B 1 ω} =ᵐ[μ]
        ((fun ω ↦ (X ω, R ω)) ⁻¹' S) := by
    have hLeft :
        {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
          ∃ t : NNReal,
            shiftedTimeInversion B t ω - b * (t : ℝ) =
              b - ProbabilityTheory.timeInversion B 1 ω} =
          ({ω | ProbabilityTheory.timeInversion B 1 ω < b ∧
            ∃ t : NNReal,
              shiftedTimeInversion B t ω - b * (t : ℝ) =
                b - ProbabilityTheory.timeInversion B 1 ω} ∩
            {ω | X ω ≤ y}) := by
      ext ω
      constructor
      · intro hω
        refine ⟨?_, ?_⟩
        · exact ⟨lt_of_le_of_lt hω.1 hyb, hω.2⟩
        · simpa [X] using hω.1
      · intro hω
        exact ⟨by simpa [X] using hω.2, hω.1.2⟩
    have hCutEq :
        {ω | X ω ≤ y} =
          ((fun ω ↦ (X ω, R ω)) ⁻¹' (Set.Iic y ×ˢ Set.univ)) := by
      ext ω
      simp [X]
    refine (Filter.EventuallyEq.of_eq hLeft).trans ?_
    refine (ae_eq_set_inter
      (lowerAnchorBranch_ae_eq_ratPathPreimage (hB := hB) (b := b))
      (Filter.EventuallyEq.of_eq hCutEq)).trans ?_
    exact Filter.EventuallyEq.of_eq <| by
      ext ω
      simp [S]
  calc
    μ {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
        ∃ t : NNReal,
          shiftedTimeInversion B t ω - b * (t : ℝ) =
            b - ProbabilityTheory.timeInversion B 1 ω}
        = μ (((fun ω ↦ (X ω, R ω)) ⁻¹' S)) := by
            rw [measure_congr hEventAe]
    _ = (μ.map (fun ω ↦ (X ω, R ω))) S := by
          rw [Measure.map_apply hPairMeas (measurableSet_lowerAnchorRatPathEvent b).inter
            (measurableSet_Iic.prod MeasurableSet.univ)]
    _ = ((μ.map X).prod (μ.map R)) S := by rw [hProd]
    _ = ∫⁻ x, (μ.map R) (Prod.mk x ⁻¹' S) ∂(μ.map X) := by
          rw [Measure.prod_apply ((measurableSet_lowerAnchorRatPathEvent b).inter
            (measurableSet_Iic.prod MeasurableSet.univ))]
    _ = ∫⁻ x, if x ≤ y then ENNReal.ofReal (Real.exp (-2 * b * (b - x))) else 0 ∂(μ.map X) := by
          refine lintegral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x ↦ by
            by_cases hxy : x ≤ y
            · have hxb : x < b := lt_of_le_of_lt hxy hyb
              have hsection :
                  Prod.mk x ⁻¹' S = Prod.mk x ⁻¹' lowerAnchorRatPathEvent b := by
                ext f
                simp [S, hxy]
              rw [hsection, lowerAnchorSectionMeasure_eq_exp (hB := hB) (b := b) (x := x) hb]
              simp [hxb, hxy]
            · have hsection :
                  Prod.mk x ⁻¹' S = ∅ := by
                ext f
                simp [S, hxy]
              simp [hsection, hxy]
    _ = ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x))) ∂(μ.map X) := by
          rw [← lintegral_indicator measurableSet_Iic]
          congr with x
          by_cases hxy : x ≤ y <;> simp [Set.indicator, hxy]

/-- Helper for Theorem 21.19: the closed terminal Brownian tail at time `1` is the
corresponding closed tail of the standard Gaussian law. -/
private lemma brownianTerminalClosedTail_eq_standardGaussianClosedTail
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} :
    μ {ω | b ≤ B 1 ω} = (gaussianReal 0 1) (Set.Ici b) := by
  let hLaw : HasLaw (B 1) (gaussianReal 0 1) μ := hB.gaussian_marginal (by positivity)
  have hmap_eq := congrArg (fun ν : Measure ℝ => ν (Set.Ici b)) hLaw.map_eq
  simpa [Measure.map_apply ((hB.stronglyMeasurable 1).measurable) measurableSet_Ici] using hmap_eq

/-- Helper for Theorem 21.19: the truncated Gaussian weighted integral is exactly the reflected
closed tail of the standard Gaussian law. -/
private lemma gaussianWeightedLowerSection_eq_reflectedClosedTail
    {b y : ℝ} (hyb : y < b) :
    ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x))) ∂(gaussianReal 0 1) =
      (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
  have hpdf :
      ∀ x : ℝ,
        ENNReal.ofReal (Real.exp (-2 * b * (b - x))) * gaussianPDF 0 1 x =
          gaussianPDF (2 * b) 1 x := by
    intro x
    -- Proof comment: completing the square identifies the weighted density with `N(2b, 1)`.
    rw [gaussianPDF, gaussianPDF]
    congr 1
    rw [gaussianPDFReal_def, gaussianPDFReal_def]
    ring_nf
    congr 2
    ring
  have hleft :
      ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x))) ∂(gaussianReal 0 1) =
        (gaussianReal (2 * b) 1) (Set.Iic y) := by
    -- Proof comment: absorb the exponential weight into the shifted Gaussian density.
    rw [gaussianReal_of_var_ne_zero (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero]
    rw [MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀]
    · simp_rw [hpdf]
      exact (gaussianReal_apply (μ := 2 * b) (v := (1 : ℝ≥0)) one_ne_zero (Set.Iic y)).symm
    · fun_prop
    · fun_prop
    · exact measurableSet_Iic
  have hmap :
      (gaussianReal 0 1).map (fun x : ℝ ↦ 2 * b - x) = gaussianReal (2 * b) 1 := by
    -- Proof comment: reflecting `N(0, 1)` across the midpoint `b` yields `N(2b, 1)`.
    simpa using gaussianReal_map_const_sub (μ := 0) (v := (1 : ℝ≥0)) (y := 2 * b)
  have hreflect :
      (gaussianReal (2 * b) 1) (Set.Iic y) = (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
    rw [← hmap]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x
    simp [sub_le_iff_le_add]
  rw [hleft, hreflect]

/-- Helper for Theorem 21.19: the unit-time upper-hit slice with terminal cutoff `y < b`
has the reflected terminal tail as its probability. -/
theorem unitHitUpperBeforeOne_terminalBelow_measure_eq_reflectedTail_core
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {b y : ℝ} (hb : 0 < b) (hyb : y < b) :
    μ {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y} =
      μ {ω | 2 * b - y ≤ B 1 ω} := by
  let X : NNReal → Ω → ℝ := ProbabilityTheory.timeInversion B
  have hTimeInv : IsBrownianMotion μ X := ProbabilityTheory.IsBrownianMotion.timeInversion hB
  have hAnchorMap :
      μ.map (fun ω ↦ X 1 ω) = gaussianReal 0 1 := by
    simpa [X] using (hTimeInv.gaussian_marginal (by positivity : 0 < (1 : NNReal))).map_eq
  calc
    μ {ω | hittingAfter B ({b} : Set ℝ) 0 ω ≤ 1 ∧ B 1 ω ≤ y}
        =
          μ {ω | ProbabilityTheory.timeInversion B 1 ω ≤ y ∧
            ∃ t : NNReal,
              shiftedTimeInversion B t ω - b * (t : ℝ) =
                b - ProbabilityTheory.timeInversion B 1 ω} := by
            rw [measure_congr
              (unitHitUpperBeforeOne_terminalBelow_ae_eq_anchorSection
                (hB := hB) (b := b) (y := y) hb hyb)]
    _ =
        ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x)))
          ∂(μ.map fun ω ↦ X 1 ω) := by
            simpa [X] using
              lowerAnchorBranchBelow_measure_eq_anchorIntegral
                (hB := hB) (b := b) (y := y) hb hyb
    _ =
        ∫⁻ x in Set.Iic y, ENNReal.ofReal (Real.exp (-2 * b * (b - x)))
          ∂(gaussianReal 0 1) := by
            rw [hAnchorMap]
    _ = (gaussianReal 0 1) (Set.Ici (2 * b - y)) := by
          exact gaussianWeightedLowerSection_eq_reflectedClosedTail (b := b) (y := y) hyb
    _ = μ {ω | 2 * b - y ≤ B 1 ω} := by
          rw [← brownianTerminalClosedTail_eq_standardGaussianClosedTail
            (hB := hB) (b := 2 * b - y)]

end ProbabilityTheory
