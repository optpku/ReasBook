/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Pointwise Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

section ContinuousVersionCore

variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.2.4: the Brownian discontinuity set records the paths that fail to be
continuous. -/
def brownianDiscontinuitySet (_hB : IsBrownianMotion μ B) : Set Ω :=
  {ω | ¬ Continuous (fun t : NNReal ↦ B t ω)}

/-- Helper for Exercise 21.2.4: the Brownian discontinuity set is null because Brownian paths are
almost surely continuous. -/
lemma brownianDiscontinuitySet_null (hB : IsBrownianMotion μ B) :
    μ (brownianDiscontinuitySet (μ := μ) (B := B) hB) = 0 := by
  -- Proof comment: almost-sure continuity is exactly the statement that the bad set has measure
  -- zero.
  have hcont_ae : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB.continuous_paths
  simpa [brownianDiscontinuitySet] using (ae_iff.mp hcont_ae)

/-- Helper for Exercise 21.2.4: choose a measurable null superset of the Brownian discontinuity
set so the continuous patch stays measurable. -/
lemma brownianContinuousVersionExceptionSet_exists (hB : IsBrownianMotion μ B) :
    ∃ N : Set Ω,
      brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆ N ∧ MeasurableSet N ∧ μ N = 0 := by
  -- Proof comment: enlarge the null bad set to a measurable null set once and for all.
  exact exists_measurable_superset_of_null
    (brownianDiscontinuitySet_null (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.4: the measurable exceptional set used to patch Brownian paths into
an everywhere-continuous version. -/
def brownianContinuousVersionExceptionSet (hB : IsBrownianMotion μ B) : Set Ω :=
  Classical.choose (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.4: the actual discontinuity set sits inside the chosen measurable
exceptional set. -/
lemma brownianDiscontinuitySet_subset_exceptionSet (hB : IsBrownianMotion μ B) :
    brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆
      brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).1

/-- Helper for Exercise 21.2.4: the chosen Brownian exceptional set is measurable. -/
lemma brownianContinuousVersionExceptionSet_measurable (hB : IsBrownianMotion μ B) :
    MeasurableSet (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.1

/-- Helper for Exercise 21.2.4: the chosen Brownian exceptional set is null. -/
lemma brownianContinuousVersionExceptionSet_null (hB : IsBrownianMotion μ B) :
    μ (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) = 0 :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.2

/-- Helper for Exercise 21.2.4: patch Brownian motion by setting it equal to `0` on the chosen
null exceptional set. -/
def brownianContinuousVersion (hB : IsBrownianMotion μ B) : NNReal → Ω → ℝ :=
  fun t ω ↦
    if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then 0 else B t ω

/-- Helper for Exercise 21.2.4: the continuous Brownian modification still starts at `0`. -/
lemma brownianContinuousVersion_zero (hB : IsBrownianMotion μ B) (ω : Ω) :
    brownianContinuousVersion (μ := μ) (B := B) hB 0 ω = 0 := by
  classical
  by_cases hω : ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
  · simp [brownianContinuousVersion, hω]
  · simp [brownianContinuousVersion, hω, congrFun hB.zero ω]

/-- Helper for Exercise 21.2.4: each time slice of the patched Brownian motion is measurable. -/
lemma brownianContinuousVersion_measurable (hB : IsBrownianMotion μ B) :
    ∀ t, Measurable (brownianContinuousVersion (μ := μ) (B := B) hB t) := by
  -- Proof comment: the patch is a measurable `if` with the original Brownian slice off a
  -- measurable null set.
  intro t
  change Measurable
    (fun ω ↦
      if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then (0 : ℝ) else B t ω)
  exact Measurable.ite
    (brownianContinuousVersionExceptionSet_measurable (μ := μ) (B := B) hB)
    measurable_const ((hB.stronglyMeasurable t).measurable)

/-- Helper for Exercise 21.2.4: every sample path of the patched Brownian motion is continuous.
-/
lemma brownianContinuousVersion_continuous (hB : IsBrownianMotion μ B) :
    ∀ ω, Continuous (fun t ↦ brownianContinuousVersion (μ := μ) (B := B) hB t ω) := by
  -- Proof comment: on the exceptional set the patch is the constant zero path; off it, the path
  -- is the original Brownian path, which is continuous by construction of the exceptional set.
  classical
  intro ω
  by_cases hω : ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
  · simpa [brownianContinuousVersion, hω] using
      (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · have hcont : Continuous (fun t : NNReal ↦ B t ω) := by
      by_contra hnot
      exact hω <|
        brownianDiscontinuitySet_subset_exceptionSet (μ := μ) (B := B) hB
          (by simpa [brownianDiscontinuitySet] using hnot)
    simpa [brownianContinuousVersion, hω] using hcont

/-- Helper for Exercise 21.2.4: outside the exceptional set, the patched process agrees with the
original Brownian motion at every time. -/
lemma brownianContinuousVersion_ae_eq (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      brownianContinuousVersion (μ := μ) (B := B) hB t ω = B t ω := by
  -- Proof comment: the patch only changes paths on the measurable null exceptional set.
  have hN_ae :
      ∀ᵐ ω ∂μ,
        ω ∉ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB := by
    exact compl_mem_ae_iff.mpr
      (brownianContinuousVersionExceptionSet_null (μ := μ) (B := B) hB)
  filter_upwards [hN_ae] with ω hω t
  change
    (if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then (0 : ℝ) else B t ω) =
      B t ω
  simp [hω]

/-- Helper for Exercise 21.2.4: the patched process is a modification of the original Brownian
motion. -/
lemma brownianContinuousVersion_areModifications (hB : IsBrownianMotion μ B) :
    AreModifications μ B (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: fixed-time almost-everywhere equality is exactly the modification relation.
  intro t
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  simpa using (hω t).symm

end ContinuousVersionCore

section Helpers

variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.2.4: a centered Gaussian interval mass is bounded by the interval
length times the Gaussian peak height. -/
lemma gaussianIntervalMeasure_le_peak_mul_length
    {a b : ℝ} (hab : a ≤ b) {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal 0 v).real (Set.Icc a b) ≤
      (b - a) * (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  have hmeasure :
      (gaussianReal 0 v).real (Set.Icc a b) =
        ∫ y in Set.Icc a b, gaussianPDFReal 0 v y := by
    -- Proof comment: rewrite the Gaussian interval mass through its density.
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.gaussianReal_apply_eq_integral (μ := 0)
      (v := v) hv (Set.Icc a b)]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦ gaussianPDFReal_nonneg 0 v y)]
  have hbound :
      ∫ y in Set.Icc a b, gaussianPDFReal 0 v y ≤
        ∫ y in Set.Icc a b, (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    -- Proof comment: dominate the density on the whole interval by its global peak value.
    have hIcc_ne_top : volume (Set.Icc a b) ≠ ⊤ := by
      rw [Real.volume_Icc]
      simp
    refine MeasureTheory.setIntegral_mono_on
      (ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn
      (MeasureTheory.integrableOn_const
        (s := Set.Icc a b)
        (μ := volume)
        (C := (Real.sqrt (2 * Real.pi * v))⁻¹)
        (hs := hIcc_ne_top))
      measurableSet_Icc ?_
    intro y hy
    simpa using gaussianPDFReal_le_peak (hε := hv) y 0
  calc
    (gaussianReal 0 v).real (Set.Icc a b)
        = ∫ y in Set.Icc a b, gaussianPDFReal 0 v y := hmeasure
    _ ≤ ∫ y in Set.Icc a b, (Real.sqrt (2 * Real.pi * v))⁻¹ := hbound
    _ = (b - a) * (Real.sqrt (2 * Real.pi * v))⁻¹ := by
          -- Proof comment: integrating a constant over `[a,b]` produces its length factor.
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hab]
          rw [smul_eq_mul]

/-- Helper for Exercise 21.2.4: on a continuous path started at `0`, an infinite two-sided
boundary clock forces every deterministic time value to stay inside `(a,b)`. -/
lemma mem_Ioo_of_twoSidedBoundaryHittingTime_eq_top
    {a b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω)
    (hzero : B 0 ω = 0) (ha : a < 0) (hb : 0 < b)
    (hτ : hittingAfter B ({a, b} : Set ℝ) 0 ω = ⊤) (t : NNReal) :
    B t ω ∈ Set.Ioo a b := by
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hle : B t ω ≤ a := le_of_not_gt hnot
    have htarget : -a ∈ Set.Icc (-B 0 ω) (-B t ω) := by
      refine ⟨?_, ?_⟩
      · simpa [hzero] using (neg_pos.mpr ha).le
      · linarith
    obtain ⟨s, hs_mem, hs_eq⟩ :=
      (intermediate_value_Icc
        (a := (0 : NNReal))
        (b := t)
        (by simp)
        hcont.neg.continuousOn) htarget
    have hs_hit : B s ω = a := by
      linarith
    have havoid :=
      (hittingAfter_eq_top_iff
        (u := B)
        (s := ({a, b} : Set ℝ))
        (n := (0 : NNReal))
        (ω := ω)).1 hτ
    exact havoid s hs_mem.1 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_hit])
  · by_contra hnot
    have hle : b ≤ B t ω := le_of_not_gt hnot
    have htarget : b ∈ Set.Icc (B 0 ω) (B t ω) := by
      refine ⟨?_, hle⟩
      simpa [hzero] using hb.le
    obtain ⟨s, hs_mem, hs_eq⟩ :=
      (intermediate_value_Icc
        (a := (0 : NNReal))
        (b := t)
        (by simp)
        hcont.continuousOn) htarget
    have havoid :=
      (hittingAfter_eq_top_iff
        (u := B)
        (s := ({a, b} : Set ℝ))
        (n := (0 : NNReal))
        (ω := ω)).1 hτ
    exact havoid s hs_mem.1 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_eq])

end Helpers

section OptionalStoppingHelpers

variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.2.4: Brownian motion is a martingale in its natural filtration. -/
lemma brownianMartingale_natural
    (hB : IsBrownianMotion μ B) :
    Martingale B (Filtration.natural B hB.stronglyMeasurable) μ := by
  -- Proof comment: split `B_t` into `B_s` plus the centered future increment and kill the
  -- increment by independence from the natural filtration at time `s`.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ℱB := Filtration.natural B hB.stronglyMeasurable
  have hB_adapted : StronglyAdapted ℱB B :=
    Filtration.stronglyAdapted_natural (u := B) hB.stronglyMeasurable
  refine ⟨hB_adapted, ?_⟩
  intro s t hst
  have hInc_meas : Measurable (fun ω ↦ B t ω - B s ω) := by
    exact (hB.stronglyMeasurable t).measurable.sub (hB.stronglyMeasurable s).measurable
  have hInc_stronglyMeas :
      StronglyMeasurable[
        MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ)]
        (fun ω ↦ B t ω - B s ω) :=
    (comap_measurable (fun ω ↦ B t ω - B s ω)).stronglyMeasurable
  have hInc_indep :
      Indep
        (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ))
        (ℱB s)
        μ :=
    brownianIncrement_indep_naturalFiltration hB hst
  have hInc_mean_zero : ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
    simpa using (brownianIncrement_hasLaw hB hst).integral_eq
  have hBs_int : Integrable (B s) μ :=
    (brownianEval_memLp_two hB s).integrable (by norm_num)
  have hInc_int : Integrable (fun ω ↦ B t ω - B s ω) μ :=
    (brownianIncrement_memLp_two hB hst).integrable (by norm_num)
  have hSplit : (fun ω ↦ B t ω) = fun ω ↦ B s ω + (B t ω - B s ω) := by
    funext ω
    ring
  have hInc_condExp_zero :
      μ[(fun ω ↦ B t ω - B s ω) | ℱB s] =ᵐ[μ] 0 := by
    refine
      (MeasureTheory.condExp_indep_eq
        hInc_meas.comap_le (ℱB.le s) hInc_stronglyMeas hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  calc
    μ[B t | ℱB s]
        =ᵐ[μ] μ[(fun ω ↦ B s ω + (B t ω - B s ω)) | ℱB s] := by
            exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[B s | ℱB s] + μ[(fun ω ↦ B t ω - B s ω) | ℱB s] := by
          exact condExp_add hBs_int hInc_int _
    _ =ᵐ[μ] B s + 0 := by
          filter_upwards
            [Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable (ℱB.le s) (hB_adapted s) hBs_int),
              hInc_condExp_zero]
            with ω hωs hωinc
          simp [hωs, hωinc]
    _ =ᵐ[μ] B s := by
          simp

/-- Helper for Exercise 21.2.4: stopping the deterministic time process at a finite sample point
recovers `ENNReal.toReal (τ ω)`. -/
private lemma stoppedValue_ennrealTimeProcess_eq_toReal
    {τ : Ω → ENNReal} {ω : Ω} (hτ : τ ω ≠ ⊤) :
    stoppedValue (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) τ ω = ENNReal.toReal (τ ω) := by
  -- Proof comment: on the finite branch, `untopA` exposes the underlying `NNReal` time and the
  -- deterministic time process simply evaluates to that real time.
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτ
  have ht' : τ ω = (t : ENNReal) := by
    simpa using ht.symm
  rw [stoppedValue, ht']
  change (((t : ENNReal).untopA : NNReal) : ℝ) = (t : ℝ)
  rfl

/-- Helper for Exercise 21.2.4: a finite two-sided boundary hit is equivalent to an actual hit of
one of the two endpoints. -/
lemma twoSidedBoundaryHittingTime_ne_top_iff_exists_eq_left_or_right
    {a b : ℝ} {ω : Ω} :
    hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤ ↔
      ∃ t : NNReal, B t ω = a ∨ B t ω = b := by
  constructor
  · intro hτ
    by_contra hnot
    apply hτ
    refine (hittingAfter_eq_top_iff
      (u := B)
      (s := ({a, b} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)).2 ?_
    intro t _ ht
    rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht) with hta | htb
    exact hnot ⟨t, Or.inl hta⟩
    exact hnot ⟨t, Or.inr htb⟩
  · rintro ⟨t, ht⟩ htop
    have havoid :=
      (hittingAfter_eq_top_iff
        (u := B)
        (s := ({a, b} : Set ℝ))
        (n := (0 : NNReal))
        (ω := ω)).1 htop
    cases ht with
    | inl hta =>
        exact havoid t (by simp) (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hta])
    | inr htb =>
        exact havoid t (by simp) (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, htb])

/-- Helper for Exercise 21.2.4: any explicit hit of either endpoint bounds the two-sided hitting
time from above. -/
lemma twoSidedBoundaryHittingTime_le_of_eq_left_or_right
    {a b : ℝ} {ω : Ω} {t : NNReal} (ht : B t ω = a ∨ B t ω = b) :
    hittingAfter B ({a, b} : Set ℝ) 0 ω ≤ t := by
  -- Proof comment: once the path is exactly at `a` or `b` at time `t`, the two-point target has
  -- been reached by time `t`, so the canonical hitting time cannot exceed `t`.
  cases ht with
  | inl hta =>
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hta] using
        (hittingAfter_le_of_mem
          (u := B)
          (s := ({a, b} : Set ℝ))
          (n := (0 : NNReal))
          (ω := ω)
          (by simp)
          (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hta]))
  | inr htb =>
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, htb] using
        (hittingAfter_le_of_mem
          (u := B)
          (s := ({a, b} : Set ℝ))
          (n := (0 : NNReal))
          (ω := ω)
          (by simp)
          (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, htb]))

/-- Helper for Exercise 21.2.4: on a continuous path, a finite singleton hit lands exactly at the
target level. -/
private lemma levelHittingTime_stoppedValue_eq_level
    {X : NNReal → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ X t ω)
    (hτ : hittingAfter X ({c} : Set ℝ) 0 ω ≠ ⊤) :
    stoppedValue X (hittingAfter X ({c} : Set ℝ) 0) ω = c := by
  classical
  let hitSet : Set NNReal := {t | X t ω = c}
  have hhit : ∃ t : NNReal, X t ω = c := by
    by_contra hnot
    apply hτ
    refine (hittingAfter_eq_top_iff
      (u := X)
      (s := ({c} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)).2 ?_
    intro t _ ht
    exact hnot ⟨t, by simpa [Set.mem_singleton_iff] using ht⟩
  have hnonempty : hitSet.Nonempty := by
    rcases hhit with ⟨t, ht⟩
    exact ⟨t, ht⟩
  have hclosed : IsClosed hitSet := by
    -- Proof comment: the singleton target is closed, so the hit set along a continuous path is
    -- closed as the preimage of a closed set.
    simpa [hitSet, Set.mem_setOf_eq, Set.mem_singleton_iff] using
      isClosed_singleton.preimage hcont
  have hbddBelow : BddBelow hitSet := by
    refine ⟨0, ?_⟩
    intro t ht
    exact bot_le
  have hsInf_mem : sInf hitSet ∈ hitSet := hclosed.csInf_mem hnonempty hbddBelow
  have hτ_eq : (hittingAfter X ({c} : Set ℝ) 0 ω).untopA = sInf hitSet := by
    -- Proof comment: once an exact singleton hit exists, `hittingAfter` is the infimum of the
    -- corresponding hit set.
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({c} : Set ℝ)} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hhit with ⟨t, ht⟩
      exact ⟨t, bot_le, by simpa [Set.mem_singleton_iff] using ht⟩
  have hvalue : X (hittingAfter X ({c} : Set ℝ) 0 ω).untopA ω = c := by
    rw [hτ_eq]
    exact hsInf_mem
  simpa [stoppedValue] using hvalue

/-- Helper for Exercise 21.2.4: finiteness of the singleton hitting time is equivalent to an
actual hit of the target level. -/
private lemma levelHittingTime_ne_top_iff_exists_eq
    {X : NNReal → Ω → ℝ} {c : ℝ} {ω : Ω} :
    hittingAfter X ({c} : Set ℝ) 0 ω ≠ ⊤ ↔ ∃ t : NNReal, X t ω = c := by
  constructor
  · intro hτ
    by_contra hnot
    apply hτ
    refine (hittingAfter_eq_top_iff
      (u := X)
      (s := ({c} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)).2 ?_
    intro t _ ht
    exact hnot ⟨t, by simpa [Set.mem_singleton_iff] using ht⟩
  · rintro ⟨t, ht⟩ htop
    have havoid :=
      (hittingAfter_eq_top_iff
        (u := X)
        (s := ({c} : Set ℝ))
        (n := (0 : NNReal))
        (ω := ω)).1 htop
    exact havoid t (by simp) (by simpa [Set.mem_singleton_iff] using ht)

/-- Helper for Exercise 21.2.4: an explicit hit of the singleton target bounds the corresponding
hitting time from above. -/
private lemma levelHittingTime_le_of_eq
    {X : NNReal → Ω → ℝ} {c : ℝ} {ω : Ω} {t : NNReal} (ht : X t ω = c) :
    hittingAfter X ({c} : Set ℝ) 0 ω ≤ t := by
  -- Proof comment: once the path is exactly at `c` at time `t`, the canonical singleton hitting
  -- time cannot exceed `t`.
  simpa [Set.mem_singleton_iff, ht] using
    (hittingAfter_le_of_mem
      (u := X)
      (s := ({c} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)
      (by simp)
      (by simpa [Set.mem_singleton_iff] using ht))

/-- Helper for Exercise 21.2.4: along a continuous path, hitting the singleton target by time `u`
is equivalent to rational-time approximations of the target level on `[0, u]`. -/
private lemma levelHittingTime_le_iff_forall_nnrat_approx
    {X : NNReal → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hcont : Continuous (fun t : NNReal ↦ X t ω)) (u : NNReal) :
    hittingAfter X ({c} : Set ℝ) 0 ω ≤ u ↔
      ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ u ∧
        |X (q : NNReal) ω - c| < (1 : ℝ) / (n + 1) := by
  constructor
  · intro hτu n
    let ε : ℝ := (1 : ℝ) / (n + 1)
    have hεpos : 0 < ε := by
      positivity
    let τ : ENNReal := hittingAfter X ({c} : Set ℝ) 0 ω
    let t : NNReal := τ.untopA
    have hτne : τ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hτu (by simp))
    have htle : t ≤ u := by
      have hτu' : τ ≤ (u : ENNReal) := by
        simpa [τ] using hτu
      simpa [t, τ] using (WithTop.untopA_le_iff hτne).2 hτu'
    have htc : X t ω = c := by
      -- Proof comment: once the singleton hitting time is finite, the stopped path value is the
      -- exact target level.
      simpa [τ, t, stoppedValue] using
        levelHittingTime_stoppedValue_eq_level
          (X := X) (c := c) (ω := ω) hcont hτne
    by_cases ht0 : t = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa [ht0] using htle
      · have hX0 : X 0 ω = c := by
          simpa [ht0] using htc
        simpa [hX0, ε] using hεpos
    · have htpos : 0 < t := by
        exact bot_lt_iff_ne_bot.mpr ht0
      let U : Set NNReal := {s : NNReal | X s ω ∈ Set.Ioo (c - ε) (c + ε)}
      have hUopen : IsOpen U := by
        -- Proof comment: continuity gives a time neighborhood on which the path stays close to
        -- the hit level.
        simpa [U] using (isOpen_Ioo.preimage hcont)
      have htU : t ∈ U := by
        simpa [U, ε, htc] using hεpos
      have hUNhds : U ∈ nhds t := hUopen.mem_nhds htU
      rcases mem_nhds_iff_exists_Ioo_subset'
          (show ∃ l : NNReal, l < t from ⟨0, htpos⟩)
          (show ∃ r : NNReal, t < r from ⟨t + 1, by simpa using lt_add_of_pos_right t zero_lt_one⟩)
          |>.1 hUNhds with ⟨l, r, ⟨hlt, htr⟩, hIoo⟩
      obtain ⟨q, hql, hqt⟩ := exists_rat_btwn
        (show (l : ℝ) < (t : ℝ) by exact_mod_cast hlt)
      have hq_nonneg : 0 ≤ q := by
        have h0le_l : (0 : ℝ) ≤ (l : ℝ) := by
          exact_mod_cast (show 0 ≤ l by simp)
        exact Rat.cast_nonneg.mp (le_trans h0le_l hql.le)
      let qnn : ℚ≥0 := ⟨q, hq_nonneg⟩
      have hql_nn : l < (qnn : NNReal) := by
        exact_mod_cast hql
      have hqt_nn : (qnn : NNReal) < t := by
        exact_mod_cast hqt
      refine ⟨qnn, le_trans hqt_nn.le htle, ?_⟩
      have hqU : (qnn : NNReal) ∈ U := hIoo ⟨hql_nn, lt_trans hqt_nn htr⟩
      rcases hqU with ⟨hqlo, hqhi⟩
      have hleft : -ε < X (qnn : NNReal) ω - c := by
        linarith
      have hright : X (qnn : NNReal) ω - c < ε := by
        linarith
      exact abs_lt.2 ⟨hleft, hright⟩
  · intro hApprox
    let R : Set ℝ := (fun t : NNReal ↦ X t ω) '' Set.Icc (0 : NNReal) u
    have hRclosed : IsClosed R := by
      -- Proof comment: the image of the compact time interval remains compact, hence closed.
      simpa [R] using (IsCompact.image isCompact_Icc hcont).isClosed
    have hcClosure : c ∈ closure R := by
      -- Proof comment: the rational approximations force `c` into the closure of the path image
      -- on `[0, u]`.
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      rcases hApprox n with ⟨q, hqu, hqε⟩
      refine ⟨X (q : NNReal) ω, ?_, ?_⟩
      · exact ⟨(q : NNReal), ⟨by simp, hqu⟩, rfl⟩
      · simpa [Real.dist_eq, abs_sub_comm] using lt_trans hqε hn
    have hcR : c ∈ R := by
      simpa [hRclosed.closure_eq] using hcClosure
    rcases hcR with ⟨t, htI, htc⟩
    exact (levelHittingTime_le_of_eq (X := X) (c := c) (ω := ω) htc).trans
      (by exact_mod_cast htI.2)

/-- Helper for Exercise 21.2.4: on a continuous path, a finite two-point hit lands exactly at one
of the two target endpoints. -/
private lemma twoPointHittingTime_stoppedValue_mem_pair_of_continuous
    {X : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ X t ω)
    (hτ : hittingAfter X ({a, b} : Set ℝ) 0 ω ≠ ⊤) :
    stoppedValue X (hittingAfter X ({a, b} : Set ℝ) 0) ω ∈ ({a, b} : Set ℝ) := by
  classical
  let hitSet : Set NNReal := {t | X t ω ∈ ({a, b} : Set ℝ)}
  have hhit : ∃ t : NNReal, X t ω ∈ ({a, b} : Set ℝ) := by
    by_contra hnot
    apply hτ
    exact (hittingAfter_eq_top_iff
      (u := X)
      (s := ({a, b} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)).2 (fun t _ ht ↦ hnot ⟨t, ht⟩)
  have hnonempty : hitSet.Nonempty := by
    rcases hhit with ⟨t, ht⟩
    exact ⟨t, ht⟩
  have hclosed : IsClosed hitSet := by
    -- Proof comment: the two-point target is closed, so its hitting set along a continuous path
    -- is also closed.
    simpa [hitSet] using
      (isClosed_singleton.union isClosed_singleton).preimage hcont
  have hbddBelow : BddBelow hitSet := by
    refine ⟨0, ?_⟩
    intro t ht
    exact bot_le
  have hsInf_mem : sInf hitSet ∈ hitSet := hclosed.csInf_mem hnonempty hbddBelow
  have hτ_eq :
      (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA = sInf hitSet := by
    -- Proof comment: once a hit exists, `hittingAfter` is the infimum of the hit set.
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({a, b} : Set ℝ)} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hhit with ⟨t, ht⟩
      exact ⟨t, bot_le, ht⟩
  have hvalue :
      X (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA ω ∈ ({a, b} : Set ℝ) := by
    rw [hτ_eq]
    exact hsInf_mem
  simpa [stoppedValue] using hvalue

/-- Helper for Exercise 21.2.4: pathwise-equal processes have the same two-sided boundary hitting
time at that sample point. -/
lemma twoSidedBoundaryHittingTime_eq_of_forall_eq
    {X Y : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hω : ∀ t : NNReal, X t ω = Y t ω) :
    hittingAfter X ({a, b} : Set ℝ) 0 ω = hittingAfter Y ({a, b} : Set ℝ) 0 ω := by
  -- Proof comment: the defining existence test and the infimum set in `hittingAfter` depend only
  -- on the path values, so pointwise path equality identifies the two hitting times.
  classical
  rw [hittingAfter_def, hittingAfter_def]
  change
    (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({a, b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({a, b} : Set ℝ)} : NNReal) : ENNReal)
      else ⊤) =
      (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({a, b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω ∈ ({a, b} : Set ℝ)} : NNReal) : ENNReal)
      else ⊤)
  have hExists :
      (∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({a, b} : Set ℝ)) ↔
        ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({a, b} : Set ℝ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
  have hSet :
      {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({a, b} : Set ℝ)} =
        {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω ∈ ({a, b} : Set ℝ)} := by
    ext i
    simp [hω i]
  by_cases hX : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({a, b} : Set ℝ)
  · have hY : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({a, b} : Set ℝ) :=
      hExists.mp hX
    rw [if_pos hX, if_pos hY]
    simpa using congrArg (fun s : Set NNReal ↦ ((sInf s : NNReal) : ENNReal)) hSet
  · have hY : ¬ ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({a, b} : Set ℝ) := by
      exact mt hExists.mpr hX
    rw [if_neg hX, if_neg hY]

/-- Helper for Exercise 21.2.4: pathwise-equal processes have the same exact stopped value at the
two-sided boundary hitting time. -/
lemma twoSidedBoundaryStoppedValue_eq_of_forall_eq
    {X Y : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hω : ∀ t : NNReal, X t ω = Y t ω) :
    stoppedValue X (hittingAfter X ({a, b} : Set ℝ) 0) ω =
      stoppedValue Y (hittingAfter Y ({a, b} : Set ℝ) 0) ω := by
  have hτ :
      hittingAfter X ({a, b} : Set ℝ) 0 ω = hittingAfter Y ({a, b} : Set ℝ) 0 ω :=
    twoSidedBoundaryHittingTime_eq_of_forall_eq (X := X) (Y := Y) (a := a) (b := b) (ω := ω) hω
  have hidx :
      (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA =
        (hittingAfter Y ({a, b} : Set ℝ) 0 ω).untopA := by
    simpa using congrArg WithTop.untopA hτ
  -- Proof comment: after identifying the pathwise hitting times, the stopped values differ only
  -- by evaluating pointwise-equal paths at the same random index.
  calc
    stoppedValue X (hittingAfter X ({a, b} : Set ℝ) 0) ω
        = X (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA ω := rfl
    _ = Y (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA ω := by
          simpa using hω (hittingAfter X ({a, b} : Set ℝ) 0 ω).untopA
    _ = Y (hittingAfter Y ({a, b} : Set ℝ) 0 ω).untopA ω := by
          rw [hidx]
    _ = stoppedValue Y (hittingAfter Y ({a, b} : Set ℝ) 0) ω := rfl

/-- Helper for Exercise 21.2.4: a continuous singleton hitting time is a stopping time for the
natural filtration of the path process. -/
private lemma levelHittingTime_isStoppingTime_of_continuous
    {X : NNReal → Ω → ℝ} (hXsm : ∀ t, StronglyMeasurable (X t))
    (hXcont : ∀ ω, Continuous (fun t : NNReal ↦ X t ω)) (c : ℝ) :
    IsStoppingTime (Filtration.natural X hXsm) (hittingAfter X ({c} : Set ℝ) 0) := by
  -- Proof comment: the finite-time hit event is equivalent to a countable family of rational-time
  -- approximations, each measurable in the natural filtration at time `u`.
  intro u
  let ℱX : Filtration NNReal ‹MeasurableSpace Ω› := Filtration.natural X hXsm
  change MeasurableSet[ℱX u] {ω | hittingAfter X ({c} : Set ℝ) 0 ω ≤ u}
  have hStrong : StronglyAdapted ℱX X := Filtration.stronglyAdapted_natural hXsm
  have hSlice :
      ∀ n : ℕ, ∀ q : {q : ℚ≥0 // (q : NNReal) ≤ u},
        MeasurableSet[ℱX u]
          {ω | |X (q : NNReal) ω - c| < (1 : ℝ) / (n + 1)} := by
    intro n q
    have hMeas :
        StronglyMeasurable[ℱX u] (fun ω ↦ X (q : NNReal) ω) := by
      exact hStrong.stronglyMeasurable_le (i := (q : NNReal)) (j := u) q.2
    have hPre :
        {ω | |X (q : NNReal) ω - c| < (1 : ℝ) / (n + 1)} =
          (fun ω ↦ X (q : NNReal) ω) ⁻¹'
            Set.Ioo (c - (1 : ℝ) / (n + 1)) (c + (1 : ℝ) / (n + 1)) := by
      ext ω
      constructor
      · intro hω
        change |X (q : NNReal) ω - c| < (1 : ℝ) / (n + 1) at hω
        rcases abs_lt.1 hω with ⟨hleft, hright⟩
        constructor <;> linarith
      · intro hω
        change X (q : NNReal) ω ∈ Set.Ioo
          (c - (1 : ℝ) / (n + 1)) (c + (1 : ℝ) / (n + 1)) at hω
        rcases hω with ⟨hleft, hright⟩
        have hleft' : -((1 : ℝ) / (n + 1)) < X (q : NNReal) ω - c := by
          linarith
        have hright' : X (q : NNReal) ω - c < (1 : ℝ) / (n + 1) := by
          linarith
        exact abs_lt.2 ⟨hleft', hright'⟩
    rw [hPre]
    exact hMeas.measurable (isOpen_Ioo.measurableSet)
  have hEvent :
      {ω | hittingAfter X ({c} : Set ℝ) 0 ω ≤ u} =
        ⋂ n : ℕ,
          ⋃ q : {q : ℚ≥0 // (q : NNReal) ≤ u},
            {ω | |X (q : NNReal) ω - c| < (1 : ℝ) / (n + 1)} := by
    -- Proof comment: continuity turns exact hitting by time `u` into the countable rational-time
    -- approximation scheme on `[0, u]`.
    ext ω
    simpa using
      (levelHittingTime_le_iff_forall_nnrat_approx
        (X := X) (c := c) (ω := ω) (hXcont ω) u)
  rw [hEvent]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun q ↦ hSlice n q

/-- Helper for Exercise 21.2.4: for a process with measurable time slices and continuous paths,
the two-sided boundary hitting time is a stopping time for the natural filtration. -/
lemma twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
    {X : NNReal → Ω → ℝ} (hXsm : ∀ t, StronglyMeasurable (X t))
    (hXcont : ∀ ω, Continuous (fun t : NNReal ↦ X t ω)) {a b : ℝ} :
    IsStoppingTime (Filtration.natural X hXsm) (hittingAfter X ({a, b} : Set ℝ) 0) := by
  intro u
  let ℱX : Filtration NNReal ‹MeasurableSpace Ω› := Filtration.natural X hXsm
  change MeasurableSet[ℱX u] {ω | hittingAfter X ({a, b} : Set ℝ) 0 ω ≤ u}
  have hStopA :
      IsStoppingTime ℱX (hittingAfter X ({a} : Set ℝ) 0) :=
    levelHittingTime_isStoppingTime_of_continuous (X := X) hXsm hXcont a
  have hStopB :
      IsStoppingTime ℱX (hittingAfter X ({b} : Set ℝ) 0) :=
    levelHittingTime_isStoppingTime_of_continuous (X := X) hXsm hXcont b
  have hEvent :
      {ω | hittingAfter X ({a, b} : Set ℝ) 0 ω ≤ u} =
        {ω | hittingAfter X ({a} : Set ℝ) 0 ω ≤ u} ∪
          {ω | hittingAfter X ({b} : Set ℝ) 0 ω ≤ u} := by
    ext ω
    constructor
    · intro hτu
      let τab : ENNReal := hittingAfter X ({a, b} : Set ℝ) 0 ω
      have hτab_ne : τab ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hτu (by simp))
      have hmem :
          stoppedValue X (hittingAfter X ({a, b} : Set ℝ) 0) ω ∈ ({a, b} : Set ℝ) :=
        twoPointHittingTime_stoppedValue_mem_pair_of_continuous
          (X := X) (a := a) (b := b) (ω := ω) (hXcont ω) hτab_ne
      have hτab_le_u :
          ((τab.untopA : NNReal) : ENNReal) ≤ (u : ENNReal) := by
        have hτab_le_u' : τab.untopA ≤ u := by
          exact (WithTop.untopA_le_iff hτab_ne).2 (by simpa [τab] using hτu)
        exact_mod_cast hτab_le_u'
      rcases hmem with hEq | hEq
      · left
        refine (levelHittingTime_le_of_eq
          (X := X) (c := a) (ω := ω) (t := τab.untopA) ?_).trans ?_
        · simpa [stoppedValue, τab] using hEq
        · exact hτab_le_u
      · right
        refine (levelHittingTime_le_of_eq
          (X := X) (c := b) (ω := ω) (t := τab.untopA) ?_).trans ?_
        · simpa [stoppedValue, τab] using hEq
        · exact hτab_le_u
    · rintro (hτa | hτb)
      · let τa : ENNReal := hittingAfter X ({a} : Set ℝ) 0 ω
        have hτa_ne : τa ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hτa (by simp))
        have hτa_le_u :
            ((τa.untopA : NNReal) : ENNReal) ≤ (u : ENNReal) := by
          have hτa_le_u' : τa.untopA ≤ u := by
            exact (WithTop.untopA_le_iff hτa_ne).2 (by simpa [τa] using hτa)
          exact_mod_cast hτa_le_u'
        have hXa : X τa.untopA ω = a := by
          simpa [stoppedValue, τa] using
            levelHittingTime_stoppedValue_eq_level
              (X := X) (c := a) (ω := ω) (hXcont ω) hτa_ne
        have hτab_le_τa :
            hittingAfter X ({a, b} : Set ℝ) 0 ω ≤ τa.untopA := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hXa] using
            (hittingAfter_le_of_mem
              (u := X)
              (s := ({a, b} : Set ℝ))
              (n := (0 : NNReal))
              (ω := ω)
              (by simp)
              (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hXa]))
        exact hτab_le_τa.trans hτa_le_u
      · let τb : ENNReal := hittingAfter X ({b} : Set ℝ) 0 ω
        have hτb_ne : τb ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hτb (by simp))
        have hτb_le_u :
            ((τb.untopA : NNReal) : ENNReal) ≤ (u : ENNReal) := by
          have hτb_le_u' : τb.untopA ≤ u := by
            exact (WithTop.untopA_le_iff hτb_ne).2 (by simpa [τb] using hτb)
          exact_mod_cast hτb_le_u'
        have hXb : X τb.untopA ω = b := by
          simpa [stoppedValue, τb] using
            levelHittingTime_stoppedValue_eq_level
              (X := X) (c := b) (ω := ω) (hXcont ω) hτb_ne
        have hτab_le_τb :
            hittingAfter X ({a, b} : Set ℝ) 0 ω ≤ τb.untopA := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hXb] using
            (hittingAfter_le_of_mem
              (u := X)
              (s := ({a, b} : Set ℝ))
              (n := (0 : NNReal))
              (ω := ω)
              (by simp)
              (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hXb]))
        exact hτab_le_τb.trans hτb_le_u
  rw [hEvent]
  exact (hStopA u).union (hStopB u)

/-- Helper for Exercise 21.2.4: on a continuous path, a finite two-sided boundary hit lands
exactly at one of the two endpoints. -/
lemma twoSidedBoundaryStoppedValue_mem_pair
    {a b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω)
    (hτ : hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤) :
    stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω ∈ ({a, b} : Set ℝ) := by
  exact
    twoPointHittingTime_stoppedValue_mem_pair_of_continuous
      (X := B) (a := a) (b := b) (ω := ω) hcont hτ

/-- Helper for Exercise 21.2.4: on a continuous path started at `0`, every deterministic time
strictly before the two-sided boundary hit still lies in the open interval `(a,b)`. -/
lemma mem_Ioo_of_lt_twoSidedBoundaryHittingTime
    {a b : ℝ} {ω : Ω} {t : NNReal}
    (hcont : Continuous fun s : NNReal ↦ B s ω)
    (hzero : B 0 ω = 0) (ha : a < 0) (hb : 0 < b)
    (hbefore : (t : ENNReal) < hittingAfter B ({a, b} : Set ℝ) 0 ω) :
    B t ω ∈ Set.Ioo a b := by
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hle : B t ω ≤ a := le_of_not_gt hnot
    have htarget : -a ∈ Set.Icc (-B 0 ω) (-B t ω) := by
      refine ⟨?_, ?_⟩
      · simpa [hzero] using (neg_pos.mpr ha).le
      · linarith
    obtain ⟨s, hs_mem, hs_eq⟩ :=
      (intermediate_value_Icc
        (a := (0 : NNReal))
        (b := t)
        (by simp)
        hcont.neg.continuousOn) htarget
    have hs_hit : B s ω = a := by
      linarith
    have hτ_le_s :
        hittingAfter B ({a, b} : Set ℝ) 0 ω ≤ s := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hs_hit] using
        (hittingAfter_le_of_mem
          (u := B)
          (s := ({a, b} : Set ℝ))
          (n := (0 : NNReal))
          (ω := ω)
          hs_mem.1
          (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_hit]))
    have hτ_le_t :
        hittingAfter B ({a, b} : Set ℝ) 0 ω ≤ (t : ENNReal) := by
      exact le_trans hτ_le_s (show (s : ENNReal) ≤ (t : ENNReal) by exact_mod_cast hs_mem.2)
    exact (not_le_of_gt hbefore) hτ_le_t
  · by_contra hnot
    have hle : b ≤ B t ω := le_of_not_gt hnot
    have htarget : b ∈ Set.Icc (B 0 ω) (B t ω) := by
      refine ⟨?_, hle⟩
      simpa [hzero] using hb.le
    obtain ⟨s, hs_mem, hs_eq⟩ :=
      (intermediate_value_Icc
        (a := (0 : NNReal))
        (b := t)
        (by simp)
        hcont.continuousOn) htarget
    have hτ_le_s :
        hittingAfter B ({a, b} : Set ℝ) 0 ω ≤ s := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hs_eq] using
        (hittingAfter_le_of_mem
          (u := B)
          (s := ({a, b} : Set ℝ))
          (n := (0 : NNReal))
          (ω := ω)
          hs_mem.1
          (by simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_eq]))
    have hτ_le_t :
        hittingAfter B ({a, b} : Set ℝ) 0 ω ≤ (t : ENNReal) := by
      exact le_trans hτ_le_s (show (s : ENNReal) ≤ (t : ENNReal) by exact_mod_cast hs_mem.2)
    exact (not_le_of_gt hbefore) hτ_le_t

/-- Helper for Exercise 21.2.4: clipping a stopping time by a deterministic horizon rewrites its
stopped value as the corresponding stopped-process slice. -/
private lemma stoppedValue_min_const_eq_stoppedProcess
    {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal} {t : NNReal} :
    stoppedValue M (fun ω ↦ min (τ ω) (t : ENNReal)) =
      stoppedProcess M τ t := by
  ext ω
  -- Proof comment: both sides evaluate `M` at the same clipped time, up to commutativity of
  -- `min`.
  change M (min (τ ω) (t : ENNReal)).untopA ω =
    M (min (t : ENNReal) (τ ω)).untopA ω
  rw [min_comm]

/-- Helper for Exercise 21.2.4: dyadic ceiling approximation of a finite nonnegative random time.
-/
private def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper for Exercise 21.2.4: the dyadic ceiling event `{σⁿ ≤ t}` rewrites as the original
stopping event at the latest dyadic mesh point not exceeding `t`. -/
private lemma dyadicCeilApprox_event_le_eq
    (n : ℕ) (τ : Ω → NNReal) (t : NNReal) :
    {ω | (dyadicCeilApprox n τ ω : ENNReal) ≤ t} =
      {ω | (τ ω : ENNReal) ≤
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
          ((2 : NNReal) ^ n))} := by
  ext ω
  have hbody :
      dyadicCeilApprox n τ ω ≤ t ↔
        τ ω ≤
          ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
            ((2 : NNReal) ^ n)) := by
    let c : NNReal := (2 : NNReal) ^ n
    have hc_pos : 0 < c := by
      -- Proof comment: the dyadic denominator is strictly positive.
      dsimp [c]
      positivity
    have hDiv :
        dyadicCeilApprox n τ ω ≤ t ↔
          (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t := by
      -- Proof comment: multiplying by the positive dyadic scale clears the denominator.
      dsimp [dyadicCeilApprox, c]
      rw [div_le_iff₀ hc_pos]
      simpa [c, mul_comm]
    have hCeilFloor :
        (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t ↔
          Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
      constructor
      · intro h
        have hreal :
            ((Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ) ≤ (((c * t : NNReal) : ℝ)) := by
          exact_mod_cast h
        exact Nat.le_floor hreal
      · intro h
        have hnn :
            (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤
              (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          exact_mod_cast h
        exact le_trans hnn <| by
          have hfloorReal :
              (((Nat.floor (((c * t : NNReal) : ℝ)) : ℕ) : ℝ)) ≤ (((c * t : NNReal) : ℝ)) := by
            exact Nat.floor_le (show 0 ≤ (((c * t : NNReal) : ℝ)) by positivity)
          exact_mod_cast hfloorReal
    have hFloorDiv :
        Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) ↔
          τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) / c := by
      constructor
      · intro h
        have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
          exact Nat.ceil_le.mp h
        have hnn' : c * τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          exact_mod_cast hreal
        exact (le_div_iff₀ hc_pos).2 (by simpa [mul_comm] using hnn')
      · intro h
        have hnn' : c * τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          have hmul := (le_div_iff₀ hc_pos).1 h
          simpa [mul_comm] using hmul
        have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
          exact_mod_cast hnn'
        exact Nat.ceil_le.2 hreal
    -- Proof comment: the dyadic ceiling only checks whether `τ` already lies below the previous
    -- mesh point.
    exact hDiv.trans (hCeilFloor.trans hFloorDiv)
  exact_mod_cast hbody

/-- Helper for Exercise 21.2.4: dyadic ceiling approximations of `NNReal`-valued stopping times
are still stopping times. -/
private lemma dyadicCeilApprox_isStoppingTime
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›} {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := by
  intro t
  let q : NNReal :=
    ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ n))
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    -- Proof comment: the dyadic scale is positive, so division preserves inequalities.
    positivity
  have hq_le_t : q ≤ t := by
    -- Proof comment: the dyadic predecessor of `t` never exceeds `t`.
    dsimp [q]
    refine (div_le_iff₀ hpow_pos).2 ?_
    have hfloor :
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal)) ≤
          ((2 : NNReal) ^ n) * t := by
      have hfloorReal :
          (((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ)) : ℕ) : ℝ) ≤
            ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) := by
        exact Nat.floor_le (show 0 ≤ ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) by positivity)
      exact_mod_cast hfloorReal
    simpa [mul_comm] using hfloor
  -- Proof comment: rewrite the dyadic event through the original stopping event and transport it
  -- along filtration monotonicity.
  change MeasurableSet[ℱ t] {ω | (dyadicCeilApprox n τ ω : ENNReal) ≤ t}
  rw [dyadicCeilApprox_event_le_eq (n := n) (τ := τ) (t := t)]
  simpa [q] using (ℱ.mono hq_le_t _ (hτ.measurableSet_le q))

/-- Helper for Exercise 21.2.4: every dyadic ceiling approximation has countable range. -/
private lemma dyadicCeilApprox_countableRange
    (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal)).Countable := by
  refine
    ((Set.countable_range
      fun k : ℕ ↦ ((((k : NNReal) / ((2 : NNReal) ^ n)) : NNReal) : ENNReal))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  -- Proof comment: every dyadic ceiling value lies on the mesh `2⁻ⁿ ℕ`.
  simp [dyadicCeilApprox]

/-- Helper for Exercise 21.2.4: the dyadic ceilings converge pointwise back to the original
finite time. -/
private lemma dyadicCeilApprox_tendsto
    (ρ : Ω → NNReal) :
    ∀ ω, Tendsto (fun m ↦ dyadicCeilApprox m ρ ω) atTop (nhds (ρ ω)) := by
  intro ω
  have hEq :
      (fun m ↦ dyadicCeilApprox m ρ ω) =
        fun m ↦ (((Nat.ceil ((ρ ω : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
    funext m
    unfold dyadicCeilApprox
    congr 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (congrArg (fun x : NNReal ↦ (x : ℝ)) (mul_comm ((2 : NNReal) ^ m) (ρ ω)))
  -- Proof comment: this is the standard dyadic ceiling convergence `⌈ρ 2^m⌉ / 2^m → ρ`.
  rw [hEq]
  refine (NNReal.tendsto_coe).mp ?_
  simpa using
    (tendsto_nat_ceil_mul_div_atTop (a := (ρ ω : ℝ))
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Exercise 21.2.4: continuity of a sample path transports convergence of finite
times to convergence of the associated stopped values. -/
private lemma stoppedValue_tendsto_of_timeApprox
    {M : NNReal → Ω → ℝ}
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {ρm : ℕ → Ω → NNReal} {ρ : Ω → NNReal}
    (hρ : ∀ ω, Tendsto (fun m ↦ ρm m ω) atTop (nhds (ρ ω))) :
    ∀ ω,
      Tendsto
        (fun m ↦ stoppedValue M (fun ω' ↦ ((ρm m ω' : NNReal) : ENNReal)) ω)
        atTop
        (nhds (stoppedValue M (fun ω' ↦ ((ρ ω' : NNReal) : ENNReal)) ω)) := by
  intro ω
  -- Proof comment: for finite stopping times, `stoppedValue` is just evaluation at that time.
  simpa [stoppedValue] using ((hM_cont ω).tendsto (ρ ω)).comp (hρ ω)

/-- Helper for Exercise 21.2.4: `L¹` convergence on the ambient measure controls integrals over
every restricted measure. -/
private lemma tendsto_restrictedIntegral_of_tendsto_L1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hg : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ ω in s, f n ω ∂μ) atTop (nhds (∫ ω in s, g ω ∂μ)) := by
  have hL1_restrict :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 (μ.restrict s)) atTop (nhds 0) := by
    -- Proof comment: restricting the measure can only decrease the `L¹` seminorm.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (fun ω ↦ f n ω - g ω) Measure.restrict_le_self
  -- Proof comment: continuity of the integral on `L¹` now gives convergence of the restricted
  -- integrals.
  exact tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hL1_restrict

/-- Helper for Exercise 21.2.4: dyadic ceiling approximations of a finite stopping time give an
integrable exact stopped slice together with `L¹` convergence of the dyadic slices. -/
private lemma stoppedProcess_dyadicCeilApprox_limitData
    [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (r : NNReal) :
    Integrable (stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r) μ ∧
      Tendsto
        (fun m ↦
          eLpNorm
            (fun ω ↦
              stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
                stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω)
            1 μ)
        atTop (nhds 0) := by
  let τm : ℕ → Ω → ENNReal := fun m ω ↦
    min ((dyadicCeilApprox m σ ω : NNReal) : ENNReal) (r : ENNReal)
  let τ : Ω → ENNReal := fun ω ↦ min ((σ ω : NNReal) : ENNReal) (r : ENNReal)
  have hτm_stop : ∀ m, IsStoppingTime ℱ (τm m) := by
    intro m
    exact (dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ m).min_const r
  have hτm_le : ∀ m ω, τm m ω ≤ (r : ENNReal) := by
    intro m ω
    exact min_le_right _ _
  have hτm_count : ∀ m, (Set.range (τm m)).Countable := by
    intro m
    refine
      ((dyadicCeilApprox_countableRange m σ).image fun u : ENNReal ↦ min u (r : ENNReal)).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨(dyadicCeilApprox m σ ω : ENNReal), ⟨ω, rfl⟩, rfl⟩
  have hCond :
      ∀ m, stoppedValue M (τm m) =ᵐ[μ] μ[M r | (hτm_stop m).measurableSpace] := by
    intro m
    -- Proof comment: each clipped dyadic stop has countable range and stays below `r`, so the
    -- countable-range optional sampling theorem applies to it.
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hτm_stop m) (hτm_le m) (hτm_count m)
  have hUIcond :
      UniformIntegrable
        (fun m : ℕ ↦ μ[M r | (hτm_stop m).measurableSpace]) 1 μ :=
    (hM.integrable r).uniformIntegrable_condExp fun m ↦ (hτm_stop m).measurableSpace_le
  have hUIstopped : UniformIntegrable (fun m : ℕ ↦ stoppedValue M (τm m)) 1 μ :=
    hUIcond.ae_eq fun m ↦ (hCond m).symm
  have hApprox :
      ∀ ω, Tendsto (fun m ↦ min (dyadicCeilApprox m σ ω) r) atTop (nhds (min (σ ω) r)) := by
    intro ω
    -- Proof comment: the dyadic times converge pointwise to `σ(ω)`, and clipping by `r`
    -- preserves that limit.
    exact ((continuous_id.min continuous_const).tendsto (σ ω)).comp
      (dyadicCeilApprox_tendsto σ ω)
  have hAeTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ stoppedValue M (τm m) ω) atTop (nhds (stoppedValue M τ ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    -- Proof comment: continuity of the sample path turns convergence of the dyadic times into
    -- convergence of the corresponding stopped values.
    simpa [τm, τ] using
      stoppedValue_tendsto_of_timeApprox
        (M := M) hM_cont
        (ρm := fun m ω' ↦ min (dyadicCeilApprox m σ ω') r)
        (ρ := fun ω' ↦ min (σ ω') r) hApprox ω
  have hInt : Integrable (stoppedValue M τ) μ :=
    hUIstopped.integrable_of_ae_tendsto hAeTendsto
  have hL1 :
      Tendsto
        (fun m ↦ eLpNorm (fun ω ↦ stoppedValue M (τm m) ω - stoppedValue M τ ω) 1 μ)
        atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun m ↦ hUIstopped.aestronglyMeasurable m)
      (memLp_one_iff_integrable.2 hInt) hUIstopped.unifIntegrable hAeTendsto
  have hτ_eq :
      stoppedValue M τ = stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r := by
    simpa [τ] using
      (stoppedValue_min_const_eq_stoppedProcess
        (M := M) (τ := fun ω ↦ (σ ω : ENNReal)) (t := r))
  have hτm_eq :
      ∀ m, stoppedValue M (τm m) =
        stoppedProcess M (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) r := by
    intro m
    simpa [τm] using
      (stoppedValue_min_const_eq_stoppedProcess
        (M := M) (τ := fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) (t := r))
  constructor
  · -- Proof comment: the exact stopped slice is the integrable `L¹` limit of the dyadic slices.
    simpa [hτ_eq] using hInt
  · -- Proof comment: rewrite the `L¹` convergence back into the stopped-process normal form.
    simpa [hτ_eq, hτm_eq] using hL1

/-- Helper for Exercise 21.2.4: covariance is unchanged by almost-everywhere replacement of both
coordinates. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: rewrite both expectations through the almost-everywhere equal coordinates and
  -- then compare the covariance integrands pointwise.
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Exercise 21.2.4: the everywhere-continuous Brownian modification is itself a
Brownian motion. -/
private lemma brownianContinuousVersion_isBrownianMotionLocal
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: the Brownian characterization is stable under fixed-time almost-everywhere
  -- modification, and the patched process has continuous paths by construction.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    -- Proof comment: record the zero-time normalization once so the Brownian base point does not
    -- rely on brittle `simp` through the path patch.
    simpa using brownianContinuousVersion_zero (μ := μ) (B := B) hB ω
  · exact
      hB.isGaussianProcess.congr
        (fun t ↦ brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.mean_zero t)
  · intro s t
    exact
      (covariance_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.covariance_eq s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 21.2.4: after passing to the continuous Brownian modification, the
two-sided hitting time, its deterministic truncation, and the corresponding stopped value all
agree almost surely with the original process. -/
private lemma twoSidedBoundaryTruncation_ae_eq_continuousVersion
    (hB : IsBrownianMotion μ B) {a b : ℝ} (n : ℕ) :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    let τn : Ω → ENNReal := fun ω ↦ min (τ ω) (n : ENNReal)
    let τcn : Ω → ENNReal := fun ω ↦ min (τc ω) (n : ENNReal)
    ∀ᵐ ω ∂μ,
      τ ω = τc ω ∧
        stoppedValue B τn ω = stoppedValue Bc τcn ω ∧
        ENNReal.toReal (τn ω) = ENNReal.toReal (τcn ω) := by
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  let τn : Ω → ENNReal := fun ω ↦ min (τ ω) (n : ENNReal)
  let τcn : Ω → ENNReal := fun ω ↦ min (τc ω) (n : ENNReal)
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  have hτ :
      τ ω = τc ω := by
    -- Proof comment: pathwise equality of all time slices identifies the two-point hitting time.
    simpa [τ, τc, Bc] using
      (twoSidedBoundaryHittingTime_eq_of_forall_eq
        (X := B) (Y := Bc) (a := a) (b := b) (ω := ω) fun t ↦ (hω t).symm)
  have hτn :
      τn ω = τcn ω := by
    -- Proof comment: deterministic truncation commutes with the already identified hitting time.
    simpa [τn, τcn] using congrArg (fun t : ENNReal ↦ min t (n : ENNReal)) hτ
  have hidx :
      (τn ω).untopA = (τcn ω).untopA := by
    simpa using congrArg WithTop.untopA hτn
  refine ⟨hτ, ?_, ?_⟩
  · -- Proof comment: the truncated stopped values evaluate pointwise-equal paths at the same
    -- clipped time index.
    calc
      stoppedValue B τn ω = B (τn ω).untopA ω := rfl
      _ = Bc (τn ω).untopA ω := by simpa using (hω (τn ω).untopA).symm
      _ = Bc (τcn ω).untopA ω := by rw [hidx]
      _ = stoppedValue Bc τcn ω := rfl
  · -- Proof comment: once the truncated stopping times match, their real-valued clocks match too.
    simpa [τn, τcn] using congrArg ENNReal.toReal hτn

/-- Helper for Exercise 21.2.4: a continuous martingale preserves expectation at a clipped finite
stopping time. -/
private lemma expected_stoppedValue_min_const_eq_initial
    [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ)
    (r : NNReal) :
    ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) ω ∂μ =
      ∫ ω, M 0 ω ∂μ := by
  let σ : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (min (τ ω) (r : ENNReal))
  have hσ_eq :
      (fun ω ↦ ((σ ω : NNReal) : ENNReal)) = fun ω ↦ min (τ ω) (r : ENNReal) := by
    funext ω
    simp [σ, ENNReal.coe_toNNReal, ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)]
  have hσ_stop : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal) := by
    rw [hσ_eq]
    exact hτ.min_const r
  have hInt :
      Integrable (stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r) μ :=
    (stoppedProcess_dyadicCeilApprox_limitData
      (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσ_stop r).1
  have hL1 :
      Tendsto
        (fun m ↦
          eLpNorm
            (fun ω ↦
              stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
                stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω)
            1 μ)
        atTop (nhds 0) :=
    (stoppedProcess_dyadicCeilApprox_limitData
      (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσ_stop r).2
  have hIntegralTendsto :
      Tendsto
        (fun m ↦ ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ)
        atTop
        (nhds (∫ ω, stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω ∂μ)) := by
    -- Proof comment: `L¹` convergence of the dyadic slices gives convergence of their
    -- expectations.
    exact tendsto_integral_of_L1' _ hInt
      (Filter.Eventually.of_forall fun m ↦ by
        have hσm :
            IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal) :=
          dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ_stop m
        exact
          (stoppedProcess_dyadicCeilApprox_limitData
            (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσm r).1)
      hL1
  have hIntegralEq :
      ∀ m,
        ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ =
          ∫ ω, M r ω ∂μ := by
    intro m
    let τm : Ω → ENNReal := fun ω ↦ min ((dyadicCeilApprox m σ ω : NNReal) : ENNReal) (r : ENNReal)
    have hτm_stop : IsStoppingTime ℱ τm := by
      exact (dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ_stop m).min_const r
    have hτm_le : ∀ ω, τm ω ≤ (r : ENNReal) := by
      intro ω
      exact min_le_right _ _
    have hτm_count : (Set.range τm).Countable := by
      refine ((dyadicCeilApprox_countableRange m σ).image fun u : ENNReal ↦ min u (r : ENNReal)).mono ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨(dyadicCeilApprox m σ ω : ENNReal), ⟨ω, rfl⟩, rfl⟩
    have hCond :
        stoppedValue M τm =ᵐ[μ] μ[M r | hτm_stop.measurableSpace] :=
      hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτm_stop hτm_le hτm_count
    have hStoppedEq :
        stoppedValue M τm =
          stoppedProcess M (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) r := by
      simpa [τm] using
        (stoppedValue_min_const_eq_stoppedProcess
          (M := M) (τ := fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) (t := r))
    -- Proof comment: integrate the conditional expectation identity and then use the martingale
    -- expectation invariance between deterministic times `0` and `r`.
    calc
      ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ
          = ∫ ω, stoppedValue M τm ω ∂μ := by simp [hStoppedEq]
      _ = ∫ ω, μ[M r | hτm_stop.measurableSpace] ω ∂μ := integral_congr_ae hCond
      _ = ∫ ω, M r ω ∂μ := integral_condExp hτm_stop.measurableSpace_le
  have hConstEq : ∫ ω, stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r ω ∂μ = ∫ ω, M r ω ∂μ := by
    have hConstTendsto :
        Tendsto
          (fun m ↦ ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ)
          atTop
          (nhds (∫ ω, M r ω ∂μ)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun m ↦ (hIntegralEq m).symm
    exact tendsto_nhds_unique hIntegralTendsto hConstTendsto
  have hStoppedEq :
      stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r =
        stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) := by
    ext ω
    have hσ_eqω :
        ((σ ω : NNReal) : ENNReal) = min (τ ω) (r : ENNReal) := by
      simpa [σ, ENNReal.coe_toNNReal,
        ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)]
    change M (min (r : ENNReal) ((σ ω : NNReal) : ENNReal)).untopA ω =
      M (min (τ ω) (r : ENNReal)).untopA ω
    have hmin : min (min (τ ω) (r : ENNReal)) (r : ENNReal) = min (τ ω) (r : ENNReal) := by
      rw [min_eq_left (min_le_right _ _)]
    rw [hσ_eqω, min_comm, hmin]
  calc
    ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) ω ∂μ
        = ∫ ω, stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r ω ∂μ := by
            simp [hStoppedEq]
    _ = ∫ ω, M r ω ∂μ := hConstEq
    _ = ∫ ω, M 0 ω ∂μ := by
          simpa [setIntegral_univ] using
            (hM.setIntegral_eq (show (0 : NNReal) ≤ r by exact zero_le _)
              (s := Set.univ) MeasurableSet.univ).symm

/-- Helper for Exercise 21.2.4: each deterministic truncation `τ ∧ n` keeps the stopped value
inside the interval `[a,b]` almost surely. -/
lemma truncatedTwoSidedBoundaryStoppedValue_mem_uIcc_ae
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) (n : ℕ) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    ∀ᵐ ω ∂μ,
      stoppedValue B (fun ω' ↦ min (τ ω') (n : ENNReal)) ω ∈ Set.uIcc a b := by
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  have hab : a ≤ b := by
    linarith
  have hzero : ∀ ω : Ω, B 0 ω = 0 := by
    intro ω
    simpa using congrFun hB.zero ω
  filter_upwards [hB.continuous_paths] with ω hωcont
  have hcont : Continuous fun t : NNReal ↦ B t ω := by
    simpa [processPath] using hωcont
  by_cases hτn : τ ω ≤ (n : ENNReal)
  · have hτne : τ ω ≠ ⊤ := ne_of_lt <| lt_of_le_of_lt hτn (by simp)
    have hmemPair :
        stoppedValue B τ ω ∈ ({a, b} : Set ℝ) :=
      twoSidedBoundaryStoppedValue_mem_pair (B := B) (a := a) (b := b) (ω := ω) hcont hτne
    have hmemIcc : stoppedValue B τ ω ∈ Set.Icc a b := by
      rcases hmemPair with hEq | hEq
      · rw [hEq]
        exact ⟨le_rfl, hab⟩
      · rw [hEq]
        exact ⟨ha.le.trans hb.le, le_rfl⟩
    have hmin : min (τ ω) (n : ENNReal) = τ ω := min_eq_left hτn
    change B (min (τ ω) (n : ENNReal)).untopA ω ∈ Set.uIcc a b
    rw [hmin]
    simpa [Set.uIcc_of_le hab] using hmemIcc
  · have hbefore : (n : ENNReal) < τ ω := lt_of_not_ge hτn
    have hmemIoo :
        B n ω ∈ Set.Ioo a b :=
      mem_Ioo_of_lt_twoSidedBoundaryHittingTime
        (B := B) (a := a) (b := b) (ω := ω) (t := n)
        hcont (hzero ω) ha hb hbefore
    have hmin : min (τ ω) (n : ENNReal) = (n : ENNReal) := min_eq_right (le_of_lt hbefore)
    have hmemIcc : B n ω ∈ Set.Icc a b := ⟨hmemIoo.1.le, hmemIoo.2.le⟩
    change B (min (τ ω) (n : ENNReal)).untopA ω ∈ Set.uIcc a b
    rw [hmin]
    simpa [Set.uIcc_of_le hab] using hmemIcc

/-- Helper for Exercise 21.2.4: evaluating `B_t^2 - t` at the truncated stop rewrites into the
stopped Brownian square minus the stopped deterministic time. -/
lemma stoppedSquareMinusTimeAtTruncation
    {a b : ℝ} (n : ℕ) (ω : Ω) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    stoppedValue (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) (fun ω' ↦ min (τ ω') (n : ENNReal)) ω =
      (stoppedValue B (fun ω' ↦ min (τ ω') (n : ENNReal)) ω) ^ 2 -
        ENNReal.toReal (min (τ ω) (n : ENNReal)) := by
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τn : Ω → ENNReal := fun ω' ↦ min (τ ω') (n : ENNReal)
  have hτn_ne : τn ω ≠ ⊤ := by
    -- Proof comment: the deterministic truncation `τ ∧ n` is always finite.
    simp [τn]
  have htime :
      (((τn ω).untopA : NNReal) : ℝ) = ENNReal.toReal (τn ω) := by
    -- Proof comment: the stopped deterministic time process reads off the real value of `τ ∧ n`.
    simpa [τn, stoppedValue] using
      (stoppedValue_ennrealTimeProcess_eq_toReal (τ := τn) (ω := ω) hτn_ne)
  have htime' :
      (((min (τ ω) (n : ENNReal)).untopA : NNReal) : ℝ) =
        ENNReal.toReal (min (τ ω) (n : ENNReal)) := by
    simpa [τn] using htime
  -- Proof comment: after expanding both stopped values, only the deterministic time coordinate
  -- needs the `ENNReal.toReal` normalization.
  simp only [stoppedValue]
  exact
    congrArg
      (fun r : ℝ ↦
        B (min (hittingAfter B ({a, b} : Set ℝ) 0 ω) (n : ENNReal)).untopA ω ^ 2 - r)
      htime'

/-- Helper for Exercise 21.2.4: bounded optional stopping at `τ ∧ n` gives the exact first and
second moment identities needed for the limit passage. -/
lemma twoSidedExitMomentIdentitiesAtTruncation
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) (n : ℕ) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τn : Ω → ENNReal := fun ω ↦ min (τ ω) (n : ENNReal)
    (∫ ω, stoppedValue B τn ω ∂μ = 0) ∧
      (∫ ω, (stoppedValue B τn ω) ^ 2 ∂μ =
        ∫ ω, ENNReal.toReal (τn ω) ∂μ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bc : NNReal → Ω → ℝ := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  let τn : Ω → ENNReal := fun ω ↦ min (τ ω) (n : ENNReal)
  let τcn : Ω → ENNReal := fun ω ↦ min (τc ω) (n : ENNReal)
  have hτc : IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
    -- Route correction: do the stopping-time step on the everywhere-continuous modification `Bc`
    -- instead of retrying the almost-surely continuous original process.
    simpa [τc] using
      (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := Bc) hBc.stronglyMeasurable
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
  have hTransport :=
    twoSidedBoundaryTruncation_ae_eq_continuousVersion
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) n
  have hFirstBc :
      ∫ ω, stoppedValue Bc τcn ω ∂μ = 0 := by
    -- Proof comment: bounded optional stopping for the Brownian martingale on `Bc` gives the
    -- stopped first moment at the clipped boundary clock.
    calc
      ∫ ω, stoppedValue Bc τcn ω ∂μ
          = ∫ ω, Bc 0 ω ∂μ := by
              simpa [τcn] using
                (expected_stoppedValue_min_const_eq_initial
                  (μ := μ)
                  (ℱ := Filtration.natural Bc hBc.stronglyMeasurable)
                  (M := Bc)
                  (hM := brownianMartingale_natural (μ := μ) (B := Bc) hBc)
                  (hM_cont := brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
                  (τ := τc)
                  hτc n)
      _ = 0 := by simp [hBc.zero]
  have hSecondBc :
      ∫ ω, (stoppedValue Bc τcn ω) ^ 2 ∂μ = ∫ ω, ENNReal.toReal (τcn ω) ∂μ := by
    have hSquareMartingale :
        Martingale (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ))
          (Filtration.natural Bc hBc.stronglyMeasurable) μ :=
      brownian_sq_sub_time_martingale (μ := μ) (B := Bc) hBc
    have hSquareCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Bc t ω ^ 2 - (t : ℝ) := by
      intro ω
      -- Proof comment: the compensated square inherits continuity from the continuous version.
      exact
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω).pow 2 |>.sub
          continuous_subtype_val
    have hZeroStop :
        ∫ ω, stoppedValue (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ)) τcn ω ∂μ = 0 := by
      calc
        ∫ ω, stoppedValue (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ)) τcn ω ∂μ
            = ∫ ω, (Bc 0 ω ^ 2 - (0 : ℝ)) ∂μ := by
                simpa [τcn] using
                  (expected_stoppedValue_min_const_eq_initial
                    (μ := μ)
                    (ℱ := Filtration.natural Bc hBc.stronglyMeasurable)
                    (M := fun t ω ↦ Bc t ω ^ 2 - (t : ℝ))
                    (hM := hSquareMartingale)
                    (hM_cont := hSquareCont)
                    (τ := τc)
                    hτc n)
        _ = 0 := by simp [hBc.zero]
    have hRewrite :
        ∫ ω, stoppedValue (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ)) τcn ω ∂μ =
          ∫ ω, (stoppedValue Bc τcn ω) ^ 2 - ENNReal.toReal (τcn ω) ∂μ := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Bc, τc, τcn] using
          (stoppedSquareMinusTimeAtTruncation
            (B := Bc) (a := a) (b := b) n ω)
    have hSubEq :
        ∫ ω, (stoppedValue Bc τcn ω) ^ 2 - ENNReal.toReal (τcn ω) ∂μ = 0 := by
      rw [← hRewrite]
      exact hZeroStop
    have hIntSq :
        Integrable (fun ω ↦ (stoppedValue Bc τcn ω) ^ 2) μ := by
      -- Proof comment: the truncated stopped value stays in `[a,b]`, so its square is bounded.
      have hab : a ≤ b := by
        linarith
      have hBcStrong :
          StronglyAdapted (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
        Filtration.stronglyAdapted_natural (u := Bc) hBc.stronglyMeasurable
      have hBcProg :
          ProgMeasurable (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
        hBcStrong.progMeasurable_of_continuous
          (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
      have hBoundAe :
          ∀ᵐ ω ∂μ,
            ‖(stoppedValue Bc τcn ω) ^ 2‖ ≤ max (a ^ 2) (b ^ 2) := by
        have hMemAe :=
          truncatedTwoSidedBoundaryStoppedValue_mem_uIcc_ae
            (μ := μ) (B := Bc) hBc ha hb n
        filter_upwards [hMemAe] with ω hω
        have hx : stoppedValue Bc τcn ω ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab] using hω
        have hsq :
            (stoppedValue Bc τcn ω) ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
          by_cases hxnonneg : 0 ≤ stoppedValue Bc τcn ω
          · have hsqb : (stoppedValue Bc τcn ω) ^ 2 ≤ b ^ 2 := by
              nlinarith [hx.2, hxnonneg]
            exact le_trans hsqb (le_max_right _ _)
          · have hxle0 : stoppedValue Bc τcn ω ≤ 0 := le_of_not_ge hxnonneg
            have hsqa : (stoppedValue Bc τcn ω) ^ 2 ≤ a ^ 2 := by
              nlinarith [hx.1, hxle0]
            exact le_trans hsqa (le_max_left _ _)
        have hsq_nonneg : 0 ≤ (stoppedValue Bc τcn ω) ^ 2 := sq_nonneg _
        simpa [Real.norm_of_nonneg hsq_nonneg] using hsq
      have hStopMeas :
          Measurable (stoppedValue Bc τcn) := by
        change Measurable (stoppedValue Bc (fun ω' ↦ min (τc ω') (n : ENNReal)))
        exact (measurable_stoppedValue hBcProg (hτc.min_const n)).mono
          (hτc.min_const n).measurableSpace_le le_rfl
      have hStopSqMeas :
          Measurable (fun ω ↦ (stoppedValue Bc τcn ω) ^ 2) := by
        exact hStopMeas.pow_const 2
      have hStopSqAesm :
          AEStronglyMeasurable (fun ω ↦ (stoppedValue Bc τcn ω) ^ 2) μ := by
        exact hStopSqMeas.aestronglyMeasurable
      refine Integrable.mono' (g := fun _ : Ω ↦ max (a ^ 2) (b ^ 2)) (integrable_const _) ?_ ?_
      · exact hStopSqAesm
      · exact hBoundAe
    have hIntTime : Integrable (fun ω ↦ ENNReal.toReal (τcn ω)) μ := by
      -- Proof comment: the truncation `τ ∧ n` is pointwise bounded by the deterministic horizon.
      refine Integrable.mono' (g := fun _ : Ω ↦ (n : ℝ)) (integrable_const _) ?_ ?_
      · exact ((hτc.min_const n).measurable'.aemeasurable.ennreal_toReal.aestronglyMeasurable)
      · exact Filter.Eventually.of_forall fun ω ↦ by
          have hle : τcn ω ≤ (n : ENNReal) := by simp [τcn]
          have hnonneg : 0 ≤ ENNReal.toReal (τcn ω) := ENNReal.toReal_nonneg
          rw [Real.norm_of_nonneg hnonneg]
          exact ENNReal.toReal_mono (by simp) hle
    have hIntegralSub :
        ∫ ω, (stoppedValue Bc τcn ω) ^ 2 - ENNReal.toReal (τcn ω) ∂μ =
          (∫ ω, (stoppedValue Bc τcn ω) ^ 2 ∂μ) -
            ∫ ω, ENNReal.toReal (τcn ω) ∂μ := by
      exact integral_sub hIntSq hIntTime
    have :
        (∫ ω, (stoppedValue Bc τcn ω) ^ 2 ∂μ) -
            ∫ ω, ENNReal.toReal (τcn ω) ∂μ = 0 := by
      simpa [hIntegralSub] using hSubEq
    linarith
  constructor
  · -- Proof comment: transport the first stopped-moment identity back from `Bc` to `B`.
    have hIntEq :
        ∫ ω, stoppedValue B τn ω ∂μ = ∫ ω, stoppedValue Bc τcn ω ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hTransport] with ω hω
      exact hω.2.1
    exact hIntEq.trans hFirstBc
  · -- Proof comment: transport the second stopped-moment identity and the truncated clock back
    -- from `Bc` to the original Brownian motion.
    have hStopSqEq :
        ∫ ω, (stoppedValue B τn ω) ^ 2 ∂μ =
          ∫ ω, (stoppedValue Bc τcn ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hTransport] with ω hω
      rw [hω.2.1]
    have hTimeEq :
        ∫ ω, ENNReal.toReal (τn ω) ∂μ =
          ∫ ω, ENNReal.toReal (τcn ω) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hTransport] with ω hω
      exact hω.2.2
    exact hStopSqEq.trans (hSecondBc.trans hTimeEq.symm)

/-- Helper for Exercise 21.2.4: the exact two-sided boundary hit and exact stopped value agree
almost surely with the everywhere-continuous Brownian modification. -/
private lemma twoSidedBoundaryExact_ae_eq_continuousVersion
    (hB : IsBrownianMotion μ B) {a b : ℝ} :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    ∀ᵐ ω ∂μ,
      τ ω = τc ω ∧
        stoppedValue B τ ω = stoppedValue Bc τc ω := by
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  have hτ :
      τ ω = τc ω := by
    -- Proof comment: pathwise equality of all time slices identifies the exact two-point hitting
    -- time.
    simpa [τ, τc, Bc] using
      (twoSidedBoundaryHittingTime_eq_of_forall_eq
        (X := B) (Y := Bc) (a := a) (b := b) (ω := ω) fun t ↦ (hω t).symm)
  have hidx :
      (τ ω).untopA = (τc ω).untopA := by
    simpa using congrArg WithTop.untopA hτ
  refine ⟨hτ, ?_⟩
  -- Proof comment: after identifying the exact hitting times, the stopped values only differ by
  -- evaluating pointwise-equal paths at the same random index.
  calc
    stoppedValue B τ ω = B (τ ω).untopA ω := rfl
    _ = Bc (τ ω).untopA ω := by simpa using (hω (τ ω).untopA).symm
    _ = Bc (τc ω).untopA ω := by rw [hidx]
    _ = stoppedValue Bc τc ω := rfl

/-- Helper for Exercise 21.2.4: truncating an `ENNReal` clock by deterministic horizons and then
taking the supremum recovers the original clock. -/
private lemma iSup_min_natCast_eq (x : ENNReal) :
    (⨆ n : ℕ, min x (n : ENNReal)) = x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simpa using ENNReal.iSup_natCast
  · rcases WithTop.ne_top_iff_exists.mp hx with ⟨t, rfl⟩
    refine le_antisymm ?_ ?_
    · exact iSup_le fun n ↦ min_le_left _ _
    · let N : ℕ := Nat.ceil (t : ℝ)
      have hN_real : (t : ℝ) ≤ N := Nat.le_ceil (t : ℝ)
      have hN : (t : ENNReal) ≤ (N : ENNReal) := by
        exact_mod_cast hN_real
      have hmin : min (t : ENNReal) (N : ENNReal) = (t : ENNReal) := min_eq_left hN
      exact le_iSup_of_le N (by simpa [hmin])

/-- Helper for Exercise 21.2.4: the two-sided Brownian boundary hit is almost surely finite. This
earlier owner keeps the truncation-limit lemmas dependency-closed. -/
private lemma ae_ne_top_twoSidedBoundaryHittingTime
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤ := by
  -- Route correction: own the almost-sure finiteness fact before the convergence lemmas so they
  -- no longer forward-reference the later public theorem.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let missEvent : Set Ω := {ω | τ ω = ⊤}
  have hab : a ≤ b := by
    linarith
  have hzero : ∀ ω : Ω, B 0 ω = 0 := by
    intro ω
    simpa using congrFun hB.zero ω
  have hMissUpper :
      ∀ n : ℕ, μ.real missEvent ≤
        (b - a) * (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)))⁻¹ := by
    intro n
    let t : NNReal := n + 1
    let slice : Set Ω := {ω | B t ω ∈ Set.Ioo a b}
    have ht_ne_zero : t ≠ 0 := by
      norm_num [t]
    have hsubset_ae : missEvent ≤ᵐ[μ] slice := by
      -- Proof comment: on continuous Brownian paths, missing both barriers forever forces every
      -- deterministic observation time to stay inside `(a, b)`.
      filter_upwards [hB.continuous_paths] with ω hωcont
      intro hωmiss
      exact mem_Ioo_of_twoSidedBoundaryHittingTime_eq_top
        (B := B)
        (ω := ω)
        (hcont := by simpa [processPath] using hωcont)
        (hzero := hzero ω)
        ha
        hb
        hωmiss
        t
    have hμ_le : μ missEvent ≤ μ slice := measure_mono_ae hsubset_ae
    have hreal_le : μ.real missEvent ≤ μ.real slice := by
      exact ENNReal.toReal_mono (measure_ne_top _ _) hμ_le
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ :=
      hB.gaussian_marginal (by positivity)
    have hSliceReal : μ.real slice = (gaussianReal 0 t).real (Set.Ioo a b) := by
      have hSlice :
          μ slice = gaussianReal 0 t (Set.Ioo a b) := by
        calc
          μ slice = μ (B t ⁻¹' Set.Ioo a b) := by
            rfl
          _ = Measure.map (B t) μ (Set.Ioo a b) := by
            rw [Measure.map_apply (hB.stronglyMeasurable t).measurable measurableSet_Ioo]
          _ = gaussianReal 0 t (Set.Ioo a b) := by
            rw [hLaw.map_eq]
      simpa [slice, MeasureTheory.Measure.real_def] using congrArg ENNReal.toReal hSlice
    have hreal_le' : μ.real missEvent ≤ (gaussianReal 0 t).real (Set.Ioo a b) := by
      rwa [hSliceReal] at hreal_le
    have hIoo_le :
        (gaussianReal 0 t).real (Set.Ioo a b) ≤
          (b - a) * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
      calc
        (gaussianReal 0 t).real (Set.Ioo a b)
            ≤ (gaussianReal 0 t).real (Set.Icc a b) :=
              MeasureTheory.measureReal_mono
                (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩)
                (measure_ne_top _ _)
        _ ≤ (b - a) * (Real.sqrt (2 * Real.pi * t))⁻¹ :=
              gaussianIntervalMeasure_le_peak_mul_length (a := a) (b := b) hab ht_ne_zero
    simpa [t] using hreal_le'.trans hIoo_le
  have hUpperTendsto :
      Tendsto
        (fun n : ℕ ↦ (b - a) * (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)))⁻¹)
        atTop
        (nhds 0) := by
    have hCastSucc : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hsqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (2 * Real.pi * (n + 1 : ℝ))) atTop atTop := by
      exact Real.tendsto_sqrt_atTop.comp
        (hCastSucc.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
    have hinv :
        Tendsto (fun n : ℕ ↦ (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)))⁻¹) atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.const_mul (b - a)
  have hMissTendsto :
      Tendsto (fun _ : ℕ ↦ μ.real missEvent) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hUpperTendsto
      ?_
      ?_
    · intro n
      exact MeasureTheory.measureReal_nonneg
    · intro n
      exact hMissUpper n
  have hMissRealZero : μ.real missEvent = 0 := by
    simpa using tendsto_nhds_unique tendsto_const_nhds hMissTendsto
  have hMissZero : μ missEvent = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff (x := μ missEvent)).mp <| by
      simpa [MeasureTheory.Measure.real_def] using hMissRealZero).resolve_right (measure_ne_top _ _)
  have hHitAe : ∀ᵐ ω ∂μ, ω ∉ missEvent := by
    simpa [missEvent] using compl_mem_ae_iff.mpr hMissZero
  simpa [τ, missEvent] using hHitAe

/-- Helper for Exercise 21.2.4: the first stopped-moment integrals at `τ ∧ n` converge to the
exact stopped first moment. -/
lemma twoSidedBoundaryStoppedValueTruncationIntegral_tendsto
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let hBc : IsBrownianMotion μ Bc :=
      brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
    Tendsto (fun n : ℕ ↦ ∫ ω, stoppedValue B (τn n) ω ∂μ) atTop
      (𝓝 (∫ ω, stoppedValue B τ ω ∂μ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
  have hτc :
      IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
    -- Proof comment: the exact stopping-time owner is available on the everywhere-continuous
    -- modification `Bc`.
    simpa [τc] using
      (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := Bc) hBc.stronglyMeasurable
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
  have hBcStrong :
      StronglyAdapted (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    Filtration.stronglyAdapted_natural (u := Bc) hBc.stronglyMeasurable
  have hBcProg :
      ProgMeasurable (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    hBcStrong.progMeasurable_of_continuous
      (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
  have hMeas :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ stoppedValue B (τn n) ω) μ := by
    intro n
    have hMeasBc :
        Measurable (stoppedValue Bc (fun ω ↦ min (τc ω) (n : ENNReal))) := by
      exact (measurable_stoppedValue hBcProg (hτc.min_const n)).mono
        (hτc.min_const n).measurableSpace_le le_rfl
    have hEqAe :
        (fun ω ↦ stoppedValue B (τn n) ω) =ᵐ[μ]
          fun ω ↦ stoppedValue Bc (fun ω' ↦ min (τc ω') (n : ENNReal)) ω := by
      filter_upwards
        [twoSidedBoundaryTruncation_ae_eq_continuousVersion
          (μ := μ) (B := B) (hB := hB) (a := a) (b := b) n]
        with ω hω
      exact hω.2.1
    exact hMeasBc.aestronglyMeasurable.congr hEqAe.symm
  have hBound :
      ∀ n : ℕ,
        ∀ᵐ ω ∂μ,
          ‖stoppedValue B (τn n) ω‖ ≤ max |a| |b| := by
    intro n
    have hab : a ≤ b := by
      linarith
    filter_upwards
      [truncatedTwoSidedBoundaryStoppedValue_mem_uIcc_ae
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb n]
      with ω hω
    have hIcc : stoppedValue B (τn n) ω ∈ Set.Icc a b := by
      simpa [τ, τn, Set.uIcc_of_le hab] using hω
    simpa [Real.norm_eq_abs] using abs_le_max_abs_abs hIcc.1 hIcc.2
  have hPointwise :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ stoppedValue B (τn n) ω) atTop
          (𝓝 (stoppedValue B τ ω)) := by
    filter_upwards
      [ae_ne_top_twoSidedBoundaryHittingTime (μ := μ) (B := B) hB (a := a) (b := b) ha hb]
      with ω hωτ
    rcases WithTop.ne_top_iff_exists.mp hωτ with ⟨t, ht⟩
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          stoppedValue B (τn n) ω = stoppedValue B τ ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨Nat.ceil (t : ℝ), ?_⟩
      intro n hn
      have htn_real : (t : ℝ) ≤ n := le_trans (Nat.le_ceil (t : ℝ)) (by exact_mod_cast hn)
      have htn : (t : ENNReal) ≤ (n : ENNReal) := by
        exact_mod_cast htn_real
      have hmin : min ((t : ENNReal)) (n : ENNReal) = (t : ENNReal) := min_eq_left htn
      have ht' : τ ω = (t : ENNReal) := by
        simpa [τ] using ht.symm
      simpa [stoppedValue, τ, τn, ht', hmin]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hEventually) tendsto_const_nhds
  -- Proof comment: the truncated stopped values are uniformly bounded in `[a,b]`, so dominated
  -- convergence upgrades the almost-sure eventual equality into convergence of expectations.
  exact MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun _ : Ω ↦ max |a| |b|)
    hMeas (integrable_const _) hBound hPointwise

/-- Helper for Exercise 21.2.4: the second stopped-moment integrals at `τ ∧ n` converge to the
exact stopped second moment. -/
lemma twoSidedBoundaryStoppedValueSqTruncationIntegral_tendsto
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
    Tendsto (fun n : ℕ ↦ ∫ ω, (stoppedValue B (τn n) ω) ^ 2 ∂μ) atTop
      (𝓝 (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
  have hMeasBase :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ stoppedValue B (τn n) ω) μ := by
    intro n
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let hBc : IsBrownianMotion μ Bc :=
      brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    have hτc :
        IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
      simpa [τc] using
        (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
          (X := Bc) hBc.stronglyMeasurable
          (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
    have hBcStrong :
        StronglyAdapted (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
      Filtration.stronglyAdapted_natural (u := Bc) hBc.stronglyMeasurable
    have hBcProg :
        ProgMeasurable (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
      hBcStrong.progMeasurable_of_continuous
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
    have hMeasBc :
        Measurable (stoppedValue Bc (fun ω ↦ min (τc ω) (n : ENNReal))) := by
      exact (measurable_stoppedValue hBcProg (hτc.min_const n)).mono
        (hτc.min_const n).measurableSpace_le le_rfl
    have hEqAe :
        (fun ω ↦ stoppedValue B (τn n) ω) =ᵐ[μ]
          fun ω ↦ stoppedValue Bc (fun ω' ↦ min (τc ω') (n : ENNReal)) ω := by
      filter_upwards
        [twoSidedBoundaryTruncation_ae_eq_continuousVersion
          (μ := μ) (B := B) (hB := hB) (a := a) (b := b) n]
        with ω hω
      exact hω.2.1
    exact hMeasBc.aestronglyMeasurable.congr hEqAe.symm
  have hMeasSq :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ (stoppedValue B (τn n) ω) ^ 2) μ := by
    intro n
    exact (AEMeasurable.pow_const (hMeasBase n).aemeasurable 2).aestronglyMeasurable
  have hBound :
      ∀ n : ℕ,
        ∀ᵐ ω ∂μ,
          ‖(stoppedValue B (τn n) ω) ^ 2‖ ≤ (max |a| |b|) ^ 2 := by
    intro n
    have hM_nonneg : 0 ≤ max |a| |b| := by positivity
    filter_upwards
      [truncatedTwoSidedBoundaryStoppedValue_mem_uIcc_ae
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb n]
      with ω hω
    have hab : a ≤ b := by
      linarith
    have hIcc : stoppedValue B (τn n) ω ∈ Set.Icc a b := by
      simpa [τ, τn, Set.uIcc_of_le hab] using hω
    have hAbs : |stoppedValue B (τn n) ω| ≤ max |a| |b| := abs_le_max_abs_abs hIcc.1 hIcc.2
    have hSq :
        (stoppedValue B (τn n) ω) ^ 2 ≤ (max |a| |b|) ^ 2 := by
      have hAbs' : |stoppedValue B (τn n) ω| ≤ |(max |a| |b|)| := by
        simpa [abs_of_nonneg hM_nonneg] using hAbs
      exact sq_le_sq.2 hAbs'
    have hSqNonneg : 0 ≤ (stoppedValue B (τn n) ω) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hSqNonneg]
    exact hSq
  have hPointwise :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ (stoppedValue B (τn n) ω) ^ 2) atTop
          (𝓝 ((stoppedValue B τ ω) ^ 2)) := by
    filter_upwards
      [ae_ne_top_twoSidedBoundaryHittingTime (μ := μ) (B := B) hB (a := a) (b := b) ha hb]
      with ω hωτ
    rcases WithTop.ne_top_iff_exists.mp hωτ with ⟨t, ht⟩
    have hEventuallyBase :
        ∀ᶠ n : ℕ in atTop,
          stoppedValue B (τn n) ω = stoppedValue B τ ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨Nat.ceil (t : ℝ), ?_⟩
      intro n hn
      have htn_real : (t : ℝ) ≤ n := le_trans (Nat.le_ceil (t : ℝ)) (by exact_mod_cast hn)
      have htn : (t : ENNReal) ≤ (n : ENNReal) := by
        exact_mod_cast htn_real
      have hmin : min ((t : ENNReal)) (n : ENNReal) = (t : ENNReal) := min_eq_left htn
      have ht' : τ ω = (t : ENNReal) := by
        simpa [τ] using ht.symm
      simpa [stoppedValue, τ, τn, ht', hmin]
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          (stoppedValue B (τn n) ω) ^ 2 = (stoppedValue B τ ω) ^ 2 :=
      hEventuallyBase.mono fun _ hn ↦ by simp [hn]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hEventually) tendsto_const_nhds
  -- Proof comment: the same eventual equality argument works for the squared stopped values once
  -- the uniform square bound is recorded.
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : Ω ↦ (max |a| |b|) ^ 2) hMeasSq (integrable_const _) hBound hPointwise

/-- Helper for Exercise 21.2.4: the truncated time expectations converge to the exact two-sided
boundary hitting-time expectation. -/
lemma twoSidedBoundaryHittingTimeTruncationIntegral_tendsto
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let hBc : IsBrownianMotion μ Bc :=
      brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
    let τcn : ℕ → Ω → ENNReal := fun n ω ↦ min (τc ω) (n : ENNReal)
    Tendsto (fun n : ℕ ↦ ∫ ω, ENNReal.toReal (τn n ω) ∂μ) atTop
      (𝓝 (∫ ω, ENNReal.toReal (τ ω) ∂μ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
  let τcn : ℕ → Ω → ENNReal := fun n ω ↦ min (τc ω) (n : ENNReal)
  have hτc :
      IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
    simpa [τc] using
      (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := Bc) hBc.stronglyMeasurable
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
  have hStageEq :
      ∀ n : ℕ,
        ∫ ω, ENNReal.toReal (τn n ω) ∂μ =
          ∫ ω, ENNReal.toReal (τcn n ω) ∂μ := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards
      [twoSidedBoundaryTruncation_ae_eq_continuousVersion
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b) n]
      with ω hω
    exact hω.2.2
  have hExactEq :
      ∫ ω, ENNReal.toReal (τ ω) ∂μ =
        ∫ ω, ENNReal.toReal (τc ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards
      [twoSidedBoundaryExact_ae_eq_continuousVersion
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b)]
      with ω hω
    simpa using congrArg ENNReal.toReal hω.1
  have hStageLimit :
      Tendsto (fun n : ℕ ↦ ∫ ω, ENNReal.toReal (τn n ω) ∂μ) atTop
        (𝓝 (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ)) := by
    have hSquareLimit :=
      twoSidedBoundaryStoppedValueSqTruncationIntegral_tendsto
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb
    have hCong :
        (fun n : ℕ ↦ ∫ ω, ENNReal.toReal (τn n ω) ∂μ) =
          fun n : ℕ ↦ ∫ ω, (stoppedValue B (τn n) ω) ^ 2 ∂μ := by
      funext n
      simpa [τ, τn] using
        (twoSidedExitMomentIdentitiesAtTruncation
          (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb n).2.symm
    simpa [hCong] using hSquareLimit
  have hStageLimitBc :
      Tendsto (fun n : ℕ ↦ ∫ ω, ENNReal.toReal (τcn n ω) ∂μ) atTop
        (𝓝 (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ)) := by
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ hStageEq n) hStageLimit
  have hTimeLintegral :
      ∫⁻ ω, τc ω ∂μ = ENNReal.ofReal (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ) := by
    have hτcnMeas : ∀ n : ℕ, Measurable (τcn n) := by
      intro n
      exact (hτc.min_const n).measurable'
    have hτcnMono :
        ∀ᵐ ω ∂μ, Monotone fun n : ℕ ↦ τcn n ω := by
      refine Filter.Eventually.of_forall fun ω m n hmn ↦ ?_
      exact min_le_min le_rfl (by exact_mod_cast hmn)
    have hLintegralSup :
        ∫⁻ ω, τc ω ∂μ = ⨆ n : ℕ, ∫⁻ ω, τcn n ω ∂μ := by
      calc
        ∫⁻ ω, τc ω ∂μ = ∫⁻ ω, (⨆ n : ℕ, τcn n ω) ∂μ := by
          congr with ω
          simp [τc, τcn, iSup_min_natCast_eq]
        _ = ⨆ n : ℕ, ∫⁻ ω, τcn n ω ∂μ := by
          simpa using
            MeasureTheory.lintegral_iSup' (μ := μ) (f := fun n ω ↦ τcn n ω)
              (fun n ↦ (hτcnMeas n).aemeasurable) hτcnMono
    have hStageIntegrable :
        ∀ n : ℕ, Integrable (fun ω ↦ ENNReal.toReal (τcn n ω)) μ := by
      intro n
      refine Integrable.mono' (g := fun _ : Ω ↦ (n : ℝ)) (integrable_const _) ?_ ?_
      · exact ((hτc.min_const n).measurable'.aemeasurable.ennreal_toReal.aestronglyMeasurable)
      · exact Filter.Eventually.of_forall fun ω ↦ by
          have hle : τcn n ω ≤ (n : ENNReal) := by simp [τcn]
          have hnonneg : 0 ≤ ENNReal.toReal (τcn n ω) := ENNReal.toReal_nonneg
          rw [Real.norm_of_nonneg hnonneg]
          exact ENNReal.toReal_mono (by simp) hle
    have hStageNonneg :
        ∀ n : ℕ, 0 ≤ᵐ[μ] fun ω ↦ ENNReal.toReal (τcn n ω) := by
      intro n
      exact Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
    have hStageLintegral :
        ∀ n : ℕ,
          ∫⁻ ω, τcn n ω ∂μ =
            ENNReal.ofReal (∫ ω, ENNReal.toReal (τcn n ω) ∂μ) := by
      intro n
      calc
        ∫⁻ ω, τcn n ω ∂μ
            = ∫⁻ ω, ENNReal.ofReal (ENNReal.toReal (τcn n ω)) ∂μ := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun ω ↦ by simp [τcn]
        _ = ENNReal.ofReal (∫ ω, ENNReal.toReal (τcn n ω) ∂μ) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (hStageIntegrable n) (hStageNonneg n)
    have hStageLintegralMono :
        Monotone fun n : ℕ ↦ ∫⁻ ω, τcn n ω ∂μ := by
      intro m n hmn
      exact MeasureTheory.lintegral_mono fun ω ↦ min_le_min le_rfl (by exact_mod_cast hmn)
    have hStageLintegralTendsto :
        Tendsto (fun n : ℕ ↦ ∫⁻ ω, τcn n ω ∂μ) atTop
          (𝓝 (ENNReal.ofReal (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ))) := by
      exact Tendsto.congr'
        (Filter.Eventually.of_forall fun n ↦ (hStageLintegral n).symm)
        (ENNReal.tendsto_ofReal hStageLimitBc)
    calc
      ∫⁻ ω, τc ω ∂μ = ⨆ n : ℕ, ∫⁻ ω, τcn n ω ∂μ := hLintegralSup
      _ = ENNReal.ofReal (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ) :=
        iSup_eq_of_tendsto hStageLintegralMono hStageLintegralTendsto
  have hTimeFinite :
      ∀ᵐ ω ∂μ, τc ω < ⊤ := by
    have hτcMeas : Measurable τc := hτc.measurable'
    have hTimeLintegral_ne_top : ∫⁻ ω, τc ω ∂μ ≠ ⊤ := by
      rw [hTimeLintegral]
      exact ENNReal.ofReal_ne_top
    exact MeasureTheory.ae_lt_top hτcMeas hTimeLintegral_ne_top
  have hTimeIntegralBc :
      ∫ ω, ENNReal.toReal (τc ω) ∂μ = ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ := by
    have hτcMeas : Measurable τc := hτc.measurable'
    have hNonneg : 0 ≤ ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ := by
      exact integral_nonneg fun _ ↦ sq_nonneg _
    calc
      ∫ ω, ENNReal.toReal (τc ω) ∂μ = (∫⁻ ω, τc ω ∂μ).toReal := by
          simpa using MeasureTheory.integral_toReal (μ := μ) hτcMeas.aemeasurable hTimeFinite
      _ = ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ := by
          rw [hTimeLintegral]
          simp [hNonneg]
  have hTimeIntegral :
      ∫ ω, ENNReal.toReal (τ ω) ∂μ = ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ := by
    exact hExactEq.trans hTimeIntegralBc
  -- Proof comment: the stage expectations converge to the finite stopped-square limit, and the
  -- monotone-convergence computation identifies that finite limit with the exact time integral.
  convert hStageLimit using 1
  rw [hTimeIntegral]

/-- Helper for Exercise 21.2.4: passing the bounded optional-stopping identities to the exact
boundary hitting time yields the exact first and second moment identities. -/
lemma twoSidedExitMomentIdentitiesAtExactTime
    (hB : IsBrownianMotion μ B) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    (∫ ω, stoppedValue B τ ω ∂μ = 0) ∧
      (∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ =
        ∫ ω, ENNReal.toReal (τ ω) ∂μ) := by
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τn : ℕ → Ω → ENNReal := fun n ω ↦ min (τ ω) (n : ENNReal)
  have hFirstTendsto :=
    twoSidedBoundaryStoppedValueTruncationIntegral_tendsto
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb
  have hSecondTendsto :=
    twoSidedBoundaryStoppedValueSqTruncationIntegral_tendsto
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb
  have hTimeTendsto :=
    twoSidedBoundaryHittingTimeTruncationIntegral_tendsto
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb
  have hFirstExact :
      ∫ ω, stoppedValue B τ ω ∂μ = 0 := by
    have hZeroTendsto :
        Tendsto (fun n : ℕ ↦ ∫ ω, stoppedValue B (τn n) ω ∂μ) atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa [τ, τn] using
          (twoSidedExitMomentIdentitiesAtTruncation
            (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb n).1.symm
    exact tendsto_nhds_unique hFirstTendsto hZeroTendsto
  have hSecondExact :
      ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ =
        ∫ ω, ENNReal.toReal (τ ω) ∂μ := by
    have hTimeAsSecond :
        Tendsto (fun n : ℕ ↦ ∫ ω, (stoppedValue B (τn n) ω) ^ 2 ∂μ) atTop
          (𝓝 (∫ ω, ENNReal.toReal (τ ω) ∂μ)) := by
      refine Tendsto.congr' ?_ hTimeTendsto
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa [τ, τn] using
          (twoSidedExitMomentIdentitiesAtTruncation
            (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb n).2.symm
    exact tendsto_nhds_unique hSecondTendsto hTimeAsSecond
  exact ⟨hFirstExact, hSecondExact⟩

end OptionalStoppingHelpers

/-- Helper for Exercise 21.2.4: for a Brownian motion and levels `a < 0 < b`, the first hitting
time of the boundary set `{a, b}` is almost surely finite. -/
theorem brownianMotion_twoSidedHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤ := by
  simpa using ae_ne_top_twoSidedBoundaryHittingTime
    (μ := μ) (B := B) hB (a := a) (b := b) ha hb

/-- Helper for Exercise 21.2.4: once the two-sided hit is almost surely finite, the exact stopped
value is almost surely the endpoint-valued piecewise random variable determined by the event
`{B_τ = b}`. -/
lemma twoSidedBoundaryStoppedValue_ae_eq_piecewise
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    ∀ᵐ ω ∂μ,
      stoppedValue B τ ω =
        ({ω' | stoppedValue B τ ω' = b} : Set Ω).piecewise (fun _ ↦ b) (fun _ ↦ a) ω := by
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  have hτ_ae :
      ∀ᵐ ω ∂μ, τ ω ≠ ⊤ :=
    brownianMotion_twoSidedHittingTime_ae_ne_top (hB := hB) (a := a) (b := b) ha hb
  filter_upwards [hB.continuous_paths, hτ_ae] with ω hωcont hωτ
  have hcont : Continuous fun t : NNReal ↦ B t ω := by
    simpa [processPath] using hωcont
  have hmem :
      stoppedValue B τ ω ∈ ({a, b} : Set ℝ) :=
    twoSidedBoundaryStoppedValue_mem_pair (B := B) (a := a) (b := b) (ω := ω) hcont hωτ
  rcases hmem with hωa | hωb
  · have hωnot :
        ω ∉ {ω' | stoppedValue B τ ω' = b} := by
      simp [hωa]
      linarith
    have hωa' :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = a := by
      simpa [τ] using hωa
    have hωne :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω ≠ b := by
      simpa [τ] using hωnot
    -- Proof comment: on the left-endpoint branch, the piecewise normal form selects `a`.
    simpa [Set.piecewise, hωne] using hωa'
  · have hωin :
        ω ∈ {ω' | stoppedValue B τ ω' = b} := by
      simpa [hωb]
    have hωb' :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = b := by
      simpa [τ] using hωin
    -- Proof comment: on the right-endpoint branch, the piecewise normal form selects `b`.
    simpa [Set.piecewise, hωb'] using hωb'

/-- Helper for Exercise 21.2.4: squaring the exact stopped value preserves the endpoint-valued
piecewise form, now with values `a^2` and `b^2`. -/
lemma twoSidedBoundaryStoppedValue_sq_ae_eq_piecewise
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    ∀ᵐ ω ∂μ,
      (stoppedValue B τ ω) ^ 2 =
        ({ω' | stoppedValue B τ ω' = b} : Set Ω).piecewise
          (fun _ ↦ b ^ 2) (fun _ ↦ a ^ 2) ω := by
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  filter_upwards
    [twoSidedBoundaryStoppedValue_ae_eq_piecewise (hB := hB) (a := a) (b := b) ha hb]
    with ω hω
  by_cases hωin : ω ∈ {ω' | stoppedValue B τ ω' = b}
  · have hωb : stoppedValue B τ ω = b := by
      simpa using hωin
    have hωb' :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = b := by
      simpa [τ] using hωb
    -- Proof comment: on the right-exit event, both sides reduce to `b^2`.
    simpa [Set.piecewise, hωb'] using congrArg (fun x : ℝ ↦ x ^ 2) hωb'
  · have hωa : stoppedValue B τ ω = a := by
      -- Proof comment: outside the right-exit event, the previous piecewise identity forces the
      -- stopped value to be `a`.
      simpa [τ, Set.piecewise, hωin] using hω
    have hωa' :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = a := by
      simpa [τ] using hωa
    have hωne :
        stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω ≠ b := by
      simpa [τ] using hωin
    have hab_ne : a ≠ b := by
      intro hab
      exact hωne (hωa'.trans hab)
    -- Proof comment: on the complementary event, both sides reduce to `a^2`.
    simpa [Set.piecewise, hωa', hab_ne] using congrArg (fun x : ℝ ↦ x ^ 2) hωa'

/-- Helper for Exercise 21.2.4: the exact stopped value at the two-sided boundary hit is
almost everywhere measurable because it agrees almost surely with the measurable stopped value of
the continuous Brownian modification. -/
private lemma twoSidedBoundaryStoppedValue_aemeasurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let hBc : IsBrownianMotion μ Bc :=
      brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    AEMeasurable (fun ω ↦ stoppedValue B τ ω) μ := by
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  have hτc :
      IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
    -- Proof comment: the exact hit time is measurable on the everywhere-continuous modification.
    simpa [τc] using
      (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := Bc) hBc.stronglyMeasurable
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
  have hBcStrong :
      StronglyAdapted (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    Filtration.stronglyAdapted_natural (u := Bc) hBc.stronglyMeasurable
  have hBcProg :
      ProgMeasurable (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    hBcStrong.progMeasurable_of_continuous
      (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
  have hMeasBc : Measurable (stoppedValue Bc τc) := by
    exact (measurable_stoppedValue hBcProg hτc).mono hτc.measurableSpace_le le_rfl
  have hEqAe :
      (fun ω ↦ stoppedValue B τ ω) =ᵐ[μ] fun ω ↦ stoppedValue Bc τc ω := by
    filter_upwards
      [twoSidedBoundaryExact_ae_eq_continuousVersion
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b)]
      with ω hω
    exact hω.2
  -- Proof comment: almost-sure transport from `B` to `Bc` turns the measurable `Bc` stopped
  -- value into an a.e.-measurable version of the exact stopped value for `B`.
  exact hMeasBc.aemeasurable.congr hEqAe.symm

/-- Helper for Exercise 21.2.4: integrating a null-measurable two-valued piecewise constant
function yields the corresponding probability-weighted average. -/
private lemma integral_piecewise_const_of_nullMeasurableSet
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (x y : ℝ) :
    ∫ ω, s.piecewise (fun _ ↦ x) (fun _ ↦ y) ω ∂μ =
      x * μ.real s + y * (1 - μ.real s) := by
  have hAe :
      s.piecewise (fun _ : Ω ↦ x) (fun _ ↦ y) =ᵐ[μ]
        (toMeasurable μ s).piecewise (fun _ : Ω ↦ x) (fun _ ↦ y) :=
    piecewise_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq.symm
  have hReal :
      μ.real (toMeasurable μ s) = μ.real s :=
    MeasureTheory.measureReal_congr hs.toMeasurable_ae_eq
  calc
    ∫ ω, s.piecewise (fun _ ↦ x) (fun _ ↦ y) ω ∂μ
        = ∫ ω, (toMeasurable μ s).piecewise (fun _ ↦ x) (fun _ ↦ y) ω ∂μ :=
          integral_congr_ae hAe
    _ = ∫ ω in toMeasurable μ s, x ∂μ + ∫ ω in (toMeasurable μ s)ᶜ, y ∂μ := by
          rw [MeasureTheory.integral_piecewise (measurableSet_toMeasurable μ s)
            (integrableOn_const) (integrableOn_const)]
    _ = μ.real (toMeasurable μ s) • x + μ.real ((toMeasurable μ s)ᶜ) • y := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
    _ = μ.real (toMeasurable μ s) * x + μ.real ((toMeasurable μ s)ᶜ) * y := by
          simp [smul_eq_mul]
    _ = x * μ.real (toMeasurable μ s) + y * μ.real ((toMeasurable μ s)ᶜ) := by
          ring
    _ = x * μ.real (toMeasurable μ s) + y * (1 - μ.real (toMeasurable μ s)) := by
          rw [MeasureTheory.probReal_compl_eq_one_sub (measurableSet_toMeasurable μ s)]
    _ = x * μ.real s + y * (1 - μ.real s) := by
          rw [hReal]

/-- Helper for Exercise 21.2.4: the probability that Brownian motion exits the interval `(a, b)`
through the upper endpoint `b` is `-a / (b - a)`. -/
theorem brownianMotion_twoSidedHittingTime_prob_hit_right
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    μ {ω | stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = b} =
      ENNReal.ofReal (-a / (b - a)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let E : Set Ω := {ω | stoppedValue B τ ω = b}
  have hFirstExact :
      ∫ ω, stoppedValue B τ ω ∂μ = 0 :=
    (twoSidedExitMomentIdentitiesAtExactTime
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb).1
  have hE_null : NullMeasurableSet E μ := by
    -- Proof comment: the right-exit event is the singleton preimage of the exact stopped value.
    simpa [E, τ] using
      (twoSidedBoundaryStoppedValue_aemeasurable
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b)).nullMeasurableSet_preimage
        (measurableSet_singleton b)
  have hIntegral :
      ∫ ω, E.piecewise (fun _ ↦ b) (fun _ ↦ a) ω ∂μ =
        b * μ.real E + a * (1 - μ.real E) := by
    -- Proof comment: the piecewise endpoint random variable integrates to the weighted endpoint
    -- average with weight `μ.real E`.
    simpa [E] using
      integral_piecewise_const_of_nullMeasurableSet (μ := μ) hE_null b a
  have hZeroEq : b * μ.real E + a * (1 - μ.real E) = 0 := by
    -- Proof comment: the exact first-moment identity says that this endpoint-weighted average is
    -- zero.
    calc
      b * μ.real E + a * (1 - μ.real E)
          = ∫ ω, E.piecewise (fun _ ↦ b) (fun _ ↦ a) ω ∂μ := hIntegral.symm
      _ = ∫ ω, stoppedValue B τ ω ∂μ := by
            symm
            exact integral_congr_ae
              (twoSidedBoundaryStoppedValue_ae_eq_piecewise
                (hB := hB) (a := a) (b := b) ha hb)
      _ = 0 := hFirstExact
  have hden : 0 < b - a := by
    linarith
  have hp : μ.real E = -a / (b - a) := by
    -- Proof comment: solve the affine endpoint equation for the right-exit mass.
    have hden_ne : b - a ≠ 0 := by
      linarith
    have hAffine : (b - a) * μ.real E = -a := by
      linarith [hZeroEq]
    exact (eq_div_iff hden_ne).2 (by simpa [mul_comm] using hAffine)
  have hp_nonneg : 0 ≤ -a / (b - a) := by
    have hnum : 0 ≤ -a := by
      linarith
    exact div_nonneg hnum hden.le
  exact
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ E) ENNReal.ofReal_ne_top).mp <| by
      simpa [MeasureTheory.Measure.real_def, hp_nonneg] using hp

/-- Exercise 21.2.4 (3): the expectation of the two-sided Brownian hitting time `τ_{a,b}` is
`-ab`. -/
theorem brownianMotion_twoSidedHittingTime_expectation_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∫ ω, ENNReal.toReal (hittingAfter B ({a, b} : Set ℝ) 0 ω) ∂μ = -a * b := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let E : Set Ω := {ω | stoppedValue B τ ω = b}
  have hSecondExact :
      ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ = ∫ ω, ENNReal.toReal (τ ω) ∂μ :=
    (twoSidedExitMomentIdentitiesAtExactTime
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb).2
  have hE_null : NullMeasurableSet E μ := by
    -- Proof comment: reuse the a.e.-measurable exact stopped value to make the right-exit event
    -- null measurable.
    simpa [E, τ] using
      (twoSidedBoundaryStoppedValue_aemeasurable
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b)).nullMeasurableSet_preimage
        (measurableSet_singleton b)
  have hProb :=
    brownianMotion_twoSidedHittingTime_prob_hit_right
      (μ := μ) (B := B) (hB := hB) (a := a) (b := b) ha hb
  have hden : 0 < b - a := by
    linarith
  have hp_nonneg : 0 ≤ -a / (b - a) := by
    have hnum : 0 ≤ -a := by
      linarith
    exact div_nonneg hnum hden.le
  have hp : μ.real E = -a / (b - a) := by
    -- Proof comment: convert the already-proved ENNReal probability formula back to real mass.
    simpa [E, MeasureTheory.Measure.real_def, hp_nonneg] using congrArg ENNReal.toReal hProb
  have hIntegralSq :
      ∫ ω, E.piecewise (fun _ ↦ b ^ 2) (fun _ ↦ a ^ 2) ω ∂μ =
        b ^ 2 * μ.real E + a ^ 2 * (1 - μ.real E) := by
    -- Proof comment: the squared endpoint-valued random variable integrates to the weighted
    -- average of `a^2` and `b^2`.
    simpa [E] using
      integral_piecewise_const_of_nullMeasurableSet (μ := μ) hE_null (b ^ 2) (a ^ 2)
  calc
    ∫ ω, ENNReal.toReal (τ ω) ∂μ = ∫ ω, (stoppedValue B τ ω) ^ 2 ∂μ := hSecondExact.symm
    _ = ∫ ω, E.piecewise (fun _ ↦ b ^ 2) (fun _ ↦ a ^ 2) ω ∂μ := by
          exact integral_congr_ae
            (twoSidedBoundaryStoppedValue_sq_ae_eq_piecewise
              (hB := hB) (a := a) (b := b) ha hb)
    _ = b ^ 2 * μ.real E + a ^ 2 * (1 - μ.real E) := hIntegralSq
    _ = b ^ 2 * (-a / (b - a)) + a ^ 2 * (1 - (-a / (b - a))) := by rw [hp]
    _ = -a * b := by
          have hden_ne : b - a ≠ 0 := by
            linarith
          field_simp [hden_ne]
          ring

end ProbabilityTheory
