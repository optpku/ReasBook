/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Corollary_22_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_4_1.LocalOneSidedBrownianHitting

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 21.10.3: a continuous square-variation process for `M` is an adapted
continuous increasing process `A` such that `M² - A` is a continuous local martingale. -/
structure IsContinuousSquareVariationProcess
    {μ : Measure Ω} (ℱ : Filtration NNReal ‹MeasurableSpace Ω›)
    (M A : NNReal → Ω → ℝ) : Prop where
  zero : A 0 = 0
  adapted : Adapted ℱ A
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  monotone : ∀ ω : Ω, Monotone (fun t : NNReal ↦ A t ω)
  local_martingale_sq_sub :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω ^ 2 - A t ω)

/-- Helper for Exercise 21.10.3: choose a continuous square-variation process for `M`, preferring
the deterministic clock `t ↦ t` when it already satisfies the bracket axioms. -/
def continuousSquareVariationProcess
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (_hM : IsContinuousLocalMartingale ℱ μ M) :
    NNReal → Ω → ℝ :=
  if _htime :
      IsContinuousSquareVariationProcess (μ := μ) ℱ M
        (fun t : NNReal => fun _ : Ω => (t : ℝ)) then
    fun t : NNReal => fun _ : Ω => (t : ℝ)
  else if hex : ∃ A : NNReal → Ω → ℝ, IsContinuousSquareVariationProcess (μ := μ) ℱ M A then
    Classical.choose hex
  else
    fun _ _ ↦ 0

/-- Helper for Exercise 21.10.3: if the deterministic clock already is a square-variation
process, then `continuousSquareVariationProcess hM` returns that clock. -/
lemma continuousSquareVariationProcess_eq_time
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hTime :
      IsContinuousSquareVariationProcess (μ := μ) ℱ M
        (fun t : NNReal => fun _ : Ω => (t : ℝ))) :
    continuousSquareVariationProcess hM = (fun t : NNReal => fun _ : Ω => (t : ℝ)) := by
  -- Proof comment: once the first chooser branch is available, the fallback branches disappear.
  classical
  simp [continuousSquareVariationProcess, hTime]

/-- Helper for Exercise 21.10.3: timewise almost-sure equality preserves the martingale property
once the target process is already known to be strongly adapted. -/
lemma martingale_congr_ae
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hN_stronglyAdapted : StronglyAdapted ℱ N) (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  -- Proof comment: rewrite the conditional expectation of `N t` to `M t`, apply the martingale
  -- identity for `M`, and then rewrite the time-`s` slice back to `N s`.
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (hMN t)).symm.trans ((hM.condExp_ae_eq hst).trans (hMN s))

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 21.10.3: deterministic stopping at time `n` is evaluation at `min t n`. -/
lemma stoppedProcess_constTime_eq_min
    {M : NNReal → Ω → ℝ} (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t = M (min t n) := by
  ext ω
  -- Proof comment: unfold deterministic stopping and split on whether `t ≤ n`.
  rw [stoppedProcess]
  change M ((min (t : ENNReal) n).untopA) ω = M (min t n) ω
  by_cases ht : t ≤ n
  · have hmin : min (t : ENNReal) n = t := by
      exact min_eq_left (by exact_mod_cast ht)
    have htop : (t : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (t : ENNReal) htop = t := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (t : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_left ht]
  · have hnle : n ≤ t := le_of_not_ge ht
    have hmin : min (t : ENNReal) n = n := by
      exact min_eq_right (by exact_mod_cast hnle)
    have htop : (n : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (n : ENNReal) htop = n := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (n : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_right hnle]

/-- Helper for Exercise 21.10.3: conditioning the fixed terminal value `M n` along the clipped
filtration `ℱ (t ∧ n)` gives a martingale. -/
lemma martingale_condExp_constTime
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (fun t ω ↦ μ[M n | ℱ (min t n)] ω) ℱ μ := by
  refine ⟨?_, ?_⟩
  · intro t
    exact stronglyMeasurable_condExp.mono (ℱ.mono (min_le_left t n))
  · intro s t hst
    -- Proof comment: before `n` use the tower property; after `n` the conditional expectations
    -- are already constant at `M n`.
    by_cases hs : s ≤ n
    · have hsle : s ≤ min t n := le_min hst hs
      simpa [min_eq_left hs] using
        (condExp_condExp_of_le (ℱ.mono hsle) (ℱ.le (min t n)) :
          μ[μ[M n | ℱ (min t n)] | ℱ s] =ᵐ[μ] μ[M n | ℱ s])
    · have hnle : n ≤ s := le_of_not_ge hs
      have hnt : n ≤ t := hnle.trans hst
      have hnn :
          μ[M n | ℱ n] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
      have hEqt : (fun ω ↦ μ[M n | ℱ (min t n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnt] using hnn)
      have hEqs : (fun ω ↦ μ[M n | ℱ (min s n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnle] using hnn)
      have hconds :
          μ[M n | ℱ s] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le s)
          ((hM.stronglyMeasurable n).mono (ℱ.mono hnle)) (hM.integrable n)
      have hleft :
          μ[(fun ω ↦ μ[M n | ℱ (min t n)] ω) | ℱ s] =ᵐ[μ] μ[M n | ℱ s] :=
        condExp_congr_ae hEqt
      have hright :
          μ[M n | ℱ s] =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min s n)] ω := by
        exact (Filter.EventuallyEq.of_eq hconds).trans hEqs.symm
      exact hleft.trans hright

/-- Helper for Exercise 21.10.3: deterministic-time stopping agrees almost everywhere with the
conditional-expectation martingale built from the terminal slice. -/
lemma stoppedProcess_constTime_ae_eq_condExp
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min t n)] ω := by
  by_cases ht : t ≤ n
  · simpa [stoppedProcess_constTime_eq_min, min_eq_left ht] using (hM.condExp_ae_eq ht).symm
  · have hnle : n ≤ t := le_of_not_ge ht
    have hnn :
        μ[M n | ℱ n] = M n :=
      condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
    exact Filter.EventuallyEq.of_eq (by
      simpa [stoppedProcess_constTime_eq_min, min_eq_right hnle] using hnn.symm)

/-- Helper for Exercise 21.10.3: deterministic stopping turns a martingale into a uniformly
integrable martingale on a finite measure space. -/
lemma martingale_uniformIntegrable_stoppedProcess_constTime
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ ∧
      UniformIntegrable (stoppedProcess M (fun _ ↦ (n : ENNReal))) 1 μ := by
  let N : NNReal → Ω → ℝ := fun t ω ↦ μ[M n | ℱ (min t n)] ω
  have hN_mart : Martingale N ℱ μ := martingale_condExp_constTime hM n
  have hStopped_strong : StronglyAdapted ℱ (stoppedProcess M (fun _ ↦ (n : ENNReal))) := by
    intro t
    simpa [N, stoppedProcess_constTime_eq_min] using
      ((hM.stronglyMeasurable (min t n)).mono (ℱ.mono (min_le_left t n)))
  have hStopped_eq :
      ∀ t : NNReal, N t =ᵐ[μ] stoppedProcess M (fun _ ↦ (n : ENNReal)) t := by
    intro t
    exact (stoppedProcess_constTime_ae_eq_condExp hM n t).symm
  have hStopped_mart :
      Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ :=
    martingale_congr_ae hN_mart hStopped_strong hStopped_eq
  letI : SigmaFinite μ := by
    infer_instance
  have hUI_N : UniformIntegrable N 1 μ := by
    simpa [N] using
      (hM.integrable n).uniformIntegrable_condExp fun t : NNReal ↦ ℱ.le (min t n)
  exact ⟨hStopped_mart, hUI_N.ae_eq hStopped_eq⟩

/-- Helper for Exercise 21.10.3: on a finite measure space, deterministic times localize any
martingale. -/
lemma martingale_isLocalMartingale_of_isFiniteMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using
      martingale_uniformIntegrable_stoppedProcess_constTime (μ := μ) (ℱ := ℱ) hM
        (n := (n : NNReal))

/-- Helper for Exercise 21.10.3: covariance is unchanged by almost-everywhere replacement of
either argument. -/
private lemma covariance_congr_ae
    {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: rewrite both expectations by almost-sure equality, then rewrite the covariance
  -- integrand pointwise.
  have hIntX : μ[X] = μ[X'] := integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Exercise 21.10.3: the null set where the Brownian sample paths fail to be
continuous. -/
def brownianDiscontinuitySet
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (_hB : IsBrownianMotion μ B) : Set Ω :=
  {ω | ¬ Continuous (fun t : NNReal ↦ B t ω)}

/-- Helper for Exercise 21.10.3: the Brownian discontinuity set is null because Brownian paths
are almost surely continuous. -/
lemma brownianDiscontinuitySet_null
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    μ (brownianDiscontinuitySet (μ := μ) (B := B) hB) = 0 := by
  -- Proof comment: almost-sure continuity is exactly the statement that the bad set has measure
  -- zero.
  have hcont_ae : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB.continuous_paths
  simpa [brownianDiscontinuitySet] using (ae_iff.mp hcont_ae)

/-- Helper for Exercise 21.10.3: choose a measurable null superset of the Brownian discontinuity
set so the continuous patch stays measurable. -/
lemma brownianContinuousVersionExceptionSet_exists
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∃ N : Set Ω,
      brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆ N ∧ MeasurableSet N ∧ μ N = 0 := by
  -- Proof comment: enlarge the null bad set to a measurable null set once and for all.
  exact exists_measurable_superset_of_null
    (brownianDiscontinuitySet_null (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.10.3: the measurable exceptional set used to patch Brownian paths into
an everywhere-continuous version. -/
def brownianContinuousVersionExceptionSet
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) : Set Ω :=
  Classical.choose (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.10.3: the actual discontinuity set sits inside the chosen measurable
exceptional set. -/
lemma brownianDiscontinuitySet_subset_exceptionSet
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    brownianDiscontinuitySet (μ := μ) (B := B) hB ⊆
      brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).1

/-- Helper for Exercise 21.10.3: the chosen Brownian exceptional set is measurable. -/
lemma brownianContinuousVersionExceptionSet_measurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    MeasurableSet (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.1

/-- Helper for Exercise 21.10.3: the chosen Brownian exceptional set is null. -/
lemma brownianContinuousVersionExceptionSet_null
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    μ (brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB) = 0 :=
  (Classical.choose_spec
    (brownianContinuousVersionExceptionSet_exists (μ := μ) (B := B) hB)).2.2

/-- Helper for Exercise 21.10.3: patch Brownian motion by setting it equal to `0` on the chosen
null exceptional set. -/
def brownianContinuousVersion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    NNReal → Ω → ℝ :=
  fun t ω ↦
    if ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB then 0 else B t ω

/-- Helper for Exercise 21.10.3: each time slice of the patched Brownian motion is measurable. -/
lemma brownianContinuousVersion_measurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
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

/-- Helper for Exercise 21.10.3: every sample path of the patched Brownian motion is continuous.
-/
lemma brownianContinuousVersion_continuous
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
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

/-- Helper for Exercise 21.10.3: outside the exceptional set, the patched process agrees with the
original Brownian motion at every time. -/
lemma brownianContinuousVersion_ae_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
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

/-- Helper for Exercise 21.10.3: the patched process is a modification of the original Brownian
motion. -/
lemma brownianContinuousVersion_areModifications
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    AreModifications μ B (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: fixed-time almost-everywhere equality is exactly the modification relation.
  intro t
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  simpa using (hω t).symm

/-- Helper for Exercise 21.10.3: patching Brownian motion on a measurable null set preserves the
Brownian owner and yields an everywhere-continuous version. -/
lemma brownianContinuousVersion_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: the Brownian characterization is stable under fixed-time almost-everywhere
  -- modification, and the patch already has continuous sample paths by construction.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases hω : ω ∈ brownianContinuousVersionExceptionSet (μ := μ) (B := B) hB
    · simp [brownianContinuousVersion, hω]
    · simp [brownianContinuousVersion, hω, hB.zero]
  · exact
      (IsBrownianMotion.isGaussianProcess hB).congr
        (fun t ↦ brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.mean_zero hB t)
  · intro s t
    exact
      (covariance_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.covariance_eq hB s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 21.10.3: Brownian motion is a martingale in its natural filtration. -/
lemma brownianMartingale_natural_local
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    Martingale B (Filtration.natural B hB.stronglyMeasurable) μ := by
  -- Proof comment: split `B_t` into the past value `B_s` and the centered future increment, then
  -- kill the increment by independence from the natural filtration at time `s`.
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

/-- Helper for Exercise 21.10.3: the everywhere-continuous Brownian patch is a continuous local
martingale in its natural filtration. -/
lemma brownianContinuousVersion_isContinuousLocalMartingaleNatural
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsContinuousLocalMartingale
      (Filtration.natural
        (brownianContinuousVersion (μ := μ) (B := B) hB)
        (brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB).stronglyMeasurable)
      μ
      (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: once the patched process is Brownian again, the natural-filtration martingale
  -- theorem and the finite-measure localization lemma finish the owner bridge.
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB
  let ℱ := Filtration.natural Bc hBc.stronglyMeasurable
  have hMart : Martingale Bc ℱ μ :=
    brownianMartingale_natural_local (hB := hBc)
  refine
    { local_martingale := martingale_isLocalMartingale_of_isFiniteMeasure hMart
      continuous := ?_ }
  intro ω
  simpa [Bc] using brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 21.10.3: for the continuous Brownian patch, deterministic time is a valid
continuous square-variation process. -/
lemma brownianContinuousVersion_time_isContinuousSquareVariationProcess
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsContinuousSquareVariationProcess
      (μ := μ)
      (Filtration.natural
        (brownianContinuousVersion (μ := μ) (B := B) hB)
        (brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB).stronglyMeasurable)
      (brownianContinuousVersion (μ := μ) (B := B) hB)
      (fun t : NNReal => fun _ : Ω => (t : ℝ)) := by
  -- Proof comment: the compensated square of Brownian motion is a martingale, so after promoting
  -- that martingale to a local martingale the deterministic clock satisfies the bracket axioms.
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB
  let ℱ := Filtration.natural Bc hBc.stronglyMeasurable
  have hSqMart : Martingale (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ)) ℱ μ :=
    brownian_sq_sub_time_martingale (hB := hBc)
  refine
    { zero := by
        funext ω
        simp
      adapted := by
        exact adapted_const' ℱ (fun t : NNReal ↦ (t : ℝ))
      continuous := by
        intro ω
        simpa using continuous_subtype_val
      monotone := by
        intro ω s t hst
        exact_mod_cast hst
      local_martingale_sq_sub := ?_ }
  refine
    { local_martingale := martingale_isLocalMartingale_of_isFiniteMeasure hSqMart
      continuous := ?_ }
  intro ω
  simpa [Bc] using ((brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω).pow 2).sub
    continuous_subtype_val

/-- Helper for Exercise 21.10.3: between two `NNReal` times there is a nonnegative rational
time. -/
private lemma exists_nnrat_between {a b : NNReal} (hab : a < b) :
    ∃ q : ℚ≥0, a < (q : NNReal) ∧ (q : NNReal) < b := by
  -- Proof comment: choose an ordinary rational between the real endpoints and package its
  -- nonnegativity into a `ℚ≥0` witness.
  obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn (show (a : ℝ) < b by exact_mod_cast hab)
  refine ⟨⟨q, by exact_mod_cast (le_trans a.2 hqa.le)⟩, ?_, ?_⟩
  · exact_mod_cast hqa
  · exact_mod_cast hqb

/-- Helper for Exercise 21.10.3: on a continuous path, a finite level hitting time really hits
the target level. -/
private lemma stoppedValue_eq_level_of_continuous_hit
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (hcont : Continuous (fun t : NNReal ↦ B t ω))
    (hτ : brownianLevelHittingTime B b ω ≠ ⊤) :
    stoppedValue B (brownianLevelHittingTime B b) ω = b := by
  classical
  let hitSet : Set NNReal := {t | B t ω = b}
  have hhit : ∃ t : NNReal, B t ω = b :=
    (brownianLevelHittingTime_ne_top_iff_exists_eq (B := B) (b := b) (ω := ω)).1 hτ
  have hnonempty : hitSet.Nonempty := by
    rcases hhit with ⟨t, ht⟩
    exact ⟨t, ht⟩
  have hclosed : IsClosed hitSet := by
    simpa [hitSet] using (isClosed_singleton : IsClosed ({b} : Set ℝ)).preimage hcont
  have hbddBelow : BddBelow hitSet := by
    refine ⟨0, ?_⟩
    intro t ht
    exact bot_le
  have hsInf_mem : sInf hitSet ∈ hitSet := hclosed.csInf_mem hnonempty hbddBelow
  have hτ_eq : (brownianLevelHittingTime B b ω).untopA = sInf hitSet := by
    rw [brownianLevelHittingTime_eq_hittingAfter, hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ B i ω ∈ ({b} : Set ℝ)} = hitSet by
            ext t
            simp [hitSet, Set.mem_singleton_iff]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hhit with ⟨t, ht⟩
      exact ⟨t, bot_le, by simpa [Set.mem_singleton_iff] using ht⟩
  have hvalue : B (brownianLevelHittingTime B b ω).untopA ω = b := by
    rw [hτ_eq]
    exact hsInf_mem
  simpa [stoppedValue, hτ] using hvalue

/-- Helper for Exercise 21.10.3: along a continuous path, hitting the level `b` by time `u` is
equivalent to rational-time approximations of `b` on `[0,u]`. -/
private lemma brownianLevelHittingTime_le_iff_forall_nnrat_approx
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (hcont : Continuous (fun t : NNReal ↦ B t ω)) (u : NNReal) :
    brownianLevelHittingTime B b ω ≤ u ↔
      ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ u ∧
        |B (q : NNReal) ω - b| < (1 : ℝ) / (n + 1) := by
  constructor
  · intro hτu n
    let ε : ℝ := (1 : ℝ) / (n + 1)
    have hεpos : 0 < ε := by
      positivity
    let τ : ENNReal := brownianLevelHittingTime B b ω
    let t : NNReal := τ.untopA
    have hτne : τ ≠ ⊤ := by
      intro hτtop
      simpa [τ, hτtop] using hτu
    have htle : t ≤ u := by
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hτne
      have hcoe_t : ((t : NNReal) : ENNReal) = τ := by
        change (((τ.untopA : NNReal) : ENNReal) = τ)
        rw [← hs]
        change ((WithTop.untopD (Classical.arbitrary NNReal) (s : ENNReal) : NNReal) : ENNReal) =
          (s : ENNReal)
        simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := s))
      have ht_eq : t = s := by
        exact WithTop.coe_inj.mp (hcoe_t.trans hs.symm)
      rw [ht_eq]
      have hτu' : τ ≤ (u : ENNReal) := by
        simpa [τ] using hτu
      have hsle' : (s : ENNReal) ≤ (u : ENNReal) := by
        rw [← hs] at hτu'
        exact hτu'
      exact ENNReal.coe_le_coe.mp hsle'
    have htb : B t ω = b := by
      simpa [τ, t, stoppedValue] using
        stoppedValue_eq_level_of_continuous_hit
          (B := B) (b := b) (ω := ω) hcont hτne
    by_cases ht0 : t = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa [ht0] using htle
      · have hB0 : B 0 ω = b := by
          simpa [ht0] using htb
        simpa [hB0, ε] using hεpos
    · have htpos : 0 < t := by
        exact bot_lt_iff_ne_bot.mpr ht0
      let U : Set NNReal := {s : NNReal | B s ω ∈ Set.Ioo (b - ε) (b + ε)}
      have hUopen : IsOpen U := by
        simpa [U] using (isOpen_Ioo.preimage hcont)
      have htU : t ∈ U := by
        simpa [U, ε, htb] using hεpos
      have hUNhds : U ∈ 𝓝 t := hUopen.mem_nhds htU
      rcases mem_nhds_iff_exists_Ioo_subset' (show ∃ l : NNReal, l < t from ⟨0, htpos⟩)
          (show ∃ r : NNReal, t < r from ⟨t + 1, by simpa using lt_add_of_pos_right t zero_lt_one⟩)
          |>.1 hUNhds with ⟨l, r, ⟨hlt, htr⟩, hIoo⟩
      obtain ⟨q, hql, hqt⟩ := exists_nnrat_between (a := l) (b := t) hlt
      refine ⟨q, le_trans hqt.le htle, ?_⟩
      have hqU : (q : NNReal) ∈ U := hIoo ⟨hql, lt_trans hqt htr⟩
      rcases hqU with ⟨hqlo, hqhi⟩
      have hleft : -ε < B (q : NNReal) ω - b := by
        linarith
      have hright : B (q : NNReal) ω - b < ε := by
        linarith
      exact abs_lt.2 ⟨hleft, hright⟩
  · intro hApprox
    let R : Set ℝ := (fun t : NNReal ↦ B t ω) '' Set.Icc (0 : NNReal) u
    have hRclosed : IsClosed R := by
      simpa [R] using (IsCompact.image isCompact_Icc hcont).isClosed
    have hbClosure : b ∈ closure R := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      rcases hApprox n with ⟨q, hqu, hqε⟩
      refine ⟨B (q : NNReal) ω, ?_, ?_⟩
      · exact ⟨(q : NNReal), ⟨by simp, hqu⟩, rfl⟩
      · simpa [Real.dist_eq, abs_sub_comm] using lt_trans hqε hn
    have hbR : b ∈ R := by
      simpa [hRclosed.closure_eq] using hbClosure
    rcases hbR with ⟨t, htI, htb⟩
    exact (brownianLevelHittingTime_le_of_eq (B := B) (b := b) (ω := ω) (t := t) htb).trans
      (by exact_mod_cast htI.2)

/-- Helper for Exercise 21.10.3: if level `1` is hit almost surely in finite time, then the
stopped Brownian value equals `1` almost surely. -/
lemma stoppedValue_brownianLevelHitting_eq_one_ae_of_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hcont : ∀ ω, Continuous (fun t : NNReal ↦ B t ω))
    (hfinite : ∀ᵐ ω ∂μ, brownianLevelHittingTime B 1 ω ≠ ⊤) :
    stoppedValue B (brownianLevelHittingTime B 1) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
  filter_upwards [hfinite] with ω hω
  simpa using
    brownianLevelHittingTime_stoppedValue_eq_level
      (B := B) (b := (1 : ℝ)) (ω := ω) (hcont ω) hω

/-- Helper for Exercise 21.10.3: removing the finite `WithTop` wrapper from an `ENNReal`
coefficient recovers the underlying `NNReal` exactly. -/
private lemma untopA_coe_eq (t : NNReal) :
    WithTop.untopA ((t : ENNReal)) = t := by
  have hne : (t : ENNReal) ≠ ⊤ := by
    simp
  rw [WithTop.untopA_eq_untop hne]
  exact ENNReal.coe_inj.mp (WithTop.coe_untop (x := (t : ENNReal)) hne)

/-- Helper for Exercise 21.10.3: once a stopping time is almost surely finite, stopping the
deterministic clock `t ↦ t` agrees almost everywhere with `τ.toReal`. -/
lemma stoppedValue_timeProcess_ae_eq_toReal_of_ae_ne_top
    {μ : Measure Ω} {τ : Ω → ENNReal}
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    stoppedValue (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) τ =ᵐ[μ]
      fun ω ↦ (τ ω).toReal := by
  filter_upwards [hfinite] with ω hω
  -- Proof comment: on the finite branch, `stoppedValue` and `ENNReal.toReal` are both the same
  -- underlying nonnegative real time.
  cases hτω : τ ω with
  | top =>
      simp [hτω] at hω
  | coe t =>
      -- Proof comment: the finite `ENNReal` branch has no top-coercion left, so `untopA`
      -- returns the underlying `NNReal` exactly.
      simp [stoppedValue, hτω, untopA_coe_eq]

/-- Helper for Exercise 21.10.3: on a continuous path that starts below `b`, staying strictly
below `b` on `[0, T]` is equivalent to the level-`b` hitting time being larger than `T`. -/
lemma brownianLevelHittingTime_gt_iff_forall_lt_of_continuous
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (h0 : B 0 ω < b)
    (hcont : Continuous (fun t : NNReal ↦ B t ω))
    (T : NNReal) :
    T < brownianLevelHittingTime B b ω ↔
      ∀ t ∈ Set.Icc (0 : NNReal) T, B t ω < b := by
  constructor
  · intro hT t ht
    -- Proof comment: any time `t ≤ T` with `B t ≥ b` would force an earlier exact hit by
    -- continuity, contradicting `T < τ_b`.
    by_contra hnot
    have hbt : b ≤ B t ω := le_of_not_gt hnot
    have hlevel : b ∈ Set.Icc (B 0 ω) (B t ω) := ⟨le_of_lt h0, hbt⟩
    obtain ⟨s, hsIcc, hs_eq⟩ :=
      (intermediate_value_Icc (a := (0 : NNReal)) (b := t) ht.1 hcont.continuousOn) hlevel
    have hs_le_t : (s : ENNReal) ≤ (t : ENNReal) := by
      exact_mod_cast hsIcc.2
    have hτle : brownianLevelHittingTime B b ω ≤ (t : ENNReal) := by
      exact le_trans
        (brownianLevelHittingTime_le_of_eq (B := B) (b := b) (ω := ω) (t := s) hs_eq)
        hs_le_t
    have ht_le_T : (t : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast ht.2
    exact not_le_of_gt hT (le_trans hτle ht_le_T)
  · intro hBelow
    -- Proof comment: if `τ_b ≤ T`, then continuity recovers the exact hit before `T`, which
    -- contradicts the strict-below hypothesis at that hitting time.
    by_cases hτne : brownianLevelHittingTime B b ω = ⊤
    · simpa [hτne]
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτne
    have hUntop : (brownianLevelHittingTime B b ω).untopA = t := by
      rw [WithTop.untopA_eq_untop hτne]
      apply ENNReal.coe_inj.mp
      exact (WithTop.coe_untop (x := brownianLevelHittingTime B b ω) hτne).trans ht.symm
    have hhit : B t ω = b := by
      simpa [stoppedValue, hUntop] using
        brownianLevelHittingTime_stoppedValue_eq_level
          (B := B) (b := b) (ω := ω) hcont hτne
    have hT_lt_t : T < t := by
      by_contra hnot
      have htle : t ≤ T := le_of_not_gt hnot
      have hstrict : B t ω < b := hBelow t ⟨by positivity, htle⟩
      exact hstrict.ne hhit
    have hT_lt_t_ennreal : (T : ENNReal) < (t : ENNReal) := by
      exact_mod_cast hT_lt_t
    simpa [← ht] using hT_lt_t_ennreal

/-- Helper for Exercise 21.10.3: once level `1` is hit almost surely in finite time, the stopped
square has finite expectation because the stopped value is almost surely the constant `1`. -/
lemma brownianLevelHittingTime_one_stoppedSquare_ne_top_of_ae_ne_top
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hcont : ∀ ω, Continuous (fun t : NNReal ↦ B t ω))
    (hfinite : ∀ᵐ ω ∂μ, brownianLevelHittingTime B 1 ω ≠ ⊤) :
    (∫⁻ ω,
        ENNReal.ofReal ((stoppedValue B (brownianLevelHittingTime B 1) ω) ^ (2 : ℕ)) ∂μ) ≠ ∞ := by
  have hconst :
      (fun ω ↦
        ENNReal.ofReal ((stoppedValue B (brownianLevelHittingTime B 1) ω) ^ (2 : ℕ))) =ᵐ[μ]
        fun _ ↦ (1 : ℝ≥0∞) := by
    filter_upwards [stoppedValue_brownianLevelHitting_eq_one_ae_of_ae_ne_top hcont hfinite] with
      ω hω
    simp [hω]
  rw [lintegral_congr_ae hconst, lintegral_const]
  simp

/- Exercise 21.10.3 is `source-facing` existential content.

Domain-style sampling for the owner abstraction:
* `IsContinuousLocalMartingale` from Definition 21.66 is the chapter owner for the process `M`.
* `continuousSquareVariationProcess` is the exercise-local bracket chooser.
* `brownianLevelHittingTime` is the singleton-hitting companion used in the intended Brownian
  counterexample. -/

-- Proof sketch: the intended route is the standard continuous Brownian modification stopped at the
-- first hit of level `1`. This file now contains the generic stopping API, the singleton-hitting
-- API, and the local Brownian continuous-version owner bridge; the unresolved part is a
-- dependency-closed Brownian witness together with the level-one hitting-time finiteness and
-- infinite-first-moment facts, whose original owner modules currently lack built `.olean` files
-- in this workspace.
/-- Helper for Exercise 21.10.3: the level-one Brownian hitting time has infinite first moment. -/
lemma brownianLevelHittingTime_one_lintegral_eq_top
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (hcont : ∀ ω, Continuous (fun t : NNReal ↦ B t ω)) :
    ∫⁻ ω, ENNReal.ofReal ((brownianLevelHittingTime B 1 ω).toReal) ∂μ = ∞ := by
  let τ : Ω → ENNReal := brownianLevelHittingTime B 1
  have hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    simpa [τ] using brownianLevelHittingTime_ae_ne_top (μ := μ) (B := B) hB (by norm_num : 0 < (1 : ℝ))
  by_contra hfinite
  have hUpper :
      ∀ n : ℕ,
        ENNReal.ofReal (n + 1 : ℝ) ≤
          ∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ := by
    intro n
    let σ : Ω → ENNReal := fun ω ↦ hittingAfter B ({-((n + 1 : ℝ)), 1} : Set ℝ) 0 ω
    have hσ_stop :
        IsStoppingTime (Filtration.natural B hB.stronglyMeasurable) σ := by
      simpa [σ] using
        twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
          (hXsm := hB.stronglyMeasurable) (hXcont := hcont)
    have hσ_finite : ∀ᵐ ω ∂μ, σ ω ≠ ⊤ := by
      simpa [σ] using
        brownianMotion_twoSidedHittingTime_ae_ne_top
          (hB := hB) (a := -((n + 1 : ℝ))) (b := (1 : ℝ))
          (by linarith) (by norm_num)
    have hσ_lt_top : ∀ᵐ ω ∂μ, σ ω < ⊤ := by
      filter_upwards [hσ_finite] with ω hω
      exact lt_top_iff_ne_top.mpr hω
    have hσ_integral :
        ∫ ω, ENNReal.toReal (σ ω) ∂μ = (n + 1 : ℝ) := by
      simpa [σ] using
        brownianMotion_twoSidedHittingTime_expectation_eq
          (hB := hB) (a := -((n + 1 : ℝ))) (b := (1 : ℝ))
          (by linarith) (by norm_num)
    have hσ_lintegral_eq :
        ∫⁻ ω, ENNReal.ofReal ((σ ω).toReal) ∂μ = ENNReal.ofReal (n + 1 : ℝ) := by
      have htoReal :
          (∫⁻ ω, σ ω ∂μ).toReal = (n + 1 : ℝ) := by
        rw [← hσ_integral]
        exact (MeasureTheory.integral_toReal hσ_stop.measurable'.aemeasurable hσ_lt_top).symm
      have hlin_ne_top : ∫⁻ ω, σ ω ∂μ ≠ ∞ := by
        intro htop
        have : (0 : ℝ) = (n + 1 : ℝ) := by simpa [htop] using htoReal
        linarith
      calc
        ∫⁻ ω, ENNReal.ofReal ((σ ω).toReal) ∂μ = ∫⁻ ω, σ ω ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hσ_lt_top] with ω hω
          rw [ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hω)]
        _ = ENNReal.ofReal ((∫⁻ ω, σ ω ∂μ).toReal) := by
          rw [ENNReal.ofReal_toReal hlin_ne_top]
        _ = ENNReal.ofReal (n + 1 : ℝ) := by
          rw [htoReal]
    have hσ_le_τ :
        ∀ ω : Ω, σ ω ≤ τ ω := by
      intro ω
      by_cases hτω : τ ω = ⊤
      · simp [hτω]
      · have hhit :
            B (τ ω).untopA ω = 1 := by
          have hstop :
              stoppedValue B (brownianLevelHittingTime B 1) ω = 1 := by
            exact brownianLevelHittingTime_stoppedValue_eq_level (B := B) (b := (1 : ℝ))
              (ω := ω) (hcont ω) hτω
          simpa [τ, stoppedValue] using hstop
        have hσ_le_time :
            σ ω ≤ (τ ω).untopA := by
          simpa [σ] using
            (twoSidedBoundaryHittingTime_le_of_eq_left_or_right
              (B := B) (a := -((n + 1 : ℝ))) (b := (1 : ℝ))
              (ω := ω) (t := (τ ω).untopA) (Or.inr hhit))
        have htime_eq : (((τ ω).untopA : NNReal) : ENNReal) = τ ω := by
          rw [WithTop.untopA_eq_untop hτω]
          exact WithTop.coe_untop (x := τ ω) hτω
        exact le_trans hσ_le_time htime_eq.le
    have hmono :
        (fun ω ↦ ENNReal.ofReal ((σ ω).toReal)) ≤ᵐ[μ]
          fun ω ↦ ENNReal.ofReal ((τ ω).toReal) := by
      filter_upwards [hτ_finite] with ω hω
      have hσω : σ ω ≠ ⊤ := ne_top_of_le_ne_top hω (hσ_le_τ ω)
      exact ENNReal.ofReal_le_ofReal <|
        (ENNReal.toReal_le_toReal hσω hω).2 (hσ_le_τ ω)
    calc
      ENNReal.ofReal (n + 1 : ℝ)
          = ∫⁻ ω, ENNReal.ofReal ((σ ω).toReal) ∂μ := hσ_lintegral_eq.symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ := lintegral_mono_ae hmono
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ).toReal)
  have htoReal_le :
      (n + 1 : ℝ) ≤
        (∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ).toReal := by
    have htmp :
        (ENNReal.ofReal (n + 1 : ℝ)).toReal ≤
          (∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ).toReal :=
      (ENNReal.toReal_le_toReal (by simp : ENNReal.ofReal (n + 1 : ℝ) ≠ ∞) hfinite).2
        (hUpper n)
    have hleft : (ENNReal.ofReal (n + 1 : ℝ)).toReal = (n + 1 : ℝ) := by
      rw [ENNReal.toReal_ofReal]
      positivity
    exact hleft ▸ htmp
  linarith

/-- Exercise 21.10.3: there exists a continuous local martingale `M` with `M_0 = 0` and an almost
surely finite stopping time `τ` such that the stopped square variation has infinite expectation,
but the stopped second moment `E[M_τ^2]` is not infinite. -/
theorem exists_infinite_bracket_expectation_without_infinite_stopped_square_expectation :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω'),
      letI := mΩ'
      ∃ (μ : Measure Ω') (_ : IsProbabilityMeasure μ) (ℱ : Filtration NNReal mΩ')
        (M : NNReal → Ω' → ℝ) (τ : Ω' → ENNReal)
        (hM : IsContinuousLocalMartingale ℱ μ M),
        (∀ ω : Ω', M 0 ω = 0) ∧
          IsStoppingTime ℱ τ ∧
          (∀ᵐ ω ∂μ, τ ω ≠ ∞) ∧
          (∫⁻ ω,
              ENNReal.ofReal
                (stoppedValue (continuousSquareVariationProcess hM) τ ω) ∂μ) = ∞ ∧
          (∫⁻ ω, ENNReal.ofReal ((stoppedValue M τ ω) ^ (2 : ℕ)) ∂μ) ≠ ∞ := by
  let P0 : Measure Unit := Measure.dirac ()
  let X0 : ℕ → Unit → ℝ := fun _ _ ↦ 0
  obtain ⟨Ω', mΩ', P, W, hW, _τEmbed, _hτ0, _hτStop, _hτMono, _hLaw, _hSquare, _hIID⟩ :=
    exists_centered_iid_brownian_stopping_embedding (P := P0) (X := X0)
  refine ⟨Ω', mΩ', ?_⟩
  letI := mΩ'
  let μ : Measure Ω' := (P : Measure Ω')
  letI : IsProbabilityMeasure μ := by
    infer_instance
  let M : NNReal → Ω' → ℝ := brownianContinuousVersion (μ := μ) (B := W) hW
  let hMW : IsBrownianMotion μ M :=
    brownianContinuousVersion_isBrownianMotion (μ := μ) (B := W) hW
  let ℱ : Filtration NNReal mΩ' := Filtration.natural M hMW.stronglyMeasurable
  let τ : Ω' → ENNReal := brownianLevelHittingTime M 1
  let hM : IsContinuousLocalMartingale ℱ μ M :=
    brownianContinuousVersion_isContinuousLocalMartingaleNatural (μ := μ) (B := W) hW
  have hM_zero : ∀ ω : Ω', M 0 ω = 0 := by
    intro ω
    simpa [M] using congrFun hMW.zero ω
  have hτ_stop : IsStoppingTime ℱ τ := by
    simpa [ℱ, M] using
      brownianLevelHittingTime_isStoppingTime
        (μ := μ) (B := M) hMW (1 : ℝ)
  have hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ∞ := by
    simpa [τ, M] using
      brownianLevelHittingTime_ae_ne_top (μ := μ) (B := M) hMW (by norm_num : (0 : ℝ) < 1)
  have hStoppedSq :
      (∫⁻ ω, ENNReal.ofReal ((stoppedValue M τ ω) ^ (2 : ℕ)) ∂μ) ≠ ∞ := by
    simpa [τ, M] using
      brownianLevelHittingTime_one_stoppedSquare_ne_top_of_ae_ne_top
        (μ := μ) (B := M)
        (brownianContinuousVersion_continuous (μ := μ) (B := W) hW) hτ_finite
  have hA :
      IsContinuousSquareVariationProcess
        (μ := μ) ℱ M (fun t : NNReal => fun _ : Ω' => (t : ℝ)) := by
    simpa [ℱ, M] using
      brownianContinuousVersion_time_isContinuousSquareVariationProcess
        (μ := μ) (B := W) hW
  have hClock :
      continuousSquareVariationProcess hM =
        (fun t : NNReal => fun _ : Ω' => (t : ℝ)) := by
    exact continuousSquareVariationProcess_eq_time hM hA
  have hBracket :
      (∫⁻ ω,
          ENNReal.ofReal (stoppedValue (continuousSquareVariationProcess hM) τ ω) ∂μ) = ∞ := by
    calc
      (∫⁻ ω, ENNReal.ofReal (stoppedValue (continuousSquareVariationProcess hM) τ ω) ∂μ)
          = ∫⁻ ω, ENNReal.ofReal (stoppedValue (fun t : NNReal => fun _ : Ω' => (t : ℝ)) τ ω) ∂μ := by
              simp [hClock]
      _ = ∫⁻ ω, ENNReal.ofReal ((τ ω).toReal) ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards
              [stoppedValue_timeProcess_ae_eq_toReal_of_ae_ne_top (μ := μ) (τ := τ) hτ_finite]
              with ω hω
            simp [hω]
      _ = ∞ := by
            simpa [τ, M] using
              brownianLevelHittingTime_one_lintegral_eq_top
                (μ := μ) hMW
                (brownianContinuousVersion_continuous (μ := μ) (B := W) hW)
  exact ⟨μ, inferInstance, ℱ, M, τ, hM, hM_zero, hτ_stop, hτ_finite, hBracket, hStoppedSq⟩

end ProbabilityTheory
