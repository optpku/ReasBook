/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.BrownianStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Remark_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 21.18: the constant-path map on `NNReal → ℝ` is measurable in the starting
point. -/
lemma measurable_constPathReal : Measurable (fun z : ℝ ↦ fun _ : NNReal ↦ z) := by
  -- Proof comment: every coordinate of the constant path is the identity map on the start value.
  refine measurable_pi_lambda _ fun t ↦ ?_
  simpa using measurable_id

/-- Helper for Theorem 21.18: translating a real-valued path by a fixed start point is measurable.
-/
lemma measurable_translatePathReal (x : ℝ) :
    Measurable (fun ω : NNReal → ℝ ↦ fun t : NNReal ↦ x + ω t) := by
  -- Proof comment: each translated coordinate is the measurable sum of a constant and the
  -- original coordinate.
  refine measurable_pi_lambda _ fun t ↦ ?_
  exact measurable_const.add (measurable_pi_apply t)

/-- Helper for Theorem 21.18: a measurable process is adapted to its own natural history
filtration. -/
lemma adapted_processFiltration_of_measurable
    (X : NNReal → Ω → ℝ) (hX : ∀ t, Measurable (X t)) :
    Adapted (processFiltration X) X := by
  intro t
  -- The time-`t` coordinate sigma algebra is one of the generators of `processFiltration X t`.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX t)) <| by
    refine le_iSup_of_le t ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Theorem 21.18: subtracting the deterministic starting point turns Brownian motion
started at `x` into Brownian motion started at `0`. -/
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

/-- Helper for Theorem 21.18: integrating a measurable path functional against the Brownian
path-law row is the same as integrating its pullback along `processPath B`. -/
lemma brownianPathLawIntegral_eq
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (f : (NNReal → ℝ) → ℝ)
    (hf : Measurable f) :
    ∫ y, f y ∂ ((P x : Measure Ω).map (processPath B)) =
      ∫ ω, f (processPath B ω) ∂ (P x : Measure Ω) := by
  -- Proof comment: the row path law is literally the pushforward of `P x` along `processPath B`.
  exact
    MeasureTheory.integral_map
      ((hB x).measurable_processPath.aemeasurable)
      hf.aestronglyMeasurable

/-- Helper for Theorem 21.18: the candidate strong-Markov kernel is obtained by translating the
zero-start Brownian path law by the current state. -/
def brownianTranslatedPathKernel
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ) :
    Kernel ℝ (NNReal → ℝ) :=
  (dirac_convolution_kernel (((P 0 : Measure Ω).map (processPath B)))) ∘ₖ
    Kernel.deterministic (fun z : ℝ ↦ fun _ : NNReal ↦ z) measurable_constPathReal

/-- Helper for Theorem 21.18: the translated Brownian path kernel has row `x` equal to the
zero-start path law translated by the constant path `t ↦ x`. -/
lemma brownianTranslatedPathKernel_apply
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (x : ℝ) :
    brownianTranslatedPathKernel P B x =
      ((P 0 : Measure Ω).map (processPath B)).map
        (fun ω : NNReal → ℝ ↦ fun t : NNReal ↦ x + ω t) := by
  -- Proof comment: composing with the deterministic constant-path kernel inserts the current
  -- state as a constant path, and `dirac_convolution_kernel` rewrites this as path translation.
  rw [brownianTranslatedPathKernel, Kernel.comp_deterministic_eq_comap _ measurable_constPathReal,
    Kernel.comap_apply, dirac_convolution_kernel_apply]
  simpa [Function.comp_def, Pi.add_apply] using
    (Measure.dirac_conv (fun _ : NNReal ↦ x) (((P 0 : Measure Ω).map (processPath B)) : Measure _))

/-- Helper for Theorem 21.18: the translated Brownian path kernel is concentrated on paths whose
time-`0` value is the current state. -/
private lemma brownianTranslatedPathKernel_timeZero_real
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (z : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (brownianTranslatedPathKernel P B z).real ((fun y : NNReal → ℝ ↦ y 0) ⁻¹' A) =
      Set.indicator A (fun _ ↦ (1 : ℝ)) z := by
  let μ0 : Measure Ω := (P 0 : Measure Ω)
  have hEvalShiftMeas : Measurable (fun ω : Ω ↦ z + B 0 ω) := by
    -- Proof comment: the time-zero translated state is a measurable sum of the constant `z`
    -- and the deterministic Brownian coordinate `B 0`.
    exact measurable_const.add ((hB 0).stronglyMeasurable 0).measurable
  have hStart0 :
      B 0 =ᵐ[μ0] fun _ : Ω ↦ (0 : ℝ) :=
    brownianStart_ae_eq_const_of_measurable ((hB 0).stronglyMeasurable 0).measurable (hB 0)
  have hShiftAe :
      (fun ω : Ω ↦ z + B 0 ω) =ᵐ[μ0] fun _ : Ω ↦ z := by
    -- Proof comment: the zero-start Brownian path begins at `0` almost surely, so translating
    -- by `z` makes the time-zero value almost surely constant equal to `z`.
    filter_upwards [hStart0] with ω hω
    simp [hω]
  have hMapShift :
      μ0.map (fun ω : Ω ↦ z + B 0 ω) = Measure.dirac z := by
    letI : IsProbabilityMeasure μ0 := (hB 0).isProbabilityMeasure
    calc
      μ0.map (fun ω : Ω ↦ z + B 0 ω) = μ0.map (fun _ : Ω ↦ z) := by
        exact Measure.map_congr hShiftAe
      _ = (μ0 Set.univ) • Measure.dirac z := Measure.map_const μ0 z
      _ = Measure.dirac z := by simp [μ0]
  -- Proof comment: evaluate the translated row at time `0`, collapse the pushforward to the
  -- scalar time-zero map, and then use that the zero-start Brownian path starts from `0`.
  calc
    (brownianTranslatedPathKernel P B z).real ((fun y : NNReal → ℝ ↦ y 0) ⁻¹' A)
        = (((μ0.map (processPath B)).map
            (fun y : NNReal → ℝ ↦ fun t : NNReal ↦ z + y t)).real
              ((fun y : NNReal → ℝ ↦ y 0) ⁻¹' A)) := by
              rw [brownianTranslatedPathKernel_apply]
    _ = ((μ0.map (processPath B)).real ((fun y : NNReal → ℝ ↦ z + y 0) ⁻¹' A)) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := (μ0.map (processPath B)))
              (f := fun y : NNReal → ℝ ↦ fun t : NNReal ↦ z + y t)
              (measurable_translatePathReal z) ((measurable_pi_apply 0) hA))
    _ = μ0.real ((fun ω : Ω ↦ z + B 0 ω) ⁻¹' A) := by
          have hpre :
              (processPath B) ⁻¹' ((fun y : NNReal → ℝ ↦ z + y 0) ⁻¹' A) =
                (fun ω : Ω ↦ z + B 0 ω) ⁻¹' A := by
            ext ω
            rfl
          rw [MeasureTheory.map_measureReal_apply
            (μ := μ0) (f := processPath B) (hB 0).measurable_processPath
            ((measurable_const.add (measurable_pi_apply 0)) hA)]
          rw [hpre]
    _ = (Measure.dirac z).real A := by
          rw [← MeasureTheory.map_measureReal_apply
            (μ := μ0) (f := fun ω : Ω ↦ z + B 0 ω) hEvalShiftMeas hA]
          rw [hMapShift]
    _ = Set.indicator A (fun _ ↦ (1 : ℝ)) z := by
          -- Proof comment: the Dirac row mass is exactly the indicator of membership in `A`.
          by_cases hz : z ∈ A
          · simp [MeasureTheory.measureReal_def, hA, hz]
          · simp [MeasureTheory.measureReal_def, hA, hz]

/-- Helper for Theorem 21.18: if `B` is Brownian under each start law `P x`, then the translated
Brownian path kernel is a Markov kernel. -/
lemma brownianTranslatedPathKernel_isMarkov
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x) :
    IsMarkovKernel (brownianTranslatedPathKernel P B) := by
  refine ⟨?_⟩
  intro x
  letI : IsProbabilityMeasure (P 0 : Measure Ω) := (hB 0).isProbabilityMeasure
  letI : IsProbabilityMeasure ((P 0 : Measure Ω).map (processPath B)) :=
    Measure.isProbabilityMeasure_map (hB 0).measurable_processPath.aemeasurable
  rw [brownianTranslatedPathKernel_apply]
  exact Measure.isProbabilityMeasure_map (measurable_translatePathReal x).aemeasurable

/-- Helper for Theorem 21.18: evaluating a path on finitely many times is measurable. -/
lemma measurable_pathEvalVector {n : ℕ} (times : Fin n → NNReal) :
    Measurable (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
  -- Proof comment: each output coordinate is ordinary path evaluation at one fixed time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

/-- Helper for Theorem 21.18: a measurable real-valued path functional is measurable for one
countable-cylinder sigma-algebra. -/
private lemma measurable_countableCylinderSupport
    (f : (NNReal → ℝ) → ℝ) (hf : Measurable f) :
    ∃ J : Set NNReal, J.Countable ∧ Measurable[cylinderEvents J] f := by
  classical
  have hCut :
      ∀ q : ℚ, MeasurableSet (f ⁻¹' Set.Iio (q : ℝ)) := by
    intro q
    exact hf (measurableSet_Iio : MeasurableSet (Set.Iio (q : ℝ)))
  have hCutSupport :
      ∀ q : ℚ, ∃ J : Set NNReal, J.Countable ∧
        MeasurableSet[cylinderEvents J] (f ⁻¹' Set.Iio (q : ℝ)) := by
    intro q
    exact measurableSet_iff_exists_countable_cylinderEvents.mp (hCut q)
  choose J hJcount hJmeas using hCutSupport
  refine ⟨⋃ q : ℚ, J q, Set.countable_iUnion hJcount, ?_⟩
  -- Proof comment: it suffices to check the rational half-line generators of `borel ℝ`, and each
  -- such generator is already measurable for the union support by monotonicity of
  -- `cylinderEvents`.
  change @Measurable (NNReal → ℝ) ℝ (cylinderEvents (⋃ q : ℚ, J q)) (borel ℝ) f
  rw [show borel ℝ = MeasurableSpace.generateFrom (⋃ q : ℚ, {Set.Iio (q : ℝ)}) by
    simpa using Real.borel_eq_generateFrom_Iio_rat]
  exact
    @measurable_generateFrom (NNReal → ℝ) ℝ (cylinderEvents (⋃ q : ℚ, J q))
      (⋃ q : ℚ, {Set.Iio (q : ℝ)}) f (by
        intro s hs
        rcases Set.mem_iUnion.1 hs with ⟨q, hsq⟩
        rw [Set.mem_singleton_iff] at hsq
        subst hsq
        exact
          (cylinderEvents_mono (show J q ⊆ ⋃ r : ℚ, J r from by
            intro t ht
            exact Set.mem_iUnion.2 ⟨q, ht⟩)) _ (hJmeas q))

/-- Helper for Theorem 21.18: every measurable real-valued path functional factors through one
countable coordinate restriction. -/
private lemma exists_countableRestrict_factor_measurablePathFunctional
    (f : (NNReal → ℝ) → ℝ) (hf : Measurable f) :
    ∃ J : Set NNReal, J.Countable ∧
      ∃ g : ((j : J) → ℝ) → ℝ, Measurable g ∧ f = g ∘ J.restrict := by
  rcases measurable_countableCylinderSupport f hf with ⟨J, hJ, hfJ⟩
  have hfComap :
      Measurable[MeasurableSpace.comap J.restrict
        (MeasurableSpace.pi : MeasurableSpace ((j : J) → ℝ))] f := by
    -- Proof comment: rewrite the cylinder sigma-algebra on `J` as the pullback along the
    -- canonical restriction map.
    rw [cylinderEvents_eq_comap_restrict J] at hfJ
    exact hfJ
  -- Proof comment: once `f` is measurable for the pullback sigma-algebra, the factorization
  -- theorem gives a measurable owner on the restricted path space.
  rcases hfComap.exists_eq_measurable_comp (f := J.restrict) with ⟨g, hg, hfg⟩
  exact ⟨J, hJ, g, hg, hfg⟩

/-- Helper for Theorem 21.18: restricting a full path to countably many coordinates is
measurable. -/
private lemma measurable_restrict_countable
    {J : Set NNReal} [Countable J] :
    Measurable (fun y : NNReal → ℝ ↦ J.restrict y) := by
  -- Proof comment: each restricted coordinate is ordinary evaluation of the ambient path at one
  -- fixed time from `J`.
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_pi_apply (j : NNReal)

/-- Helper for Theorem 21.18: a uniform bound on `g ∘ J.restrict` already bounds `g` on the
restricted path space. -/
private lemma bound_of_comp_restrict_bound
    {J : Set NNReal} {g : ((j : J) → ℝ) → ℝ} {C : ℝ}
    (hC : ∀ y : NNReal → ℝ, |g (J.restrict y)| ≤ C) :
    ∀ z : (j : J) → ℝ, |g z| ≤ C := by
  classical
  intro z
  let y : NNReal → ℝ := fun t ↦ if h : t ∈ J then z ⟨t, h⟩ else 0
  have hy : J.restrict y = z := by
    ext j
    simp [y]
  -- Proof comment: extend a restricted path by zero outside `J` and pull the bound back along
  -- the exact restriction identity.
  simpa [hy] using hC y

/-- Helper for Theorem 21.18: a bounded factorization `f = g ∘ J.restrict` transfers the same
bound to the restricted test function `g`. -/
private lemma bound_countableFactor_of_factorization
    {J : Set NNReal} {f : (NNReal → ℝ) → ℝ} {g : ((j : J) → ℝ) → ℝ} {C : ℝ}
    (hfg : f = g ∘ J.restrict)
    (hC : ∀ y : NNReal → ℝ, |f y| ≤ C) :
    ∀ z : (j : J) → ℝ, |g z| ≤ C := by
  -- Proof comment: rewrite the full-path bound through the factorization and then descend it
  -- along the surjective restriction map.
  refine bound_of_comp_restrict_bound ?_
  intro y
  simpa [hfg] using hC y

/-- Helper for Theorem 21.18: evaluating a measurable path-valued map along a simple `NNReal`
clock is measurable. -/
private lemma measurable_evalAlongSimpleClock
    {β : Type*} [MeasurableSpace β]
    {path : Ω → NNReal → β} (hPath : Measurable path)
    (σ : MeasureTheory.SimpleFunc Ω NNReal) :
    Measurable (fun ω ↦ path ω (σ ω)) := by
  induction σ using MeasureTheory.SimpleFunc.induction' with
  | const c =>
      -- Proof comment: a deterministic clock reduces evaluation to one fixed coordinate of the
      -- measurable path map.
      simpa using (measurable_pi_apply c).comp hPath
  | @pcw f g s hs hf hg =>
      -- Proof comment: a piecewise simple clock is handled by evaluating each branch separately
      -- and then recombining them with `Measurable.piecewise`.
      classical
      have hpiece :
          Measurable (s.piecewise (fun ω ↦ path ω (f ω)) fun ω ↦ path ω (g ω)) :=
        hf.piecewise hs hg
      convert hpiece using 1
      ext ω
      by_cases hω : ω ∈ s <;> simp [MeasureTheory.SimpleFunc.coe_piecewise, Set.piecewise, hω]

/-- Helper for Theorem 21.18: integrating a kernel against a restricted pushforward agrees with
the corresponding set integral of kernel row masses. -/
lemma kernelComp_restrictMap_real_eq_setIntegral_local
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel ℝ F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    {s : Set Ω} (hs : MeasurableSet s) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict s).map Y)).real A) = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
  let ν : Measure ℝ := (μ.restrict s).map Y
  have hKernelInt : Integrable (fun y : ℝ ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hKernelNonneg :
      0 ≤ᵐ[ν] fun y : ℝ ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hCompReal :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hLIntegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKernelInt hKernelNonneg
    rw [hLIntegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hKernelNonneg
  have hMapReal :
      ∫ y, (κ y).real A ∂ν = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict s).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict s)
    rw [MeasureTheory.integral_map hY.aemeasurable hKernelInt.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict s).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hCompReal
    _ = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hMapReal

/-- Helper for Theorem 21.18: the local kernel-composition set-integral formula only needs
`AEMeasurable` data on the restricted slice. -/
lemma kernelComp_restrictMap_real_eq_setIntegral_local_ae
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel ℝ F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → ℝ}
    {s : Set Ω} (hs : MeasurableSet s)
    (hY : AEMeasurable Y (μ.restrict s)) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict s).map Y)).real A) = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
  let ν : Measure ℝ := (μ.restrict s).map Y
  have hKernelInt : Integrable (fun y : ℝ ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hKernelNonneg :
      0 ≤ᵐ[ν] fun y : ℝ ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hCompReal :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hLIntegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKernelInt hKernelNonneg
    rw [hLIntegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hKernelNonneg
  have hMapReal :
      ∫ y, (κ y).real A ∂ν = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict s).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict s)
    rw [MeasureTheory.integral_map hY hKernelInt.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict s).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hCompReal
    _ = ∫ ω in s, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hMapReal

/-- Helper for Theorem 21.18: evaluating the translated Brownian path kernel on finitely many
future times gives the translated zero-start finite-vector law. -/
lemma brownianTranslatedPathKernel_futureVector_apply
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (z : ℝ) {n : ℕ} (times : Fin n → NNReal) :
    (brownianTranslatedPathKernel P B z).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) =
      (P 0 : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ z + B (times i) ω) := by
  have hTranslateEvalMeas :
      Measurable (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ z + y (times i)) := by
    -- Proof comment: after fixing `z`, each vector coordinate is a translated path evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_const.add (measurable_pi_apply (times i))
  -- Proof comment: first unfold the translated path-kernel row, then collapse the two pushforward
  -- maps to the direct finite-vector image under `P 0`.
  calc
    (brownianTranslatedPathKernel P B z).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))
      = (((P 0 : Measure Ω).map (processPath B)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ z + y (times i))) := by
            rw [brownianTranslatedPathKernel_apply]
            rw [Measure.map_map (measurable_pathEvalVector times) (measurable_translatePathReal z)]
            rfl
    _ = (P 0 : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ z + B (times i) ω) := by
          rw [Measure.map_map hTranslateEvalMeas (hB 0).measurable_processPath]
          rfl

/-- Helper for Theorem 21.18: integrating a bounded continuous finite-dimensional test against the
translated Brownian path kernel depends continuously on the starting point. -/
private lemma continuous_brownianTranslatedPathKernel_futureVectorIntegral
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    {n : ℕ} (times : Fin n → NNReal) (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    Continuous fun z : ℝ ↦
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let F : ℝ → Ω → ℝ := fun z ω ↦ φ (fun i : Fin n ↦ z + B (times i) ω)
  have hEq :
      (fun z : ℝ ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))) =
        fun z : ℝ ↦ ∫ ω, F z ω ∂μ := by
    funext z
    have hVectorMeas :
        Measurable (fun ω : Ω ↦ fun i : Fin n ↦ z + B (times i) ω) := by
      -- Proof comment: for fixed `z`, each future-vector coordinate is a translated Brownian
      -- coordinate and hence measurable.
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_const.add ((hB 0).stronglyMeasurable (times i)).measurable
    calc
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))
        = ∫ v, φ v ∂((μ).map (fun ω : Ω ↦ fun i : Fin n ↦ z + B (times i) ω)) := by
            rw [brownianTranslatedPathKernel_futureVector_apply P B hB z times]
      _ = ∫ ω, F z ω ∂μ := by
            simpa [F, μ] using
              (MeasureTheory.integral_map hVectorMeas.aemeasurable
                (((φ : C(Fin n → ℝ, ℝ)).continuous.measurable).aestronglyMeasurable))
  have hF_meas : ∀ z : ℝ, AEStronglyMeasurable (F z) μ := by
    intro z
    have hVectorMeas :
        Measurable (fun ω : Ω ↦ fun i : Fin n ↦ z + B (times i) ω) := by
      -- Proof comment: each coordinate remains measurable after translating by the start value.
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_const.add ((hB 0).stronglyMeasurable (times i)).measurable
    exact ((((φ : C(Fin n → ℝ, ℝ)).continuous.measurable).comp hVectorMeas).aestronglyMeasurable)
  have hF_bound : ∀ z : ℝ, ∀ᵐ ω ∂μ, ‖F z ω‖ ≤ ‖φ‖ := by
    intro z
    -- Proof comment: bounded continuous tests are uniformly bounded by their sup norm.
    exact Filter.Eventually.of_forall fun ω ↦ φ.norm_coe_le_norm _
  have hbound_int : Integrable (fun _ : Ω ↦ ‖φ‖) μ := by
    -- Proof comment: the dominating constant is integrable under the Brownian start law.
    simpa [μ] using integrable_const (‖φ‖ : ℝ)
  have hF_cont : ∀ᵐ ω ∂μ, Continuous fun z : ℝ ↦ F z ω := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hVectorCont : Continuous (fun z : ℝ ↦ fun i : Fin n ↦ z + B (times i) ω) := by
      -- Proof comment: for fixed sample point `ω`, the evaluation vector varies affinely in the
      -- start value.
      refine continuous_pi fun i ↦ ?_
      exact continuous_id.add continuous_const
    -- Proof comment: composing the affine evaluation vector with the bounded continuous test
    -- gives pointwise continuity of the integrand.
    simpa [F] using ((φ : C(Fin n → ℝ, ℝ)).continuous.comp hVectorCont)
  rw [hEq]
  -- Proof comment: dominated convergence upgrades the pointwise continuity in `z` to continuity
  -- of the integrated kernel row.
  exact MeasureTheory.continuous_of_dominated hF_meas hF_bound hbound_int hF_cont

/-- Helper for Theorem 21.18: the increment of a Brownian motion started at `x` has the centered
Gaussian law with variance equal to the time lag. -/
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

/-- Helper for Theorem 21.18: after shifting to deterministic time `r` and recentering at `B r`,
the future increment process is Brownian motion started at `0`. -/
lemma brownianStartedAt_shiftSub_startedAtZero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) (r : NNReal) :
    IsBrownianMotionStartedAt μ (fun s ω ↦ B (r + s) ω - B r ω) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: each shifted difference is a difference of two measurable Brownian
    -- coordinates.
    intro s
    exact (hB.stronglyMeasurable (r + s)).sub (hB.stronglyMeasurable r)
  · -- Proof comment: the shifted increment process vanishes at its new origin pointwise.
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    have hzero :
        (fun ω ↦ B (r + 0) ω - B r ω) = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp
    rw [hzero]
    simp
  · -- Proof comment: translated increment blocks are still increment blocks of the original
    -- Brownian motion.
    intro n times hmono
    have htranslated :
        ∀ i j, i ≤ j → (fun k ↦ r + times k) i ≤ (fun k ↦ r + times k) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (hmono hij) r
    simpa [add_assoc] using hB.indepIncrements n (fun k ↦ r + times k) htranslated
  · -- Proof comment: stationary increments are invariant under deterministic time translation.
    intro u s t
    simpa [add_assoc, add_left_comm, add_comm] using hB.stationaryIncrements (r + u) s t
  · intro s hs
    -- Proof comment: the shifted future value is exactly the Brownian increment on `[r, r + s]`.
    simpa [add_assoc, add_comm, add_left_comm] using
      brownianStartedAtIncrement_hasLaw hB (show r ≤ r + s by simp)
  · -- Proof comment: translating the time parameter and subtracting the anchor preserve path
    -- continuity.
    filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun s : NNReal ↦ B (r + s) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Theorem 21.18: after shifting to deterministic time `r` and recentering at `B r`,
the future process is a standard Brownian motion in the pointwise-start sense. -/
lemma brownianStartedAt_shiftSub_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) (r : NNReal) :
    IsBrownianMotion μ (fun s ω ↦ B (r + s) ω - B r ω) := by
  let X : NNReal → Ω → ℝ := fun s ω ↦ B (r + s) ω - B r ω
  have hX_started : IsBrownianMotionStartedAt μ X 0 :=
    brownianStartedAt_shiftSub_startedAtZero hB r
  rcases
      (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance
        μ X).mp hX_started with
    ⟨hX_meas, hX_gauss, hX_mean, hX_cov, hX_cont⟩
  -- Proof comment: the shifted process already has centered Gaussian finite-dimensional laws and
  -- Brownian covariance, while its new time-zero value vanishes pointwise.
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ X).mpr
      ⟨by
          funext ω
          simp [X]
        , hX_gauss
        , hX_mean
        , hX_cov
        , hX_cont⟩

/-- Helper for Theorem 21.18: every increment of the recentered future Brownian process has the
expected centered Gaussian law. -/
lemma brownianStartedAt_shiftSub_increment_hasLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) (r : NNReal)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B (r + t) ω - B (r + s) ω) (gaussianReal 0 (t - s)) μ := by
  let X : NNReal → Ω → ℝ := fun u ω ↦ B (r + u) ω - B r ω
  have hX_started : IsBrownianMotionStartedAt μ X 0 :=
    brownianStartedAt_shiftSub_startedAtZero hB r
  -- Proof comment: once the future process is recentered at time `r`, its increments are the
  -- increments of a Brownian motion started at `0`.
  simpa [X, add_assoc, add_left_comm, add_comm] using
    startedAtZeroIncrement_hasLaw hX_started (s := s) (t := t) hst

/-- Helper for Theorem 21.18: evaluating the recentered future Brownian process along a monotone
finite family of times gives a jointly Gaussian vector. -/
lemma brownianStartedAt_shiftSub_hasGaussianLaw_of_monotone
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) (r : NNReal)
    {n : ℕ} (times : Fin n → NNReal) (htimes : Monotone times) :
    HasGaussianLaw (fun ω i ↦ B (r + times i) ω - B r ω) μ := by
  let X : NNReal → Ω → ℝ := fun u ω ↦ B (r + u) ω - B r ω
  have hX_started : IsBrownianMotionStartedAt μ X 0 :=
    brownianStartedAt_shiftSub_startedAtZero hB r
  -- Proof comment: the recentered future process is Brownian motion started at `0`, so its
  -- monotone coordinate vectors inherit the canonical joint Gaussian law.
  simpa [X] using brownianStartedAtZero_hasGaussianLaw_of_monotone hX_started times htimes

/-- Helper for Theorem 21.18: under the Brownian path-law row, the time-zero coordinate is the
deterministic starting point `x`. -/
lemma brownianPathLaw_start_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) :
    HasLaw (fun y : NNReal → ℝ ↦ y 0) (Measure.dirac x)
      ((P x : Measure Ω).map (processPath B)) := by
  have hZeroAe :
      B 0 =ᵐ[(P x : Measure Ω)] fun _ ↦ x :=
    brownianStart_ae_eq_const_of_measurable ((hB x).stronglyMeasurable 0).measurable (hB x)
  refine
    { aemeasurable := (measurable_pi_apply 0).aemeasurable
      map_eq := ?_ }
  -- Proof comment: compose the path-law pushforward with time-zero evaluation and then use the
  -- almost-sure start identity.
  calc
    ((P x : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ y 0)
        = (P x : Measure Ω).map (fun ω ↦ processPath B ω 0) := by
            simpa [Function.comp] using
              (Measure.map_map (measurable_pi_apply 0) (hB x).measurable_processPath
                (μ := (P x : Measure Ω)))
    _ = (P x : Measure Ω).map (B 0) := by
          simp [processPath_apply]
    _ = (P x : Measure Ω).map (fun _ : Ω ↦ x) := Measure.map_congr hZeroAe
    _ = Measure.dirac x := by
          simp

/-- Helper for Theorem 21.18: under the Brownian path-law row, every ordered increment has the
centered Gaussian law with variance equal to its time lag. -/
lemma brownianPathLaw_increment_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun y : NNReal → ℝ ↦ y t - y s) (gaussianReal 0 (t - s))
      ((P x : Measure Ω).map (processPath B)) := by
  refine
    { aemeasurable := ((measurable_pi_apply t).sub (measurable_pi_apply s)).aemeasurable
      map_eq := ?_ }
  -- Proof comment: evaluate the path law at the two coordinates `s` and `t`, then reuse the
  -- increment law of `B` under `P x`.
  calc
    ((P x : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ y t - y s)
        = (P x : Measure Ω).map (fun ω ↦ processPath B ω t - processPath B ω s) := by
            simpa [Function.comp] using
              (Measure.map_map ((measurable_pi_apply t).sub (measurable_pi_apply s))
                (hB x).measurable_processPath (μ := (P x : Measure Ω)))
    _ = (P x : Measure Ω).map (fun ω ↦ B t ω - B s ω) := by
          simp [processPath_apply]
    _ = gaussianReal 0 (t - s) :=
      (brownianStartedAtIncrement_hasLaw (hB x) hst).map_eq

/-- Helper for Theorem 21.18: the time-`t` coordinate under the Brownian path-law row has the
expected Gaussian marginal started from `x`. -/
lemma brownianPathLaw_eval_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (t : NNReal) :
    HasLaw (fun y : NNReal → ℝ ↦ y t) (gaussianReal x t)
      ((P x : Measure Ω).map (processPath B)) := by
  refine
    { aemeasurable := (measurable_pi_apply t).aemeasurable
      map_eq := ?_ }
  by_cases ht : t = 0
  · subst ht
    -- Proof comment: at time `0`, the path-law row is exactly the Dirac start law `δ_x`.
    rw [(brownianPathLaw_start_hasLaw P B hB x).map_eq]
    simp [gaussianReal_zero_var]
  · -- Proof comment: for positive time, evaluating the pushed-forward path law at `t` recovers
    -- the Brownian marginal `B t` under `P x`.
    calc
      ((P x : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ y t)
          = (P x : Measure Ω).map (fun ω ↦ B t ω) := by
              rw [Measure.map_map
                (g := fun y : NNReal → ℝ ↦ y t)
                (f := processPath B)
                (measurable_pi_apply t) (hB x).measurable_processPath]
              rfl
      _ = gaussianReal x t := (hB x).gaussian_marginal (pos_iff_ne_zero.mpr ht) |>.map_eq

/-- Helper for Theorem 21.18: the translated Brownian path-kernel row starts at the current state
`x` almost surely. -/
lemma brownianTranslatedPathKernel_start_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) :
    HasLaw (fun y : NNReal → ℝ ↦ y 0) (Measure.dirac x)
      (brownianTranslatedPathKernel P B x) := by
  refine
    { aemeasurable := (measurable_pi_apply 0).aemeasurable
      map_eq := ?_ }
  -- Proof comment: evaluating the translated path at time `0` is the shifted time-zero
  -- coordinate of the zero-start row, and that coordinate is almost surely `0`.
  calc
    (brownianTranslatedPathKernel P B x).map (fun y : NNReal → ℝ ↦ y 0)
        = (((P 0 : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ x + y 0)) := by
            rw [brownianTranslatedPathKernel_apply]
            rw [Measure.map_map (g := fun y : NNReal → ℝ ↦ y 0)
              (f := fun ω : NNReal → ℝ ↦ fun t : NNReal ↦ x + ω t)
              (measurable_pi_apply 0) (measurable_translatePathReal x)]
            simp [Function.comp_def]
    _ = ((((P 0 : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ y 0))).map
          (fun z : ℝ ↦ x + z) := by
            symm
            rw [Measure.map_map (g := fun z : ℝ ↦ x + z)
              (f := fun y : NNReal → ℝ ↦ y 0)
              (measurable_const.add measurable_id) (measurable_pi_apply 0)]
            simp [Function.comp_def]
    _ = (Measure.dirac (0 : ℝ)).map (fun z : ℝ ↦ x + z) := by
          rw [(brownianPathLaw_start_hasLaw P B hB 0).map_eq]
    _ = Measure.dirac x := by
          simp

/-- Helper for Theorem 21.18: translating the zero-start Brownian path law does not change future
increment laws. -/
lemma brownianTranslatedPathKernel_increment_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun y : NNReal → ℝ ↦ y t - y s) (gaussianReal 0 (t - s))
      (brownianTranslatedPathKernel P B x) := by
  refine
    { aemeasurable := ((measurable_pi_apply t).sub (measurable_pi_apply s)).aemeasurable
      map_eq := ?_ }
  -- Proof comment: path translation adds the same constant to both coordinates, so the increment
  -- collapses back to the zero-start increment law.
  calc
    (brownianTranslatedPathKernel P B x).map (fun y : NNReal → ℝ ↦ y t - y s)
        = (((P 0 : Measure Ω).map (processPath B)).map
            (fun y : NNReal → ℝ ↦ (x + y t) - (x + y s))) := by
            rw [brownianTranslatedPathKernel_apply]
            rw [Measure.map_map
              (g := fun y : NNReal → ℝ ↦ y t - y s)
              (f := fun ω : NNReal → ℝ ↦ fun u : NNReal ↦ x + ω u)
              ((measurable_pi_apply t).sub (measurable_pi_apply s))
              (measurable_translatePathReal x)]
            simp [Function.comp_def]
    _ = (((P 0 : Measure Ω).map (processPath B)).map
          (fun y : NNReal → ℝ ↦ y t - y s)) := by
            congr 1
            funext y
            ring
    _ = gaussianReal 0 (t - s) := (brownianPathLaw_increment_hasLaw P B hB 0 hst).map_eq

/-- Helper for Theorem 21.18: the translated Brownian path-kernel row has the expected Gaussian
time-`t` marginal `N(x,t)`. -/
lemma brownianTranslatedPathKernel_eval_hasLaw
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (t : NNReal) :
    HasLaw (fun y : NNReal → ℝ ↦ y t) (gaussianReal x t)
      (brownianTranslatedPathKernel P B x) := by
  refine
    { aemeasurable := (measurable_pi_apply t).aemeasurable
      map_eq := ?_ }
  -- Proof comment: evaluating the translated row at time `t` is the zero-start coordinate at
  -- time `t` shifted by the deterministic start `x`.
  calc
    (brownianTranslatedPathKernel P B x).map (fun y : NNReal → ℝ ↦ y t)
        = (((P 0 : Measure Ω).map (processPath B)).map (fun y : NNReal → ℝ ↦ x + y t)) := by
            rw [brownianTranslatedPathKernel_apply]
            rw [Measure.map_map
              (g := fun y : NNReal → ℝ ↦ y t)
              (f := fun ω : NNReal → ℝ ↦ fun u : NNReal ↦ x + ω u)
              (measurable_pi_apply t) (measurable_translatePathReal x)]
            simp [Function.comp_def]
    _ = gaussianReal x t := by
          simpa [add_comm] using
            (ProbabilityTheory.gaussianReal_add_const
              (brownianPathLaw_eval_hasLaw P B hB 0 t) x).map_eq

/-- Helper for Theorem 21.18: the time-`t` marginal of the translated Brownian path kernel is the
translated Gaussian convolution row `δ_x ∗ N(0,t)`. -/
lemma brownianTranslatedPathKernel_timeMarginal_eq
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (t : NNReal) :
    (brownianTranslatedPathKernel P B x).map (fun y : NNReal → ℝ ↦ y t) =
      dirac_convolution_kernel (gaussianReal 0 t) x := by
  refine Measure.ext fun A hA ↦ ?_
  -- Proof comment: identify the row marginal with `gaussianReal x t`, then rewrite that measure
  -- as translation of the centered Gaussian `gaussianReal 0 t`.
  calc
    (brownianTranslatedPathKernel P B x).map (fun y : NNReal → ℝ ↦ y t) A
        = (gaussianReal x t) A := by
            simpa using
              congrArg (fun μ : Measure ℝ ↦ μ A)
                (brownianTranslatedPathKernel_eval_hasLaw P B hB x t).map_eq
    _ = ((gaussianReal 0 t).map (fun z : ℝ ↦ x + z)) A := by
          simpa [add_comm] using
            congrArg (fun μ : Measure ℝ ↦ μ A)
              (ProbabilityTheory.gaussianReal_add_const
                (ProbabilityTheory.HasLaw.id (μ := gaussianReal 0 t)) x).map_eq.symm
    _ = dirac_convolution_kernel (gaussianReal 0 t) x A := by
          rw [dirac_convolution_kernel_apply, Measure.dirac_conv]

/-- Helper for Theorem 21.18: finite future Brownian increment vectors are independent of finite
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
          (fun i : Fin n => futureIncrements i)
          (fun j : Fin (m + 1) => historyVector j))
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
    -- Proof comment: for the centered Gaussian process `Z`, each future increment is
    -- uncorrelated with every history coordinate before the anchor time `s`.
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hJoint ?_ ?_ ?_
    · intro i
      exact ((hZ.stronglyMeasurable (s + times i)).aemeasurable.sub (hZ.stronglyMeasurable s).aemeasurable)
    · intro j
      exact (hZ.stronglyMeasurable (hist j)).aemeasurable
    · intro i j
      have hs_mem : MemLp (Z s) 2 μ := (hGaussian.hasGaussianLaw_eval s).memLp_two
      have hsi_mem : MemLp (Z (s + times i)) 2 μ := (hGaussian.hasGaussianLaw_eval (s + times i)).memLp_two
      have hj_mem : MemLp (Z (hist j)) 2 μ := (hGaussian.hasGaussianLaw_eval (hist j)).memLp_two
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
    -- Proof comment: adding the deterministic start value to each centered history coordinate is
    -- measurable coordinatewise.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact (measurable_pi_apply j).add measurable_const
  -- Proof comment: translate the centered history tuple back to the original Brownian history;
  -- the future increment vector is unchanged by subtracting the same constant twice.
  refine (hIndepCentered.comp measurable_id hTranslateHistory).congr ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦ by
      ext i
      simp [futureIncrements, Z, s]
  · exact Filter.Eventually.of_forall fun ω ↦ by
      ext j
      simp [historyVector, Z]

/-- Helper for Theorem 21.18: the joint law of a finite Brownian history tuple and the recentered
future increment vector factors as the history law composed with the constant future-increment
kernel. -/
lemma brownianHistoryTupleFutureIncrement_map_eq_compProd
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x)
    {m n : ℕ} (hist : Fin (m + 1) → NNReal) (hhist : StrictMono hist)
    (times : Fin n → NNReal) :
    μ.map
      (fun ω ↦
        ((fun j : Fin (m + 1) ↦ B (hist j) ω),
          fun i : Fin n ↦ B (hist (Fin.last m) + times i) ω - B (hist (Fin.last m)) ω)) =
      (μ.map (fun ω ↦ fun j : Fin (m + 1) ↦ B (hist j) ω)) ⊗ₘ
        Kernel.const (Fin (m + 1) → ℝ)
          (μ.map
            (fun ω ↦ fun i : Fin n ↦ B (hist (Fin.last m) + times i) ω -
              B (hist (Fin.last m)) ω)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let H : Ω → Fin (m + 1) → ℝ := fun ω j ↦ B (hist j) ω
  let U : Ω → Fin n → ℝ := fun ω i ↦
    B (hist (Fin.last m) + times i) ω - B (hist (Fin.last m)) ω
  have hH_meas : Measurable H := by
    -- Proof comment: the history tuple is measurable coordinatewise.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact (hB.stronglyMeasurable (hist j)).measurable
  have hU_meas : Measurable U := by
    -- Proof comment: each future increment coordinate is a measurable difference of two Brownian
    -- coordinates.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((hB.stronglyMeasurable (hist (Fin.last m) + times i)).measurable).sub
      ((hB.stronglyMeasurable (hist (Fin.last m))).measurable)
  have hIndep : IndepFun H U μ :=
    (brownianFutureIncrementVector_indep_historyTuple hB hist hhist times).symm
  have hProd :
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (μ.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH_meas.aemeasurable hU_meas.aemeasurable).mp hIndep
  -- Proof comment: convert the independent pair law to the `compProd` normal form used by
  -- `condDistrib_ae_eq_of_measure_eq_compProd`.
  calc
    μ.map
        (fun ω ↦
          ((fun j : Fin (m + 1) ↦ B (hist j) ω),
            fun i : Fin n ↦ B (hist (Fin.last m) + times i) ω - B (hist (Fin.last m)) ω))
      = μ.map (fun ω ↦ (H ω, U ω)) := by
          rfl
    _ = (μ.map H).prod (μ.map U) := hProd
    _ = (μ.map H) ⊗ₘ Kernel.const (Fin (m + 1) → ℝ) (μ.map U) := by
          simpa using (Measure.compProd_const (μ := μ.map H) (ν := μ.map U)).symm

/-- Helper for Theorem 21.18: conditioning a scalar future increment on a finite Brownian history
tuple ending at the anchor time gives the centered Gaussian increment law `N(0, t)`. -/
lemma brownianHistoryTupleFutureIncrement_condDistrib_eq_const
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) {m : ℕ} (hist : Fin (m + 1) → NNReal) (hhist : StrictMono hist)
    (t : NNReal) :
    condDistrib
        (fun ω ↦ B (hist (Fin.last m) + t) ω - B (hist (Fin.last m)) ω)
        (fun ω ↦ fun j : Fin (m + 1) ↦ B (hist j) ω)
        (P x : Measure Ω) =ᵐ[
          (P x : Measure Ω).map (fun ω ↦ fun j : Fin (m + 1) ↦ B (hist j) ω)]
      Kernel.const (Fin (m + 1) → ℝ) (gaussianReal 0 t) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → Fin (m + 1) → ℝ := fun ω j ↦ B (hist j) ω
  let U : Ω → ℝ := fun ω ↦ B (hist (Fin.last m) + t) ω - B (hist (Fin.last m)) ω
  have hH_meas : Measurable H := by
    -- Proof comment: the history tuple is measurable coordinatewise.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact ((hB x).stronglyMeasurable (hist j)).measurable
  have hU_meas : Measurable U := by
    -- Proof comment: the future increment is the difference of two measurable Brownian
    -- coordinates.
    exact
      (((hB x).stronglyMeasurable (hist (Fin.last m) + t)).measurable).sub
        (((hB x).stronglyMeasurable (hist (Fin.last m))).measurable)
  have hIndepVec :
      IndepFun
        (fun ω (i : Fin 1) ↦ B (hist (Fin.last m) + (fun _ : Fin 1 ↦ t) i) ω -
          B (hist (Fin.last m)) ω)
        H
        μ :=
    brownianFutureIncrementVector_indep_historyTuple (hB x) hist hhist (fun _ : Fin 1 ↦ t)
  have hIndep : IndepFun U H μ := by
    -- Proof comment: the scalar future increment is the lone coordinate of the one-point future
    -- increment vector.
    simpa [U] using hIndepVec.comp (measurable_pi_apply (0 : Fin 1)) measurable_id
  have hProd :
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (μ.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH_meas.aemeasurable hU_meas.aemeasurable).mp
      hIndep.symm
  have hU_law : μ.map U = gaussianReal 0 t :=
    by
      simpa [U, add_comm, add_left_comm, add_assoc] using
        (brownianStartedAtIncrement_hasLaw (hB x)
          (show hist (Fin.last m) ≤ hist (Fin.last m) + t by simp)).map_eq
  have hCompProd :
      μ.map (fun ω ↦ (H ω, U ω)) =
        (μ.map H) ⊗ₘ Kernel.const (Fin (m + 1) → ℝ) (gaussianReal 0 t) := by
    -- Proof comment: the joint law of history and the scalar increment is the product of the
    -- history law with the constant centered Gaussian increment law.
    calc
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (μ.map U) := hProd
      _ = (μ.map H).prod (gaussianReal 0 t) := by rw [hU_law]
      _ = (μ.map H) ⊗ₘ Kernel.const (Fin (m + 1) → ℝ) (gaussianReal 0 t) := by
            simpa using
              (Measure.compProd_const (μ := μ.map H) (ν := gaussianReal 0 t)).symm
  -- Proof comment: `condDistrib` is characterized by the history/increment product factorization.
  exact
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hH_meas hU_meas hCompProd

/-- Helper for Theorem 21.18: conditioning a scalar future increment event on a finite Brownian
history tuple ending at the anchor time gives the centered Gaussian increment probability. -/
lemma brownianHistoryTupleFutureIncrement_condExp_eq_const
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) {m : ℕ} (hist : Fin (m + 1) → NNReal) (hhist : StrictMono hist)
    {A : Set ℝ} (hA : MeasurableSet A) (t : NNReal) :
    ((P x : Measure Ω)⟦(fun ω ↦ B (hist (Fin.last m) + t) ω - B (hist (Fin.last m)) ω) ⁻¹' A
        | MeasurableSpace.comap (fun ω ↦ fun j : Fin (m + 1) ↦ B (hist j) ω) inferInstance⟧)
      =ᵐ[(P x : Measure Ω)]
        fun _ ↦ (gaussianReal 0 t).real A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → Fin (m + 1) → ℝ := fun ω j ↦ B (hist j) ω
  let U : Ω → ℝ := fun ω ↦ B (hist (Fin.last m) + t) ω - B (hist (Fin.last m)) ω
  have hH_meas : Measurable H := by
    -- Proof comment: the history tuple is measurable coordinatewise.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact ((hB x).stronglyMeasurable (hist j)).measurable
  have hU_meas : Measurable U := by
    -- Proof comment: the future increment is the difference of two measurable Brownian
    -- coordinates.
    exact
      (((hB x).stronglyMeasurable (hist (Fin.last m) + t)).measurable).sub
        (((hB x).stronglyMeasurable (hist (Fin.last m))).measurable)
  have hcondU :
      condDistrib U H μ =ᵐ[μ.map H] Kernel.const (Fin (m + 1) → ℝ) (gaussianReal 0 t) :=
    brownianHistoryTupleFutureIncrement_condDistrib_eq_const P B hB x hist hhist t
  have hCondProb :
      (fun ω ↦ (condDistrib U H μ (H ω)).real A) =ᵐ[μ]
        fun _ ↦ (gaussianReal 0 t).real A := by
    -- Proof comment: evaluate the almost-sure constant-kernel identity on the measurable set
    -- `A`.
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcondU] with ω hω
    simpa using congrArg (fun ν : Measure ℝ ↦ ν.real A) hω
  -- Proof comment: the conditional probability of the increment event is the conditional
  -- distribution kernel evaluated on `A`.
  exact
    (ProbabilityTheory.condDistrib_ae_eq_condExp hH_meas hU_meas hA).symm.trans hCondProb

/-- Helper for Theorem 21.18: the finite past up to time `s` generated by a finite family of
Brownian coordinates. -/
@[reducible] private def finitePastSigma
    (B : NNReal → Ω → ℝ) (s : NNReal) (J : Finset (Set.Iic s)) :
    MeasurableSpace Ω :=
  ⨆ u ∈ (J : Set (Set.Iic s)), MeasurableSpace.comap (B u.1) inferInstance

/-- Helper for Theorem 21.18: the finite past generated by `J` is the pullback sigma-algebra of
the bundled history-restriction map `ω ↦ (u ↦ B u ω)` on `J`. -/
private lemma finitePastSigma_eq_comap_historyRestriction
    (B : NNReal → Ω → ℝ) (s : NNReal) (J : Finset (Set.Iic s)) :
    finitePastSigma B s J =
      MeasurableSpace.comap (fun ω : Ω ↦ fun u : J ↦ B u.1 ω) inferInstance := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every generator `B u` from `J` is one coordinate of the bundled
    -- restriction map.
    refine iSup₂_le fun u hu ↦ ?_
    let v : J := ⟨u, hu⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (fun ω : Ω ↦ fun w : J ↦ B w.1 ω) inferInstance]
          (B u.1) := by
      simpa [v] using
        (measurable_pi_apply v).comp
          (comap_measurable (fun ω : Ω ↦ fun w : J ↦ B w.1 ω))
    exact hCoord.comap_le
  · -- Proof comment: conversely, each coordinate of the restriction map is one of the defining
    -- generators of `finitePastSigma`.
    have hRestriction :
        Measurable[finitePastSigma B s J]
          (fun ω : Ω ↦ fun u : J ↦ B u.1 ω) := by
      rw [@measurable_pi_iff]
      intro u
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le u.1 <| le_iSup_of_le u.2 le_rfl
    exact hRestriction.comap_le

/-- Helper for Theorem 21.18: enlarging the observed finite set of past times enlarges the
corresponding finite past sigma-algebra. -/
private lemma finitePastSigma_mono
    (B : NNReal → Ω → ℝ) {s : NNReal} {J K : Finset (Set.Iic s)} (hJK : J ⊆ K) :
    finitePastSigma B s J ≤ finitePastSigma B s K := by
  -- Proof comment: each coordinate sigma-algebra coming from `J` also appears in the larger
  -- family indexed by `K`.
  refine iSup₂_le fun u hu ↦ ?_
  exact le_iSup_of_le u <| le_iSup_of_le (hJK hu) le_rfl

/-- Helper for Theorem 21.18: the directed supremum of the finite past sigma-algebras recovers
the generated filtration at deterministic time `s`. -/
private lemma iSup_finitePastSigma_eq_generatedFiltrationSpace
    (B : NNReal → Ω → ℝ) (s : NNReal) :
    (⨆ J : Finset (Set.Iic s), finitePastSigma B s J) = generatedFiltrationSpace B s := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every finite coordinate sigma-algebra is built from generators already
    -- present in `generatedFiltrationSpace B s`.
    refine iSup_le fun J ↦ ?_
    rw [finitePastSigma]
    refine iSup₂_le fun u _ ↦ ?_
    exact le_iSup_of_le u.1 <| le_iSup_of_le u.2 le_rfl
  · -- Proof comment: each single past time `t ≤ s` is itself one of the finite generators.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let J : Finset (Set.Iic s) := {⟨t, ht⟩}
    have hmem : (⟨t, ht⟩ : Set.Iic s) ∈ J := by
      simp [J]
    exact le_iSup_of_le J <| le_iSup_of_le ⟨t, ht⟩ <| le_iSup_of_le hmem le_rfl

/-- Helper for Theorem 21.18: for a measurable Brownian process, the process filtration at time
`s` is exactly the generated filtration space at `s`. -/
private lemma processFiltration_eq_generatedFiltrationSpace_of_measurable
    (B : NNReal → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t)) (s : NNReal) :
    processFiltration B s = generatedFiltrationSpace B s := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: `processFiltration` is defined as the infimum with the generated
    -- filtration, so it is automatically below that generated piece.
    exact inf_le_right
  · -- Proof comment: measurability of every Brownian coordinate places the generated filtration
    -- inside the ambient measurable space, so the infimum is redundant.
    exact le_inf (generatedFiltrationSpace_le_ambient (X := B) hBmeas s) le_rfl

/-- Helper for Theorem 21.18: the deterministic-time process filtration is the supremum of the
finite past sigma-algebras. -/
private lemma iSup_finitePastSigma_eq_processFiltration
    (B : NNReal → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t)) (s : NNReal) :
    (⨆ J : Finset (Set.Iic s), finitePastSigma B s J) = processFiltration B s := by
  -- Proof comment: first identify the finite-past supremum with `generatedFiltrationSpace`,
  -- then collapse `processFiltration` to the same sigma-algebra using coordinate measurability.
  rw [iSup_finitePastSigma_eq_generatedFiltrationSpace, processFiltration_eq_generatedFiltrationSpace_of_measurable B hBmeas s]

/-- Helper for Theorem 21.18: the full Brownian past up to time `s`, viewed as a path indexed by
`Set.Iic s`. -/
private def pastPathRestriction
    (B : NNReal → Ω → ℝ) (s : NNReal) :
    Ω → Set.Iic s → ℝ :=
  fun ω u ↦ B u.1 ω

/-- Helper for Theorem 21.18: restricting a process to the interval `[0,s]` is measurable when
its coordinates are measurable. -/
private lemma measurable_pastPathRestriction
    (B : NNReal → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t)) (s : NNReal) :
    Measurable (pastPathRestriction B s) := by
  -- Proof comment: each coordinate of the restricted path is just evaluation at one fixed past
  -- time `u ≤ s`.
  refine measurable_pi_lambda _ fun u ↦ ?_
  simpa [pastPathRestriction] using hBmeas u.1

/-- Helper for Theorem 21.18: the deterministic-time Brownian history sigma-algebra is exactly
the pullback sigma-algebra of the bundled past-path restriction. -/
private lemma generatedFiltrationSpace_eq_pastPathRestriction_comap
    (B : NNReal → Ω → ℝ) (s : NNReal) :
    generatedFiltrationSpace B s =
      MeasurableSpace.comap (pastPathRestriction B s) inferInstance := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every generator `B t` with `t ≤ s` is recovered by evaluating the bundled
    -- past path at the coordinate `⟨t, ht⟩`.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let u : Set.Iic s := ⟨t, ht⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (pastPathRestriction B s) inferInstance]
          (B t) := by
      simpa [pastPathRestriction, u] using
        (measurable_pi_apply u).comp (comap_measurable (pastPathRestriction B s))
    exact hCoord.comap_le
  · -- Proof comment: conversely, every coordinate of the bundled past path is one of the
    -- generators of `generatedFiltrationSpace B s`.
    have hPast :
        Measurable[generatedFiltrationSpace B s] (pastPathRestriction B s) := by
      rw [@measurable_pi_iff]
      intro u
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le u.1 <| le_iSup_of_le u.2 le_rfl
    exact hPast.comap_le

/-- Helper for Theorem 21.18: for a measurable Brownian process, the deterministic-time process
filtration is the pullback sigma-algebra of the bundled past path. -/
private lemma processFiltration_eq_pastPathRestriction_comap
    (B : NNReal → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t)) (s : NNReal) :
    processFiltration B s =
      MeasurableSpace.comap (pastPathRestriction B s) inferInstance := by
  -- Proof comment: first collapse `processFiltration` to `generatedFiltrationSpace`, then use
  -- the bundled past-path description of that generated history.
  rw [processFiltration_eq_generatedFiltrationSpace_of_measurable B hBmeas s,
    generatedFiltrationSpace_eq_pastPathRestriction_comap]

/-- Helper for Theorem 21.18: conditioning a translated finite real vector `g (X ω) + U ω` on
`X` only shifts the law of the independent residual vector `U`. -/
private lemma condDistrib_translate_of_indepFunRealVector
    {β : Type*} [MeasurableSpace β] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → β} {U : Ω → Fin n → ℝ}
    (hU : AEMeasurable U μ) (hX : AEMeasurable X μ)
    {g : β → Fin n → ℝ} (hg : Measurable g) (hUX : IndepFun U X μ) :
    condDistrib (fun ω ↦ g (X ω) + U ω) X μ =ᵐ[μ.map X]
      fun x ↦ (μ.map U).map (fun u ↦ g x + u) := by
  let ν : Measure β := μ.map X
  let η : Measure (Fin n → ℝ) := μ.map U
  let κ : Kernel β (Fin n → ℝ) :=
    ((Kernel.id : Kernel β β) ×ₖ Kernel.const β η).map fun z : β × (Fin n → ℝ) ↦ g z.1 + z.2
  have hTranslateMeas : Measurable fun z : β × (Fin n → ℝ) ↦ g z.1 + z.2 := by
    fun_prop
  have hPairTranslateMeas :
      Measurable fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2) := by
    fun_prop
  have hκ_apply : ∀ x : β, κ x = η.map (fun u ↦ g x + u) := by
    intro x
    change
      (((Kernel.id : Kernel β β) ×ₖ Kernel.const β η).map
          (fun z : β × (Fin n → ℝ) ↦ g z.1 + z.2)) x =
        η.map (fun u ↦ g x + u)
    rw [Kernel.map_apply _ hTranslateMeas, Kernel.prod_apply, Kernel.id_apply,
      Kernel.const_apply]
    rw [Measure.dirac_prod, Measure.map_map hTranslateMeas measurable_prodMk_left]
    rfl
  have hUX_map : μ.map (fun ω ↦ (X ω, U ω)) = ν.prod η := by
    simpa [ν, η] using
      (indepFun_iff_map_prod_eq_prod_map_map hX hU).mp hUX.symm
  have hmap :
      μ.map (fun ω ↦ (X ω, g (X ω) + U ω)) =
        (ν.prod η).map (fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) := by
    rw [← hUX_map]
    change
      μ.map ((fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) ∘ fun ω ↦ (X ω, U ω)) =
        Measure.map (fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2))
          (Measure.map (fun ω ↦ (X ω, U ω)) μ)
    rw [AEMeasurable.map_map_of_aemeasurable hPairTranslateMeas.aemeasurable (hX.prodMk hU)]
  have hcomp :
      (ν.prod η).map (fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) = ν ⊗ₘ κ := by
    refine Measure.ext_prod ?_
    intro s t hs ht
    rw [Measure.map_apply hPairTranslateMeas (hs.prod ht), Measure.compProd_apply_prod hs ht]
    rw [Measure.prod_apply (hPairTranslateMeas (hs.prod ht))]
    have hslice :
        (fun x : β ↦
          η
            (Prod.mk x ⁻¹'
              ((fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) ⁻¹' (s ×ˢ t)))) =
          s.indicator (fun x ↦ κ x t) := by
      funext x
      by_cases hx : x ∈ s
      · have hpre :
          Prod.mk x ⁻¹'
              ((fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) ⁻¹' (s ×ˢ t)) =
            (fun u : Fin n → ℝ ↦ g x + u) ⁻¹' t := by
          ext u
          simp [hx]
        rw [hpre, Set.indicator_of_mem hx, hκ_apply x]
        simpa using
          (Measure.map_apply (μ := η) (f := fun u : Fin n → ℝ ↦ g x + u) (by fun_prop) ht).symm
      · have hpre :
          Prod.mk x ⁻¹'
              ((fun z : β × (Fin n → ℝ) ↦ (z.1, g z.1 + z.2)) ⁻¹' (s ×ˢ t)) =
            ∅ := by
          ext u
          simp [hx]
        simp [hpre, Set.indicator, hx]
    rw [hslice, lintegral_indicator hs]
  have hKernel :
      μ.map (fun ω ↦ (X ω, g (X ω) + U ω)) = μ.map X ⊗ₘ κ := by
    simpa [ν] using hmap.trans hcomp
  have hCond :
      condDistrib (fun ω ↦ g (X ω) + U ω) X μ =ᵐ[μ.map X] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd X ((hg.comp_aemeasurable hX).add hU) hKernel
  filter_upwards [hCond] with x hx
  rw [hx, hκ_apply]

/-- Helper for Theorem 21.18: finite Brownian future increment vectors are independent of every
finite restriction of the past path up to the anchor time `s`. -/
private lemma brownianFutureIncrementVector_indep_pastRestrictionFinite
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal) :
    ∀ J : Finset (Set.Iic s),
      IndepFun
        (fun ω i ↦ B (s + times i) ω - B s ω)
        (fun ω (u : J) ↦ B u.1 ω)
        (P x : Measure Ω) := by
  intro J
  let μ : Measure Ω := (P x : Measure Ω)
  let K : Finset (Set.Iic s) := insert ⟨s, by simp⟩ J
  let m : ℕ := K.card - 1
  have hK_nonempty : K.Nonempty := by
    -- Proof comment: the augmented history set always contains the anchor time `s`.
    exact Finset.insert_nonempty _ _
  have hKcard : K.card = m + 1 := by
    -- Proof comment: after adjoining the anchor time, the ordered history tuple has one terminal
    -- coordinate.
    dsimp [m]
    simpa [Nat.succ_eq_add_one] using
      (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr hK_nonempty)).symm
  let hist : Fin (m + 1) → NNReal := fun i ↦ (K.orderEmbOfFin hKcard i).1
  have hhist : StrictMono hist := by
    -- Proof comment: the `orderEmbOfFin` enumeration of the finite set `K` is strictly
    -- increasing, and coercing subtype values does not change the order.
    intro i j hij
    simpa [hist] using (K.orderEmbOfFin hKcard).strictMono hij
  have hKmax : K.max' hK_nonempty = (⟨s, by simp⟩ : Set.Iic s) := by
    -- Proof comment: every element of `K` lies in `Iic s`, while the adjoined anchor point
    -- `⟨s, _⟩` itself belongs to `K`, so it is the maximum.
    apply le_antisymm
    · exact Finset.max'_le (s := K) (H := hK_nonempty) (x := (⟨s, by simp⟩ : Set.Iic s))
        (fun u _ ↦ u.2)
    · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hKpos : 0 < m + 1 := by
    -- Proof comment: the ordered history tuple is nonempty because it contains the anchor.
    simpa [hKcard] using Finset.card_pos.mpr hK_nonempty
  have hlast_hist : hist (Fin.last m) = s := by
    -- Proof comment: the last coordinate in the ordered enumeration of `K` is exactly the
    -- maximal anchor time `s`.
    have hlastK : K.orderEmbOfFin hKcard (Fin.last m) = K.max' hK_nonempty := by
      simpa [Fin.last, Nat.succ_eq_add_one] using
        (Finset.orderEmbOfFin_last (s := K) (h := hKcard) hKpos)
    simpa [hist, hKmax] using congrArg Subtype.val hlastK
  have hBase :
      IndepFun
        (fun ω i ↦ B (s + times i) ω - B s ω)
        (fun ω j ↦ B (hist j) ω)
        μ := by
    -- Route correction: instead of fighting subtype/order-transport directly on `J`, insert the
    -- anchor into `K`, enumerate `K` once in increasing order, and then reuse the stable history
    -- tuple independence theorem.
    simpa [μ, hist, hlast_hist] using
      (brownianFutureIncrementVector_indep_historyTuple (hB x) hist hhist times :
        IndepFun
          (fun ω i ↦ B (hist (Fin.last m) + times i) ω - B (hist (Fin.last m)) ω)
          (fun ω j ↦ B (hist j) ω)
          μ)
  let reindex : (Fin (m + 1) → ℝ) → J → ℝ := fun z u ↦
    z ((K.orderIsoOfFin hKcard).symm ⟨u.1, Finset.mem_insert_of_mem u.2⟩)
  have hreindex : Measurable reindex := by
    -- Proof comment: reindexing the ordered `K`-tuple back to the original `J`-indexed family is
    -- coordinatewise evaluation at deterministic indices.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact measurable_pi_apply ((K.orderIsoOfFin hKcard).symm ⟨u.1, Finset.mem_insert_of_mem u.2⟩)
  have hReindexed :
      IndepFun
        (fun ω i ↦ B (s + times i) ω - B s ω)
        (fun ω ↦ reindex (fun j ↦ B (hist j) ω))
        μ :=
    hBase.comp measurable_id hreindex
  have hRestrict :
      (fun ω ↦ reindex (fun j ↦ B (hist j) ω)) =
        (fun ω (u : J) ↦ B u.1 ω) := by
    -- Proof comment: undoing the `orderIsoOfFin` reindexing recovers the original finite past
    -- restriction exactly.
    funext ω u
    let ku : K := ⟨u.1, Finset.mem_insert_of_mem u.2⟩
    have hindex :
        K.orderEmbOfFin hKcard ((K.orderIsoOfFin hKcard).symm ku) = u.1 := by
      change (((K.orderIsoOfFin hKcard) ((K.orderIsoOfFin hKcard).symm ku) : K) : Set.Iic s) = u.1
      simpa [ku] using congrArg (fun v : K ↦ (v : Set.Iic s))
        ((K.orderIsoOfFin hKcard).apply_symm_apply ku)
    have hindex_val :
        hist ((K.orderIsoOfFin hKcard).symm ku) = u.1.1 := by
      simpa [hist] using congrArg Subtype.val hindex
    simpa [reindex] using congrArg (fun t : NNReal ↦ B t ω) hindex_val
  -- Proof comment: composing the history tuple with the deterministic reindexing map gives the
  -- desired `J`-indexed past restriction.
  simpa [μ, hRestrict] using hReindexed
/-- Helper for Theorem 21.18: finite Brownian future increment vectors are independent of the full
past path up to the anchor time `s`. -/
private lemma brownianFutureIncrementVector_indep_pastPathRestriction
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal) :
    IndepFun
      (fun ω i ↦ B (s + times i) ω - B s ω)
      (pastPathRestriction B s)
      (P x : Measure Ω) := by
  let μx : Measure Ω := (P x : Measure Ω)
  let U : Ω → Fin n → ℝ := fun ω i ↦ B (s + times i) ω - B s ω
  have hU_meas : Measurable U := by
    -- Proof comment: each future increment coordinate is a measurable difference of two Brownian
    -- coordinates.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (((hB x).stronglyMeasurable (s + times i)).measurable).sub
      (((hB x).stronglyMeasurable s).measurable)
  have hFinite :
      ∀ J : Finset (Set.Iic s),
        IndepFun U (fun ω (u : J) ↦ B u.1 ω) μx :=
    brownianFutureIncrementVector_indep_pastRestrictionFinite P B hB x s times
  have hProcess :
      IndepFun U (fun ω (u : Set.Iic s) ↦ B u.1 ω) μx := by
    -- Proof comment: once every finite past restriction is independent from the future
    -- increment vector, `IndepFun.indepFun_process` upgrades this to independence from the full
    -- past path process.
    refine IndepFun.indepFun_process hU_meas (fun u ↦ ((hB x).stronglyMeasurable u.1).measurable) ?_
    intro J
    exact hFinite J
  simpa [U, pastPathRestriction] using hProcess

/-- Helper for Theorem 21.18: the finite-dimensional law of the future increment vector after the
deterministic anchor time `s` is the same as the zero-start Brownian vector law. -/
private lemma brownianFutureIncrementVector_map_eq_zeroStart
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal) :
    ((P x : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω - B s ω)) =
      (P 0 : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ B (times i) ω) := by
  let μx : Measure Ω := (P x : Measure Ω)
  let μ0 : Measure Ω := (P 0 : Measure Ω)
  let X : NNReal → Ω → ℝ := fun t ω ↦ B (s + t) ω - B s ω
  let Y : NNReal → Ω → ℝ := B
  let Xvec : Fin n → Ω → ℝ := fun i ω ↦ X (times i) ω
  let Yvec : Fin n → Ω → ℝ := fun i ω ↦ Y (times i) ω
  let I : Finset (Fin n) := Finset.univ
  let restrictToVector : (↑I → ℝ) → Fin n → ℝ := fun z i ↦ z ⟨i, by simp [I]⟩
  have hX_started : IsBrownianMotionStartedAt μx X 0 :=
    brownianStartedAt_shiftSub_startedAtZero (hB x) s
  have hX_centered :
      (∀ t : NNReal, ∫ ω, X t ω ∂μx = 0) ∧
        (∀ u v : NNReal, cov[X u, X v; μx] = ((u ⊓ v : NNReal) : ℝ)) := by
    rcases
        (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance
          μx X).mp hX_started with
      ⟨_, _, hmean, hcov, _⟩
    exact ⟨hmean, hcov⟩
  have hY_centered :
      (∀ t : NNReal, ∫ ω, Y t ω ∂μ0 = 0) ∧
        (∀ u v : NNReal, cov[Y u, Y v; μ0] = ((u ⊓ v : NNReal) : ℝ)) := by
    rcases
        (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance
          μ0 Y).mp (hB 0) with
      ⟨_, _, hmean, hcov, _⟩
    exact ⟨hmean, hcov⟩
  have hX_gauss : IsGaussianProcess Xvec μx :=
    (IsBrownianMotionStartedAt.isGaussianProcess_zero hX_started).comp_right times
  have hY_gauss : IsGaussianProcess Yvec μ0 :=
    (IsBrownianMotionStartedAt.isGaussianProcess_zero (hB 0)).comp_right times
  have hfd :
      μx.map (fun ω ↦ I.restrict (Xvec · ω)) =
        μ0.map (fun ω ↦ I.restrict (Yvec · ω)) := by
    -- Proof comment: the recentered future process and the zero-start Brownian motion are both
    -- centered Gaussian with the same Brownian covariance kernel along the chosen time family.
    refine finiteDimensionalDistributions_eq_of_centered_gaussian_covariance
      hX_gauss hY_gauss ?_ ?_ ?_ I
    · intro i
      exact hX_centered.1 (times i)
    · intro i
      exact hY_centered.1 (times i)
    · intro i j
      simpa [Xvec, X, Yvec, Y] using
        (hX_centered.2 (times i) (times j)).trans (hY_centered.2 (times i) (times j)).symm
  have hRestrictToVector_meas : Measurable restrictToVector := by
    -- Proof comment: recovering the `Fin n` vector from the restricted coordinates is just
    -- coordinate evaluation on the finite function space.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (⟨i, by simp [I]⟩ : I)
  have hXrestrict_meas : Measurable (fun ω ↦ I.restrict (Xvec · ω)) := by
    -- Proof comment: every restricted coordinate is one of the measurable future increments.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (((hB x).stronglyMeasurable (s + times i.1)).measurable).sub
      (((hB x).stronglyMeasurable s).measurable)
  have hYrestrict_meas : Measurable (fun ω ↦ I.restrict (Yvec · ω)) := by
    -- Proof comment: every restricted coordinate is one deterministic-time Brownian evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((hB 0).stronglyMeasurable (times i.1)).measurable
  -- Proof comment: the finite-dimensional restriction law equality transports back to the
  -- original `Fin n`-indexed future increment vectors.
  calc
    μx.map (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω - B s ω)
        = (μx.map (fun ω ↦ I.restrict (Xvec · ω))).map restrictToVector := by
            rw [Measure.map_map hRestrictToVector_meas hXrestrict_meas]
            rfl
    _ = (μ0.map (fun ω ↦ I.restrict (Yvec · ω))).map restrictToVector := by
          rw [hfd]
    _ = μ0.map (fun ω ↦ fun i : Fin n ↦ B (times i) ω) := by
          rw [Measure.map_map hRestrictToVector_meas hYrestrict_meas]
          rfl

/-- Helper for Theorem 21.18: translating the future increment vector law by the observed present
state matches the corresponding finite row of the translated Brownian path kernel. -/
private lemma brownianFutureValueVector_kernelRow
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x z : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal) :
    (((P x : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω - B s ω)).map
        (fun u ↦ fun i : Fin n ↦ z + u i)) =
      (brownianTranslatedPathKernel P B z).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
  let μ0Vec : Ω → Fin n → ℝ := fun ω i ↦ B (times i) ω
  have hTranslate_meas : Measurable (fun u : Fin n → ℝ ↦ fun i : Fin n ↦ z + u i) := by
    -- Proof comment: the row translation acts coordinatewise by adding the present state `z`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_const.add (measurable_pi_apply i)
  have hμ0Vec_meas : Measurable μ0Vec := by
    -- Proof comment: each future coordinate under the zero-start law is measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((hB 0).stronglyMeasurable (times i)).measurable
  calc
    (((P x : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω - B s ω)).map
        (fun u ↦ fun i : Fin n ↦ z + u i))
      = (((P 0 : Measure Ω).map μ0Vec).map (fun u ↦ fun i : Fin n ↦ z + u i)) := by
          rw [brownianFutureIncrementVector_map_eq_zeroStart P B hB x s times]
    _ = (P 0 : Measure Ω).map (fun ω ↦ fun i : Fin n ↦ z + B (times i) ω) := by
          rw [Measure.map_map hTranslate_meas hμ0Vec_meas]
          rfl
    _ = (brownianTranslatedPathKernel P B z).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
          symm
          exact brownianTranslatedPathKernel_futureVector_apply P B hB z times

/-- Helper for Theorem 21.18: conditioning the deterministic future-value vector on the full past
path up to time `s` yields the translated Brownian path-kernel row. -/
private lemma brownianFutureValueVector_condDistrib_eq_translatedKernelMap
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal) :
    condDistrib
        (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω)
        (pastPathRestriction B s)
        (P x : Measure Ω) =ᵐ[
          (P x : Measure Ω).map (pastPathRestriction B s)]
      fun h ↦
        (brownianTranslatedPathKernel P B (h ⟨s, by simp⟩)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → Set.Iic s → ℝ := pastPathRestriction B s
  let U : Ω → Fin n → ℝ := fun ω i ↦ B (s + times i) ω - B s ω
  let g : (Set.Iic s → ℝ) → Fin n → ℝ := fun h _ ↦ h ⟨s, by simp⟩
  let anchor : Set.Iic s := ⟨s, by simp⟩
  have hH_meas : Measurable H :=
    measurable_pastPathRestriction B (fun t ↦ ((hB x).stronglyMeasurable t).measurable) s
  have hU_meas : Measurable U := by
    -- Proof comment: each future increment coordinate is a measurable Brownian difference.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (((hB x).stronglyMeasurable (s + times i)).measurable).sub
      (((hB x).stronglyMeasurable s).measurable)
  have hg_meas : Measurable g := by
    -- Proof comment: the translation vector only reads the current state `h(s)` and repeats it
    -- across all finite future coordinates.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply anchor
  have hIndep : IndepFun U H μ :=
    brownianFutureIncrementVector_indep_pastPathRestriction P B hB x s times
  have hTranslate :
      condDistrib (fun ω ↦ g (H ω) + U ω) H μ =ᵐ[μ.map H]
        fun h ↦ (μ.map U).map (fun u ↦ g h + u) := by
    -- Proof comment: conditioning future values on the past path reduces to translating the
    -- independent future increment law by the observed present value.
    exact
      condDistrib_translate_of_indepFunRealVector μ hU_meas.aemeasurable
        hH_meas.aemeasurable hg_meas hIndep
  have hRow :
      ∀ h,
        (μ.map U).map (fun u ↦ g h + u) =
          (brownianTranslatedPathKernel P B (h anchor)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
    -- Proof comment: the translated increment law is exactly the corresponding finite row of the
    -- translated Brownian path kernel.
    intro h
    simpa [μ, U, g] using
      (brownianFutureValueVector_kernelRow P B hB x (h anchor) s times)
  have hFuture :
      (fun ω ↦ g (H ω) + U ω) = (fun ω ↦ fun i : Fin n ↦ B (s + times i) ω) := by
    -- Proof comment: the observed present state `H ω anchor = B s ω` translates the future
    -- increment vector back to the future-value vector.
    funext ω
    funext i
    simp [H, U, g, anchor, pastPathRestriction]
  have hRowAe :
      (fun h ↦ (μ.map U).map (fun u ↦ g h + u)) =ᵐ[μ.map H]
        fun h ↦
          (brownianTranslatedPathKernel P B (h anchor)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) :=
    Filter.Eventually.of_forall hRow
  -- Proof comment: after rewriting `g (H ω) + U ω` as the future-value vector itself, the kernel
  -- identity is already in final form.
  simpa [anchor] using (hFuture ▸ (hTranslate.trans hRowAe))
/-- Helper for Theorem 21.18: deterministic-time future-cylinder conditional expectations reduce
to integrating against the translated Brownian path-kernel row over `processFiltration B s`. -/
private lemma brownianProcessFiltration_futureCylinderCondExp_eq_kernelIntegral
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (s : NNReal) {n : ℕ} (times : Fin n → NNReal)
    {φ : (Fin n → ℝ) → ℝ}
    (hφ_meas : Measurable φ)
    (hφ_bdd : ∃ C : ℝ, ∀ v, |φ v| ≤ C) :
    (P x : Measure Ω)[fun ω ↦ φ (fun i : Fin n ↦ B (s + times i) ω) | processFiltration B s] =ᵐ[
        (P x : Measure Ω)]
      fun ω ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B s ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → Set.Iic s → ℝ := pastPathRestriction B s
  let next : Ω → Fin n → ℝ := fun ω i ↦ B (s + times i) ω
  have hH_meas : Measurable H :=
    measurable_pastPathRestriction B (fun t ↦ ((hB x).stronglyMeasurable t).measurable) s
  have hNext_meas : Measurable next := by
    -- Proof comment: each future-value coordinate is one deterministic-time Brownian
    -- evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((hB x).stronglyMeasurable (s + times i)).measurable
  have hNext_int : Integrable (fun ω ↦ φ (next ω)) μ := by
    obtain ⟨C, hC⟩ := hφ_bdd
    -- Proof comment: bounded future-cylinder observables are integrable under the Brownian start
    -- law.
    refine Integrable.of_bound (hφ_meas.comp hNext_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC (next ω)
  have hcondExp :
      μ[fun ω ↦ φ (next ω) | MeasurableSpace.comap H inferInstance] =ᵐ[μ]
        fun ω ↦ ∫ v, φ v ∂condDistrib next H μ (H ω) := by
    -- Proof comment: `condDistrib` packages the deterministic-time conditional expectation over
    -- the full past path sigma-algebra.
    exact
      ProbabilityTheory.condExp_ae_eq_integral_condDistrib
        (μ := μ) (X := H) (Y := next) hH_meas hNext_meas.aemeasurable
        hφ_meas.stronglyMeasurable hNext_int
  have hkernel :
      (fun ω ↦ ∫ v, φ v ∂condDistrib next H μ (H ω)) =ᵐ[μ]
        fun ω ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B s ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
    -- Proof comment: after the deterministic-time conditional-distribution identity, only the
    -- endpoint rewrite `H ω ⟨s, le_rfl⟩ = B s ω` remains.
    filter_upwards
      [ae_eq_comp hH_meas.aemeasurable
        (brownianFutureValueVector_condDistrib_eq_translatedKernelMap P B hB x s times)]
      with ω hω
    simpa [H, next, pastPathRestriction] using congrArg (fun ν : Measure (Fin n → ℝ) ↦ ∫ v, φ v ∂ν) hω
  -- Proof comment: rewrite the conditioning sigma-algebra only after the kernel row is already in
  -- final form.
  simpa [μ, H,
    processFiltration_eq_pastPathRestriction_comap B
      (fun t ↦ ((hB x).stronglyMeasurable t).measurable) s] using hcondExp.trans hkernel

/-- Helper for Theorem 21.18: evaluating the measurable Brownian path map at an ambient
measurable random time is at least almost-everywhere measurable under each start law. -/
private lemma aemeasurable_processPath_eval_randomTime
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    {τ : Ω → NNReal} (hτ : Measurable τ) (x : ℝ) :
    AEMeasurable (fun ω : Ω ↦ processPath B ω (τ ω)) (P x : Measure Ω) := by
  let σ : ℕ → MeasureTheory.SimpleFunc Ω NNReal := fun n ↦
    MeasureTheory.SimpleFunc.approxOn τ hτ (Set.range τ ∪ {0}) 0 (by simp) n
  have hApproxMeas :
      ∀ n, AEMeasurable (fun ω : Ω ↦ processPath B ω (σ n ω)) (P x : Measure Ω) := by
    intro n
    exact
      (measurable_evalAlongSimpleClock
        (hPath := (hB x).measurable_processPath) (σ := σ n)).aemeasurable
  have hApproxClock :
      ∀ ω : Ω, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) := by
    intro ω
    exact
      MeasureTheory.SimpleFunc.tendsto_approxOn hτ (by simp)
        (subset_closure (Or.inl ⟨ω, rfl⟩))
  have hContAE :
      ∀ᵐ ω ∂(P x : Measure Ω), Continuous (processPath B ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using (hB x).continuous_paths
  -- Proof comment: the exact random-time evaluation is the a.e. limit of measurable
  -- simple-clock evaluations, using Brownian continuity along almost every sample path.
  refine aemeasurable_of_tendsto_metrizable_ae' hApproxMeas ?_
  filter_upwards [hContAE] with ω hω
  exact hω.continuousAt.tendsto.comp (hApproxClock ω)

/-- Helper for Theorem 21.18: after restricting to countably many future times, the Brownian
future path after a stopping time is almost everywhere measurable under each start law. -/
private lemma aemeasurable_restrictFuturePathAfterStoppingTime_countable
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    {J : Set NNReal} (hJ : J.Countable) :
    AEMeasurable
      (fun ω ↦ J.restrict (futurePathAfterStoppingTime B τ ω))
      (P x : Measure Ω) := by
  letI : Countable J := hJ.to_subtype
  refine aemeasurable_pi_lambda _ fun j ↦ ?_
  have htime : Measurable (fun ω : Ω ↦ (τ ω).untopA + (j : NNReal)) := by
    -- Proof comment: each restricted coordinate is evaluated at the measurable shifted stopping
    -- time `(τ.untopA + j)`.
    exact ((hτ.measurable.untopA).mono hτ.measurableSpace_le le_rfl).add measurable_const
  -- Proof comment: every coordinate of the restricted future path is exactly evaluation of
  -- `processPath B ω` along the measurable clock `τ.untopA + j`.
  simpa [futurePathAfterStoppingTime, stoppedValue, processPath] using
    (aemeasurable_processPath_eval_randomTime P B hB htime x)

/-- Helper for Theorem 21.18: after factorization through countably many coordinates, the stopped
future Brownian path remains almost everywhere measurable under the start law. -/
private lemma aemeasurable_countableFactor_futurePathAfterStoppingTime
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    {J : Set NNReal} (hJ : J.Countable)
    {g : ((j : J) → ℝ) → ℝ} (hg : Measurable g) :
    AEMeasurable
      (fun ω ↦ g (J.restrict (futurePathAfterStoppingTime B τ ω)))
      (P x : Measure Ω) := by
  letI : Countable J := hJ.to_subtype
  -- Proof comment: compose the countable-coordinate future-path owner with the measurable test
  -- factor on the restricted path space.
  exact
    hg.comp_aemeasurable
      (aemeasurable_restrictFuturePathAfterStoppingTime_countable P B hB x τ hτ hJ)

/-- Helper for Theorem 21.18: if a finite stopping time has countable range, then every shifted
Brownian coordinate `ω ↦ B (σ ω + t) ω` is measurable by splitting over the countable atoms of
`σ`. -/
private lemma measurable_brownianShiftedValue_of_countableRange
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (σ : Ω → NNReal) (hσ_meas : Measurable σ)
    (hσcount : (Set.range σ).Countable) (t : NNReal) :
    Measurable (fun ω : Ω ↦ B (σ ω + t) ω) := by
  classical
  letI : Countable (Set.range σ) := hσcount.to_subtype
  intro s hs
  have hEq :
      (fun ω : Ω ↦ B (σ ω + t) ω) ⁻¹' s =
        ⋃ r : Set.range σ, ({ω | σ ω = r.1} ∩ B (r.1 + t) ⁻¹' s) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨⟨σ ω, ⟨ω, rfl⟩⟩, ?_⟩
      exact ⟨rfl, hω⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨r, hr⟩
      rcases hr with ⟨hσr, hr⟩
      change σ ω = r.1 at hσr
      simpa [hσr] using hr
  -- Proof comment: on each countable atom `{σ = r}`, the random time becomes deterministic, so
  -- measurability reduces to the ordinary measurable time slice `B (r + t)`.
  rw [hEq]
  refine MeasurableSet.iUnion fun r ↦ ?_
  have hAtom : MeasurableSet {ω : Ω | σ ω = r.1} := by
    change MeasurableSet (σ ⁻¹' ({r.1} : Set NNReal))
    simpa using hσ_meas (measurableSet_singleton (x := r.1))
  exact hAtom.inter (((hB 0).stronglyMeasurable (r.1 + t)).measurable hs)

/-- Helper for Theorem 21.18: a countable-range Brownian clock that is already visible in
`𝓕_τ` and never exceeds `τ` yields an `𝓕_τ`-measurable stopped value. -/
private lemma measurable_brownianValue_of_countableRange_hτ
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    (σ : Ω → NNReal)
    (hσ_meas : Measurable[hτ.measurableSpace] σ)
    (hσcount : (Set.range σ).Countable)
    (hσ_le : ∀ ω, σ ω ≤ (τ ω).untopA) :
    Measurable[hτ.measurableSpace] (fun ω ↦ B (σ ω) ω) := by
  classical
  letI : Countable (Set.range σ) := hσcount.to_subtype
  let hAdapted : Adapted (processFiltration B) B :=
    adapted_processFiltration_of_measurable B
      (fun t ↦ ((hB 0).stronglyMeasurable t).measurable)
  have hσ_meas_ambient : Measurable σ := by
    exact hσ_meas.mono hτ.measurableSpace_le le_rfl
  intro s hs
  refine ⟨?_, fun i ↦ ?_⟩
  · -- Proof comment: ambient measurability only uses the countable-range decomposition of `σ`.
    simpa using
      (measurable_brownianShiftedValue_of_countableRange
        P B hB σ hσ_meas_ambient hσcount 0) hs
  · have hEq :
        ((fun ω ↦ B (σ ω) ω) ⁻¹' s) ∩ {ω | τ ω ≤ i} =
          ⋃ r : Set.range σ, (({ω | σ ω = r.1} ∩ {ω | τ ω ≤ i}) ∩ B r.1 ⁻¹' s) := by
        ext ω
        constructor
        · intro hω
          refine Set.mem_iUnion.2 ⟨⟨σ ω, ⟨ω, rfl⟩⟩, ?_⟩
          exact ⟨⟨rfl, hω.2⟩, hω.1⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨r, hr⟩
          rcases hr with ⟨⟨hσr, hτωi⟩, hBs⟩
          change σ ω = r.1 at hσr
          exact ⟨by simpa [hσr] using hBs, hτωi⟩
    rw [hEq]
    refine MeasurableSet.iUnion fun r ↦ ?_
    have hAtom_meas_hτ : MeasurableSet[hτ.measurableSpace] {ω : Ω | σ ω = r.1} := by
      change MeasurableSet[hτ.measurableSpace] (σ ⁻¹' ({r.1} : Set NNReal))
      simpa using hσ_meas (measurableSet_singleton (x := r.1))
    have hAtom_slice :
        MeasurableSet[processFiltration B i] ({ω : Ω | σ ω = r.1} ∩ {ω | τ ω ≤ i}) :=
      (hAtom_meas_hτ.2 i)
    by_cases hri : r.1 ≤ i
    · have hCoord_meas :
          MeasurableSet[processFiltration B i] (B r.1 ⁻¹' s) := by
        exact (processFiltration B).mono hri _ ((hAdapted r.1) hs)
      -- Proof comment: on atoms with `σ = r ≤ i`, the Brownian value is the deterministic
      -- coordinate `B r`, which is measurable at time `i`.
      exact hAtom_slice.inter hCoord_meas
    · have hEmpty :
          (({ω : Ω | σ ω = r.1} ∩ {ω | τ ω ≤ i}) ∩ B r.1 ⁻¹' s) = ∅ := by
        ext ω
        constructor
        · intro hω
          rcases hω with ⟨⟨hσr, hτωi⟩, _⟩
          change τ ω ≤ (i : WithTop NNReal) at hτωi
          have hτ_ne_top : τ ω ≠ ⊤ :=
            ne_top_of_le_ne_top (by exact WithTop.coe_ne_top) hτωi
          have hσ_le_i : σ ω ≤ i := by
            exact le_trans (hσ_le ω) ((WithTop.untopA_le_iff hτ_ne_top).2 hτωi)
          have hr_le_i : r.1 ≤ i := by
            change σ ω = r.1 at hσr
            simpa [hσr] using hσ_le_i
          exact (hri hr_le_i).elim
        · intro hω
          simp at hω
      rw [hEmpty]
      simpa using (MeasurableSet.empty : MeasurableSet[processFiltration B i] (∅ : Set Ω))

/-- Helper for Theorem 21.18: a finite Brownian future-vector observable evaluated at a
countable-range stopping time is measurable. -/
private lemma measurable_brownianStoppedFutureVector_of_countableRange
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {n : ℕ} (times : Fin n → NNReal)
    {φ : (Fin n → ℝ) → ℝ}
    (hφ_meas : Measurable φ) :
    Measurable (fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω)) := by
  have hσ_meas : Measurable σ := by
    -- Proof comment: coercing the finite stopping time into `WithTop NNReal` and applying
    -- `untopA` recovers the original `NNReal`-valued time; measurability then lifts from
    -- `𝓕_σ` to the ambient sigma algebra.
    simpa using (hσ.measurable.untopA).mono hσ.measurableSpace_le le_rfl
  have hVector_meas :
      Measurable (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    -- Proof comment: once `σ` has countable range, each shifted coordinate is measurable by
    -- splitting over the countable atoms `{σ = r}`.
    exact measurable_brownianShiftedValue_of_countableRange P B hB σ hσ_meas hσcount (times i)
  -- Proof comment: compose the measurable finite future vector with the measurable test function
  -- `φ`.
  exact hφ_meas.comp hVector_meas
/-- Helper for Theorem 21.18: on the slice `{σ = s}`, the stopped future Brownian vector is the
deterministic-time future vector anchored at `s`. -/
private lemma brownianFuturePath_eq_fixedTime_on_slice
    (B : NNReal → Ω → ℝ) (σ : Ω → NNReal)
    {s : NNReal} {ω : Ω}
    (hσω : (σ ω : WithTop NNReal) = s) :
    futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω = fun t ↦ B (s + t) ω := by
  -- Proof comment: on the atom where the stopping time equals `s`, the stopped future path is the
  -- deterministic time-shifted Brownian path starting from `s`.
  funext t
  have hτ_ne_top : (σ ω : WithTop NNReal) ≠ ⊤ := by
    exact WithTop.coe_ne_top
  have hτ_untop : ((σ ω : WithTop NNReal)).untop hτ_ne_top = s := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, hσω]
  calc
    futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω t
        = B ((((σ ω : WithTop NNReal)).untop hτ_ne_top) + t) ω := by
            exact
              futurePathAfterStoppingTime_apply_of_ne_top
                B (fun ω ↦ (σ ω : WithTop NNReal)) ω t hτ_ne_top
    _ = B (s + t) ω := by rw [hτ_untop]

/-- Helper for Theorem 21.18: on the slice `{σ = s}`, the stopped future Brownian vector is the
deterministic-time future vector anchored at `s`. -/
private lemma brownianStoppedFutureVector_eq_fixedTime_on_slice
    (B : NNReal → Ω → ℝ) (σ : Ω → NNReal)
    {n : ℕ} (times : Fin n → NNReal)
    {φ : (Fin n → ℝ) → ℝ} {s : NNReal} {ω : Ω}
    (hσω : (σ ω : WithTop NNReal) = s) :
    φ (fun i : Fin n ↦ B (σ ω + times i) ω) =
      φ (fun i : Fin n ↦ B (s + times i) ω) := by
  -- Proof comment: after rewriting the stopping time value to `s`, the future vector becomes the
  -- ordinary deterministic-time future vector.
  have hσeq : σ ω = s := WithTop.coe_injective hσω
  simp [hσeq]

/-- Helper for Theorem 21.18: on the slice `{σ = s}`, the stopped Brownian present value is the
deterministic-time value `B s`. -/
private lemma brownianStoppedValue_eq_fixedTime_on_slice
    (B : NNReal → Ω → ℝ) (σ : Ω → NNReal)
    {s : NNReal} {ω : Ω}
    (hσω : (σ ω : WithTop NNReal) = s) :
    stoppedValue B (fun ω ↦ (σ ω : WithTop NNReal)) ω = B s ω := by
  -- Proof comment: the generic stopped-value API already collapses to deterministic evaluation on
  -- the slice where the finite stopping time equals `s`.
  have hs_ne_top : (s : WithTop NNReal) ≠ ⊤ := WithTop.coe_ne_top
  have hs_untop : ((s : WithTop NNReal)).untop hs_ne_top = s := by
    exact WithTop.coe_injective (WithTop.coe_untop (x := (s : WithTop NNReal)) hs_ne_top)
  rw [stoppedValue, hσω, WithTop.untopA_eq_untop hs_ne_top, hs_untop]

/-- Helper for Theorem 21.18: a countable `NNReal`-valued stopping-time range stays countable
after coercion into `WithTop NNReal`. -/
private lemma countableRange_withTopCoe
    (σ : Ω → NNReal) (hσcount : (Set.range σ).Countable) :
    (Set.range fun ω ↦ (σ ω : WithTop NNReal)).Countable := by
  have hrange :
      Set.range (fun ω ↦ (σ ω : WithTop NNReal)) =
        ((fun r : NNReal ↦ (r : WithTop NNReal)) '' Set.range σ) := by
    ext z
    constructor
    · rintro ⟨ω, rfl⟩
      exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨ω, hω⟩, rfl⟩
      exact ⟨ω, by simpa [hω]⟩
  -- Proof comment: the coerced range is exactly the image of the original range under the
  -- injective embedding `NNReal ↪ WithTop NNReal`.
  rw [hrange]
  exact hσcount.image fun r : NNReal ↦ (r : WithTop NNReal)

/-- Helper for Theorem 21.18: for a countable-range stopping time, the stopped Brownian future
vector already satisfies the desired conditional-expectation formula on each atom `{σ = r}`. -/
private lemma brownianFutureVectorCondExp_eq_kernel_countableRangeStop_onSlice
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {n : ℕ} (times : Fin n → NNReal)
    {φ : (Fin n → ℝ) → ℝ}
    (hφ_meas : Measurable φ)
    (hφ_bdd : ∃ C : ℝ, ∀ v, |φ v| ≤ C)
    (r : NNReal) (_hr : r ∈ Set.range σ) :
    (P x : Measure Ω)[fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω) | hσ.measurableSpace] =ᵐ[
        (P x : Measure Ω).restrict {ω | (σ ω : WithTop NNReal) = r}]
      fun ω ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let A : Set Ω := {ω | (σ ω : WithTop NNReal) = r}
  let f : Ω → ℝ := fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω)
  let g : Ω → ℝ := fun ω ↦ φ (fun i : Fin n ↦ B (r + times i) ω)
  let k : Ω → ℝ := fun ω ↦
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
      (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))
  have hσcount' : (Set.range fun ω ↦ (σ ω : WithTop NNReal)).Countable :=
    countableRange_withTopCoe σ hσcount
  have hA_hist : MeasurableSet[hσ.measurableSpace] A := by
    simpa [A] using hσ.measurableSet_eq_of_countable_range' hσcount' r
  have hA_proc : MeasurableSet[processFiltration B r] A := by
    simpa [A] using hσ.measurableSet_eq_of_countable_range hσcount' r
  have hA : MeasurableSet A := hσ.measurableSpace_le _ hA_hist
  have hf_meas : Measurable f := by
    simpa [f] using
      measurable_brownianStoppedFutureVector_of_countableRange
        P B hB x σ hσ hσcount times hφ_meas
  have hg_meas : Measurable g := by
    refine hφ_meas.comp ?_
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((hB x).stronglyMeasurable (r + times i)).measurable
  have hf_int : Integrable f μ := by
    obtain ⟨C, hC⟩ := hφ_bdd
    -- Proof comment: the stopped future-cylinder observable is measurable and uniformly bounded.
    refine Integrable.of_bound hf_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC (fun i : Fin n ↦ B (σ ω + times i) ω)
  have hg_int : Integrable g μ := by
    obtain ⟨C, hC⟩ := hφ_bdd
    -- Proof comment: the deterministic-time future-cylinder observable has the same uniform bound.
    refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC (fun i : Fin n ↦ B (r + times i) ω)
  have hstop :
      μ[f | hσ.measurableSpace] =ᵐ[μ.restrict A] μ[f | processFiltration B r] := by
    -- Proof comment: on the atom `{σ = r}`, the stopping-time sigma algebra reduces to the
    -- deterministic filtration at time `r`.
    simpa [μ, A, f] using
      (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
        (μ := μ) (ℱ := processFiltration B) (f := f) hσ hσcount' r)
  have hindicator_fg :
      A.indicator f = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A
    · have hσω : (σ ω : WithTop NNReal) = r := hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact
        brownianStoppedFutureVector_eq_fixedTime_on_slice
          (B := B) (σ := σ) (times := times) (φ := φ) hσω
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hproc :
      μ[f | processFiltration B r] =ᵐ[μ.restrict A] μ[g | processFiltration B r] := by
    rw [ae_eq_restrict_iff_indicator_ae_eq hA]
    -- Proof comment: conditional expectation is local on the measurable atom `{σ = r}` because
    -- the indicators of the stopped and deterministic-time observables agree globally.
    exact
      ((MeasureTheory.condExp_indicator hf_int hA_proc).symm.trans
        ((MeasureTheory.condExp_congr_ae
            (Filter.Eventually.of_forall fun ω ↦ by simpa using congrFun hindicator_fg ω)).trans
          (MeasureTheory.condExp_indicator hg_int hA_proc)))
  have hdet :
      μ[g | processFiltration B r] =ᵐ[μ]
        fun ω ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B r ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
    -- Proof comment: after freezing the atom value to `r`, this is exactly the deterministic-time
    -- future-cylinder conditional-expectation formula.
    simpa [μ, g] using
      (brownianProcessFiltration_futureCylinderCondExp_eq_kernelIntegral
        P B hB x r times hφ_meas hφ_bdd)
  have hdetA :
      μ[g | processFiltration B r] =ᵐ[μ.restrict A] k := by
    -- Proof comment: after restricting to `{σ = r}`, the kernel row rewrites by the literal
    -- identity `σ ω = r`.
    rw [Filter.EventuallyEq, ae_restrict_iff' hA]
    filter_upwards [hdet] with ω hdetω hω
    have hσeq : σ ω = r := WithTop.coe_injective hω
    simpa [k, hσeq] using hdetω
  exact hstop.trans (hproc.trans hdetA)

/-- Helper for Theorem 21.18: for a countable-range stopping time, the stopped Brownian future
vector already satisfies the desired conditional-expectation formula slicewise. -/
private lemma brownianFutureVectorCondExp_eq_kernel_countableRangeStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {n : ℕ} (times : Fin n → NNReal)
    {φ : (Fin n → ℝ) → ℝ}
    (hφ_meas : Measurable φ)
    (hφ_bdd : ∃ C : ℝ, ∀ v, |φ v| ≤ C) :
    (P x : Measure Ω)[fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω) | hσ.measurableSpace] =ᵐ[
        (P x : Measure Ω)]
      fun ω ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
  classical
  let A : Set.range σ → Set Ω := fun r ↦ {ω | (σ ω : WithTop NNReal) = r.1}
  letI : Countable (Set.range σ) := hσcount.to_subtype
  have hcover : (⋃ r : Set.range σ, A r) = Set.univ := by
    ext ω
    constructor
    · intro _
      simp
    · intro _
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨σ ω, ⟨ω, rfl⟩⟩, ?_⟩
      simp [A]
  -- Route correction: the atomwise conditional-expectation transport is now isolated in the
  -- dedicated slice lemma, so the outer theorem is only the countable partition assembly.
  have hUnion :
      (P x : Measure Ω)[fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω) | hσ.measurableSpace] =ᵐ[
          (P x : Measure Ω).restrict (⋃ r : Set.range σ, A r)]
        fun ω ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
    rw [MeasureTheory.ae_eq_restrict_iUnion_iff A]
    intro r
    simpa [A] using
      (brownianFutureVectorCondExp_eq_kernel_countableRangeStop_onSlice
        P B hB x σ hσ hσcount times hφ_meas hφ_bdd r.1 r.2)
  simpa [hcover] using hUnion
/-- Helper for Theorem 21.18: for a countable-range stopping time, every finite Brownian future
vector cylinder event already matches the translated kernel row. -/
private lemma brownianFutureVectorEvent_condExp_eq_kernel_countableRangeStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {n : ℕ} (times : Fin n → NNReal)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)⟦(fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω) ⁻¹' A
        | hσ.measurableSpace⟧) =ᵐ[(P x : Measure Ω)]
      fun ω ↦
        (((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))).real A) := by
  let φ : (Fin n → ℝ) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hφ_meas : Measurable φ := by
    -- Proof comment: the finite-vector indicator of the measurable event `A` is measurable.
    exact Measurable.indicator measurable_const hA
  have hφ_bdd : ∃ C : ℝ, ∀ v, |φ v| ≤ C := by
    -- Proof comment: an indicator only takes the values `0` and `1`, so it is uniformly bounded.
    refine ⟨1, ?_⟩
    intro v
    by_cases hv : v ∈ A
    · simp [φ, hv]
    · simp [φ, hv]
  have hcond :
      (P x : Measure Ω)[fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω)
          | hσ.measurableSpace] =ᵐ[(P x : Measure Ω)]
        fun ω ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
    -- Proof comment: the event formula is the indicator specialization of the finite-vector
    -- conditional-expectation identity.
    exact
      brownianFutureVectorCondExp_eq_kernel_countableRangeStop
        P B hB x σ hσ hσcount times hφ_meas hφ_bdd
  have hleft :
      (fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω)) =
        Set.indicator ((fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω) ⁻¹' A)
          (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : (fun i : Fin n ↦ B (σ ω + times i) ω) ∈ A
    · simp [φ, hω]
    · simp [φ, hω]
  have hright :
      (fun ω ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))) =
        fun ω ↦
          (((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))).real A) := by
    funext ω
    -- Proof comment: integrating the indicator of `A` against the pushed-forward kernel row
    -- returns the row mass of `A`.
    simpa [φ] using
      (MeasureTheory.integral_indicator_one
        (μ := ((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))) hA)
  -- Proof comment: after rewriting both sides as indicator expectations, the identity is exactly
  -- the desired cylinder-event conditional expectation formula.
  simpa [hleft, hright] using hcond
/-- Helper for Theorem 21.18: reindexing the ordered tuple attached to `I.orderEmbOfFin` recovers
the ordinary finite restriction map on `NNReal → ℝ`. -/
private lemma orderedTimeRestriction_eq_restrict
    (I : Finset NNReal) (y : NNReal → ℝ) :
    let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
    let t : Fin I.card → NNReal := fun i ↦ I.orderEmbOfFin rfl i
    (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) (fun i ↦ y (t i)) = I.restrict y := by
  -- Proof comment: the order isomorphism `Fin I.card ≃ I` turns the sorted tuple coordinates back
  -- into the canonical finite restriction map on `I`.
  dsimp
  ext j
  have hindex :
      I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : I ↦ ℝ) ((I.orderIsoOfFin rfl).toEquiv))
      (fun i ↦ y (I.orderEmbOfFin rfl i)) j) = I.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [Finset.restrict_def, hindex]

/-- Helper for Theorem 21.18: reindexing the ordered tuple attached to `I.orderEmbOfFin` recovers
the ordinary finite restriction map on `(j : J) → ℝ`. -/
private lemma orderedSubtypeRestriction_eq_restrict
    {J : Set NNReal} (I : Finset J) (y : (j : J) → ℝ) :
    let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
    let t : Fin I.card → J := fun i ↦ I.orderEmbOfFin rfl i
    (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) (fun i ↦ y (t i)) = I.restrict y := by
  -- Proof comment: the same finite-order reindexing argument works verbatim on the subtype-indexed
  -- restricted path space.
  dsimp
  ext j
  have hindex :
      I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : I ↦ ℝ) ((I.orderIsoOfFin rfl).toEquiv))
      (fun i ↦ y (I.orderEmbOfFin rfl i)) j) = I.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [Finset.restrict_def, hindex]

/-- Helper for Theorem 21.18: pulling a future-path cylinder back along
`futurePathAfterStoppingTime B τ` is the same as pulling back its finite base set along the
restricted future path. -/
private lemma futurePathAfterStoppingTime_preimage_cylinder_eq_restrictPreimage
    (B : NNReal → Ω → ℝ) (τ : Ω → WithTop NNReal)
    (I : Finset NNReal) (S : Set (∀ i : I, ℝ)) :
    futurePathAfterStoppingTime B τ ⁻¹' MeasureTheory.cylinder I S =
      (fun ω ↦ I.restrict (futurePathAfterStoppingTime B τ ω)) ⁻¹' S := by
  -- Proof comment: membership in a finite cylinder is exactly membership of the restricted path
  -- in its base set `S`.
  ext ω
  simp [MeasureTheory.cylinder]

/-- Helper for Theorem 21.18: for a countable-range stopping time, measurable path cylinders
already match the translated Brownian path-kernel row. -/
private lemma brownianFuturePathCylinderEvent_eq_kernel_countableRangeStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {I : Finset NNReal} {S : Set (∀ i : I, ℝ)} (hS : MeasurableSet S) :
    ((P x : Measure Ω)⟦futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ⁻¹'
        MeasureTheory.cylinder I S | hσ.measurableSpace⟧) =ᵐ[(P x : Measure Ω)]
      fun ω ↦
        ((brownianTranslatedPathKernel P B (B (σ ω) ω)).real
          (MeasureTheory.cylinder I S)) := by
  let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
  let times : Fin I.card → NNReal := fun i ↦ I.orderEmbOfFin rfl i
  let A : Set (Fin I.card → ℝ) := (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) ⁻¹' S
  have hA : MeasurableSet A := by
    -- Proof comment: the ordered tuple event corresponding to the cylinder base `S` is measurable
    -- because `piCongrLeft` is a measurable equivalence.
    exact (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e).measurableSet_preimage.2 hS
  have hcond :
      ((P x : Measure Ω)⟦(fun ω ↦ fun i : Fin I.card ↦ B (σ ω + times i) ω) ⁻¹' A
          | hσ.measurableSpace⟧) =ᵐ[(P x : Measure Ω)]
        fun ω ↦
          (((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
            (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (times i))).real A) := by
    -- Proof comment: first apply the already proved finite-vector event formula to the ordered
    -- tuple of cylinder times.
    exact
      brownianFutureVectorEvent_condExp_eq_kernel_countableRangeStop
        P B hB x σ hσ hσcount times hA
  have hleft :
      (fun ω ↦ fun i : Fin I.card ↦ B (σ ω + times i) ω) ⁻¹' A =
        futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ⁻¹'
          MeasureTheory.cylinder I S := by
    calc
      (fun ω ↦ fun i : Fin I.card ↦ B (σ ω + times i) ω) ⁻¹' A
          = (fun ω ↦
              (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e)
                (fun i : Fin I.card ↦ B (σ ω + times i) ω)) ⁻¹' S := by
              rfl
      _ = (fun ω ↦ I.restrict
            (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω)) ⁻¹' S := by
            congr 1
            funext ω
            have hτ_ne_top : ((σ ω : NNReal) : WithTop NNReal) ≠ ⊤ := WithTop.coe_ne_top
            have hcoord :
                (fun i : Fin I.card ↦ B (σ ω + times i) ω) =
                  fun i : Fin I.card ↦
                    futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω (times i) := by
              funext i
              symm
              simpa [times] using
                futurePathAfterStoppingTime_apply_of_ne_top
                  B (fun ω ↦ (σ ω : WithTop NNReal)) ω (times i) hτ_ne_top
            rw [hcoord]
            simpa [e, times] using
              (orderedTimeRestriction_eq_restrict I
                (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω))
      _ = futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ⁻¹'
          MeasureTheory.cylinder I S := by
            symm
            exact
              futurePathAfterStoppingTime_preimage_cylinder_eq_restrictPreimage
                B (fun ω ↦ (σ ω : WithTop NNReal)) I S
  have hright :
      (fun ω ↦
        (((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (times i))).real A)) =
        fun ω ↦
          ((brownianTranslatedPathKernel P B (B (σ ω) ω)).real
            (MeasureTheory.cylinder I S)) := by
    funext ω
    calc
      (((brownianTranslatedPathKernel P B (B (σ ω) ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (times i))).real A)
          = (brownianTranslatedPathKernel P B (B (σ ω) ω)).real
              ((fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (times i)) ⁻¹' A) := by
                simpa [times] using
                  (MeasureTheory.map_measureReal_apply
                    (μ := brownianTranslatedPathKernel P B (B (σ ω) ω))
                    (f := fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (times i))
                    (measurable_pathEvalVector times) hA)
      _ = (brownianTranslatedPathKernel P B (B (σ ω) ω)).real
            (MeasureTheory.cylinder I S) := by
              congr 1
              ext y
              change
                ((MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e)
                    (fun i : Fin I.card ↦ y (times i)) ∈ S) ↔
                  y ∈ MeasureTheory.cylinder I S
              rw [orderedTimeRestriction_eq_restrict I y]
              simp [MeasureTheory.cylinder, A, e]
  -- Proof comment: the cylinder event is exactly the ordered finite-vector event after normalizing
  -- both the pullback event and the kernel row mass.
  simpa [hleft, hright] using hcond
/-- Helper for Theorem 21.18: a restricted-law identity on every `𝓕_τ`-measurable slice implies
the corresponding conditional-expectation formula for each measurable future-path event. -/
private lemma futurePathEvent_eq_kernel_of_restrictedLaw
    (μ : Measure Ω) [IsFiniteMeasure μ] {κ : Kernel ℝ (NNReal → ℝ)} [IsMarkovKernel κ]
    (B : NNReal → Ω → ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    (hfuture_meas : Measurable (futurePathAfterStoppingTime B τ))
    (hstopped_meas : Measurable[hτ.measurableSpace] (stoppedValue B τ))
    (hRestrictedLaw :
      ∀ ⦃s : Set Ω⦄, MeasurableSet[hτ.measurableSpace] s →
        ((μ.restrict s).map (futurePathAfterStoppingTime B τ)) =
          κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ)))
    ⦃A : Set (NNReal → ℝ)⦄ (hA : MeasurableSet A) :
    μ⟦futurePathAfterStoppingTime B τ ⁻¹' A | hτ.measurableSpace⟧ =ᵐ[μ]
      fun ω ↦ (κ (stoppedValue B τ ω)).real A := by
  let f : Ω → ℝ :=
    fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePathAfterStoppingTime B τ ω)
  let g : Ω → ℝ := fun ω ↦ (κ (stoppedValue B τ ω)).real A
  let F : Set Ω := futurePathAfterStoppingTime B τ ⁻¹' A
  have hgenerated_le : hτ.measurableSpace ≤ ‹MeasurableSpace Ω› := hτ.measurableSpace_le
  have hfutureEvent_meas : MeasurableSet F := by
    simpa [F] using hfuture_meas hA
  have hf_int : Integrable f μ := by
    -- Proof comment: the path-event indicator is bounded by `1`, so it is integrable.
    refine Integrable.of_bound
      ((Measurable.indicator measurable_const hA).comp hfuture_meas).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : futurePathAfterStoppingTime B τ ω ∈ A
      · simp [f, hω]
      · simp [f, hω]
  have hstopped_meas_ambient : Measurable (stoppedValue B τ) := by
    intro s hs
    exact hτ.measurableSpace_le _ (hstopped_meas hs)
  have hg_meas_hτ : Measurable[hτ.measurableSpace] g := by
    -- Proof comment: kernel row masses are measurable in the stopped state and hence along
    -- `𝓕_τ`.
    simpa [g] using (((Kernel.measurable_coe κ hA).ennreal_toReal).comp hstopped_meas)
  have hg_meas_ambient : Measurable g := by
    simpa [g] using
      (((Kernel.measurable_coe κ hA).ennreal_toReal).comp hstopped_meas_ambient)
  have hf_eq_indicator : f = Set.indicator F (fun _ ↦ (1 : ℝ)) := by
    -- Proof comment: composing the indicator of `A` with the stopped future path is the same as
    -- the indicator of the preimage event `F`.
    funext ω
    by_cases hω : futurePathAfterStoppingTime B τ ω ∈ A
    · simp [f, F, hω]
    · simp [f, F, hω]
  have hCond :
      g =ᵐ[μ] μ[f | hτ.measurableSpace] := by
    refine
      MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hf_int
        (fun s hs hμs ↦ ?_) (fun s hs hμs ↦ ?_) hg_meas_hτ.aestronglyMeasurable
    · -- Proof comment: the candidate kernel row mass is also bounded by `1` on every history
      -- slice because each kernel row is a probability measure.
      refine IntegrableOn.of_bound hμs hg_meas_ambient.aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      have hmass_le :
          (κ (stoppedValue B τ ω)).real A ≤ 1 := by
        calc
          (κ (stoppedValue B τ ω)).real A ≤ (κ (stoppedValue B τ ω)).real Set.univ := by
            exact
              MeasureTheory.measureReal_mono (μ := κ (stoppedValue B τ ω))
                (s₁ := A) (s₂ := Set.univ) (by intro y hy; simp)
          _ = 1 := by simp
      simpa [g, abs_of_nonneg MeasureTheory.measureReal_nonneg] using hmass_le
    · have hs_ambient : MeasurableSet s := hgenerated_le _ hs
      -- Proof comment: on each `𝓕_τ`-measurable slice, the assumed restricted law identifies the
      -- stopped future-path mass of `A` with the set integral of the kernel row mass.
      calc
        ∫ ω in s, g ω ∂μ
            = ((κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ))).real A) := by
                symm
                simpa [g] using
                  (kernelComp_restrictMap_real_eq_setIntegral_local
                    (κ := κ) (μ := μ) (hY := hstopped_meas_ambient) hs_ambient hA)
        _ = (((μ.restrict s).map (futurePathAfterStoppingTime B τ)).real A) := by
              rw [← hRestrictedLaw hs]
        _ = ∫ ω in s, f ω ∂μ := by
              calc
                (((μ.restrict s).map (futurePathAfterStoppingTime B τ)).real A)
                    = (μ.restrict s).real F := by
                        simpa [F] using
                          (MeasureTheory.map_measureReal_apply
                            (μ := μ.restrict s) (f := futurePathAfterStoppingTime B τ)
                            hfuture_meas hA)
                _ = ∫ ω, Set.indicator F (fun _ ↦ (1 : ℝ)) ω ∂(μ.restrict s) := by
                      symm
                      simpa [F] using
                        (MeasureTheory.integral_indicator_one
                          (μ := μ.restrict s) (s := F) hfutureEvent_meas)
                _ = ∫ ω in s, Set.indicator F (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                      rfl
                _ = ∫ ω in s, f ω ∂μ := by
                      rw [hf_eq_indicator]
  -- Proof comment: rewriting the generic conditional expectation of the indicator function back
  -- into event notation gives the desired stopped future-path event formula.
  simpa [f, F] using hCond.symm

/-- Helper for Theorem 21.18: a countable-range finite stopping time gives an ambient measurable
stopped future path. -/
private lemma measurable_futurePathAfterStoppingTime_of_countableRange
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable) :
    Measurable (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal))) := by
  have hσ_meas : Measurable σ := by
    -- Proof comment: finite stopping times become ambient measurable after removing the
    -- `WithTop` coercion.
    simpa using (hσ.measurable.untopA).mono hσ.measurableSpace_le le_rfl
  refine measurable_pi_lambda _ fun t ↦ ?_
  have hcoord :
      (fun ω : Ω ↦ futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω t) =
        fun ω : Ω ↦ B (σ ω + t) ω := by
    -- Proof comment: for finite stopping times, each future-path coordinate is the shifted
    -- Brownian value at deterministic offset `t`.
    funext ω
    symm
    simpa using
      (futurePathAfterStoppingTime_apply_of_ne_top
        B (fun ω ↦ (σ ω : WithTop NNReal)) ω t WithTop.coe_ne_top)
  rw [hcoord]
  exact measurable_brownianShiftedValue_of_countableRange P B hB σ hσ_meas hσcount t
/-- Helper for Theorem 21.18: for a countable-range stopping time, the restricted law of the
stopped future Brownian path already agrees with the translated Brownian path-kernel law on every
history slice. -/
private lemma brownianFuturePathRestrictedLaw_eq_kernel_countableRangeStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s) :
    (((P x : Measure Ω).restrict s).map
      (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)))) =
      brownianTranslatedPathKernel P B ∘ₘ
        (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let τ : Ω → WithTop NNReal := fun ω ↦ (σ ω : WithTop NNReal)
  let future : Ω → NNReal → ℝ := futurePathAfterStoppingTime B τ
  let Z : Ω → ℝ := fun ω ↦ B (σ ω) ω
  let ν : Measure (NNReal → ℝ) := ((μ.restrict s).map future)
  let ρ : Measure (NNReal → ℝ) :=
    brownianTranslatedPathKernel P B ∘ₘ ((μ.restrict s).map Z)
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  have hσ_meas : Measurable σ := by
    -- Proof comment: coercing away the finite `WithTop` stopping time yields an ambient
    -- measurable `NNReal`-valued time.
    simpa using (hσ.measurable.untopA).mono hσ.measurableSpace_le le_rfl
  have hfuture_meas : Measurable future := by
    -- Proof comment: countable-range stopping times make every future-path coordinate measurable.
    simpa [future, τ] using
      measurable_futurePathAfterStoppingTime_of_countableRange P B hB σ hσ hσcount
  have hZ_meas : Measurable Z := by
    -- Proof comment: the stopped present value is the shifted Brownian coordinate at time `0`.
    simpa [Z] using
      measurable_brownianShiftedValue_of_countableRange P B hB σ hσ_meas hσcount 0
  have hCylinderEq :
      ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : NNReal ↦ ℝ), ν u = ρ u := by
    intro u hu
    obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders u).1 hu
    let C : Set (NNReal → ℝ) := MeasureTheory.cylinder I S
    have hC_meas : MeasurableSet C := by
      -- Proof comment: measurable cylinders are measurable in the ambient product sigma algebra.
      rw [← MeasureTheory.generateFrom_measurableCylinders]
      exact MeasurableSpace.measurableSet_generateFrom hu
    have hIndicator_int :
        Integrable (fun ω ↦ Set.indicator (future ⁻¹' C) (fun _ ↦ (1 : ℝ)) ω) μ := by
      -- Proof comment: the cylinder-event indicator is bounded by `1`, so it is integrable.
      refine Integrable.of_bound
        ((Measurable.indicator measurable_const ((hfuture_meas hC_meas))).aestronglyMeasurable) 1 ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        by_cases hω : future ω ∈ C
        · simp [C, hω]
        · simp [C, hω]
    have hEventCond :
        μ⟦future ⁻¹' C | hσ.measurableSpace⟧ =ᵐ[μ]
          fun ω ↦ (brownianTranslatedPathKernel P B (Z ω)).real C := by
      -- Proof comment: the earlier cylinder-event conditional-expectation formula is exactly the
      -- needed slice identity for the path cylinder `C`.
      simpa [C, future, τ, Z] using
        (brownianFuturePathCylinderEvent_eq_kernel_countableRangeStop
          P B hB x σ hσ hσcount (I := I) (S := S) hS)
    have hleft_real :
        ν.real C = ∫ ω in s, (brownianTranslatedPathKernel P B (Z ω)).real C ∂μ := by
      calc
        ν.real C = (μ.restrict s).real (future ⁻¹' C) := by
            rw [show ν = ((μ.restrict s).map future) by rfl]
            simpa [C] using
              (MeasureTheory.map_measureReal_apply
                (μ := μ.restrict s) (f := future) hfuture_meas hC_meas)
        _ = μ.real (future ⁻¹' C ∩ s) := by
              simpa [C] using
                (MeasureTheory.measureReal_restrict_apply
                  (μ := μ) (s := s) (t := future ⁻¹' C) (hfuture_meas hC_meas))
        _ = ∫ ω in s, Set.indicator (future ⁻¹' C) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              symm
              calc
                ∫ ω in s, Set.indicator (future ⁻¹' C) (fun _ ↦ (1 : ℝ)) ω ∂μ
                    = ∫ ω, Set.indicator (future ⁻¹' C) (fun _ ↦ (1 : ℝ)) ω ∂(μ.restrict s) := by
                        rfl
                _ = (μ.restrict s).real (future ⁻¹' C) := by
                      simpa [C] using
                        (MeasureTheory.integral_indicator_one
                          (μ := μ.restrict s) (s := future ⁻¹' C) (hfuture_meas hC_meas))
                _ = μ.real (future ⁻¹' C ∩ s) := by
                      simpa [C] using
                        (MeasureTheory.measureReal_restrict_apply
                          (μ := μ) (s := s) (t := future ⁻¹' C) (hfuture_meas hC_meas))
        _ = ∫ ω in s, (μ⟦future ⁻¹' C | hσ.measurableSpace⟧) ω ∂μ := by
              symm
              exact MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hIndicator_int hs
        _ = ∫ ω in s, (brownianTranslatedPathKernel P B (Z ω)).real C ∂μ := by
              exact MeasureTheory.integral_congr_ae (ae_restrict_of_ae hEventCond)
    have hright_real :
        ρ.real C = ∫ ω in s, (brownianTranslatedPathKernel P B (Z ω)).real C ∂μ := by
      simpa [ρ, C, Z] using
        (kernelComp_restrictMap_real_eq_setIntegral_local
          (κ := brownianTranslatedPathKernel P B)
          (μ := μ) (hY := hZ_meas) (s := s) (A := C)
          (hs := hσ.measurableSpace_le _ hs) hC_meas)
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := ν) (ν := ρ) (s := C) (t := C)).mp
        (hleft_real.trans hright_real.symm)
  have hEq : ν = ρ := by
    -- Proof comment: equality on measurable cylinders follows from the already proved
    -- cylinder-event conditional-expectation formula, and finite-measure extensionality upgrades
    -- this to equality of the full path laws.
    refine
      MeasureTheory.ext_of_generate_finite
        (MeasureTheory.measurableCylinders fun _ : NNReal ↦ ℝ)
        MeasureTheory.generateFrom_measurableCylinders.symm
        MeasureTheory.isPiSystem_measurableCylinders
        hCylinderEq
        ?_
    · simpa using
        hCylinderEq Set.univ
          (MeasureTheory.univ_mem_measurableCylinders (fun _ : NNReal ↦ ℝ))
  exact hEq
/-- Helper for Theorem 21.18: the dyadic ceiling approximation `2^{-n}⌈2^n τ⌉` of an
`NNReal`-valued time. -/
private def brownianDyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper for Theorem 21.18: the dyadic ceiling approximation dominates the original finite
stopping time pointwise. -/
private lemma le_brownianDyadicCeilApprox
    (n : ℕ) (τ : Ω → NNReal) :
    ∀ ω, τ ω ≤ brownianDyadicCeilApprox n τ ω := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ n
  have hc_pos : 0 < c := by
    -- Proof comment: every dyadic mesh denominator is strictly positive.
    dsimp [c]
    positivity
  have hceil :
      (c * τ ω : NNReal) ≤ (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) := by
    -- Proof comment: the ceiling of a real number always lies above that number.
    exact_mod_cast (Nat.le_ceil (((c * τ ω : NNReal) : ℝ)))
  -- Proof comment: divide the basic ceiling inequality by the positive mesh denominator.
  refine (le_div_iff₀ hc_pos).2 ?_
  simpa [brownianDyadicCeilApprox, c, mul_comm] using hceil

/-- Helper for Theorem 21.18: the dyadic ceiling event `{τₙ ≤ t}` rewrites as an ordinary
deterministic threshold event for `τ`. -/
private lemma brownianDyadicCeilApprox_event_le_eq
    (n : ℕ) (τ : Ω → NNReal) (t : NNReal) :
    {ω | (brownianDyadicCeilApprox n τ ω : WithTop NNReal) ≤ t} =
      {ω | (τ ω : WithTop NNReal) ≤
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
          ((2 : NNReal) ^ n))} := by
  ext ω
  have hbody :
      brownianDyadicCeilApprox n τ ω ≤ t ↔
        τ ω ≤
          ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
            ((2 : NNReal) ^ n)) := by
    let c : NNReal := (2 : NNReal) ^ n
    have hc_pos : 0 < c := by
      -- Proof comment: the dyadic mesh denominator is strictly positive.
      dsimp [c]
      positivity
    have hDiv :
        brownianDyadicCeilApprox n τ ω ≤ t ↔
          (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t := by
      -- Proof comment: multiplying by the positive dyadic scale removes the denominator.
      dsimp [brownianDyadicCeilApprox, c]
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
    -- Proof comment: the dyadic ceiling only asks whether `τ` already fell below the latest mesh
    -- point not exceeding `t`.
    exact hDiv.trans (hCeilFloor.trans hFloorDiv)
  exact_mod_cast hbody

/-- Helper for Theorem 21.18: dyadic ceiling approximants of an `NNReal`-valued stopping time are
again stopping times. -/
private lemma brownianDyadicCeilApprox_isStoppingTime
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›} {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop NNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (brownianDyadicCeilApprox n τ ω : WithTop NNReal) := by
  intro t
  let q : NNReal :=
    ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ n))
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    -- Proof comment: the dyadic mesh denominator is positive.
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
  -- Proof comment: rewrite the dyadic event to an original stopping event at time `q`, then use
  -- filtration monotonicity along `q ≤ t`.
  change MeasurableSet[ℱ t] {ω | (brownianDyadicCeilApprox n τ ω : WithTop NNReal) ≤ t}
  rw [brownianDyadicCeilApprox_event_le_eq n τ t]
  simpa [q] using (ℱ.mono hq_le_t _ (hτ q))
/-- Helper for Theorem 21.18: each dyadic ceiling approximation has countable range. -/
private lemma brownianDyadicCeilApprox_countableRange
    (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ brownianDyadicCeilApprox n τ ω).Countable := by
  refine (Set.countable_range fun k : ℕ ↦ ((k : NNReal) / ((2 : NNReal) ^ n))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  simp [brownianDyadicCeilApprox]

/-- Helper for Theorem 21.18: dyadic ceiling approximations converge pointwise to the original
finite stopping time. -/
private lemma brownianDyadicCeilApprox_tendsto
    (ρ : Ω → NNReal) :
    ∀ ω, Tendsto (fun m ↦ brownianDyadicCeilApprox m ρ ω) atTop (𝓝 (ρ ω)) := by
  intro ω
  have hEq :
      (fun m ↦ brownianDyadicCeilApprox m ρ ω) =
        fun m ↦ (((Nat.ceil ((ρ ω : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
    funext m
    unfold brownianDyadicCeilApprox
    congr 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (congrArg (fun x : NNReal ↦ (x : ℝ)) (mul_comm ((2 : NNReal) ^ m) (ρ ω)))
  -- Proof comment: this is the standard dyadic approximation
  -- `⌈ρ(ω) 2^m⌉ / 2^m → ρ(ω)`.
  rw [hEq]
  refine (NNReal.tendsto_coe).mp ?_
  simpa using
    (tendsto_nat_ceil_mul_div_atTop (a := (ρ ω : ℝ))
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Theorem 21.18: every `𝓕_σ`-measurable history slice stays measurable for the dyadic
ceiling approximants because those approximants only reveal more past. -/
private lemma measurableSet_brownianDyadicCeilApprox
    (B : NNReal → Ω → ℝ) {σ : Ω → NNReal}
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s) (n : ℕ) :
    MeasurableSet[(brownianDyadicCeilApprox_isStoppingTime hσ n).measurableSpace] s := by
  have hσ_le_σn :
      (fun ω ↦ (σ ω : WithTop NNReal)) ≤
        fun ω ↦ (brownianDyadicCeilApprox n σ ω : WithTop NNReal) := by
    intro ω
    change (σ ω : WithTop NNReal) ≤ (brownianDyadicCeilApprox n σ ω : WithTop NNReal)
    exact_mod_cast le_brownianDyadicCeilApprox n σ ω
  -- Proof comment: each dyadic ceiling dominates `σ`, so every `𝓕_σ`-measurable set stays
  -- measurable for the larger stopping-time sigma-algebra `𝓕_{σₙ}`.
  exact
    (hσ.measurableSpace_mono (brownianDyadicCeilApprox_isStoppingTime hσ n) hσ_le_σn) _ hs

/-- Helper for Theorem 21.18: the dyadic floor approximation `2^{-n}⌊2^n τ⌋` of an
`NNReal`-valued time. -/
private def brownianDyadicFloorApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.floor ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper for Theorem 21.18: dyadic floor approximations stay below the original finite
stopping time pointwise. -/
private lemma brownianDyadicFloorApprox_le
    (n : ℕ) (τ : Ω → NNReal) :
    ∀ ω, brownianDyadicFloorApprox n τ ω ≤ τ ω := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ n
  have hc_pos : 0 < c := by
    -- Proof comment: every dyadic mesh denominator is strictly positive.
    dsimp [c]
    positivity
  have hfloor :
      (Nat.floor (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * τ ω := by
    -- Proof comment: the floor of a real number always lies below that number.
    exact_mod_cast
      (Nat.floor_le (show 0 ≤ (((c * τ ω : NNReal) : ℝ)) by positivity))
  -- Proof comment: divide the basic floor inequality by the positive mesh denominator.
  refine (div_le_iff₀ hc_pos).2 ?_
  simpa [brownianDyadicFloorApprox, c, mul_comm] using hfloor

/-- Helper for Theorem 21.18: each dyadic floor approximation has countable range. -/
private lemma brownianDyadicFloorApprox_countableRange
    (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ brownianDyadicFloorApprox n τ ω).Countable := by
  refine (Set.countable_range fun k : ℕ ↦ ((k : NNReal) / ((2 : NNReal) ^ n))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.floor ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  -- Proof comment: every dyadic floor value lies on the mesh `2⁻ⁿ ℕ`.
  simp [brownianDyadicFloorApprox]

/-- Helper for Theorem 21.18: dyadic floor approximations converge pointwise to the original
finite stopping time. -/
private lemma brownianDyadicFloorApprox_tendsto
    (ρ : Ω → NNReal) :
    ∀ ω, Tendsto (fun m ↦ brownianDyadicFloorApprox m ρ ω) atTop (𝓝 (ρ ω)) := by
  intro ω
  have hEq :
      (fun m ↦ brownianDyadicFloorApprox m ρ ω) =
        fun m ↦ (((Nat.floor ((ρ ω : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
    funext m
    unfold brownianDyadicFloorApprox
    congr 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (congrArg (fun x : NNReal ↦ (x : ℝ)) (mul_comm ((2 : NNReal) ^ m) (ρ ω)))
  -- Proof comment: this is the standard dyadic approximation
  -- `⌊ρ(ω) 2^m⌋ / 2^m → ρ(ω)`.
  rw [hEq]
  refine (NNReal.tendsto_coe).mp ?_
  simpa using
    (tendsto_nat_floor_mul_div_atTop (a := (ρ ω : ℝ))
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Theorem 21.18: the dyadic floor stopped values are already
`𝓕_τ`-measurable. -/
private lemma measurable_brownianDyadicStoppedValue
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    (n : ℕ) :
    Measurable[hτ.measurableSpace]
      (fun ω ↦ B (brownianDyadicFloorApprox n (fun ω ↦ (τ ω).untopA) ω) ω) := by
  let σ : Ω → NNReal := fun ω ↦ (τ ω).untopA
  have hσ_meas : Measurable[hτ.measurableSpace] σ := by
    -- Proof comment: the finite representative `τ.untopA` is measurable for the stopping-time
    -- sigma algebra.
    simpa [σ] using hτ.measurable.untopA
  have hσn_meas :
      Measurable[hτ.measurableSpace] (brownianDyadicFloorApprox n σ) := by
    -- Proof comment: the dyadic floor approximation is a measurable transform of `τ.untopA`.
    unfold brownianDyadicFloorApprox
    fun_prop
  -- Route correction: unlike the earlier dyadic ceilings, the floor clocks stay below `τ`, so
  -- the existing countable-range `𝓕_τ` bridge applies directly.
  exact
    measurable_brownianValue_of_countableRange_hτ
      P B hB τ hτ (brownianDyadicFloorApprox n σ) hσn_meas
      (brownianDyadicFloorApprox_countableRange n σ)
      (by
        intro ω
        simpa [σ] using brownianDyadicFloorApprox_le n σ ω)
/-- Helper for Theorem 21.18: every strong-Markov witness kernel yields the corresponding
stopped-future path event formula. -/
lemma futurePathEvent_eq_kernel_of_hasStrongMarkovProperty
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (κ : Kernel ℝ (NNReal → ℝ))
    (hStrong : HasStrongMarkovProperty P B κ)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    (hτfinite : ∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤)
    {A : Set (NNReal → ℝ)} (hA : MeasurableSet A) :
    (P x : Measure Ω)⟦futurePathAfterStoppingTime B τ ⁻¹' A | hτ.measurableSpace⟧ =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (κ (stoppedValue B τ ω)).real A := by
  let f : (NNReal → ℝ) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hf_meas : Measurable f := by
    -- Proof comment: the test functional is the measurable indicator of the measurable path event
    -- `A`.
    exact Measurable.indicator measurable_const hA
  have hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C := by
    -- Proof comment: the indicator test functional only takes the values `0` and `1`.
    refine ⟨1, ?_⟩
    intro y
    by_cases hy : y ∈ A
    · simp [f, hy]
    · simp [f, hy]
  have hcond :
      (P x : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime B τ ω) | hτ.measurableSpace] =ᵐ[
        (P x : Measure Ω)] fun ω ↦ ∫ y, f y ∂κ (stoppedValue B τ ω) := by
    -- Proof comment: specialize the strong Markov conditional-expectation identity to the
    -- indicator of `A`.
    exact
      (hasStrongMarkovProperty_iff P B κ).mp hStrong x τ hτ hτfinite f hf_meas hf_bdd
  have hleft :
      (fun ω ↦ f (futurePathAfterStoppingTime B τ ω)) =
        Set.indicator (futurePathAfterStoppingTime B τ ⁻¹' A) (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : futurePathAfterStoppingTime B τ ω ∈ A
    · simp [f, hω]
    · simp [f, hω]
  have hright :
      (fun ω ↦ ∫ y, f y ∂κ (stoppedValue B τ ω)) =
        fun ω ↦ (κ (stoppedValue B τ ω)).real A := by
    funext ω
    -- Proof comment: integrating the indicator of `A` against the kernel row returns the row mass
    -- of `A`.
    simpa [f] using
      (MeasureTheory.integral_indicator_one (μ := κ (stoppedValue B τ ω)) hA)
  -- Proof comment: after rewriting the indicator test on both sides, the conditional expectation
  -- identity is exactly the desired path-event formula.
  simpa [hleft, hright] using hcond
/-- Helper for Theorem 21.18: once the stopped future path law is known on all measurable path
events, the full strong Markov conditional-expectation formula follows by measure
reconstruction. -/
lemma hasStrongMarkovProperty_of_futurePathEventEqKernel
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (κ : Kernel ℝ (NNReal → ℝ)) [IsMarkovKernel κ]
    (hfuture_meas :
      ∀ (τ : Ω → WithTop NNReal)
        (hτ : IsStoppingTime (processFiltration B) τ),
          Measurable (futurePathAfterStoppingTime B τ))
    (hstopped_meas :
      ∀ (τ : Ω → WithTop NNReal)
        (hτ : IsStoppingTime (processFiltration B) τ),
          Measurable[hτ.measurableSpace] (stoppedValue B τ))
    (hLaw :
      ∀ (x : ℝ) (τ : Ω → WithTop NNReal)
        (hτ : IsStoppingTime (processFiltration B) τ)
        (hτfinite : ∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤)
        ⦃A : Set (NNReal → ℝ)⦄, MeasurableSet A →
          (P x : Measure Ω)⟦futurePathAfterStoppingTime B τ ⁻¹' A | hτ.measurableSpace⟧ =ᵐ[
            (P x : Measure Ω)] fun ω ↦ (κ (stoppedValue B τ ω)).real A) :
    HasStrongMarkovProperty P B κ := by
  refine (hasStrongMarkovProperty_iff P B κ).2 ?_
  intro x τ hτ hτfinite f hf_meas hf_bdd
  let μ : Measure Ω := (P x : Measure Ω)
  let lhs : Ω → ℝ :=
    μ[fun ω ↦ f (futurePathAfterStoppingTime B τ ω) | hτ.measurableSpace]
  let rhs : Ω → ℝ := fun ω ↦ ∫ y, f y ∂κ (stoppedValue B τ ω)
  have hgenerated_le : hτ.measurableSpace ≤ ‹MeasurableSpace Ω› := hτ.measurableSpace_le
  obtain ⟨C, hC⟩ := hf_bdd
  have hfuture_measurable : Measurable (futurePathAfterStoppingTime B τ) := hfuture_meas τ hτ
  have hstopped_meas_hτ : Measurable[hτ.measurableSpace] (stoppedValue B τ) :=
    hstopped_meas τ hτ
  have hstopped_meas_ambient : Measurable (stoppedValue B τ) := by
    intro s hs
    exact hτ.measurableSpace_le _ (hstopped_meas_hτ hs)
  have hf_int : Integrable (fun ω ↦ f (futurePathAfterStoppingTime B τ ω)) μ := by
    -- Proof comment: bounded measurable path functionals are integrable once the stopped future
    -- path is measurable.
    refine Integrable.of_bound (hf_meas.comp hfuture_measurable).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC (futurePathAfterStoppingTime B τ ω)
  have hKernelIntegral_meas : Measurable fun z : ℝ ↦ ∫ y, f y ∂κ z := by
    -- Proof comment: kernel integration of a measurable bounded path functional is measurable in
    -- the starting state.
    exact
      (hf_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : ℝ ↦ ∫ y, f y ∂κ z).measurable
  have hKernelIntegral_meas_hτ : Measurable[hτ.measurableSpace] rhs := by
    -- Proof comment: compose the measurable kernel integral with the stopped state.
    simpa [rhs] using hKernelIntegral_meas.comp hstopped_meas_hτ
  have hKernelIntegral_meas_ambient : Measurable rhs := by
    simpa [rhs] using hKernelIntegral_meas.comp hstopped_meas_ambient
  have hRestrictedLaw :
      ∀ ⦃s : Set Ω⦄, MeasurableSet[hτ.measurableSpace] s →
        ((μ.restrict s).map (futurePathAfterStoppingTime B τ)) =
          κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ)) := by
    intro s hs
    have hs_ambient : MeasurableSet s := hgenerated_le _ hs
    refine Measure.ext fun A hA ↦ ?_
    have hfutureEvent_meas : MeasurableSet (futurePathAfterStoppingTime B τ ⁻¹' A) :=
      hfuture_measurable hA
    have hindicator_int :
        Integrable
          (fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePathAfterStoppingTime B τ ω)) μ := by
      -- Proof comment: the indicator of a measurable stopped-future path event is bounded by `1`.
      refine Integrable.of_bound
        ((Measurable.indicator measurable_const hA).comp hfuture_measurable).aestronglyMeasurable
        1 ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        by_cases hω : futurePathAfterStoppingTime B τ ω ∈ A
        · simp [hω]
        · simp [hω]
    have hmass :
        μ.real (futurePathAfterStoppingTime B τ ⁻¹' A ∩ s) =
          ∫ ω in s, (κ (stoppedValue B τ ω)).real A ∂μ := by
      calc
        μ.real (futurePathAfterStoppingTime B τ ⁻¹' A ∩ s)
            = ∫ ω in s,
                Set.indicator A (fun _ ↦ (1 : ℝ)) (futurePathAfterStoppingTime B τ ω) ∂μ := by
                  symm
                  calc
                    ∫ ω in s, Set.indicator A (fun _ ↦ (1 : ℝ))
                        (futurePathAfterStoppingTime B τ ω) ∂μ
                        =
                          ∫ ω in s,
                            Set.indicator (futurePathAfterStoppingTime B τ ⁻¹' A)
                              (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                                refine MeasureTheory.integral_congr_ae <|
                                  Filter.Eventually.of_forall fun ω ↦ ?_
                                by_cases hω : futurePathAfterStoppingTime B τ ω ∈ A
                                · simp [hω]
                                · simp [hω]
                    _ = (μ.restrict s).real (futurePathAfterStoppingTime B τ ⁻¹' A) := by
                          calc
                            ∫ ω in s,
                                Set.indicator (futurePathAfterStoppingTime B τ ⁻¹' A)
                                  (fun _ ↦ (1 : ℝ)) ω ∂μ
                                =
                                  ∫ ω,
                                    Set.indicator (futurePathAfterStoppingTime B τ ⁻¹' A)
                                      (fun _ ↦ (1 : ℝ)) ω ∂(μ.restrict s) := by
                                        rfl
                            _ = (μ.restrict s).real (futurePathAfterStoppingTime B τ ⁻¹' A) := by
                                  simpa using
                                    (MeasureTheory.integral_indicator_one
                                      (μ := μ.restrict s)
                                      (s := futurePathAfterStoppingTime B τ ⁻¹' A)
                                      hfutureEvent_meas)
                    _ = μ.real (futurePathAfterStoppingTime B τ ⁻¹' A ∩ s) := by
                          simpa using
                            (MeasureTheory.measureReal_restrict_apply
                              (μ := μ) (s := s)
                              (t := futurePathAfterStoppingTime B τ ⁻¹' A)
                              hfutureEvent_meas)
        _ = ∫ ω in s,
            (μ⟦futurePathAfterStoppingTime B τ ⁻¹' A | hτ.measurableSpace⟧) ω ∂μ := by
              symm
              exact MeasureTheory.setIntegral_condExp hgenerated_le hindicator_int hs
        _ = ∫ ω in s, (κ (stoppedValue B τ ω)).real A ∂μ := by
              exact MeasureTheory.integral_congr_ae (ae_restrict_of_ae (hLaw x τ hτ hτfinite hA))
    have hleft_real :
        (((μ.restrict s).map (futurePathAfterStoppingTime B τ)).real A) =
          ∫ ω in s, (κ (stoppedValue B τ ω)).real A ∂μ := by
      calc
        (((μ.restrict s).map (futurePathAfterStoppingTime B τ)).real A)
            = (μ.restrict s).real (futurePathAfterStoppingTime B τ ⁻¹' A) := by
                simpa using
                  (MeasureTheory.map_measureReal_apply
                    (μ := μ.restrict s) (f := futurePathAfterStoppingTime B τ)
                    hfuture_measurable hA)
        _ = μ.real (futurePathAfterStoppingTime B τ ⁻¹' A ∩ s) := by
              simpa using
                (MeasureTheory.measureReal_restrict_apply
                  (μ := μ) (s := s) (t := futurePathAfterStoppingTime B τ ⁻¹' A)
                  hfutureEvent_meas)
        _ = ∫ ω in s, (κ (stoppedValue B τ ω)).real A ∂μ := by
              exact hmass
    have hright_real :
        ((κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ))).real A) =
          ∫ ω in s, (κ (stoppedValue B τ ω)).real A ∂μ := by
      simpa using
        (kernelComp_restrictMap_real_eq_setIntegral_local
          (κ := κ) (μ := μ) (hY := hstopped_meas_ambient) hs_ambient hA)
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := (μ.restrict s).map (futurePathAfterStoppingTime B τ))
        (ν := κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ))) (s := A) (t := A)).mp
        (hleft_real.trans hright_real.symm)
  have hCondExp :
      rhs =ᵐ[μ] μ[fun ω ↦ f (futurePathAfterStoppingTime B τ ω) | hτ.measurableSpace] := by
    refine
      MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hf_int
        (fun s hs hμs ↦ ?_) (fun s hs hμs ↦ ?_)
        hKernelIntegral_meas_hτ.aestronglyMeasurable
    · -- Proof comment: the kernel-integral candidate is bounded on each history event because
      -- the path functional is uniformly bounded by `C`.
      refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      have hfC :
          ∀ᵐ y ∂κ (stoppedValue B τ ω), ‖f y‖ ≤ C :=
        Filter.Eventually.of_forall fun y ↦ by simpa using hC y
      simpa using
        (MeasureTheory.norm_integral_le_of_norm_le_const
          (μ := κ (stoppedValue B τ ω)) hfC)
    · -- Proof comment: on every `𝓕_τ`-measurable set, the restricted stopped-future law agrees
      -- with the mixed kernel law, so both set integrals are the integral of `f` against the
      -- same path measure.
      let νs : Measure (NNReal → ℝ) := (μ.restrict s).map (futurePathAfterStoppingTime B τ)
      let ρs : Measure (NNReal → ℝ) := κ ∘ₘ ((μ.restrict s).map (stoppedValue B τ))
      have hlaw : νs = ρs := by
        simpa [νs, ρs] using hRestrictedLaw hs
      haveI : IsFiniteMeasure νs := by
        dsimp [νs]
        infer_instance
      have hf_νs_int : Integrable f νs := by
        refine Integrable.of_bound hf_meas.aestronglyMeasurable C ?_
        exact Filter.Eventually.of_forall fun y ↦ hC y
      have hf_ρs_int : Integrable f ρs := by
        rw [← hlaw]
        exact hf_νs_int
      have hleft :
          ∫ ω in s, f (futurePathAfterStoppingTime B τ ω) ∂μ = ∫ y, f y ∂νs := by
        change ∫ ω, f (futurePathAfterStoppingTime B τ ω) ∂(μ.restrict s) = ∫ y, f y ∂νs
        rw [show νs = (μ.restrict s).map (futurePathAfterStoppingTime B τ) by rfl]
        exact
          (MeasureTheory.integral_map hfuture_measurable.aemeasurable
            hf_meas.aestronglyMeasurable).symm
      have hright :
          ∫ y, f y ∂ρs = ∫ ω in s, ∫ y, f y ∂κ (stoppedValue B τ ω) ∂μ := by
        let κ₀ : Kernel Unit ℝ := Kernel.const Unit ((μ.restrict s).map (stoppedValue B τ))
        have hcomp : (κ ∘ₖ κ₀) () = ρs := by
          simp [κ₀, ρs]
        calc
          ∫ y, f y ∂ρs = ∫ y, f y ∂((κ ∘ₖ κ₀) ()) := by
            rw [← hcomp]
          _ = ∫ z, ∫ y, f y ∂κ z ∂κ₀ () := by
                simpa using
                  (ProbabilityTheory.Kernel.integral_comp
                    (η := κ) (κ := κ₀) (a := ()) hf_ρs_int)
          _ = ∫ z, ∫ y, f y ∂κ z ∂((μ.restrict s).map (stoppedValue B τ)) := by
                simp [κ₀]
          _ = ∫ ω in s, ∫ y, f y ∂κ (stoppedValue B τ ω) ∂μ := by
                simpa using
                  (MeasureTheory.integral_map hstopped_meas_ambient.aemeasurable
                    hKernelIntegral_meas.aestronglyMeasurable)
      exact (hleft.trans (hlaw ▸ hright)).symm
  simpa [lhs, rhs, μ] using hCondExp.symm
/-- Helper for Theorem 21.18: the bounded representative of the clipped stopping time `τ ∧ T`
viewed in `NNReal`. -/
private def clippedStoppingTimeNNReal
    (τ : Ω → WithTop NNReal) (T : NNReal) : Ω → NNReal :=
  fun ω ↦ (min (τ ω) (T : WithTop NNReal)).untopA

/-- Helper for Theorem 21.18: coercing the bounded clipped stop back to `WithTop NNReal`
recovers the original clip `τ ∧ T`. -/
@[simp] private lemma clippedStoppingTimeNNReal_coe
    (τ : Ω → WithTop NNReal) (T : NNReal) :
    (fun ω ↦ ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal)) =
      fun ω ↦ min (τ ω) (T : WithTop NNReal) := by
  funext ω
  -- Proof comment: the clipped time is never `⊤`, so `untopA` followed by coercion is exact.
  have hclip_ne_top : min (τ ω) (T : WithTop NNReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact WithTop.coe_ne_top) (min_le_right _ _)
  rw [clippedStoppingTimeNNReal, WithTop.untopA_eq_untop hclip_ne_top, WithTop.coe_untop]

/-- Helper for Theorem 21.18: the clipped stopping time is bounded by the clipping horizon. -/
private lemma clippedStoppingTimeNNReal_le
    (τ : Ω → WithTop NNReal) (T : NNReal) :
    ∀ ω, clippedStoppingTimeNNReal τ T ω ≤ T := by
  intro ω
  have hclip_ne_top : min (τ ω) (T : WithTop NNReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact WithTop.coe_ne_top) (min_le_right _ _)
  -- Proof comment: the clipped stop is literally the finite representative of `min (τ,T)`, so
  -- the `WithTop` inequality `min (τ,T) ≤ T` descends through `untopA`.
  simpa [clippedStoppingTimeNNReal] using
    (WithTop.untopA_le_iff hclip_ne_top).2 (min_le_right _ _)
/-- Helper for Theorem 21.18: clipping a Brownian stopping time at a deterministic horizon again
gives a stopping time, now represented in `NNReal`. -/
private lemma clippedStoppingTimeNNReal_isStoppingTime
    (B : NNReal → Ω → ℝ) {τ : Ω → WithTop NNReal}
    (hτ : IsStoppingTime (processFiltration B) τ) (T : NNReal) :
    IsStoppingTime (processFiltration B)
      (fun ω ↦ (clippedStoppingTimeNNReal τ T ω : WithTop NNReal)) := by
  -- Proof comment: after coercing the bounded representative back into `WithTop`, the clipped
  -- stop is exactly the minimum stopping time `τ ∧ T`.
  rw [clippedStoppingTimeNNReal_coe]
  exact hτ.min_const T
/-- Helper for Theorem 21.18: an `𝓕_τ`-measurable history slice stays measurable for the clipped
stopping time on the finite slice `{τ ≤ T}`. -/
private lemma measurableSet_inter_le_clippedStoppingTime
    (B : NNReal → Ω → ℝ) {τ : Ω → WithTop NNReal}
    (hτ : IsStoppingTime (processFiltration B) τ)
    {s : Set Ω} (hs : MeasurableSet[hτ.measurableSpace] s) (T : NNReal) :
    MeasurableSet[(clippedStoppingTimeNNReal_isStoppingTime B hτ T).measurableSpace]
      (s ∩ {ω | τ ω ≤ T}) := by
  have hs_inter :
      MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ T}) :=
    hs.inter (hτ.measurableSet_le' T)
  have hs_clipped :
      MeasurableSet[(hτ.min_const T).measurableSpace] (s ∩ {ω | τ ω ≤ T}) :=
    (hτ.measurableSet_inter_le_const_iff s T).1 hs_inter
  have hspace_eq :
      (clippedStoppingTimeNNReal_isStoppingTime B hτ T).measurableSpace =
        (hτ.min_const T).measurableSpace := by
    simpa [clippedStoppingTimeNNReal_coe] using
      MeasureTheory.IsStoppingTime.measurableSpace.congr_simp
        (e_f := rfl) (e_τ := clippedStoppingTimeNNReal_coe τ T)
        (clippedStoppingTimeNNReal_isStoppingTime B hτ T)
  -- Proof comment: after identifying the clipped stopping time with `τ ∧ T`, the standard
  -- stopping-time measurability transport gives the result.
  rw [hspace_eq]
  exact hs_clipped
/-- Helper for Theorem 21.18: on the slice `{τ ≤ T}`, clipping `τ` at `T` does not change the
stopped present value. -/
private lemma stoppedValue_clippedStoppingTime_eqOn_le_const
    (B : NNReal → Ω → ℝ) {τ : Ω → WithTop NNReal} (T : NNReal) :
    Set.EqOn
      (stoppedValue B (fun ω ↦ (clippedStoppingTimeNNReal τ T ω : WithTop NNReal)))
      (stoppedValue B τ)
      {ω | τ ω ≤ T} := by
  intro ω hω
  have hclip_eq : ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal) = τ ω := by
    rw [show ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal) =
        min (τ ω) (T : WithTop NNReal) by
          exact congrFun (clippedStoppingTimeNNReal_coe τ T) ω]
    rw [min_eq_left hω]
  have hidx : clippedStoppingTimeNNReal τ T ω = (τ ω).untopA := by
    -- Proof comment: once the clipped and original stopping times agree in `WithTop`, their
    -- finite representatives agree after applying `untopA`.
    simpa using congrArg WithTop.untopA hclip_eq
  -- Proof comment: matching finite stopping indices give identical stopped values.
  simpa [stoppedValue] using congrArg (fun t : NNReal ↦ B t ω) hidx
/-- Helper for Theorem 21.18: on the slice `{τ ≤ T}`, clipping `τ` at `T` does not change the
stopped future path. -/
private lemma futurePathAfterStoppingTime_clippedStoppingTime_eqOn_le_const
    (B : NNReal → Ω → ℝ) {τ : Ω → WithTop NNReal} (T : NNReal) :
    Set.EqOn
      (futurePathAfterStoppingTime B
        (fun ω ↦ (clippedStoppingTimeNNReal τ T ω : WithTop NNReal)))
      (futurePathAfterStoppingTime B τ)
      {ω | τ ω ≤ T} := by
  intro ω hω
  have hτ_ne_top : τ ω ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact WithTop.coe_ne_top) hω
  have hclip_eq : ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal) = τ ω := by
    rw [show ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal) =
        min (τ ω) (T : WithTop NNReal) by
          exact congrFun (clippedStoppingTimeNNReal_coe τ T) ω]
    rw [min_eq_left hω]
  have hidx : clippedStoppingTimeNNReal τ T ω = (τ ω).untopA := by
    -- Proof comment: on the finite slice `{τ ≤ T}`, clipping preserves the underlying finite
    -- stopping index.
    simpa using congrArg WithTop.untopA hclip_eq
  have hclip_ne_top :
      ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal) ≠ ⊤ := by
    rw [hclip_eq]
    exact hτ_ne_top
  have hclip_untop :
      (((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal).untop hclip_ne_top) =
        clippedStoppingTimeNNReal τ T ω := by
    exact
      WithTop.coe_injective
        (WithTop.coe_untop
          (x := ((clippedStoppingTimeNNReal τ T ω : NNReal) : WithTop NNReal)) hclip_ne_top)
  ext t
  -- Proof comment: evaluate both future paths at time `t`, rewrite the clipped stop to the
  -- original finite index, and then use the explicit stopped-future formula away from `⊤`.
  calc
    futurePathAfterStoppingTime B
        (fun ω ↦ (clippedStoppingTimeNNReal τ T ω : WithTop NNReal)) ω t =
      B (clippedStoppingTimeNNReal τ T ω + t) ω := by
        rw [futurePathAfterStoppingTime_apply_of_ne_top
          B (fun ω ↦ (clippedStoppingTimeNNReal τ T ω : WithTop NNReal)) ω t hclip_ne_top]
        rw [hclip_untop]
    _ = B ((τ ω).untopA + t) ω := by rw [hidx]
    _ = B ((τ ω).untop hτ_ne_top + t) ω := by
        rw [WithTop.untopA_eq_untop hτ_ne_top]
    _ = futurePathAfterStoppingTime B τ ω t := by
        symm
        exact futurePathAfterStoppingTime_apply_of_ne_top B τ ω t hτ_ne_top
/-- Helper for Theorem 21.18: the already proved countable-range restricted path law immediately
induces the corresponding finite-vector restricted law by pushforward along path evaluation. -/
private lemma brownianFutureVectorRestrictedLaw_eq_kernel_countableRangeStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (hσcount : (Set.range σ).Countable)
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s)
    {n : ℕ} (times : Fin n → NNReal) :
    (((P x : Measure Ω).restrict s).map
      (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)) =
      (brownianTranslatedPathKernel P B ∘ₘ
        (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω))).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let Y : Ω → Fin n → ℝ := fun ω i ↦ B (σ ω + times i) ω
  let Z : Ω → ℝ := fun ω ↦ B (σ ω) ω
  let evalVec : (NNReal → ℝ) → Fin n → ℝ := fun y i ↦ y (times i)
  let ν : Measure (Fin n → ℝ) := ((μ.restrict s).map Y)
  let ρ : Measure (Fin n → ℝ) :=
    (brownianTranslatedPathKernel P B ∘ₘ ((μ.restrict s).map Z)).map evalVec
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  have hσ_meas : Measurable σ := by
    -- Proof comment: the finite stopping time is ambient measurable after removing the `WithTop`
    -- coercion.
    simpa using (hσ.measurable.untopA).mono hσ.measurableSpace_le le_rfl
  have hY_meas : Measurable Y := by
    -- Proof comment: countable-range stopping times make every shifted Brownian coordinate
    -- measurable, so the whole future vector is measurable coordinatewise.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_brownianShiftedValue_of_countableRange P B hB σ hσ_meas hσcount (times i)
  have hZ_meas : Measurable Z := by
    -- Proof comment: the stopped present value is the shifted coordinate at time `0`.
    simpa [Z] using
      measurable_brownianShiftedValue_of_countableRange P B hB σ hσ_meas hσcount 0
  have hs_ambient : MeasurableSet s := hσ.measurableSpace_le _ hs
  -- Proof comment: reconstruct the restricted law by comparing both measures on each measurable
  -- cylinder event `A`.
  refine Measure.ext fun A hA ↦ ?_
  have hEvent_meas : MeasurableSet (Y ⁻¹' A) := hY_meas hA
  have hIndicator_int :
      Integrable (fun ω ↦ Set.indicator (Y ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω) μ := by
    -- Proof comment: the indicator of the future-vector event is bounded by `1`.
    refine Integrable.of_bound
      ((Measurable.indicator measurable_const hEvent_meas).aestronglyMeasurable) 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ Y ⁻¹' A
      · simp [hω]
      · simp [hω]
  have hEventCond :
      (μ⟦Y ⁻¹' A | hσ.measurableSpace⟧) =ᵐ[μ]
        fun ω ↦ (((brownianTranslatedPathKernel P B (Z ω)).map evalVec).real A) := by
    -- Proof comment: specialize the already established countable-range vector event formula and
    -- rewrite the explicit stopping-time future vector as the local abbreviation `Y`.
    simpa [μ, Y, Z, evalVec] using
      (brownianFutureVectorEvent_condExp_eq_kernel_countableRangeStop
        P B hB x σ hσ hσcount (times := times) (hA := hA))
  have hleft_real :
      ν.real A = ∫ ω in s,
          (((brownianTranslatedPathKernel P B (Z ω)).map evalVec).real A) ∂μ := by
    calc
      ν.real A = (μ.restrict s).real (Y ⁻¹' A) := by
        simpa [ν] using
          (MeasureTheory.map_measureReal_apply
            (μ := μ.restrict s) (f := Y) hY_meas hA)
      _ = μ.real (Y ⁻¹' A ∩ s) := by
        simpa using
          (MeasureTheory.measureReal_restrict_apply
            (μ := μ) (s := s) (t := Y ⁻¹' A) hEvent_meas)
      _ = ∫ ω in s, Set.indicator (Y ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
        symm
        calc
          ∫ ω in s, Set.indicator (Y ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ
              = ∫ ω, Set.indicator (Y ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂(μ.restrict s) := by
                  rfl
          _ = (μ.restrict s).real (Y ⁻¹' A) := by
                simpa using
                  (MeasureTheory.integral_indicator_one
                    (μ := μ.restrict s) (s := Y ⁻¹' A) hEvent_meas)
          _ = μ.real (Y ⁻¹' A ∩ s) := by
                simpa using
                  (MeasureTheory.measureReal_restrict_apply
                    (μ := μ) (s := s) (t := Y ⁻¹' A) hEvent_meas)
      _ = ∫ ω in s, (μ⟦Y ⁻¹' A | hσ.measurableSpace⟧) ω ∂μ := by
        symm
        exact MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hIndicator_int hs
      _ = ∫ ω in s,
          (((brownianTranslatedPathKernel P B (Z ω)).map evalVec).real A) ∂μ := by
        exact MeasureTheory.integral_congr_ae (ae_restrict_of_ae hEventCond)
  have hright_real :
      ρ.real A = ∫ ω in s,
          (((brownianTranslatedPathKernel P B (Z ω)).map evalVec).real A) ∂μ := by
    calc
      ρ.real A =
          ((brownianTranslatedPathKernel P B ∘ₘ ((μ.restrict s).map Z)).real
            (evalVec ⁻¹' A)) := by
              simpa [ρ, evalVec] using
                (MeasureTheory.map_measureReal_apply
                  (μ := brownianTranslatedPathKernel P B ∘ₘ ((μ.restrict s).map Z))
                  (f := evalVec) (measurable_pathEvalVector times) hA)
      _ = ∫ ω in s,
            (brownianTranslatedPathKernel P B (Z ω)).real (evalVec ⁻¹' A) ∂μ := by
              simpa [Z] using
                (kernelComp_restrictMap_real_eq_setIntegral_local
                  (κ := brownianTranslatedPathKernel P B)
                  (μ := μ) (hY := hZ_meas) hs_ambient
                  ((measurable_pathEvalVector times) hA))
      _ = ∫ ω in s,
            (((brownianTranslatedPathKernel P B (Z ω)).map evalVec).real A) ∂μ := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              exact
                (MeasureTheory.map_measureReal_apply
                  (μ := brownianTranslatedPathKernel P B (Z ω))
                  (f := evalVec) (measurable_pathEvalVector times) hA).symm
  -- Proof comment: equality of the real masses on every measurable event yields equality of the
  -- restricted future-vector laws themselves.
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ν) (ν := ρ) (s := A) (t := A)).mp
      (hleft_real.trans hright_real.symm)
/-- Helper for Theorem 21.18: once the stopping time is already `NNReal`-valued, the restricted
finite-dimensional Brownian future-vector law already matches the translated Brownian kernel on
bounded continuous tests. -/
private lemma aestronglyMeasurable_brownianStoppedValue_finiteStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal)) :
    AEStronglyMeasurable (fun ω ↦ B (σ ω) ω) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hApprox_meas :
      ∀ m : ℕ, AEStronglyMeasurable (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω) μ := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: each dyadic approximation is itself a finite stopping time, hence an
      -- ambient measurable `NNReal`-valued random variable.
      simpa using (hσm.measurable.untopA).mono hσm.measurableSpace_le le_rfl
    simpa using
      (measurable_brownianShiftedValue_of_countableRange
        P B hB (brownianDyadicCeilApprox m σ) hσm_meas
        (brownianDyadicCeilApprox_countableRange m σ) 0).aestronglyMeasurable
  have hApprox_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun m ↦ B (brownianDyadicCeilApprox m σ ω) ω) atTop
        (𝓝 (B (σ ω) ω)) := by
    filter_upwards [(hB x).continuous_paths] with ω hω
    -- Proof comment: along an almost surely continuous sample path, evaluating at dyadic ceiling
    -- times converging to `σ(ω)` converges to the stopped value `B(σ(ω), ω)`.
    simpa [processPath] using
      ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω)).tendsto.comp
        (brownianDyadicCeilApprox_tendsto σ ω))
  -- Proof comment: the measurable dyadic stopped values converge almost surely to the target
  -- stopped value, so the limit is `AEStronglyMeasurable`.
  simpa [μ] using
    (aestronglyMeasurable_of_tendsto_ae atTop hApprox_meas hApprox_tendsto)

/-- Helper for Theorem 21.18: under each start law, the Brownian stopped value at an arbitrary
`WithTop` stopping time is at least ambient almost-everywhere measurable. -/
private lemma aemeasurable_stoppedValue_brownian
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ) :
    AEMeasurable (stoppedValue B τ) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let σ : Ω → NNReal := fun ω ↦ (τ ω).untopA
  have hσ_meas : Measurable σ := by
    -- Proof comment: the finite-valued clock extracted from the stopping time is ambient
    -- measurable because `τ` is measurable for its stopping-time sigma algebra.
    simpa [σ] using (hτ.measurable.untopA).mono hτ.measurableSpace_le le_rfl
  have hApprox_meas :
      ∀ m : ℕ, AEMeasurable (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω) μ := by
    intro m
    -- Proof comment: each dyadic ceiling approximation has countable range, so every dyadic
    -- stopped value is genuinely measurable.
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: the dyadic ceiling approximation is a measurable transform of the ambient
      -- measurable finite clock `σ = τ.untopA`.
      unfold brownianDyadicCeilApprox
      fun_prop
    simpa using
      (measurable_brownianShiftedValue_of_countableRange
        P B hB (brownianDyadicCeilApprox m σ) hσm_meas
        (brownianDyadicCeilApprox_countableRange m σ) 0).aemeasurable
  have hApprox_tendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ B (brownianDyadicCeilApprox m σ ω) ω) atTop
          (𝓝 (stoppedValue B τ ω)) := by
    filter_upwards [(hB x).continuous_paths] with ω hω
    -- Proof comment: along an almost surely continuous Brownian sample path, evaluating at the
    -- dyadic ceiling times converging to `(τ ω).untopA` recovers the stopped value.
    simpa [σ, stoppedValue, processPath] using
      ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω)).tendsto.comp
        (brownianDyadicCeilApprox_tendsto σ ω))
  -- Proof comment: the stopped value is the almost-sure limit of measurable dyadic stopped
  -- values, so it is at least ambient `AEMeasurable`.
  simpa [μ] using
    (aemeasurable_of_tendsto_metrizable_ae' hApprox_meas hApprox_tendsto)

/-- Helper for Theorem 21.18: the Brownian stopped value is almost everywhere strongly measurable
for the stopping-time sigma algebra `𝓕_τ`. -/
private lemma aestronglyMeasurable_stoppedValue_brownian_hTau
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ) :
    AEStronglyMeasurable[hτ.measurableSpace] (stoppedValue B τ) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let σ : Ω → NNReal := fun ω ↦ (τ ω).untopA
  let u : ℕ → Ω → ℝ := fun m ω ↦ B (brownianDyadicFloorApprox m σ ω) ω
  let l : Ω → ℝ := fun ω ↦ Filter.limsup (fun m ↦ u m ω) atTop
  have hl_meas : Measurable[hτ.measurableSpace] l := by
    -- Proof comment: the pointwise `limsup` of the dyadic floor approximants is still
    -- `𝓕_τ`-measurable because every approximant already is.
    simpa [l, u] using
      (Measurable.limsup fun m ↦ measurable_brownianDyadicStoppedValue P B hB τ hτ m)
  have hApprox_tendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ B (brownianDyadicFloorApprox m σ ω) ω) atTop
          (𝓝 (stoppedValue B τ ω)) := by
    filter_upwards [(hB x).continuous_paths] with ω hω
    -- Proof comment: along an almost surely continuous Brownian sample path, the dyadic floor
    -- times converge upward to `τ(ω).untopA`, so the corresponding values converge to the stopped
    -- value.
    simpa [σ, stoppedValue, processPath] using
      ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω)).tendsto.comp
        (brownianDyadicFloorApprox_tendsto σ ω))
  have hl_ae : l =ᵐ[μ] stoppedValue B τ := by
    filter_upwards [hApprox_tendsto] with ω hω
    simpa [l, u] using Filter.Tendsto.limsup_eq hω
  -- Proof comment: the `limsup` representative is genuinely `𝓕_τ`-measurable and agrees almost
  -- surely with the stopped value.
  exact (hl_meas.stronglyMeasurable.aestronglyMeasurable).congr hl_ae

/-- Helper for Theorem 21.18: the finite stopped Brownian future vector is almost everywhere
strongly measurable under the start law. -/
private lemma aestronglyMeasurable_brownianStoppedFutureVector_finiteStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {n : ℕ} (times : Fin n → NNReal) :
    AEStronglyMeasurable
      (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)
      (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hApprox_meas :
      ∀ m : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)
          μ := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: each dyadic approximation is an ambient measurable stopping time.
      simpa using (hσm.measurable.untopA).mono hσm.measurableSpace_le le_rfl
    have hVector_meas :
        Measurable
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω) := by
      -- Proof comment: countable dyadic ranges reduce every shifted coordinate to a measurable
      -- deterministic-time Brownian coordinate on each atom.
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact
        measurable_brownianShiftedValue_of_countableRange
          P B hB (brownianDyadicCeilApprox m σ) hσm_meas
          (brownianDyadicCeilApprox_countableRange m σ) (times i)
    exact hVector_meas.aestronglyMeasurable
  have hApprox_tendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun m ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)
          atTop
          (𝓝 (fun i : Fin n ↦ B (σ ω + times i) ω)) := by
    filter_upwards [(hB x).continuous_paths] with ω hω
    refine tendsto_pi_nhds.2 ?_
    intro i
    have hTime_tendsto :
        Tendsto
          (fun m ↦ brownianDyadicCeilApprox m σ ω + times i)
          atTop
          (𝓝 (σ ω + times i)) := by
      -- Proof comment: adding the fixed future offset `times i` preserves the dyadic convergence
      -- to `σ(ω)`.
      simpa using (brownianDyadicCeilApprox_tendsto σ ω).add tendsto_const_nhds
    -- Proof comment: continuity of the sample path transports the dyadic time convergence to each
    -- future Brownian coordinate.
    simpa [processPath, Function.comp] using
      ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω + times i)).tendsto.comp
        hTime_tendsto)
  -- Proof comment: the measurable dyadic future vectors converge coordinatewise almost surely to
  -- the stopped future vector, so the target vector is `AEStronglyMeasurable`.
  simpa [μ] using
    (aestronglyMeasurable_of_tendsto_ae atTop hApprox_meas hApprox_tendsto)

/-- Helper for Theorem 21.18: composing the Brownian stopped value with the continuous translated
kernel row functional gives an almost everywhere strongly measurable candidate under the start
law. -/
private lemma aestronglyMeasurable_brownianFutureVectorKernelIntegral_stoppedValue
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    {n : ℕ} (times : Fin n → NNReal)
    (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    AEStronglyMeasurable
      (fun ω ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B (stoppedValue B τ ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))))
      (P x : Measure Ω) := by
  let evalVec : (NNReal → ℝ) → Fin n → ℝ := fun y i ↦ y (times i)
  let g : ℝ → ℝ := fun z ↦
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map evalVec)
  have hg_cont : Continuous g := by
    -- Proof comment: this is exactly the deterministic-time translated-kernel continuity owner
    -- already proved earlier in the file.
    simpa [g, evalVec] using
      continuous_brownianTranslatedPathKernel_futureVectorIntegral P B hB times φ
  have hStopped :
      AEMeasurable (stoppedValue B τ) (P x : Measure Ω) :=
    aemeasurable_stoppedValue_brownian P B hB x τ hτ
  -- Proof comment: compose the continuous kernel-row functional with the ambient AE measurable
  -- stopped state, then upgrade the real-valued result to `AEStronglyMeasurable`.
  exact (hg_cont.measurable.comp_aemeasurable hStopped).aestronglyMeasurable

/-- Helper for Theorem 21.18: kernel-side finite-vector integrals over a restricted stopped-value
law reduce to a restricted integral of the corresponding kernel row functional. -/
private lemma brownianKernelFutureVectorIntegral_eq_setIntegral
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) {s : Set Ω} (hs : MeasurableSet s)
    {n : ℕ} (times : Fin n → NNReal)
    (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {Z : Ω → ℝ} (hZ : AEMeasurable Z ((P x : Measure Ω).restrict s)) :
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
      (((P x : Measure Ω).restrict s).map Z)).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) =
      ∫ ω in s,
        (∫ v, φ v ∂((brownianTranslatedPathKernel P B (Z ω)).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)))) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure ℝ := (μ.restrict s).map Z
  let evalVec : (NNReal → ℝ) → Fin n → ℝ := fun y i ↦ y (times i)
  let κVec : Kernel ℝ (Fin n → ℝ) := (brownianTranslatedPathKernel P B).map evalVec
  let g : ℝ → ℝ := fun z ↦
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map evalVec)
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  have hg_cont : Continuous g := by
    -- Proof comment: the finite-vector kernel row integral varies continuously with the starting
    -- state by the deterministic-time translated-kernel continuity lemma.
    simpa [g, evalVec] using
      continuous_brownianTranslatedPathKernel_futureVectorIntegral P B hB times φ
  have hg_aestrong : AEStronglyMeasurable g ν :=
    hg_cont.measurable.aestronglyMeasurable
  have hMap_comp :
      ((brownianTranslatedPathKernel P B ∘ₘ ν).map evalVec) = κVec ∘ₘ ν := by
    -- Proof comment: mapping the measure-kernel composition by finite-time evaluation is the
    -- same as first mapping the kernel rows and then composing with the stopped-value law.
    simpa [ν, κVec, evalVec] using
      (Measure.map_comp ν (brownianTranslatedPathKernel P B) (measurable_pathEvalVector times))
  have hφ_int : Integrable φ (κVec ∘ₘ ν) := by
    simpa [κVec] using φ.integrable (κVec ∘ₘ ν)
  let κ₀ : Kernel Unit ℝ := Kernel.const Unit ν
  have hComp : (κVec ∘ₖ κ₀) () = κVec ∘ₘ ν := by
    simp [κ₀, ν]
  calc
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ ν).map evalVec)
      = ∫ v, φ v ∂(κVec ∘ₘ ν) := by
          rw [hMap_comp]
    _ = ∫ v, φ v ∂((κVec ∘ₖ κ₀) ()) := by
          rw [← hComp]
    _ = ∫ z, ∫ v, φ v ∂κVec z ∂κ₀ () := by
          simpa using
            (ProbabilityTheory.Kernel.integral_comp
              (η := κVec) (κ := κ₀) (a := ()) hφ_int)
    _ = ∫ z, g z ∂ν := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          rw [Kernel.map_apply _ (measurable_pathEvalVector times) z]
    _ = ∫ ω, g (Z ω) ∂(μ.restrict s) := by
          simpa [ν] using MeasureTheory.integral_map hZ hg_aestrong
    _ = ∫ ω in s, g (Z ω) ∂μ := by
          rfl

/-- Helper for Theorem 21.18: the stopped future-vector observables of the dyadic ceiling
approximants converge in integral to the full finite-stop observable. -/
private lemma tendsto_brownianStoppedFutureVectorIntegral_dyadicCeilApprox
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s)
    {n : ℕ} (times : Fin n → NNReal)
    (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    Tendsto
      (fun m ↦
        ∫ v, φ v ∂(((P x : Measure Ω).restrict s).map
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)))
      atTop
      (𝓝
        (∫ v, φ v ∂(((P x : Measure Ω).restrict s).map
          (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let μs : Measure Ω := μ.restrict s
  let F : Ω → ℝ := fun ω ↦ φ (fun i : Fin n ↦ B (σ ω + times i) ω)
  let Fn : ℕ → Ω → ℝ :=
    fun m ω ↦ φ (fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)
  have hApprox_meas : ∀ m : ℕ, AEStronglyMeasurable (Fn m) μs := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    -- Proof comment: every dyadic future observable is measurable because the dyadic stop has
    -- countable range, so the composed bounded continuous test is `AEStronglyMeasurable`.
    exact
      (measurable_brownianStoppedFutureVector_of_countableRange
        P B hB x (brownianDyadicCeilApprox m σ) hσm
        (brownianDyadicCeilApprox_countableRange m σ) times
        ((φ : C(Fin n → ℝ, ℝ)).continuous.measurable)).aestronglyMeasurable
  have hApprox_dom :
      ∀ m : ℕ, ∀ᵐ ω ∂μs, ‖Fn m ω‖ ≤ ‖φ‖ := by
    intro m
    -- Proof comment: bounded continuous tests are uniformly dominated by their sup norm.
    exact Filter.Eventually.of_forall fun ω ↦ φ.norm_coe_le_norm _
  have hApprox_tendsto :
      ∀ᵐ ω ∂μs, Tendsto (fun m ↦ Fn m ω) atTop (𝓝 (F ω)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [(hB x).continuous_paths] with ω hω
    have hVector_tendsto :
        Tendsto
          (fun m ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)
          atTop
          (𝓝 (fun i : Fin n ↦ B (σ ω + times i) ω)) := by
      refine tendsto_pi_nhds.2 ?_
      intro i
      have hTime_tendsto :
          Tendsto
            (fun m ↦ brownianDyadicCeilApprox m σ ω + times i)
            atTop
            (𝓝 (σ ω + times i)) := by
        -- Proof comment: the deterministic future offset preserves dyadic convergence to `σ(ω)`.
        simpa using (brownianDyadicCeilApprox_tendsto σ ω).add tendsto_const_nhds
      -- Proof comment: continuity of the Brownian sample path transports the dyadic time
      -- convergence to each vector coordinate.
      simpa [processPath, Function.comp] using
        ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω + times i)).tendsto.comp
          hTime_tendsto)
    -- Proof comment: applying the bounded continuous test `φ` to the convergent future vectors
    -- yields pointwise convergence of the scalar observables.
    simpa [Fn, F] using
      (((φ : C(Fin n → ℝ, ℝ)).continuous.continuousAt).tendsto.comp hVector_tendsto)
  have hBound_int : Integrable (fun _ : Ω ↦ ‖φ‖) μs := by
    simpa using (integrable_const ‖φ‖ : Integrable (fun _ : Ω ↦ ‖φ‖) μs)
  have hIntegral_tendsto :
      Tendsto (fun m : ℕ ↦ ∫ ω, Fn m ω ∂μs) atTop (𝓝 (∫ ω, F ω ∂μs)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ ‖φ‖) hApprox_meas hBound_int hApprox_dom hApprox_tendsto
  have hTargetVector_aestrong :
      AEStronglyMeasurable
        (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)
        μs := by
    -- Proof comment: restrict the global finite-stop future-vector measurability owner to the
    -- history slice `s`.
    exact
      (aestronglyMeasurable_brownianStoppedFutureVector_finiteStop
        P B hB x σ hσ times).mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hRewrite_target :
      ∫ v, φ v ∂(μs.map (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)) = ∫ ω, F ω ∂μs := by
    -- Proof comment: rewrite the limiting pushforward integral as an ordinary integral over the
    -- restricted history slice.
    simpa [μs, F] using
      (MeasureTheory.integral_map hTargetVector_aestrong.aemeasurable
        (((φ : C(Fin n → ℝ, ℝ)).continuous.measurable).aestronglyMeasurable))
  have hRewrite_seq :
      ∀ m : ℕ,
        ∫ v, φ v ∂(μs.map
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)) =
            ∫ ω, Fn m ω ∂μs := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: the dyadic ceiling approximation is ambient measurable as an
      -- `NNReal`-valued finite stopping time.
      simpa using (hσm.measurable.untopA).mono hσm.measurableSpace_le le_rfl
    have hVector_meas :
        Measurable
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact
        measurable_brownianShiftedValue_of_countableRange
          P B hB (brownianDyadicCeilApprox m σ) hσm_meas
          (brownianDyadicCeilApprox_countableRange m σ) (times i)
    -- Proof comment: the dyadic pushforward integral is the integral of the corresponding scalar
    -- observable over the restricted measure.
    simpa [μs, Fn] using
      (MeasureTheory.integral_map hVector_meas.aemeasurable
        (((φ : C(Fin n → ℝ, ℝ)).continuous.measurable).aestronglyMeasurable))
  -- Proof comment: after rewriting both the dyadic and target pushforward integrals as ordinary
  -- restricted integrals, dominated convergence yields the desired limit.
  have hSeqEq :
      (fun m : ℕ ↦ ∫ ω, Fn m ω ∂μs) =
        fun m ↦
          ∫ v, φ v ∂(μs.map
            (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)) := by
    funext m
    symm
    exact hRewrite_seq m
  have hTargetEq :
      ∫ ω, F ω ∂μs =
        ∫ v, φ v ∂(μs.map (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)) := by
    symm
    exact hRewrite_target
  simpa [hSeqEq, hTargetEq] using hIntegral_tendsto

/-- Helper for Theorem 21.18: the kernel-side dyadic future-vector integrals converge to the full
finite-stop kernel integral. -/
private lemma tendsto_brownianKernelFutureVectorIntegral_dyadicCeilApprox
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s)
    {n : ℕ} (times : Fin n → NNReal)
    (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    Tendsto
      (fun m ↦
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
          (((P x : Measure Ω).restrict s).map
            (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map
              (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))))
      atTop
      (𝓝
        (∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
          (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω))).map
            (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let μs : Measure Ω := μ.restrict s
  let evalVec : (NNReal → ℝ) → Fin n → ℝ := fun y i ↦ y (times i)
  let g : ℝ → ℝ := fun z ↦
    ∫ v, φ v ∂((brownianTranslatedPathKernel P B z).map evalVec)
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  have hs_ambient : MeasurableSet s := hσ.measurableSpace_le _ hs
  have hg_cont : Continuous g := by
    -- Proof comment: the translated Brownian finite-vector row integral is continuous in the
    -- present state.
    simpa [g, evalVec] using
      continuous_brownianTranslatedPathKernel_futureVectorIntegral P B hB times φ
  have hApprox_meas :
      ∀ m : ℕ,
        AEStronglyMeasurable (fun ω ↦ g (B (brownianDyadicCeilApprox m σ ω) ω)) μs := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: the dyadic finite stopping time is ambient measurable.
      simpa using (hσm.measurable.untopA).mono hσm.measurableSpace_le le_rfl
    have hZm_meas :
        Measurable (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω) := by
      simpa using
        measurable_brownianShiftedValue_of_countableRange
          P B hB (brownianDyadicCeilApprox m σ) hσm_meas
          (brownianDyadicCeilApprox_countableRange m σ) 0
    exact (hg_cont.measurable.comp hZm_meas).aestronglyMeasurable
  have hApprox_dom :
      ∀ m : ℕ, ∀ᵐ ω ∂μs, ‖g (B (brownianDyadicCeilApprox m σ ω) ω)‖ ≤ ‖φ‖ := by
    intro m
    exact Filter.Eventually.of_forall fun ω ↦ by
      haveI : IsProbabilityMeasure (brownianTranslatedPathKernel P B (B (brownianDyadicCeilApprox m σ ω) ω)) :=
        inferInstance
      haveI :
          IsProbabilityMeasure
            ((brownianTranslatedPathKernel P B (B (brownianDyadicCeilApprox m σ ω) ω)).map
              evalVec) :=
        Measure.isProbabilityMeasure_map (measurable_pathEvalVector times).aemeasurable
      -- Proof comment: every translated-kernel row is a probability measure, so integrating `φ`
      -- against it is bounded by `‖φ‖`.
      simpa [g, evalVec] using
        (BoundedContinuousFunction.norm_integral_le_norm
          (μ := ((brownianTranslatedPathKernel P B
            (B (brownianDyadicCeilApprox m σ ω) ω)).map evalVec)) φ)
  have hApprox_tendsto :
      ∀ᵐ ω ∂μs, Tendsto (fun m ↦ g (B (brownianDyadicCeilApprox m σ ω) ω)) atTop
        (𝓝 (g (B (σ ω) ω))) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [(hB x).continuous_paths] with ω hω
    have hStopped_tendsto :
        Tendsto (fun m ↦ B (brownianDyadicCeilApprox m σ ω) ω) atTop
          (𝓝 (B (σ ω) ω)) := by
      -- Proof comment: continuity of the Brownian sample path upgrades dyadic time convergence to
      -- convergence of the stopped values.
      simpa [processPath] using
        ((hω.continuousAt : ContinuousAt (processPath B ω) (σ ω)).tendsto.comp
          (brownianDyadicCeilApprox_tendsto σ ω))
    exact (hg_cont.continuousAt.tendsto.comp hStopped_tendsto)
  have hBound_int : Integrable (fun _ : Ω ↦ ‖φ‖) μs := by
    simpa using (integrable_const ‖φ‖ : Integrable (fun _ : Ω ↦ ‖φ‖) μs)
  have hIntegral_tendsto :
      Tendsto (fun m : ℕ ↦ ∫ ω, g (B (brownianDyadicCeilApprox m σ ω) ω) ∂μs) atTop
        (𝓝 (∫ ω, g (B (σ ω) ω) ∂μs)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ ‖φ‖) hApprox_meas hBound_int hApprox_dom hApprox_tendsto
  have hStopped_aestrong :
      AEStronglyMeasurable (fun ω ↦ B (σ ω) ω) μs := by
    -- Proof comment: restrict the global finite-stop stopped-value measurability owner to the
    -- history slice `s`.
    exact
      (aestronglyMeasurable_brownianStoppedValue_finiteStop
        P B hB x σ hσ).mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hRewrite_target :
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ (μs.map (fun ω ↦ B (σ ω) ω))).map
        evalVec) =
          ∫ ω, g (B (σ ω) ω) ∂μs := by
    -- Proof comment: rewrite the limiting kernel-side integral as the ordinary integral of the
    -- continuous row functional `g` over the restricted stopped-value law.
    calc
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ (μs.map (fun ω ↦ B (σ ω) ω))).map
          evalVec)
        = ∫ ω in s, g (B (σ ω) ω) ∂μ := by
            simpa [μ, μs, g, evalVec] using
              (brownianKernelFutureVectorIntegral_eq_setIntegral
                P B hB x hs_ambient times φ hStopped_aestrong.aemeasurable)
      _ = ∫ ω, g (B (σ ω) ω) ∂μs := by
            rfl
  have hRewrite_seq :
      ∀ m : ℕ,
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
          (μs.map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map evalVec) =
            ∫ ω, g (B (brownianDyadicCeilApprox m σ ω) ω) ∂μs := by
    intro m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hσm_meas : Measurable (brownianDyadicCeilApprox m σ) := by
      -- Proof comment: the dyadic finite stopping time is ambient measurable.
      simpa using (hσm.measurable.untopA).mono hσm.measurableSpace_le le_rfl
    have hStopped_meas :
        Measurable (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω) := by
      simpa using
        measurable_brownianShiftedValue_of_countableRange
          P B hB (brownianDyadicCeilApprox m σ) hσm_meas
          (brownianDyadicCeilApprox_countableRange m σ) 0
    calc
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
          (μs.map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map evalVec)
        = ∫ ω in s, g (B (brownianDyadicCeilApprox m σ ω) ω) ∂μ := by
            simpa [μ, μs, g, evalVec] using
              (brownianKernelFutureVectorIntegral_eq_setIntegral
                P B hB x hs_ambient times φ hStopped_meas.aemeasurable)
      _ = ∫ ω, g (B (brownianDyadicCeilApprox m σ ω) ω) ∂μs := by
            rfl
  -- Proof comment: after normalizing both the dyadic and limiting kernel expressions to the same
  -- restricted integral of `g`, dominated convergence gives the desired limit.
  have hSeqEq :
      (fun m : ℕ ↦ ∫ ω, g (B (brownianDyadicCeilApprox m σ ω) ω) ∂μs) =
        fun m ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
            (μs.map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map evalVec) := by
    funext m
    symm
    exact hRewrite_seq m
  have hTargetEq :
      ∫ ω, g (B (σ ω) ω) ∂μs =
        ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
          (μs.map (fun ω ↦ B (σ ω) ω))).map evalVec) := by
    symm
    exact hRewrite_target
  simpa [hSeqEq, hTargetEq] using hIntegral_tendsto

private lemma brownianFutureVectorIntegral_eq_kernel_finiteStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s)
    {n : ℕ} (times : Fin n → NNReal) (φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ∫ v, φ v ∂(((P x : Measure Ω).restrict s).map
      (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)) =
      ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
        (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω))).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let evalVec : (NNReal → ℝ) → Fin n → ℝ := fun y i ↦ y (times i)
  have hLeft_tendsto :
      Tendsto
        (fun m ↦
          ∫ v, φ v ∂((μ.restrict s).map
            (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)))
        atTop
        (𝓝
          (∫ v, φ v ∂((μ.restrict s).map
            (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)))) := by
    -- Proof comment: the dyadic stopped future vectors converge to the full finite-stop future
    -- vector on the sample side.
    simpa [μ] using
      tendsto_brownianStoppedFutureVectorIntegral_dyadicCeilApprox
        P B hB x σ hσ hs times φ
  have hRight_tendsto :
      Tendsto
        (fun m ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
            ((μ.restrict s).map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map
              evalVec))
        atTop
        (𝓝
          (∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
            ((μ.restrict s).map (fun ω ↦ B (σ ω) ω))).map evalVec))) := by
    -- Proof comment: the same dyadic approximation converges on the kernel side after rewriting
    -- against the continuous row functional.
    simpa [μ, evalVec] using
      tendsto_brownianKernelFutureVectorIntegral_dyadicCeilApprox
        P B hB x σ hσ hs times φ
  have hDyadic_eq :
      (fun m ↦
        ∫ v, φ v ∂((μ.restrict s).map
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω))) =
        fun m ↦
          ∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
            ((μ.restrict s).map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map
              evalVec) := by
    funext m
    have hσm :
        IsStoppingTime (processFiltration B)
          (fun ω ↦ (brownianDyadicCeilApprox m σ ω : WithTop NNReal)) :=
      brownianDyadicCeilApprox_isStoppingTime hσ m
    have hs_m :
        MeasurableSet[hσm.measurableSpace] s :=
      measurableSet_brownianDyadicCeilApprox B hσ hs m
    have hLaw_m :
        ((μ.restrict s).map
          (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)) =
          (brownianTranslatedPathKernel P B ∘ₘ
            ((μ.restrict s).map (fun ω ↦ B (brownianDyadicCeilApprox m σ ω) ω))).map
              evalVec := by
      simpa [μ, evalVec] using
        (brownianFutureVectorRestrictedLaw_eq_kernel_countableRangeStop
          P B hB x (brownianDyadicCeilApprox m σ) hσm
          (brownianDyadicCeilApprox_countableRange m σ) hs_m times)
    -- Proof comment: each dyadic approximation already satisfies the countable-range restricted
    -- law, so the corresponding bounded continuous integrals agree exactly.
    exact congrArg (fun ν : Measure (Fin n → ℝ) ↦ ∫ v, φ v ∂ν) hLaw_m
  have hRight_tendsto' :
      Tendsto
        (fun m ↦
          ∫ v, φ v ∂((μ.restrict s).map
            (fun ω ↦ fun i : Fin n ↦ B (brownianDyadicCeilApprox m σ ω + times i) ω)))
        atTop
        (𝓝
          (∫ v, φ v ∂((brownianTranslatedPathKernel P B ∘ₘ
            ((μ.restrict s).map (fun ω ↦ B (σ ω) ω))).map evalVec))) := by
    simpa [hDyadic_eq] using hRight_tendsto
  -- Proof comment: the dyadic sequence has the same left and right values for every `m`, so the
  -- two limiting bounded continuous integrals must coincide.
  exact tendsto_nhds_unique hLeft_tendsto hRight_tendsto'
/-- Helper for Theorem 21.18: the dyadic finite-vector integral identity upgrades to full
restricted-law equality on finite Brownian future vectors. -/
private lemma brownianFutureVectorRestrictedLaw_eq_kernel_finiteStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s)
    {n : ℕ} (times : Fin n → NNReal) :
    (((P x : Measure Ω).restrict s).map
      (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)) =
      (brownianTranslatedPathKernel P B ∘ₘ
        (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω))).map
          (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i)) := by
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  let ν : FiniteMeasure (Fin n → ℝ) :=
    ⟨(((P x : Measure Ω).restrict s).map
      (fun ω ↦ fun i : Fin n ↦ B (σ ω + times i) ω)), inferInstance⟩
  let ρ : FiniteMeasure (Fin n → ℝ) :=
    ⟨((brownianTranslatedPathKernel P B ∘ₘ
      (((P x : Measure Ω).restrict s).map (fun ω ↦ B (σ ω) ω))).map
        (fun y : NNReal → ℝ ↦ fun i : Fin n ↦ y (times i))), inferInstance⟩
  have hEq : ν = ρ := by
    -- Proof comment: equality of all bounded continuous test integrals determines finite
    -- measures, so the integral identity upgrades directly to equality of the vector laws.
    refine FiniteMeasure.ext_of_forall_integral_eq ?_
    intro ψ
    simpa [ν, ρ] using
      (brownianFutureVectorIntegral_eq_kernel_finiteStop
        P B hB x σ hσ hs times ψ)
  exact congrArg ((↑) : FiniteMeasure (Fin n → ℝ) → Measure (Fin n → ℝ)) hEq
/-- Helper for Theorem 21.18: for a finite set of future times, the restricted stopped future
path is a.e. measurable as a finite vector under the Brownian start law. -/
private lemma aemeasurable_restrictFuturePathAfterStoppingTime_finiteStop
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (processFiltration B) fun ω ↦ (σ ω : WithTop NNReal))
    (I : Finset NNReal) :
    AEMeasurable
      (fun ω ↦ I.restrict
        (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω))
      (P x : Measure Ω) := by
  let τ : Ω → WithTop NNReal := fun ω ↦ (σ ω : WithTop NNReal)
  let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
  let times : Fin I.card → NNReal := fun i ↦ I.orderEmbOfFin rfl i
  -- Proof comment: after reindexing the finite time set by `Fin I.card`, the restricted future
  -- path is exactly the finite stopped future vector already known to be a.e. measurable.
  have hVector :
      AEStronglyMeasurable
        (fun ω ↦ fun i : Fin I.card ↦ B (σ ω + times i) ω)
        (P x : Measure Ω) := by
    simpa [times] using
      (aestronglyMeasurable_brownianStoppedFutureVector_finiteStop
        P B hB x σ hσ times)
  have hRewrite :
      (fun ω ↦ I.restrict (futurePathAfterStoppingTime B τ ω)) =
        fun ω ↦
          (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e)
            (fun i : Fin I.card ↦ B (σ ω + times i) ω) := by
    funext ω
    symm
    have hCoord :
        (fun i : Fin I.card ↦ B (σ ω + times i) ω) =
          fun i : Fin I.card ↦ futurePathAfterStoppingTime B τ ω (times i) := by
      funext i
      symm
      simpa [τ, times] using
        futurePathAfterStoppingTime_apply_of_ne_top
          B τ ω (times i) WithTop.coe_ne_top
    rw [hCoord]
    simpa [e, times] using
      orderedTimeRestriction_eq_restrict I (futurePathAfterStoppingTime B τ ω)
  -- Proof comment: compose the measurable finite-vector equivalence with the finished
  -- finite-stop future-vector measurability owner.
  refine AEMeasurable.congr
    (((MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e).measurable.comp_aemeasurable
      hVector.aemeasurable))
    ?_
  filter_upwards with ω
  simpa [Function.comp] using (congrFun hRewrite ω).symm

/-- Helper for Theorem 21.18: evaluating a restricted path on the ordered coordinates of a finite
subfamily is measurable. -/
private lemma measurableOrderedSubtypeEvalVector
    {J : Set NNReal} (I : Finset J) :
    Measurable (fun y : ((j : J) → ℝ) ↦ fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i)) := by
  -- Proof comment: each ordered coordinate is ordinary evaluation at one fixed restricted time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (I.orderEmbOfFin rfl i)

/-- Helper for Theorem 21.18: equal maps on a measurable slice have the same restricted
pushforward. -/
private lemma restrictMap_eq_of_eqOn_slice
    {F : Type*} [MeasurableSpace F]
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s)
    {f g : Ω → F} (hfg : Set.EqOn f g s) :
    (μ.restrict s).map f = (μ.restrict s).map g := by
  -- Proof comment: after restricting to `s`, the two maps agree everywhere on the support of the
  -- restricted measure, so their pushforwards coincide.
  refine MeasureTheory.Measure.map_congr ?_
  exact MeasureTheory.ae_restrict_of_forall_mem hs fun ω hω ↦ hfg hω

/-- Helper for Theorem 21.18: mapping the translated Brownian kernel first to the restricted
product and then to the ordered coordinates of `I` is the same as mapping directly to that finite
future vector. -/
private lemma brownianTranslatedPathKernel_map_restrict_orderedEval
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    {J : Set NNReal} [Countable J] (I : Finset J) :
    ((brownianTranslatedPathKernel P B).map J.restrict).map
        (fun y : ((j : J) → ℝ) ↦ fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i)) =
      (brownianTranslatedPathKernel P B).map
        (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦
          y (((I.orderEmbOfFin rfl i : J) : NNReal))) := by
  -- Proof comment: compose the measurable countable restriction with the measurable ordered
  -- coordinate evaluation once at the kernel owner, so downstream proofs can stay in the finite
  -- vector normal form.
  simpa using
    (Kernel.map_comp_right (brownianTranslatedPathKernel P B)
      measurable_restrict_countable (measurableOrderedSubtypeEvalVector I)).symm

/-- Helper for Theorem 21.18: for a finite stopping time `σ`, restricting the stopped future path
to `J` and then reading off the ordered coordinates of `I` gives the Brownian future vector at
those times. -/
private lemma orderedSubtypeEval_comp_restrict_futurePathAfterStoppingTime_finiteStop
    (B : NNReal → Ω → ℝ) {J : Set NNReal} (I : Finset J) (σ : Ω → NNReal) :
    (fun ω ↦
      (fun y : ((j : J) → ℝ) ↦ fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i))
        (J.restrict (futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω))) =
      fun ω ↦ fun i : Fin I.card ↦ B (σ ω + (((I.orderEmbOfFin rfl i : J) : NNReal))) ω := by
  -- Proof comment: finite stopping times remove the `WithTop` transport, so each ordered
  -- restricted coordinate is just evaluation of the shifted Brownian path at the same time.
  funext ω
  ext i
  have hPath :
      futurePathAfterStoppingTime B (fun ω ↦ (σ ω : WithTop NNReal)) ω =
        fun t ↦ B (σ ω + t) ω :=
    brownianFuturePath_eq_fixedTime_on_slice B σ (ω := ω) (s := σ ω) rfl
  exact congrArg
    (fun f : NNReal → ℝ ↦ f (((I.orderEmbOfFin rfl i : J) : NNReal))) hPath

/-- Helper for Theorem 21.18: a finite stopping time evaluates the stopped present value by
ordinary substitution into the Brownian path. -/
private lemma stoppedValue_finiteStoppingTime_eq
    (B : NNReal → Ω → ℝ) (σ : Ω → NNReal) :
    stoppedValue B (fun ω ↦ (σ ω : WithTop NNReal)) = fun ω ↦ B (σ ω) ω := by
  -- Proof comment: on the singleton slice where the finite stopping time equals its own value,
  -- the generic stopped-value API collapses to direct evaluation.
  funext ω
  simpa using brownianStoppedValue_eq_fixedTime_on_slice B σ (ω := ω) (s := σ ω) rfl

/-- Helper for Theorem 21.18: on every clipped slice `s ∩ {τ ≤ T}`, the countable-coordinate
future law matches the translated Brownian kernel after restricting to `J`. -/
private lemma restrictedProductOrderedEvalLaw_eq_clippedSlice
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    {J : Set NNReal} (hJ : J.Countable)
    {s : Set Ω} (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : NNReal) (I : Finset J) :
    Measure.map
        (fun y : ((j : J) → ℝ) ↦ fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i))
        (((P x : Measure Ω).restrict (s ∩ {ω | τ ω ≤ T})).map
          (fun ω ↦ J.restrict (futurePathAfterStoppingTime B τ ω))) =
    Measure.map
        (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦
          y (((I.orderEmbOfFin rfl i : J) : NNReal)))
        ((brownianTranslatedPathKernel P B) ∘ₘ
          (((P x : Measure Ω).restrict (s ∩ {ω | τ ω ≤ T})).map (stoppedValue B τ))) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let σ : Ω → NNReal := clippedStoppingTimeNNReal τ T
  let τT : Ω → WithTop NNReal := fun ω ↦ (σ ω : WithTop NNReal)
  let sT : Set Ω := s ∩ {ω | τ ω ≤ T}
  let evalJ : ((j : J) → ℝ) → Fin I.card → ℝ := fun y i ↦ y (I.orderEmbOfFin rfl i)
  let evalTimes : (NNReal → ℝ) → Fin I.card → ℝ := fun y i ↦
    y (((I.orderEmbOfFin rfl i : J) : NNReal))
  let futureRestricted : Ω → ((j : J) → ℝ) := fun ω ↦
    J.restrict (futurePathAfterStoppingTime B τ ω)
  let futureRestrictedClip : Ω → ((j : J) → ℝ) := fun ω ↦
    J.restrict (futurePathAfterStoppingTime B τT ω)
  let futureVector : Ω → Fin I.card → ℝ := fun ω i ↦
    B (σ ω + (((I.orderEmbOfFin rfl i : J) : NNReal))) ω
  letI : Countable J := hJ.to_subtype
  have hs_ambient : MeasurableSet s := hτ.measurableSpace_le _ hs
  have hleT_ambient : MeasurableSet {ω | τ ω ≤ T} :=
    hτ.measurableSpace_le _ (hτ.measurableSet_le' T)
  have hsT_ambient : MeasurableSet sT := hs_ambient.inter hleT_ambient
  have hsT_clip :
      MeasurableSet[(clippedStoppingTimeNNReal_isStoppingTime B hτ T).measurableSpace] sT :=
    measurableSet_inter_le_clippedStoppingTime B hτ hs T
  have hFutureMap :
      (μ.restrict sT).map futureRestricted = (μ.restrict sT).map futureRestrictedClip := by
    -- Proof comment: on the clipped slice `{τ ≤ T}`, the original and clipped stopping times
    -- produce the same restricted future path.
    refine restrictMap_eq_of_eqOn_slice (μ := μ) hsT_ambient ?_
    intro ω hω
    exact congrArg J.restrict
      ((futurePathAfterStoppingTime_clippedStoppingTime_eqOn_le_const
        B (τ := τ) T) hω.2).symm
  have hFutureClip_ae :
      AEMeasurable futureRestrictedClip (μ.restrict sT) := by
    -- Proof comment: countable coordinate restriction gives an a.e. measurable owner for the
    -- clipped future path on the restricted slice.
    exact
      (aemeasurable_restrictFuturePathAfterStoppingTime_countable
        P B hB x τT (clippedStoppingTimeNNReal_isStoppingTime B hτ T) hJ).mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hFutureEval :
      Measure.map evalJ ((μ.restrict sT).map futureRestrictedClip) =
        (μ.restrict sT).map (evalJ ∘ futureRestrictedClip) := by
    -- Proof comment: after the clipped-stop rewrite, push the restricted future path directly to
    -- its ordered finite coordinates.
    exact
      AEMeasurable.map_map_of_aemeasurable
        (μ := μ.restrict sT)
        (g := evalJ) (f := futureRestrictedClip)
        (measurableOrderedSubtypeEvalVector I).aemeasurable
        hFutureClip_ae
  have hEvalEq :
      evalJ ∘ futureRestrictedClip = futureVector := by
    -- Proof comment: the ordered finite coordinates of the clipped restricted future path are
    -- exactly the finite Brownian future vector at the same ordered times.
    simpa [evalJ, futureRestrictedClip, futureVector, Function.comp]
      using
        orderedSubtypeEval_comp_restrict_futurePathAfterStoppingTime_finiteStop
          B I σ
  have hStoppedFiniteMap :
      (μ.restrict sT).map (fun ω ↦ B (σ ω) ω) =
        (μ.restrict sT).map (stoppedValue B τT) := by
    -- Proof comment: for the finite clipped stopping time, the stopped value is just ordinary
    -- Brownian evaluation at the clipped time.
    rw [stoppedValue_finiteStoppingTime_eq B σ]
  have hStoppedClipMap :
      (μ.restrict sT).map (stoppedValue B τT) =
        (μ.restrict sT).map (stoppedValue B τ) := by
    -- Proof comment: on the clipped slice `{τ ≤ T}`, clipping the stopping time does not change
    -- the stopped present value.
    refine restrictMap_eq_of_eqOn_slice (μ := μ) hsT_ambient ?_
    intro ω hω
    exact stoppedValue_clippedStoppingTime_eqOn_le_const B (τ := τ) T hω.2
  have hFinite :
      (μ.restrict sT).map futureVector =
        Measure.map evalTimes
          ((brownianTranslatedPathKernel P B) ∘ₘ
            ((μ.restrict sT).map (fun ω ↦ B (σ ω) ω))) := by
    -- Proof comment: once everything is normalized to the finite clipped stopping time, the
    -- existing finite-stop vector law applies directly.
    simpa [μ, sT, σ, futureVector, evalTimes] using
      (brownianFutureVectorRestrictedLaw_eq_kernel_finiteStop
        P B hB x σ (clippedStoppingTimeNNReal_isStoppingTime B hτ T)
        hsT_clip
        (fun i : Fin I.card ↦ (((I.orderEmbOfFin rfl i : J) : NNReal))))
  calc
    Measure.map evalJ ((μ.restrict sT).map futureRestricted)
        = Measure.map evalJ ((μ.restrict sT).map futureRestrictedClip) := by
            rw [hFutureMap]
    _ = (μ.restrict sT).map (evalJ ∘ futureRestrictedClip) := hFutureEval
    _ = (μ.restrict sT).map futureVector := by rw [hEvalEq]
    _ = Measure.map evalTimes
          ((brownianTranslatedPathKernel P B) ∘ₘ
            ((μ.restrict sT).map (fun ω ↦ B (σ ω) ω))) := hFinite
    _ = Measure.map evalTimes
          ((brownianTranslatedPathKernel P B) ∘ₘ
            ((μ.restrict sT).map (stoppedValue B τT))) := by
            rw [hStoppedFiniteMap]
    _ = Measure.map evalTimes
          ((brownianTranslatedPathKernel P B) ∘ₘ
            ((μ.restrict sT).map (stoppedValue B τ))) := by
            rw [hStoppedClipMap]

/-- Helper for Theorem 21.18: on every clipped slice `s ∩ {τ ≤ T}`, the countable-coordinate
future law matches the translated Brownian kernel after restricting to `J`. -/
private lemma orderedSubtypeCylinder_eq_orderedEvalPreimage
    {J : Set NNReal} (I : Finset J) (S : Set (∀ i : I, ℝ)) :
    let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
    let A : Set (Fin I.card → ℝ) :=
      (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) ⁻¹' S
    (fun y : ((j : J) → ℝ) ↦ fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i)) ⁻¹' A =
      MeasureTheory.cylinder I S := by
  -- Proof comment: the finite cylinder on the restricted product is exactly the preimage of its
  -- ordered finite-coordinate base after reindexing by `I.orderEmbOfFin`.
  ext y
  -- Proof comment: membership in the ordered-coordinate preimage is exactly membership of the
  -- finite restriction `I.restrict y` in the cylinder base set `S`.
  change
    (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) ((I.orderIsoOfFin rfl).toEquiv)
      (fun i : Fin I.card ↦ y (I.orderEmbOfFin rfl i))) ∈ S ↔
      I.restrict y ∈ S
  rw [orderedSubtypeRestriction_eq_restrict I y]

/-- Helper for Theorem 21.18: pulling a restricted-product cylinder back along `J.restrict`
matches the same ordered finite-coordinate event on the full path space. -/
private lemma restrictCylinder_preimage_eq_orderedEvalPreimage
    {J : Set NNReal} (I : Finset J) (S : Set (∀ i : I, ℝ)) :
    let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
    let A : Set (Fin I.card → ℝ) :=
      (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) ⁻¹' S
    J.restrict ⁻¹' MeasureTheory.cylinder I S =
      (fun y : NNReal → ℝ ↦ fun i : Fin I.card ↦ y (((I.orderEmbOfFin rfl i : J) : NNReal))) ⁻¹' A := by
  -- Proof comment: restricting an ambient path to `J` and then taking the cylinder coordinates is
  -- the same as reading those coordinates directly on the ambient path.
  ext y
  -- Proof comment: after restricting an ambient path to `J`, the cylinder test is still the same
  -- ordered finite-coordinate test on those ambient times.
  change I.restrict (J.restrict y) ∈ S ↔
    (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) ((I.orderIsoOfFin rfl).toEquiv)
      (fun i : Fin I.card ↦ y (((I.orderEmbOfFin rfl i : J) : NNReal)))) ∈ S
  have hEq :
      (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) ((I.orderIsoOfFin rfl).toEquiv)
        (fun i : Fin I.card ↦ y (((I.orderEmbOfFin rfl i : J) : NNReal)))) =
        I.restrict (J.restrict y) := by
    simpa using orderedSubtypeRestriction_eq_restrict I (J.restrict y)
  constructor <;> intro hy
  · simpa [hEq] using hy
  · simpa [hEq] using hy

/-- Helper for Theorem 21.18: on every clipped slice `s ∩ {τ ≤ T}`, the countable-coordinate
future law matches the translated Brownian kernel after restricting to `J`. -/
private lemma brownianRestrictedFutureLaw_eq_kernel_countableFactor_clippedSlice
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    {J : Set NNReal} (hJ : J.Countable)
    {s : Set Ω} (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : NNReal) :
    (((P x : Measure Ω).restrict (s ∩ {ω | τ ω ≤ T})).map
      (fun ω ↦ J.restrict (futurePathAfterStoppingTime B τ ω))) =
      (((brownianTranslatedPathKernel P B) ∘ₘ
        (((P x : Measure Ω).restrict (s ∩ {ω | τ ω ≤ T})).map (stoppedValue B τ))).map
          J.restrict) :=
  by
    let μ : Measure Ω := (P x : Measure Ω)
    let sT : Set Ω := s ∩ {ω | τ ω ≤ T}
    let futureRestricted : Ω → ((j : J) → ℝ) := fun ω ↦
      J.restrict (futurePathAfterStoppingTime B τ ω)
    let ρ0 : Measure (NNReal → ℝ) :=
      (brownianTranslatedPathKernel P B) ∘ₘ ((μ.restrict sT).map (stoppedValue B τ))
    let ν : Measure ((j : J) → ℝ) := (μ.restrict sT).map futureRestricted
    let ρ : Measure ((j : J) → ℝ) := ρ0.map J.restrict
    letI : Countable J := hJ.to_subtype
    letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
      brownianTranslatedPathKernel_isMarkov P B hB
    letI : IsFiniteMeasure ρ0 := by
      dsimp [ρ0]
      infer_instance
    letI : IsFiniteMeasure ρ := by
      dsimp [ρ]
      infer_instance
    have hCylinderEq :
        ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : J ↦ ℝ), ν u = ρ u := by
      intro u hu
      obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders u).1 hu
      let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
      let A : Set (Fin I.card → ℝ) :=
        (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e) ⁻¹' S
      let evalJ : ((j : J) → ℝ) → Fin I.card → ℝ := fun y i ↦ y (I.orderEmbOfFin rfl i)
      let evalTimes : (NNReal → ℝ) → Fin I.card → ℝ := fun y i ↦
        y (((I.orderEmbOfFin rfl i : J) : NNReal))
      have hA : MeasurableSet A := by
        -- Proof comment: the ordered finite-vector base set stays measurable under the
        -- reindexing equivalence.
        exact (MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e).measurableSet_preimage.2 hS
      have hMapLeft :
          Measure.map evalJ ν = Measure.map evalTimes ρ0 := by
        -- Proof comment: the clipped-slice finite-vector law is already proved after pushing both
        -- measures to the ordered coordinates of `I`.
        simpa [μ, sT, futureRestricted, ν, ρ0, evalJ, evalTimes] using
          (restrictedProductOrderedEvalLaw_eq_clippedSlice
            P B hB x τ hτ hJ hs T I)
      have hMapRight :
          Measure.map evalJ ρ = Measure.map evalTimes ρ0 := by
        -- Proof comment: mapping the kernel law first to `J` and then to the ordered coordinates
        -- is the same as mapping directly to those ambient coordinates.
        calc
          Measure.map evalJ ρ = Measure.map evalJ (Measure.map J.restrict ρ0) := by
              rfl
          _ = Measure.map (evalJ ∘ J.restrict) ρ0 := by
                rw [Measure.map_map
                  (measurableOrderedSubtypeEvalVector I) measurable_restrict_countable]
          _ = Measure.map evalTimes ρ0 := by
                rfl
      have hRealEq :
          ν.real (MeasureTheory.cylinder I S) = ρ.real (MeasureTheory.cylinder I S) := by
        -- Proof comment: after normalizing the cylinder to the ordered finite-vector base `A`,
        -- both real masses are read from the same pushed-forward finite-vector law.
        calc
          ν.real (MeasureTheory.cylinder I S) = (Measure.map evalJ ν).real A := by
              symm
              rw [MeasureTheory.map_measureReal_apply
                (μ := ν) (f := evalJ) (measurableOrderedSubtypeEvalVector I) hA]
              rw [orderedSubtypeCylinder_eq_orderedEvalPreimage (I := I) (S := S)]
          _ = (Measure.map evalTimes ρ0).real A := by rw [hMapLeft]
          _ = (Measure.map evalJ ρ).real A := by rw [hMapRight]
          _ = ρ.real (MeasureTheory.cylinder I S) := by
              rw [MeasureTheory.map_measureReal_apply
                (μ := ρ) (f := evalJ) (measurableOrderedSubtypeEvalVector I) hA]
              rw [orderedSubtypeCylinder_eq_orderedEvalPreimage (I := I) (S := S)]
      exact
        (MeasureTheory.measureReal_eq_measureReal_iff
          (μ := ν) (ν := ρ) (s := MeasureTheory.cylinder I S)
          (t := MeasureTheory.cylinder I S)
          (h₁ := measure_ne_top ν (MeasureTheory.cylinder I S))
          (h₂ := measure_ne_top ρ (MeasureTheory.cylinder I S))).mp hRealEq
    have hEq : ν = ρ := by
      -- Proof comment: equality on the cylinder generators upgrades to equality of the full
      -- restricted-product measures by finite-measure extensionality.
      refine
        MeasureTheory.ext_of_generate_finite
          (MeasureTheory.measurableCylinders fun _ : J ↦ ℝ)
          MeasureTheory.generateFrom_measurableCylinders.symm
          MeasureTheory.isPiSystem_measurableCylinders
          hCylinderEq
          ?_
      simpa using
        hCylinderEq Set.univ
          (MeasureTheory.univ_mem_measurableCylinders (fun _ : J ↦ ℝ))
    simpa [μ, sT, futureRestricted, ν, ρ0, ρ] using hEq

/-- Helper for Theorem 21.18: on every `𝓕_τ`-measurable slice, the countable-coordinate future
path law agrees with the translated Brownian kernel pushed forward by `J.restrict`. -/
private lemma aeEventually_mem_sliceInter_le_nat_of_aeFiniteStop
    (μ : Measure Ω) {τ : Ω → WithTop NNReal} {s : Set Ω}
    (hτfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      (ω ∈ s ∩ {ω | τ ω ≤ (n : NNReal)}) ↔ ω ∈ s :=
  by
    filter_upwards [hτfinite] with ω hω
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (τ ω).untop hω ≤ (N : NNReal) :=
      exists_nat_ge ((τ ω).untop hω)
    -- Proof comment: once the finite stopping value is bounded by one natural number `N`, every
    -- larger clipping horizon contains `ω`, so the clipped slice agrees with the original slice.
    refine (eventually_ge_atTop N).mono ?_
    intro n hn
    have hτ_le_n' : (τ ω).untop hω ≤ (n : NNReal) := by
      exact le_trans hN (by exact_mod_cast hn)
    have hτ_le_n : τ ω ≤ (n : NNReal) := by
      simpa [WithTop.coe_untop] using hτ_le_n'
    constructor
    · intro hsω
      exact hsω.1
    · intro hsω
      exact ⟨hsω, hτ_le_n⟩

/-- Helper for Theorem 21.18: mapped masses on clipped slices converge to the full-slice mapped
mass once the stopping time is finite almost everywhere. -/
private lemma tendsto_mapReal_restrictInter_le_nat_of_aeFiniteStop
    {F : Type*} [MeasurableSpace F]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {τ : Ω → WithTop NNReal}
    (hτ_meas : ∀ T : NNReal, MeasurableSet {ω | τ ω ≤ T})
    {s : Set Ω} (hs : MeasurableSet s)
    (hτfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {Y : Ω → F} (hY : AEMeasurable Y (μ.restrict s))
    {A : Set F} (hA : MeasurableSet A) :
    Tendsto
      (fun n : ℕ ↦
        (((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map Y).real A))
      atTop
      (𝓝 (((μ.restrict s).map Y).real A)) :=
  by
    let Ym : Ω → F := AEMeasurable.mk Y hY
    let E : Set Ω := Ym ⁻¹' A ∩ s
    have hYm_meas : Measurable Ym := hY.measurable_mk
    have hE_meas : MeasurableSet E := (hYm_meas hA).inter hs
    have hEventual :
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          (ω ∈ E ∩ {ω | τ ω ≤ (n : NNReal)}) ↔ ω ∈ E := by
      filter_upwards
        [aeEventually_mem_sliceInter_le_nat_of_aeFiniteStop (μ := μ) (τ := τ) (s := s) hτfinite]
        with ω hω
      refine hω.mono ?_
      intro n hn
      constructor
      · intro hmem
        exact hmem.1
      · intro hmem
        exact ⟨hmem, ((hn).2 hmem.2).2⟩
    have hMeasureTendsto :
        Tendsto
          (fun n : ℕ ↦ μ.real (E ∩ {ω | τ ω ≤ (n : NNReal)}))
          atTop
          (𝓝 (μ.real E)) := by
      have hENN :
          Tendsto
            (fun n : ℕ ↦ μ (E ∩ {ω | τ ω ≤ (n : NNReal)}))
            atTop
            (𝓝 (μ E)) :=
        MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
          (L := atTop) (μ := μ)
          (A := E)
          (As := fun n : ℕ ↦ E ∩ {ω | τ ω ≤ (n : NNReal)})
          hE_meas
          (fun n ↦ hE_meas.inter (hτ_meas (n : NNReal)))
          hEventual
      have hToReal :
          Tendsto
            (fun n : ℕ ↦ (μ (E ∩ {ω | τ ω ≤ (n : NNReal)})).toReal)
            atTop
            (𝓝 ((μ E).toReal)) :=
        (ENNReal.continuousAt_toReal (measure_ne_top μ E)).tendsto.comp hENN
      simpa [MeasureTheory.measureReal_def, E] using hToReal
    have hSeqEq :
        (fun n : ℕ ↦ (((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map Y).real A)) =
          fun n : ℕ ↦ μ.real (E ∩ {ω | τ ω ≤ (n : NNReal)}) := by
      funext n
      let sn : Set Ω := s ∩ {ω | τ ω ≤ (n : NNReal)}
      have hsn_meas : MeasurableSet sn := hs.inter (hτ_meas (n : NNReal))
      have hY_eq_sn :
          Y =ᵐ[μ.restrict sn] Ym := by
        have hY_eq_restrict :
            Y =ᵐ[(μ.restrict s).restrict {ω | τ ω ≤ (n : NNReal)}] Ym :=
          hY.ae_eq_mk.restrict
        rw [MeasureTheory.Measure.restrict_restrict' (μ := μ) (s := {ω | τ ω ≤ (n : NNReal)})
          (t := s) hs] at hY_eq_restrict
        simpa [sn, Set.inter_comm] using hY_eq_restrict
      have hMapEq :
          (μ.restrict sn).map Y = (μ.restrict sn).map Ym :=
        MeasureTheory.Measure.map_congr hY_eq_sn
      calc
        (((μ.restrict sn).map Y).real A) = (((μ.restrict sn).map Ym).real A) := by
          rw [hMapEq]
        _ = (μ.restrict sn).real (Ym ⁻¹' A) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := μ.restrict sn) (f := Ym) hYm_meas hA)
        _ = μ.real (Ym ⁻¹' A ∩ sn) := by
          simpa [sn, E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            (MeasureTheory.measureReal_restrict_apply
              (μ := μ) (s := sn) (t := Ym ⁻¹' A) (hYm_meas hA))
        _ = μ.real (E ∩ {ω | τ ω ≤ (n : NNReal)}) := by
          simp [sn, E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have hTargetEq :
        (((μ.restrict s).map Y).real A) = μ.real E := by
      have hMapEq :
          (μ.restrict s).map Y = (μ.restrict s).map Ym :=
        MeasureTheory.Measure.map_congr hY.ae_eq_mk
      calc
        (((μ.restrict s).map Y).real A) = (((μ.restrict s).map Ym).real A) := by
          rw [hMapEq]
        _ = (μ.restrict s).real (Ym ⁻¹' A) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := μ.restrict s) (f := Ym) hYm_meas hA)
        _ = μ.real (Ym ⁻¹' A ∩ s) := by
          simpa [E, Set.inter_comm] using
            (MeasureTheory.measureReal_restrict_apply
              (μ := μ) (s := s) (t := Ym ⁻¹' A) (hYm_meas hA))
        _ = μ.real E := by
          rfl
    rw [hSeqEq, hTargetEq]
    exact hMeasureTendsto

/-- Helper for Theorem 21.18: kernel-composition masses on clipped slices converge to the
full-slice kernel-composition mass once the stopping time is finite almost everywhere. -/
private lemma tendsto_kernelCompReal_restrictInter_le_nat_of_aeFiniteStop
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel ℝ F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {τ : Ω → WithTop NNReal}
    (hτ_meas : ∀ T : NNReal, MeasurableSet {ω | τ ω ≤ T})
    {s : Set Ω} (hs : MeasurableSet s)
    (hτfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {Y : Ω → ℝ} (hY : AEMeasurable Y (μ.restrict s))
    {A : Set F} (hA : MeasurableSet A) :
    Tendsto
      (fun n : ℕ ↦
        ((κ ∘ₘ ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map Y)).real A))
      atTop
      (𝓝 ((κ ∘ₘ ((μ.restrict s).map Y)).real A)) :=
  by
    let Ym : Ω → ℝ := AEMeasurable.mk Y hY
    let G : Ω → ℝ := fun ω ↦ (κ (Ym ω)).real A
    let F0 : Ω → ℝ := Set.indicator s G
    let Fn : ℕ → Ω → ℝ := fun n ↦ Set.indicator (s ∩ {ω | τ ω ≤ (n : NNReal)}) G
    have hYm_meas : Measurable Ym := hY.measurable_mk
    have hG_meas : Measurable G := by
      -- Proof comment: kernel row masses are measurable in the stopped state once the test set
      -- `A` is measurable.
      simpa [G] using (((Kernel.measurable_coe κ hA).ennreal_toReal).comp hYm_meas)
    have hMass_le_one : ∀ ω : Ω, G ω ≤ 1 := by
      intro ω
      calc
        G ω ≤ (κ (Ym ω)).real Set.univ := by
          simpa [G] using
            (MeasureTheory.measureReal_mono
              (μ := κ (Ym ω)) (s₁ := A) (s₂ := Set.univ)
              (by intro z hz; simp))
        _ = 1 := by
          simp [MeasureTheory.measureReal_def]
    have hApprox_meas : ∀ n : ℕ, AEStronglyMeasurable (Fn n) μ := by
      intro n
      exact
        ((Measurable.indicator hG_meas (hs.inter (hτ_meas (n : NNReal)))).aestronglyMeasurable)
    have hApprox_dom : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Fn n ω‖ ≤ 1 := by
      intro n
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      by_cases hω : ω ∈ s ∩ {ω | τ ω ≤ (n : NNReal)}
      · have hG_nonneg : 0 ≤ G ω := by
          simp [G, MeasureTheory.measureReal_nonneg]
        change ‖Set.indicator (s ∩ {ω | τ ω ≤ (n : NNReal)}) G ω‖ ≤ 1
        rw [Set.indicator_of_mem hω, Real.norm_of_nonneg hG_nonneg]
        exact hMass_le_one ω
      · change ‖Set.indicator (s ∩ {ω | τ ω ≤ (n : NNReal)}) G ω‖ ≤ 1
        rw [Set.indicator_of_notMem hω]
        norm_num
    have hApprox_tendsto :
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Fn n ω) atTop (𝓝 (F0 ω)) := by
      filter_upwards
        [aeEventually_mem_sliceInter_le_nat_of_aeFiniteStop (μ := μ) (τ := τ) (s := s) hτfinite]
        with ω hω
      have hEq :
          (fun n : ℕ ↦ Fn n ω) =ᶠ[atTop] fun _ : ℕ ↦ F0 ω := by
        refine hω.mono ?_
        intro n hn
        change Set.indicator (s ∩ {ω | τ ω ≤ (n : NNReal)}) G ω = Set.indicator s G ω
        by_cases hsω : ω ∈ s
        · have hsnω : ω ∈ s ∩ {ω | τ ω ≤ (n : NNReal)} := (hn.2 hsω)
          rw [Set.indicator_of_mem hsnω, Set.indicator_of_mem hsω]
        · have hsnω : ω ∉ s ∩ {ω | τ ω ≤ (n : NNReal)} := by
            intro hsω'
            exact hsω hsω'.1
          rw [Set.indicator_of_notMem hsnω, Set.indicator_of_notMem hsω]
      exact tendsto_const_nhds.congr' hEq.symm
    have hBound_int : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := by
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ)
    have hIntegral_tendsto :
        Tendsto (fun n : ℕ ↦ ∫ ω, Fn n ω ∂μ) atTop (𝓝 (∫ ω, F0 ω ∂μ)) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : Ω ↦ (1 : ℝ)) hApprox_meas hBound_int hApprox_dom hApprox_tendsto
    have hSeqEq :
        (fun n : ℕ ↦
          ((κ ∘ₘ ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map Y)).real A)) =
          fun n : ℕ ↦ ∫ ω, Fn n ω ∂μ := by
      funext n
      let sn : Set Ω := s ∩ {ω | τ ω ≤ (n : NNReal)}
      have hsn_meas : MeasurableSet sn := hs.inter (hτ_meas (n : NNReal))
      have hY_eq_sn : Y =ᵐ[μ.restrict sn] Ym := by
        have hY_eq_restrict :
            Y =ᵐ[(μ.restrict s).restrict {ω | τ ω ≤ (n : NNReal)}] Ym :=
          hY.ae_eq_mk.restrict
        rw [MeasureTheory.Measure.restrict_restrict' (μ := μ)
          (s := {ω | τ ω ≤ (n : NNReal)}) (t := s) hs] at hY_eq_restrict
        simpa [sn, Set.inter_comm] using hY_eq_restrict
      have hMapEq :
          (μ.restrict sn).map Y = (μ.restrict sn).map Ym :=
        MeasureTheory.Measure.map_congr hY_eq_sn
      calc
        ((κ ∘ₘ ((μ.restrict sn).map Y)).real A)
            = ((κ ∘ₘ ((μ.restrict sn).map Ym)).real A) := by
                rw [hMapEq]
        _ = ∫ ω in sn, (κ (Ym ω)).real A ∂μ := by
              simpa [sn, G] using
                (kernelComp_restrictMap_real_eq_setIntegral_local
                  (κ := κ) (μ := μ) (hY := hYm_meas) (s := sn) hsn_meas hA)
        _ = ∫ ω, Fn n ω ∂μ := by
              symm
              simpa [Fn, G, sn] using
                (MeasureTheory.integral_indicator (μ := μ) (s := sn) (f := G) hsn_meas)
    have hTargetEq :
        ((κ ∘ₘ ((μ.restrict s).map Y)).real A) = ∫ ω, F0 ω ∂μ := by
      have hMapEq :
          (μ.restrict s).map Y = (μ.restrict s).map Ym :=
        MeasureTheory.Measure.map_congr hY.ae_eq_mk
      calc
        ((κ ∘ₘ ((μ.restrict s).map Y)).real A)
            = ((κ ∘ₘ ((μ.restrict s).map Ym)).real A) := by
                rw [hMapEq]
        _ = ∫ ω in s, (κ (Ym ω)).real A ∂μ := by
              simpa [G] using
                (kernelComp_restrictMap_real_eq_setIntegral_local
                  (κ := κ) (μ := μ) (hY := hYm_meas) (s := s) hs hA)
        _ = ∫ ω, F0 ω ∂μ := by
              symm
              simpa [F0, G] using
                (MeasureTheory.integral_indicator (μ := μ) (s := s) (f := G) hs)
    rw [hSeqEq, hTargetEq]
    exact hIntegral_tendsto

/-- Helper for Theorem 21.18: on every `𝓕_τ`-measurable slice, the countable-coordinate future
path law agrees with the translated Brownian kernel pushed forward by `J.restrict`. -/
private lemma brownianRestrictedFutureLaw_eq_kernel_countableFactor
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x)
    (x : ℝ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration B) τ)
    (hτfinite : ∀ᵐ ω ∂(P x : Measure Ω), τ ω ≠ ⊤)
    {J : Set NNReal} (hJ : J.Countable)
    {s : Set Ω} (hs : MeasurableSet[hτ.measurableSpace] s) :
    (((P x : Measure Ω).restrict s).map
      (fun ω ↦ J.restrict (futurePathAfterStoppingTime B τ ω))) =
      (((brownianTranslatedPathKernel P B) ∘ₘ
        (((P x : Measure Ω).restrict s).map (stoppedValue B τ))).map J.restrict) :=
  by
    let μ : Measure Ω := (P x : Measure Ω)
    let futureRestricted : Ω → ((j : J) → ℝ) := fun ω ↦
      J.restrict (futurePathAfterStoppingTime B τ ω)
    let ν : Measure ((j : J) → ℝ) := ((μ.restrict s).map futureRestricted)
    let ρ0 : Measure (NNReal → ℝ) :=
      (brownianTranslatedPathKernel P B) ∘ₘ ((μ.restrict s).map (stoppedValue B τ))
    let ρ : Measure ((j : J) → ℝ) := ρ0.map J.restrict
    letI : Countable J := hJ.to_subtype
    letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
      brownianTranslatedPathKernel_isMarkov P B hB
    have hs_ambient : MeasurableSet s := hτ.measurableSpace_le _ hs
    have hfuture_ae :
        AEMeasurable futureRestricted (μ.restrict s) := by
      -- Proof comment: countable coordinate restriction makes the stopped future path
      -- almost-everywhere measurable on the history slice.
      exact
        (aemeasurable_restrictFuturePathAfterStoppingTime_countable
          P B hB x τ hτ hJ).mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hstopped_ae :
        AEMeasurable (stoppedValue B τ) (μ.restrict s) := by
      -- Proof comment: the stopped present value is already ambient a.e. measurable, hence also
      -- a.e. measurable on the restricted history slice.
      exact
        (aemeasurable_stoppedValue_brownian P B hB x τ hτ).mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hCylinderEq :
        ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : J ↦ ℝ), ν u = ρ u := by
      intro u hu
      obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders u).1 hu
      let C : Set ((j : J) → ℝ) := MeasureTheory.cylinder I S
      have hC_meas : MeasurableSet C := by
        rw [← MeasureTheory.generateFrom_measurableCylinders]
        exact MeasurableSpace.measurableSet_generateFrom hu
      have hLeft_tendsto :
          Tendsto
            (fun n : ℕ ↦
              (((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map futureRestricted).real C))
            atTop
            (𝓝 (ν.real C)) := by
        -- Proof comment: the clipped-slice future-path masses converge to the full-slice mass on
        -- each restricted-product cylinder.
        simpa [μ, futureRestricted, ν] using
          (tendsto_mapReal_restrictInter_le_nat_of_aeFiniteStop
            (μ := μ)
            (hτ_meas := fun T ↦ hτ.measurableSpace_le _ (hτ.measurableSet_le' T))
            (hs := hs_ambient) hτfinite hfuture_ae hC_meas)
      have hRight_tendsto :
          Tendsto
            (fun n : ℕ ↦
              ((((brownianTranslatedPathKernel P B) ∘ₘ
                  ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).map
                    J.restrict).real C))
            atTop
            (𝓝 (ρ.real C)) := by
        have hPreC_meas : MeasurableSet (J.restrict ⁻¹' C) := measurable_restrict_countable hC_meas
        have hKernel_tendsto :
            Tendsto
              (fun n : ℕ ↦
                ((brownianTranslatedPathKernel P B ∘ₘ
                    ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).real
                  (J.restrict ⁻¹' C)))
              atTop
              (𝓝
                ((brownianTranslatedPathKernel P B ∘ₘ
                    ((μ.restrict s).map (stoppedValue B τ))).real (J.restrict ⁻¹' C))) := by
          simpa [μ] using
            (tendsto_kernelCompReal_restrictInter_le_nat_of_aeFiniteStop
              (κ := brownianTranslatedPathKernel P B)
              (μ := μ)
              (hτ_meas := fun T ↦ hτ.measurableSpace_le _ (hτ.measurableSet_le' T))
              (hs := hs_ambient) hτfinite hstopped_ae hPreC_meas)
        have hSeqEq :
            (fun n : ℕ ↦
              ((((brownianTranslatedPathKernel P B) ∘ₘ
                  ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).map
                    J.restrict).real C)) =
              fun n : ℕ ↦
                ((brownianTranslatedPathKernel P B ∘ₘ
                    ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).real
                  (J.restrict ⁻¹' C)) := by
          funext n
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := (brownianTranslatedPathKernel P B) ∘ₘ
                ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ)))
              (f := J.restrict) measurable_restrict_countable hC_meas)
        have hTargetEq :
            ρ.real C =
              ((brownianTranslatedPathKernel P B ∘ₘ
                  ((μ.restrict s).map (stoppedValue B τ))).real (J.restrict ⁻¹' C)) := by
          calc
            ρ.real C = (Measure.map J.restrict ρ0).real C := by
                rfl
            _ = ρ0.real (J.restrict ⁻¹' C) := by
                  simpa [ρ0] using
                    (MeasureTheory.map_measureReal_apply
                      (μ := ρ0) (f := J.restrict) measurable_restrict_countable hC_meas)
        have hKernel_tendsto' :
            Tendsto
              (fun n : ℕ ↦
                ((((brownianTranslatedPathKernel P B) ∘ₘ
                    ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).map
                      J.restrict).real C))
              atTop
              (𝓝
                ((brownianTranslatedPathKernel P B ∘ₘ
                    ((μ.restrict s).map (stoppedValue B τ))).real (J.restrict ⁻¹' C))) := by
          refine Tendsto.congr' ?_ hKernel_tendsto
          exact Filter.Eventually.of_forall fun n ↦ (congrFun hSeqEq n).symm
        simpa [hTargetEq] using hKernel_tendsto'
      have hClipEq :
          ∀ n : ℕ,
            (((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map futureRestricted).real C) =
              ((((brownianTranslatedPathKernel P B) ∘ₘ
                  ((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map (stoppedValue B τ))).map
                    J.restrict).real C) := by
        intro n
        exact congrArg (fun m : Measure ((j : J) → ℝ) ↦ m.real C)
          (brownianRestrictedFutureLaw_eq_kernel_countableFactor_clippedSlice
            P B hB x τ hτ hJ hs (n : NNReal))
      have hRight_tendsto' :
          Tendsto
            (fun n : ℕ ↦
              (((μ.restrict (s ∩ {ω | τ ω ≤ (n : NNReal)})).map futureRestricted).real C))
            atTop
            (𝓝 (ρ.real C)) := by
        refine Tendsto.congr' ?_ hRight_tendsto
        exact Filter.Eventually.of_forall fun n ↦ (hClipEq n).symm
      have hMassEq : ν.real C = ρ.real C :=
        tendsto_nhds_unique hLeft_tendsto hRight_tendsto'
      exact
        (MeasureTheory.measureReal_eq_measureReal_iff
          (μ := ν) (ν := ρ) (s := C) (t := C)
          (h₁ := measure_ne_top ν C) (h₂ := measure_ne_top ρ C)).mp hMassEq
    have hEq : ν = ρ := by
      -- Proof comment: once every restricted-product cylinder has the same mass, the full
      -- countable-coordinate future laws agree.
      refine
        MeasureTheory.ext_of_generate_finite
          (MeasureTheory.measurableCylinders fun _ : J ↦ ℝ)
          MeasureTheory.generateFrom_measurableCylinders.symm
          MeasureTheory.isPiSystem_measurableCylinders
          hCylinderEq
          ?_
      simpa using
        hCylinderEq Set.univ
          (MeasureTheory.univ_mem_measurableCylinders (fun _ : J ↦ ℝ))
    simpa [μ, futureRestricted, ν, ρ0, ρ] using hEq

/-- Theorem 21.18: Brownian motion with start laws `(P x)` has the strong Markov property. -/
theorem brownianStrongMarkov_of_countableFactor
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x) :
    ∃ κ : Kernel ℝ (NNReal → ℝ), HasStrongMarkovProperty P B κ := by
  refine ⟨brownianTranslatedPathKernel P B, ?_⟩
  -- Proof comment: the translated Brownian path kernel is the canonical witness, and the proof
  -- stays on a single countable restriction before reconstructing the conditional expectation.
  refine (hasStrongMarkovProperty_iff P B (brownianTranslatedPathKernel P B)).2 ?_
  intro x τ hτ hτfinite f hf_meas hf_bdd
  let μ : Measure Ω := (P x : Measure Ω)
  rcases exists_countableRestrict_factor_measurablePathFunctional f hf_meas with
    ⟨J, hJ, g, hg, hfg⟩
  letI : Countable J := hJ.to_subtype
  let κJ : Kernel ℝ ((j : J) → ℝ) := (brownianTranslatedPathKernel P B).map J.restrict
  let futureRestricted : Ω → ((j : J) → ℝ) := fun ω ↦
    J.restrict (futurePathAfterStoppingTime B τ ω)
  letI : IsMarkovKernel (brownianTranslatedPathKernel P B) :=
    brownianTranslatedPathKernel_isMarkov P B hB
  letI : IsMarkovKernel κJ := Kernel.IsMarkovKernel.map _ measurable_restrict_countable
  obtain ⟨C, hC⟩ := hf_bdd
  have hg_bound : ∀ z : (j : J) → ℝ, |g z| ≤ C :=
    bound_countableFactor_of_factorization hfg hC
  have hgenerated_le : hτ.measurableSpace ≤ ‹MeasurableSpace Ω› := hτ.measurableSpace_le
  have hfutureRestricted_ae :
      AEMeasurable futureRestricted μ :=
    aemeasurable_restrictFuturePathAfterStoppingTime_countable P B hB x τ hτ hJ
  have hgFuture_ae :
      AEMeasurable (fun ω ↦ g (futureRestricted ω)) μ :=
    aemeasurable_countableFactor_futurePathAfterStoppingTime P B hB x τ hτ hJ hg
  have hstopped_ae :
      AEMeasurable (stoppedValue B τ) μ :=
    aemeasurable_stoppedValue_brownian P B hB x τ hτ
  have hstopped_hτ :
      AEStronglyMeasurable[hτ.measurableSpace] (stoppedValue B τ) μ :=
    aestronglyMeasurable_stoppedValue_brownian_hTau P B hB x τ hτ
  have hg_int :
      Integrable (fun ω ↦ g (futureRestricted ω)) μ := by
    -- Proof comment: the countable-factor future observable is integrable because the
    -- factorization transfers the original uniform bound from `f` to `g`.
    refine Integrable.of_bound hgFuture_ae.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using hg_bound (futureRestricted ω)
  have hKernelIntegral_meas :
      Measurable fun z : ℝ ↦ ∫ y, g y ∂κJ z := by
    -- Proof comment: integrating the measurable bounded factor `g` against the restricted-path
    -- kernel is measurable in the starting state.
    exact
      (hg.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : ℝ ↦ ∫ y, g y ∂κJ z).measurable
  have hKernelIntegral_ae :
      AEStronglyMeasurable
        (fun ω ↦ ∫ z, g z ∂κJ (stoppedValue B τ ω)) μ := by
    -- Proof comment: ambient AE measurability follows by composing the kernel-integral owner
    -- with the ambient AE measurable stopped value.
    exact hKernelIntegral_meas.aestronglyMeasurable.comp_aemeasurable hstopped_ae
  have hKernelIntegral_hτ :
      AEStronglyMeasurable[hτ.measurableSpace]
        (fun ω ↦ ∫ z, g z ∂κJ (stoppedValue B τ ω)) μ := by
    let stoppedMk : Ω → ℝ := hstopped_hτ.mk (stoppedValue B τ)
    have hcomp_meas :
        Measurable[hτ.measurableSpace]
          (fun ω ↦ ∫ z, g z ∂κJ (stoppedMk ω)) := by
      exact hKernelIntegral_meas.comp hstopped_hτ.measurable_mk
    -- Proof comment: replace the stopped value by its `𝓕_τ`-measurable representative and then
    -- transport back along the almost-everywhere equality.
    refine hcomp_meas.aestronglyMeasurable.congr ?_
    exact (hstopped_hτ.ae_eq_mk.fun_comp fun z ↦ ∫ y, g y ∂κJ z).symm
  have hCondExp :
      (fun ω ↦ ∫ z, g z ∂κJ (stoppedValue B τ ω)) =ᵐ[μ]
        μ[fun ω ↦ g (futureRestricted ω) | hτ.measurableSpace] := by
    refine
      MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
        (fun s hs hμs ↦ ?_) (fun s hs hμs ↦ ?_) hKernelIntegral_hτ
    · -- Proof comment: every restricted-path kernel row is a probability measure, so the
      -- kernel-integral candidate inherits the same uniform bound `C` on each history slice.
      refine IntegrableOn.of_bound hμs
        (hKernelIntegral_ae.mono_measure Measure.restrict_le_self) C ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        have hgC :
            ∀ᵐ z ∂κJ (stoppedValue B τ ω), ‖g z‖ ≤ C :=
          Filter.Eventually.of_forall fun z ↦ by
            simpa [Real.norm_eq_abs] using hg_bound z
        simpa using
          (MeasureTheory.norm_integral_le_of_norm_le_const
            (μ := κJ (stoppedValue B τ ω)) hgC)
    · -- Proof comment: on every `𝓕_τ`-measurable slice, the left and right set integrals are
      -- both integrals of the same bounded `g` against the equal restricted laws supplied by
      -- `brownianRestrictedFutureLaw_eq_kernel_countableFactor`.
      let νs : Measure ((j : J) → ℝ) := (μ.restrict s).map futureRestricted
      let ρs : Measure ((j : J) → ℝ) := κJ ∘ₘ ((μ.restrict s).map (stoppedValue B τ))
      have hfutureRestricted_ae_s :
          AEMeasurable futureRestricted (μ.restrict s) :=
        hfutureRestricted_ae.mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      have hstopped_ae_s :
          AEMeasurable (stoppedValue B τ) (μ.restrict s) :=
        hstopped_ae.mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      have hlaw : νs = ρs := by
        calc
          νs =
              (((brownianTranslatedPathKernel P B) ∘ₘ
                ((μ.restrict s).map (stoppedValue B τ))).map J.restrict) := by
                  simpa [μ, futureRestricted, νs] using
                    (brownianRestrictedFutureLaw_eq_kernel_countableFactor
                      P B hB x τ hτ hτfinite hJ hs)
          _ = ρs := by
                simpa [κJ, ρs] using
                  (MeasureTheory.Measure.map_comp
                    ((μ.restrict s).map (stoppedValue B τ))
                    (brownianTranslatedPathKernel P B)
                    measurable_restrict_countable)
      haveI : IsFiniteMeasure νs := by
        dsimp [νs]
        infer_instance
      have hg_νs_int : Integrable g νs := by
        refine Integrable.of_bound hg.aestronglyMeasurable C ?_
        exact Filter.Eventually.of_forall fun z ↦ by
          simpa [Real.norm_eq_abs] using hg_bound z
      have hg_ρs_int : Integrable g ρs := by
        rw [← hlaw]
        exact hg_νs_int
      have hleft :
          ∫ ω in s, g (futureRestricted ω) ∂μ = ∫ y, g y ∂νs := by
        change ∫ ω, g (futureRestricted ω) ∂(μ.restrict s) = ∫ y, g y ∂νs
        rw [show νs = (μ.restrict s).map futureRestricted by rfl]
        exact
          (MeasureTheory.integral_map hfutureRestricted_ae_s
            hg.aestronglyMeasurable).symm
      have hright :
          ∫ y, g y ∂ρs = ∫ ω in s, ∫ z, g z ∂κJ (stoppedValue B τ ω) ∂μ := by
        let κ₀ : Kernel Unit ℝ :=
          Kernel.const Unit ((μ.restrict s).map (stoppedValue B τ))
        have hcomp : (κJ ∘ₖ κ₀) () = ρs := by
          simp [κ₀, ρs]
        calc
          ∫ y, g y ∂ρs = ∫ y, g y ∂((κJ ∘ₖ κ₀) ()) := by
            rw [← hcomp]
          _ = ∫ z, ∫ y, g y ∂κJ z ∂κ₀ () := by
                simpa using
                  (ProbabilityTheory.Kernel.integral_comp
                    (η := κJ) (κ := κ₀) (a := ()) hg_ρs_int)
          _ = ∫ z, ∫ y, g y ∂κJ z ∂((μ.restrict s).map (stoppedValue B τ)) := by
                simp [κ₀]
          _ = ∫ ω in s, ∫ z, g z ∂κJ (stoppedValue B τ ω) ∂μ := by
                simpa using
                  (MeasureTheory.integral_map hstopped_ae_s
                    hKernelIntegral_meas.aestronglyMeasurable)
      exact (hleft.trans (hlaw ▸ hright)).symm
  have hFuture_eq :
      (fun ω ↦ g (futureRestricted ω)) =
        fun ω ↦ f (futurePathAfterStoppingTime B τ ω) := by
    funext ω
    simpa [futureRestricted, Function.comp_def] using
      congrArg (fun h ↦ h (futurePathAfterStoppingTime B τ ω)) hfg.symm
  have hKernel_eq :
      (fun ω ↦ ∫ z, g z ∂κJ (stoppedValue B τ ω)) =
        fun ω ↦ ∫ y, f y ∂brownianTranslatedPathKernel P B (stoppedValue B τ ω) := by
    funext ω
    have hrow :
        κJ (stoppedValue B τ ω) =
          Measure.map J.restrict
            ((brownianTranslatedPathKernel P B) (stoppedValue B τ ω)) := by
      simpa [κJ] using
        (Kernel.map_apply
          (brownianTranslatedPathKernel P B) measurable_restrict_countable
          (stoppedValue B τ ω))
    calc
      ∫ z, g z ∂κJ (stoppedValue B τ ω)
          =
            ∫ z, g z ∂Measure.map J.restrict
              ((brownianTranslatedPathKernel P B) (stoppedValue B τ ω)) := by
                rw [hrow]
      _ = ∫ y, g (J.restrict y) ∂brownianTranslatedPathKernel P B (stoppedValue B τ ω) := by
            simpa using
              (MeasureTheory.integral_map_of_stronglyMeasurable
                (μ := brownianTranslatedPathKernel P B (stoppedValue B τ ω))
                (φ := J.restrict) measurable_restrict_countable
                hg.stronglyMeasurable)
      _ = ∫ y, f y ∂brownianTranslatedPathKernel P B (stoppedValue B τ ω) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun y ↦ by
              simpa [Function.comp_def] using congrArg (fun h ↦ h y) hfg.symm
  simpa [μ, hFuture_eq, hKernel_eq] using hCondExp.symm

/-- Helper for Theorem 21.18: exported alias for the labeled strong Markov theorem. -/
theorem brownianMotionFamily_hasStrongMarkovProperty
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ)
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x) :
    ∃ κ : Kernel ℝ (NNReal → ℝ), HasStrongMarkovProperty P B κ := by
  -- Proof comment: keep the established API name as a thin alias of the labeled theorem.
  simpa using brownianStrongMarkov_of_countableFactor P B hB
end ProbabilityTheory
