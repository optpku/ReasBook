/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_4

open Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

namespace BrownianItoIntegral

/-- Helper for Theorem 25.11: the canonical closure point attached to a globally square-integrable
predictable simple process. -/
noncomputable abbrev predictableSimpleProcessClosure
    {μ : Measure Ω} {ℱ : TimeFiltration}
    (H : MeasureTheory.PredictableSimpleProcess ℱ)
    (hH :
      MemLp (MeasureTheory.processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  ⟨((MeasureTheory.predictableSimpleProcessToL2 H hH :
        MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
      Lp ℝ 2 (MeasureTheory.processMeasure μ)),
    Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ)
      (MeasureTheory.predictableSimpleProcessToL2 H hH).2⟩

/-- Helper for Theorem 25.11: every closure point `H : \overline{\mathcal E}` is the limit of a
sequence of globally square-integrable predictable simple processes, repackaged in the canonical
closure owner from Definition 25.10. -/
theorem closurePoint_hasPredictableSimpleApproximation
    {μ : Measure Ω} {ℱ : TimeFiltration}
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ,
      ∃ hHs_mem :
        ∀ n,
          MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
            (MeasureTheory.processMeasure μ),
        Tendsto
          (fun n ↦
            (⟨((MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n) :
                  MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)),
              Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ)
                (MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n)).2⟩ :
              PredictableSimpleProcessL2Closure ℱ μ))
          atTop (nhds H) := by
  have hmem :
      ((H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) ∈
        closure
          (MeasureTheory.predictableSimpleProcessL2 ℱ μ :
            Set (Lp ℝ 2 (MeasureTheory.processMeasure μ))) := by
    -- Proof comment: unwrap the closure owner to the ambient `L²(μ ⊗ dt)` statement.
    exact H.2
  rcases (mem_closure_iff_seq_limit.mp hmem) with ⟨fs, hfs_mem, hfs_tendsto⟩
  let Fs : ℕ → MeasureTheory.predictableSimpleProcessL2 ℱ μ := fun n ↦ ⟨fs n, hfs_mem n⟩
  choose Hs hHs_mem hHs_repr using fun n ↦ (Fs n).2
  let HsClosure : ℕ → PredictableSimpleProcessL2Closure ℱ μ := fun n ↦
    ⟨((MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n) :
          MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
        Lp ℝ 2 (MeasureTheory.processMeasure μ)),
      Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ)
        (MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n)).2⟩
  refine ⟨Hs, hHs_mem, ?_⟩
  -- Proof comment: rewrite the ambient approximants back into canonical closure points coming
  -- from honest predictable simple processes.
  have hHsClosure_tendsto : Tendsto HsClosure atTop (nhds H) := by
    refine tendsto_subtype_rng.2 ?_
    convert hfs_tendsto using 1
    funext n
    apply Subtype.ext
    simpa [HsClosure, Fs] using (hHs_repr n).symm
  simpa [HsClosure]
    using hHsClosure_tendsto

-- Semantic recall note: `lean_leansearch` only surfaced generic martingale/continuous-process
-- APIs, so the source-facing modification owner below stays project-local around Definition 25.10.

/- Analogue note: Chapter 21 continuous-version owners such as `brownianContinuousVersion` use a
named process together with companion specification theorems. The source-facing owner below follows
that pattern: the existence theorem stays as a helper, while `continuousModification` names the
process `I^W(H)` directly from the Brownian hypotheses and `H`. -/
/-- Helper for Theorem 25.11: a process `IwH` is a source-facing realization of the continuous
modification `I^W(H)` if it has almost surely continuous paths and is a modification of the
concrete Definition 25.10 truncation process `brownianItoIntegralTruncatedProcess W H`. -/
@[mk_iff isContinuousModification_iff]
class IsContinuousModification
    {μ : Measure Ω} {ℱ : TimeFiltration} (W : Process)
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (IwH : Process) : Prop where
  continuous_paths : HasAlmostSurelyContinuousPaths μ IwH
  modifies_truncated : AreModifications μ IwH (brownianItoIntegralTruncatedProcess W H)

/-- Helper for Theorem 25.11: `IsContinuousModification hIto H IwH` is a proposition. -/
instance instSubsingletonIsContinuousModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (IwH : Process) :
    Subsingleton (IsContinuousModification W H IwH) := by
  infer_instance

/-- Companion API for Theorem 25.11: any `IsContinuousModification` witness has almost surely
continuous paths and is a modification of the concrete process `brownianItoIntegralTruncatedProcess
W H`. -/
theorem isContinuousModification_spec
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    {H : PredictableSimpleProcessL2Closure ℱ μ}
    {IwH : Process}
    (hIwH : IsContinuousModification W H IwH) :
    HasAlmostSurelyContinuousPaths μ IwH ∧
      AreModifications μ IwH (brownianItoIntegralTruncatedProcess W H) := by
  -- Proof comment: unpack the two fields recorded in the source-facing owner.
  exact ⟨hIwH.continuous_paths, hIwH.modifies_truncated⟩

/-- Helper for Theorem 25.11: on a genuinely predictable simple input, the closure-side terminal
Brownian Itô map agrees with the public Theorem 25.4 linear-isometry value. -/
theorem simpleClosure_terminal_eq_publicLinearIsometry
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : MeasureTheory.PredictableSimpleProcess ℱ)
    (hH :
      MemLp (MeasureTheory.processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
    hIto.toContinuousLinearMap (predictableSimpleProcessClosure H hH) =
      ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry
        ℱ hBrownian hAdapted hIndependentIncrements
        (MeasureTheory.predictableSimpleProcessToL2 H hH) := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  have hL2Eq :
      (MeasureTheory.predictableSimpleProcessToL2 H hH :
        MeasureTheory.predictableSimpleProcessL2 ℱ μ) =
      MeasureTheory.predictableSimpleProcessToL2 H
        (ProbabilityTheory.predictableSimpleProcess_memLp H) := by
    apply Subtype.ext
    -- Proof comment: both `MemLp` witnesses produce the same ambient `L²` class of `H`.
    exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hH
      (ProbabilityTheory.predictableSimpleProcess_memLp H)).2 <|
      Filter.EventuallyEq.of_eq rfl
  have hItoAe :
      ((hIto.toContinuousLinearMap (predictableSimpleProcessClosure H hH) :
          Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegralAtInfinity W H :=
    hIto.ae_eq_brownianElementaryIntegralAtInfinity H hH
  have hPublicAe :
      ((ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry
          ℱ hBrownian hAdapted hIndependentIncrements
          (MeasureTheory.predictableSimpleProcessToL2 H hH) : Lp ℝ 2 μ) :
        Ω → ℝ) =ᵐ[μ]
          MeasureTheory.brownianElementaryIntegralAtInfinity W H := by
    -- Proof comment: rewrite the domain point to the canonical witness used by the public API.
    rw [hL2Eq]
    exact ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry_ae_eq
      hBrownian hAdapted hIndependentIncrements H
  apply Lp.ext
  -- Proof comment: both `Lp` classes have the same almost-everywhere representative.
  filter_upwards [hItoAe, hPublicAe] with ω hωIto hωPublic
  exact hωIto.trans hωPublic.symm

/-- Helper for Theorem 25.11: the square of the `L²` norm of a real-valued `MemLp` function is
its raw second moment. -/
theorem toLpNormSq_eq_integral_sq_local
    {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂P := by
  have hELpNorm :
      eLpNorm f 2 P = ENNReal.ofReal (Real.sqrt (∫ x, (f x) ^ 2 ∂P)) := by
    -- Proof comment: at exponent `2`, the `L²` seminorm is the square root of the second moment.
    simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
      (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hf)
  have hNorm :
      ‖hf.toLp f‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂P) := by
    -- Proof comment: rewrite the norm of the `Lp` class through the explicit `L²` seminorm.
    rw [Lp.norm_toLp, hELpNorm, ENNReal.toReal_ofReal]
    positivity
  calc
    ‖hf.toLp f‖ ^ 2 = (Real.sqrt (∫ x, (f x) ^ 2 ∂P)) ^ 2 := by
      rw [hNorm]
    _ = ∫ x, (f x) ^ 2 ∂P := by
      rw [Real.sq_sqrt]
      positivity

/-- Companion API for Theorem 25.11 (1): the same source-side `L²`-isometry can be exposed as the
ambient norm identity on the closure owner `PredictableSimpleProcessL2Closure`. -/
theorem norm_eq
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ‖hIto.toContinuousLinearMap H‖ = ‖H‖ := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  rcases closurePoint_hasPredictableSimpleApproximation H with ⟨Hs, hHs_mem, hHs_tendsto⟩
  let HsClosure : ℕ → PredictableSimpleProcessL2Closure ℱ μ := fun n ↦
    predictableSimpleProcessClosure (Hs n) (hHs_mem n)
  have hHsClosure_tendsto : Tendsto HsClosure atTop (nhds H) := by
    -- Proof comment: the approximation theorem already returns these canonical closure points.
    simpa [HsClosure, predictableSimpleProcessClosure] using hHs_tendsto
  have hSimpleNorm :
      ∀ n, ‖hIto.toContinuousLinearMap (HsClosure n)‖ = ‖HsClosure n‖ := by
    intro n
    have hTerminalEq :
        hIto.toContinuousLinearMap (HsClosure n) =
          ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry
            ℱ hBrownian hAdapted hIndependentIncrements
            (MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n)) :=
      simpleClosure_terminal_eq_publicLinearIsometry
        hBrownian hAdapted hIndependentIncrements (Hs n) (hHs_mem n)
    -- Proof comment: the public Theorem 25.4 owner is an isometry on the simple approximants.
    calc
      ‖hIto.toContinuousLinearMap (HsClosure n)‖ =
          ‖ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry
              ℱ hBrownian hAdapted hIndependentIncrements
              (MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n))‖ := by
            rw [hTerminalEq]
      _ = ‖MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n)‖ := by
            simpa using
              (ProbabilityTheory.brownianElementaryIntegralAtInfinityLinearIsometry
                ℱ hBrownian hAdapted hIndependentIncrements).norm_map
                (MeasureTheory.predictableSimpleProcessToL2 (Hs n) (hHs_mem n))
      _ = ‖HsClosure n‖ := rfl
  have hLeft :
      Tendsto (fun n ↦ ‖hIto.toContinuousLinearMap (HsClosure n)‖) atTop
        (nhds ‖hIto.toContinuousLinearMap H‖) := by
    let T := hIto.toContinuousLinearMap
    have hMap :
        Tendsto (fun n ↦ T (HsClosure n)) atTop (nhds (T H)) :=
      (T.continuous.tendsto H).comp hHsClosure_tendsto
    simpa [T] using (continuous_norm.tendsto _).comp hMap
  have hRight :
      Tendsto (fun n ↦ ‖HsClosure n‖) atTop (nhds ‖H‖) :=
    (continuous_norm.tendsto _).comp hHsClosure_tendsto
  have hSimpleNormEq :
      (fun n ↦ ‖hIto.toContinuousLinearMap (HsClosure n)‖) =
        fun n ↦ ‖HsClosure n‖ := by
    funext n
    exact hSimpleNorm n
  have hSimpleNormRight :
      Tendsto (fun n ↦ ‖hIto.toContinuousLinearMap (HsClosure n)‖) atTop (nhds ‖H‖) := by
    rw [hSimpleNormEq]
    exact hRight
  -- Proof comment: the norm equality holds on a dense simple sequence, so continuity identifies
  -- the two limits.
  exact tendsto_nhds_unique hLeft hSimpleNormRight

/-- Companion API for Theorem 25.11 (1): for the concrete Definition 25.10 terminal map
`I^W_∞`, linearity is
carried by the `ContinuousLinearMap` owner `hIto.toContinuousLinearMap`, and the source-facing
second-moment identity is the equality between the terminal `L²(μ)` square integral and the
ambient `L²(μ ⊗ dt)` square integral of `H`. In this project, `IsBrownianMotion μ W` only
remembers the law-side Brownian data, so the filtration-relative Brownian hypothesis is expressed
by adding adaptation and the explicit increment-independence premise. -/
theorem sq_integral_eq
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∫ ω, ((((hIto.toContinuousLinearMap H : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 2) ∂μ =
      ∫ x,
        ((((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x) ^ 2) ∂
          (MeasureTheory.processMeasure μ) := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  let hTerminalMem :
      MemLp (((hIto.toContinuousLinearMap H : Lp ℝ 2 μ) : Ω → ℝ)) 2 μ :=
    MeasureTheory.Lp.memLp (hIto.toContinuousLinearMap H)
  let hProcessMem :
      MemLp
        ((((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ))) 2
        (MeasureTheory.processMeasure μ) :=
    MeasureTheory.Lp.memLp (H : Lp ℝ 2 (MeasureTheory.processMeasure μ))
  have hTerminalToLp :
      hTerminalMem.toLp (((hIto.toContinuousLinearMap H : Lp ℝ 2 μ) : Ω → ℝ)) =
        hIto.toContinuousLinearMap H := by
    -- Proof comment: converting the chosen representative of an `Lp` class back into `Lp`
    -- recovers the original terminal Brownian-Itô class.
    apply Lp.ext
    exact MeasureTheory.MemLp.coeFn_toLp hTerminalMem
  have hProcessToLp :
      hProcessMem.toLp
          (((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =
        (H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) := by
    -- Proof comment: the same representative-recovery statement holds for the ambient
    -- `L²(μ ⊗ dt)` class of `H`.
    apply Lp.ext
    exact MeasureTheory.MemLp.coeFn_toLp hProcessMem
  have hNormSq :
      ‖hIto.toContinuousLinearMap H‖ ^ 2 = ‖H‖ ^ 2 := by
    -- Proof comment: square the already-proved norm isometry from part (i).
    exact congrArg (fun r : ℝ ↦ r ^ 2)
      (norm_eq hBrownian hAdapted hIndependentIncrements H)
  calc
    ∫ ω, ((((hIto.toContinuousLinearMap H : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 2) ∂μ =
        ‖hTerminalMem.toLp
            (((hIto.toContinuousLinearMap H : Lp ℝ 2 μ) : Ω → ℝ))‖ ^ 2 := by
          symm
          exact toLpNormSq_eq_integral_sq_local hTerminalMem
    _ = ‖hIto.toContinuousLinearMap H‖ ^ 2 := by
          rw [hTerminalToLp]
    _ = ‖H‖ ^ 2 := hNormSq
    _ = ‖((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)))‖ ^ 2 := by
          rfl
    _ = ‖hProcessMem.toLp
            (((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ))‖ ^ 2 := by
          rw [hProcessToLp]
    _ =
        ∫ x,
          ((((H : Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x) ^ 2) ∂
            (MeasureTheory.processMeasure μ) := by
          exact toLpNormSq_eq_integral_sq_local hProcessMem

/-- Helper for Theorem 25.11: deterministic-time stopping agrees pointwise with the cutoff normal
form `if s ≤ t then H s ω else 0`. -/
def cutoffBeforeDeterministicTime_local
    (t : NNReal) (H : Process) : Process :=
  fun s ω ↦ if s ≤ t then H s ω else 0

omit mΩ in
/-- Helper for Theorem 25.11: realizing the deterministic cutoff on `Ω × ℝ` is exactly the
ambient indicator cutoff used by `PredictableSimpleProcessL2Closure.cutoffBefore`. -/
theorem processToTimeSpaceFun_cutoffBeforeDeterministicTime_local
    (t : NNReal) (H : Process) :
    MeasureTheory.processToTimeSpaceFun (cutoffBeforeDeterministicTime_local t H) =
      Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
        (MeasureTheory.processToTimeSpaceFun H) := by
  -- Proof comment: unfolding the time-space realization shows the same deterministic strip cutoff
  -- on `Ω × ℝ`.
  funext x
  by_cases hx : x.2 ≤ (t : ℝ)
  · have hx' : x.2.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hx
    rw [Set.indicator_of_mem (by simpa using hx)]
    simp [Function.uncurry, MeasureTheory.processToTimeSpaceFun,
      cutoffBeforeDeterministicTime_local, hx']
  · have hx' : ¬ x.2.toNNReal ≤ t := by
      intro hx'
      exact hx (Real.toNNReal_le_iff_le_coe.1 hx')
    rw [Set.indicator_of_notMem (by simpa using hx)]
    simp [Function.uncurry, MeasureTheory.processToTimeSpaceFun,
      cutoffBeforeDeterministicTime_local, hx']

omit mΩ in
/-- Helper for Theorem 25.11: the deterministic stopping-time truncation is exactly the cutoff
normal form used in the simple-process bridge. -/
theorem processBeforeStoppingTime_eq_cutoffBeforeDeterministicTime_local
    (H : Process) (t : NNReal) :
    processBeforeStoppingTime H (fun _ ↦ (t : ENNReal)) =
      cutoffBeforeDeterministicTime_local t H := by
  -- Proof comment: for a constant stopping time, `stoppedValue` is just evaluation on the branch
  -- `s ≤ t` and vanishes otherwise.
  funext s ω
  by_cases hs : (s : ENNReal) ≤ (t : ENNReal)
  · have hs' : s ≤ t := by
      exact_mod_cast hs
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, cutoffBeforeDeterministicTime_local,
      hs, hs']
  · have hs' : ¬ s ≤ t := by
      intro hst
      exact hs (by exact_mod_cast hst)
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, cutoffBeforeDeterministicTime_local,
      hs, hs']

/-- Helper for Theorem 25.11: a point of a finite ordered subset of `NNReal` cannot lie strictly
between consecutive points of its `orderEmbOfFin` enumeration. -/
theorem not_mem_Ioo_between_orderEmbOfFin_consecutive_local
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) (i : Fin n) {x : NNReal} (hx : x ∈ B) :
    x ∉ Set.Ioo (B.orderEmbOfFin hB i.castSucc) (B.orderEmbOfFin hB i.succ) := by
  -- Proof comment: reindex `x` in the ordered enumeration and compare the resulting indices.
  intro hxIoo
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change (((B.orderIsoOfFin hB) j : B) : NNReal) = x
    simp [j]
  have hij_left : i.castSucc < j := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.1)
  have hij_right : j < i.succ := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.2)
  have hij_left' : i.1 < j.1 := by
    simpa using hij_left
  have hij_right' : j.1 < i.1 + 1 := by
    exact hij_right
  exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt hij_left')) hij_right'

/-- Helper for Theorem 25.11: every point of a finite ordered subset of `NNReal` is bounded above
by the final point of its ordered enumeration. -/
theorem le_orderEmbOfFin_last_of_mem_local
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) {x : NNReal} (hx : x ∈ B) :
    x ≤ B.orderEmbOfFin hB (Fin.last n) := by
  -- Proof comment: reindex `x` in the ordered enumeration and compare it with the last index.
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change (((B.orderIsoOfFin hB) j : B) : NNReal) = x
    simp [j]
  exact hjx ▸ (B.orderEmbOfFin hB).monotone (Fin.le_last j)

/-- Helper for Theorem 25.11: once a refined predictable-step partition is fixed, truncating the
coefficients after `t` realizes the deterministic cutoff process. -/
theorem exists_cutoffRepresentation_of_refinedPartition_local
    {ℱ : TimeFiltration}
    (representation : MeasureTheory.PredictableStepRepresentation ℱ)
    {nRef : ℕ}
    (times : Fin (nRef + 1) → NNReal)
    (hTimesZero : times 0 = 0)
    (hTimesStrictMono : StrictMono times)
    (coeff : Fin nRef → Ω → ℝ)
    (hCoeffMeasurable : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeff i))
    (hCoeffBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C)
    (hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        representation.toProcess s = coeff i)
    (hEndpointMem :
      ∀ j : Fin (representation.n + 1), ∃ k : Fin (nRef + 1), times k = representation.times j)
    (t : NNReal)
    (hLastGeT : t ≤ times (Fin.last nRef))
    (hLeftOfCutoff : ∀ i : Fin nRef, ¬ times i.succ ≤ t → t ≤ times i.castSucc) :
    ∃ cutoff : MeasureTheory.PredictableStepRepresentation ℱ,
      cutoff.toProcess = cutoffBeforeDeterministicTime_local t representation.toProcess ∧
        ∀ W : Process,
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
              representation W t =
            MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
              cutoff W := by
  let coeffCut : Fin nRef → Ω → ℝ := fun i ω ↦ if times i.succ ≤ t then coeff i ω else 0
  have hCoeffCutMeasurable :
      ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffCut i) := by
    intro i
    by_cases hi : times i.succ ≤ t
    · simp [coeffCut, hi, hCoeffMeasurable i]
    · simp [coeffCut, hi]
  have hCoeffCutBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffCut i ω| ≤ C := by
    intro i
    by_cases hi : times i.succ ≤ t
    · rcases hCoeffBounded i with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro ω
      simpa [coeffCut, hi] using hC ω
    · refine ⟨0, ?_⟩
      intro ω
      simp [coeffCut, hi]
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    { n := nRef
      times := times
      coeff := coeffCut
      times_zero := hTimesZero
      times_strictMono := hTimesStrictMono
      coeff_bounded := hCoeffCutBounded
      coeff_measurable := hCoeffCutMeasurable }
  refine ⟨cutoff, ?_, ?_⟩
  · -- Proof comment: compare the explicit cutoff representation interval-by-interval with the
    -- pointwise formula `if s ≤ t then H s ω else 0`.
    funext s ω
    by_cases hAfter : times (Fin.last nRef) < s
    · have hCutZero : cutoff.toProcess s ω = 0 := by
        exact cutoff.toProcess_eq_zero_of_last_lt hAfter ω
      have hsNotLe : ¬ s ≤ t := by
        exact not_le_of_gt (lt_of_le_of_lt hLastGeT hAfter)
      simp [cutoffBeforeDeterministicTime_local, hCutZero, hsNotLe]
    · by_cases hs0 : s = 0
      · subst hs0
        simp [MeasureTheory.PredictableStepRepresentation.toProcess_apply,
          cutoffBeforeDeterministicTime_local]
      · have hsPos : 0 < s := by
          exact lt_of_le_of_ne bot_le (by simpa [eq_comm] using hs0)
        have hsLast : s ≤ times (Fin.last nRef) := le_of_not_gt hAfter
        obtain ⟨i, hsi⟩ := cutoff.exists_mem_interval_of_pos_le_last hsPos hsLast
        have hCutCoeff : cutoff.toProcess s ω = coeffCut i ω := by
          exact cutoff.toProcess_eq_coeff_of_mem_interval i hsi ω
        by_cases hi : times i.succ ≤ t
        · have hsLeT : s ≤ t := le_trans hsi.2 hi
          have hRepCoeff : representation.toProcess s ω = coeff i ω := by
            exact congrFun (hCoeffEq i hsi) ω
          simp [cutoffBeforeDeterministicTime_local, hCutCoeff, coeffCut, hi, hsLeT, hRepCoeff]
        · have hsNotLe : ¬ s ≤ t := by
            exact not_le_of_gt (lt_of_le_of_lt (hLeftOfCutoff i hi) hsi.1)
          simp [cutoffBeforeDeterministicTime_local, hCutCoeff, coeffCut, hi, hsNotLe]
  · intro W
    have hLastLe :
        representation.times (Fin.last representation.n) ≤ times (Fin.last nRef) := by
      rcases hEndpointMem (Fin.last representation.n) with ⟨k, hk⟩
      calc
        representation.times (Fin.last representation.n) = times k := hk.symm
        _ ≤ times (Fin.last nRef) := hTimesStrictMono.monotone (Fin.le_last k)
    have hRefined :
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral representation W =
          fun s ω ↦
            ∑ i : Fin nRef,
              coeff i ω *
                (W (min (times i.succ) s) ω - W (min (times i.castSucc) s) ω) := by
      -- Proof comment: rewrite the stopped integral of the original representation on the refined
      -- deterministic partition built for the cutoff process.
      exact
        MeasureTheory.brownianElementaryIntegral_eq_commonRefinementSum
          W representation times hTimesStrictMono coeff hCoeffEq hEndpointMem hLastLe
    funext ω
    calc
      MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral representation W t ω =
          ∑ i : Fin nRef,
            coeff i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := by
                simpa using congrFun (congrFun hRefined t) ω
      _ =
          ∑ i : Fin nRef,
            coeffCut i ω * (W (times i.succ) ω - W (times i.castSucc) ω) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              by_cases hi : times i.succ ≤ t
              · have hCastSuccLe : times i.castSucc ≤ t := by
                  exact le_trans (le_of_lt (hTimesStrictMono i.castSucc_lt_succ)) hi
                simp [coeffCut, hi, min_eq_left hCastSuccLe]
              · have hCastSuccGe : t ≤ times i.castSucc := hLeftOfCutoff i hi
                have hSuccGe : t ≤ times i.succ := by
                  exact hCastSuccGe.trans (le_of_lt (hTimesStrictMono i.castSucc_lt_succ))
                simp [coeffCut, hi, min_eq_right hSuccGe, min_eq_right hCastSuccGe]
      _ =
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
            cutoff W ω := by
              rw [PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply]
              rfl

/-- Helper for Theorem 25.11: inserting a deterministic time `t` into a predictable-step
partition yields a predictable-step representation of the cutoff process `H · 1_[0,t]`. -/
theorem exists_predictableStepRepresentation_cutoffBefore_local
    {ℱ : TimeFiltration}
    (representation : MeasureTheory.PredictableStepRepresentation ℱ)
    (t : NNReal) :
    ∃ cutoff : MeasureTheory.PredictableStepRepresentation ℱ,
      cutoff.toProcess = cutoffBeforeDeterministicTime_local t representation.toProcess ∧
        ∀ W : Process,
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
              representation W t =
            MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
              cutoff W := by
  let B : Finset NNReal := insert t (Finset.image representation.times Finset.univ)
  have hBt : t ∈ B := Finset.mem_insert_self t _
  have hB0 : (0 : NNReal) ∈ B := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨0, Finset.mem_univ _, representation.times_zero⟩)
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hB0⟩
  let nRef : ℕ := B.card - 1
  have hBcard : B.card = nRef + 1 := by
    have hcard : B.card = (B.card - 1) + 1 := by
      omega
    simpa [nRef] using hcard
  let times : Fin (nRef + 1) → NNReal := B.orderEmbOfFin hBcard
  have hTimesZero : times 0 = 0 := by
    have hBnonempty : B.Nonempty := Finset.card_pos.mp hBpos
    have hBmin : B.min' hBnonempty = 0 := by
      refine (Finset.min'_eq_iff B hBnonempty 0).2 ?_
      constructor
      · exact hB0
      · intro b hb
        exact bot_le
    calc
      times 0 = B.min' hBnonempty := by
        have hBcardPos : 0 < nRef + 1 := by
          simpa [hBcard] using hBpos
        have hzero := Finset.orderEmbOfFin_zero hBcard hBcardPos
        simpa [times] using hzero
      _ = 0 := hBmin
  have hTimesStrictMono : StrictMono times := (B.orderEmbOfFin hBcard).strictMono
  have hStrip :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
            representation.toProcess s = g := by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin representation.n,
          representation.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      exact
        not_mem_Ioo_between_orderEmbOfFin_consecutive_local B hBcard i
          (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩))
    -- Proof comment: each refined strip avoids the original partition boundary, so the process is
    -- constant there with a bounded measurable coefficient.
    exact representation.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  let coeff : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStrip i)
  have hCoeffMeasurable : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeff i) := by
    intro i
    exact (Classical.choose_spec (hStrip i)).1
  have hCoeffBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStrip i)).2.1
  have hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        representation.toProcess s = coeff i := by
    intro i s hs
    exact (Classical.choose_spec (hStrip i)).2.2 hs
  have hEndpointMem :
      ∀ j : Fin (representation.n + 1), ∃ k : Fin (nRef + 1), times k = representation.times j := by
    intro j
    have hj_mem : representation.times j ∈ B := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
    refine ⟨(B.orderIsoOfFin hBcard).symm ⟨representation.times j, hj_mem⟩, ?_⟩
    change (((B.orderIsoOfFin hBcard)
      ((B.orderIsoOfFin hBcard).symm ⟨representation.times j, hj_mem⟩) : B) : NNReal) =
      representation.times j
    simp
  have hLastGeT : t ≤ times (Fin.last nRef) := by
    exact le_orderEmbOfFin_last_of_mem_local B hBcard hBt
  have hLeftOfCutoff : ∀ i : Fin nRef, ¬ times i.succ ≤ t → t ≤ times i.castSucc := by
    intro i hi
    have hNotMem :=
      not_mem_Ioo_between_orderEmbOfFin_consecutive_local B hBcard i hBt
    have htLtRight : t < times i.succ := lt_of_not_ge hi
    exact le_of_not_gt fun htLeftLt ↦ hNotMem ⟨htLeftLt, htLtRight⟩
  exact
    exists_cutoffRepresentation_of_refinedPartition_local representation times hTimesZero
      hTimesStrictMono coeff hCoeffMeasurable hCoeffBounded hCoeffEq hEndpointMem t hLastGeT
      hLeftOfCutoff

/-- Helper for Theorem 25.11: a predictable simple process admits a predictable simple
deterministic-time cutoff with the expected process formula `H · 1_[0,t]`. -/
noncomputable def predictableSimpleProcessCutoffBefore_local
    {ℱ : TimeFiltration} (K : MeasureTheory.PredictableSimpleProcess ℱ) (t : NNReal) :
    MeasureTheory.PredictableSimpleProcess ℱ :=
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore_local representation t)
  cutoff.toPredictableSimpleProcess

/-- Helper for Theorem 25.11: the cutoff simple process realizes the deterministic-time cutoff of
the original predictable simple stage. -/
theorem predictableSimpleProcessCutoffBefore_coe_local
    {ℱ : TimeFiltration} (K : MeasureTheory.PredictableSimpleProcess ℱ) (t : NNReal) :
    ((predictableSimpleProcessCutoffBefore_local K t : MeasureTheory.PredictableSimpleProcess ℱ) :
      Process) = cutoffBeforeDeterministicTime_local t (K : Process) := by
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore_local representation t)
  have hRepresentation :
      (K : Process) = representation.toProcess :=
    Classical.choose_spec (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  have hCutoff :
      cutoff.toProcess = cutoffBeforeDeterministicTime_local t representation.toProcess :=
    (Classical.choose_spec
      (exists_predictableStepRepresentation_cutoffBefore_local representation t)).1
  -- Proof comment: compare both sides through the chosen predictable-step representation of `K`.
  change cutoff.toProcess = cutoffBeforeDeterministicTime_local t (K : Process)
  simpa [hRepresentation] using hCutoff

/-- Helper for Theorem 25.11: the chosen deterministic cutoff representation computes the
fixed-time stopped Brownian elementary integral of the original predictable-step representation.
-/
theorem predictableStepRepresentation_brownianElementaryIntegral_eq_cutoffAtInfinity_local
    {ℱ : TimeFiltration}
    (representation : MeasureTheory.PredictableStepRepresentation ℱ)
    (W : Process) (t : NNReal) :
    let cutoff :
        MeasureTheory.PredictableStepRepresentation ℱ :=
      Classical.choose (exists_predictableStepRepresentation_cutoffBefore_local representation t)
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
        representation W t =
      MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
        cutoff W := by
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore_local representation t)
  -- Proof comment: the strengthened cutoff-existence theorem stores the exact fixed-time integral
  -- identity for the chosen deterministic cutoff representation.
  exact
    (Classical.choose_spec
      (exists_predictableStepRepresentation_cutoffBefore_local representation t)).2 W

/-- Helper for Theorem 25.11: on a predictable simple stage, the stopped Brownian elementary
integral at time `t` is exactly the terminal Brownian integral of the deterministic cutoff stage.
-/
theorem brownianElementaryIntegral_predictableSimple_eq_cutoffTerminal_local
    {ℱ : TimeFiltration} {W : Process}
    (K : MeasureTheory.PredictableSimpleProcess ℱ) (t : NNReal) :
    MeasureTheory.brownianElementaryIntegral W K t =
      MeasureTheory.brownianElementaryIntegralAtInfinity W
        (predictableSimpleProcessCutoffBefore_local K t) := by
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore_local representation t)
  have hRepresentation :
      (K : Process) = representation.toProcess :=
    Classical.choose_spec (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  -- Proof comment: normalize both source-facing integrals to the chosen predictable-step
  -- representations and invoke the fixed-time cutoff identity.
  calc
    MeasureTheory.brownianElementaryIntegral W K t =
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
          representation W t := by
            simpa using
              congrFun
                (MeasureTheory.brownianElementaryIntegral_spec W K hRepresentation) t
    _ =
        MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
          cutoff W := by
            simpa [cutoff] using
              predictableStepRepresentation_brownianElementaryIntegral_eq_cutoffAtInfinity_local
                representation W t
    _ =
        MeasureTheory.brownianElementaryIntegralAtInfinity W cutoff.toPredictableSimpleProcess := by
            symm
            simpa using
              MeasureTheory.brownianElementaryIntegralAtInfinity_toPredictableSimpleProcess
                W cutoff
    _ =
        MeasureTheory.brownianElementaryIntegralAtInfinity W
          (predictableSimpleProcessCutoffBefore_local K t) := by
            rfl

/-- Helper for Theorem 25.11: cutting off a canonical simple closure point before `t` agrees with
the canonical closure point of the cutoff simple process. -/
theorem cutoffBefore_predictableSimpleClosure_eq_local
    {μ : Measure Ω} {ℱ : TimeFiltration}
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (t : NNReal) :
    let Kcut := predictableSimpleProcessCutoffBefore_local K t
    let hCutMem :
        MemLp
          (MeasureTheory.processToTimeSpaceFun
            (cutoffBeforeDeterministicTime_local t (K : Process)))
          (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
      (memLp_congr_ae
        (Filter.EventuallyEq.of_eq
          (processToTimeSpaceFun_cutoffBeforeDeterministicTime_local t (K : Process)).symm)).mp <|
        MeasureTheory.MemLp.indicator
          (show MeasurableSet ({x : Ω × ℝ | x.2 ≤ (t : ℝ)}) from
            measurableSet_le measurable_snd measurable_const)
          hK
    let hKcut :
        MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : Process)) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ) :=
      (memLp_congr_ae (Filter.EventuallyEq.of_eq <| by
        simpa [Kcut] using
          congrArg MeasureTheory.processToTimeSpaceFun
            (predictableSimpleProcessCutoffBefore_coe_local K t).symm)).mp hCutMem
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
        (predictableSimpleProcessClosure K hK) =
      predictableSimpleProcessClosure Kcut hKcut := by
  let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
    predictableSimpleProcessCutoffBefore_local K t
  let hCutMem :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (cutoffBeforeDeterministicTime_local t (K : Process)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae
      (Filter.EventuallyEq.of_eq
        (processToTimeSpaceFun_cutoffBeforeDeterministicTime_local t (K : Process)).symm)).mp <|
      MeasureTheory.MemLp.indicator
        (show MeasurableSet ({x : Ω × ℝ | x.2 ≤ (t : ℝ)}) from
          measurableSet_le measurable_snd measurable_const)
        hK
  let hKcut :
      MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : Process))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae (Filter.EventuallyEq.of_eq <| by
      simpa [Kcut] using
        congrArg MeasureTheory.processToTimeSpaceFun
          (predictableSimpleProcessCutoffBefore_coe_local K t).symm)).mp hCutMem
  have hCoeK :
      ((((predictableSimpleProcessClosure K hK :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun (K : Process) := by
    simpa [predictableSimpleProcessClosure] using (MeasureTheory.MemLp.coeFn_toLp hK)
  have hIndicatorToCutoff :
      Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
          (fun x ↦
            ((((predictableSimpleProcessClosure K hK :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x)) =ᵐ[
            MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun
          (cutoffBeforeDeterministicTime_local t (K : Process)) := by
    have hIndicatorLift :
        Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
            (fun x ↦
              ((((predictableSimpleProcessClosure K hK :
                    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                  Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x)) =ᵐ[
              MeasureTheory.processMeasure μ]
          Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
            (MeasureTheory.processToTimeSpaceFun (K : Process)) := by
      filter_upwards [hCoeK] with x hx
      by_cases hxt : x.2 ≤ (t : ℝ)
      · simpa [Set.indicator_of_mem, hxt] using hx
      · simp [Set.indicator_of_notMem, hxt]
    exact hIndicatorLift.trans <|
      Filter.EventuallyEq.of_eq
        (processToTimeSpaceFun_cutoffBeforeDeterministicTime_local t (K : Process)).symm
  have hCutoffToKcut :
      MeasureTheory.processToTimeSpaceFun
          (cutoffBeforeDeterministicTime_local t (K : Process)) =ᵐ[
            MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun (Kcut : Process) := by
    exact Filter.EventuallyEq.of_eq <| by
      simpa [Kcut] using
        congrArg MeasureTheory.processToTimeSpaceFun
          (predictableSimpleProcessCutoffBefore_coe_local K t).symm
  have hCoeKcut :
      ((((predictableSimpleProcessClosure Kcut hKcut :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun (Kcut : Process) := by
    simpa [predictableSimpleProcessClosure] using (MeasureTheory.MemLp.coeFn_toLp hKcut)
  apply Subtype.ext
  rw [Lp.ext_iff]
  exact
    ((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn
      t (predictableSimpleProcessClosure K hK)).trans hIndicatorToCutoff).trans <|
      hCutoffToKcut.trans hCoeKcut.symm

/-- Helper for Theorem 25.11: on a predictable simple input, the canonical truncated Brownian-Itô
slice agrees almost surely with the terminal Brownian integral of the deterministic cutoff stage.
-/
theorem brownianItoIntegralTruncatedProcess_predictableSimple_ae_eq_cutoffTerminal_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (t : NNReal) :
    brownianItoIntegralTruncatedProcess W (predictableSimpleProcessClosure K hK) t =ᵐ[μ]
      MeasureTheory.brownianElementaryIntegralAtInfinity W
        (predictableSimpleProcessCutoffBefore_local K t) := by
  let hIto : BrownianItoIntegral μ ℱ W := inferInstance
  let Kcut : MeasureTheory.PredictableSimpleProcess ℱ :=
    predictableSimpleProcessCutoffBefore_local K t
  let hCutMem :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (cutoffBeforeDeterministicTime_local t (K : Process)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae
      (Filter.EventuallyEq.of_eq
        (processToTimeSpaceFun_cutoffBeforeDeterministicTime_local t (K : Process)).symm)).mp <|
      MeasureTheory.MemLp.indicator
        (show MeasurableSet ({x : Ω × ℝ | x.2 ≤ (t : ℝ)}) from
          measurableSet_le measurable_snd measurable_const)
        hK
  let hKcut :
      MemLp (MeasureTheory.processToTimeSpaceFun (Kcut : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae (Filter.EventuallyEq.of_eq <| by
      simpa [Kcut] using
        congrArg MeasureTheory.processToTimeSpaceFun
          (predictableSimpleProcessCutoffBefore_coe_local K t).symm)).mp hCutMem
  have hClosure :
      MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
          (predictableSimpleProcessClosure K hK) =
        predictableSimpleProcessClosure Kcut
          hKcut := by
    -- Proof comment: normalize the closure-side cutoff to the canonical simple cutoff object.
    simpa [Kcut] using cutoffBefore_predictableSimpleClosure_eq_local K hK t
  calc
    brownianItoIntegralTruncatedProcess W (predictableSimpleProcessClosure K hK) t =
        hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
            (predictableSimpleProcessClosure K hK)) := by
              rfl
    _ = hIto.toContinuousLinearMap
          (predictableSimpleProcessClosure Kcut
            hKcut) := by
              rw [hClosure]
    _ =ᵐ[μ] MeasureTheory.brownianElementaryIntegralAtInfinity W Kcut := by
          simpa [hIto, Kcut] using
            hIto.ae_eq_brownianElementaryIntegralAtInfinity Kcut hKcut

/-- Helper for Theorem 25.11: the public stopped Brownian elementary integral of a predictable
simple process agrees almost surely with the closure-side truncated Brownian-Itô process. -/
theorem brownianElementaryIntegral_predictableSimple_ae_eq_truncatedClosure_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (t : NNReal) :
    MeasureTheory.brownianElementaryIntegral W K t =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W (predictableSimpleProcessClosure K hK) t := by
  -- Proof comment: identify both fixed-time slices with the same deterministic-cutoff terminal
  -- Brownian integral.
  refine
    (Filter.EventuallyEq.of_eq
      (brownianElementaryIntegral_predictableSimple_eq_cutoffTerminal_local
        K t)).trans ?_
  exact
    (brownianItoIntegralTruncatedProcess_predictableSimple_ae_eq_cutoffTerminal_local
      K hK t).symm

/-- Helper for Theorem 25.11: every deterministic-time slice of the concrete truncation process
already lies in `L²(μ)`. -/
theorem brownianItoIntegralTruncatedProcess_memLp_two_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (t : NNReal) :
    MemLp (brownianItoIntegralTruncatedProcess W H t) 2 μ := by
  -- Proof comment: a truncation slice is literally the chosen representative of the terminal
  -- `Lp` class `I^W_∞(H^(t))`, so its `L²` membership comes from the ambient `Lp` owner.
  simpa [brownianItoIntegralTruncatedProcess] using
    (MeasureTheory.Lp.memLp
      (hIto.toContinuousLinearMap
        (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H)))

/-- Helper for Theorem 25.11: every closure approximation by predictable simple stages yields the
timewise `L²` limit required by Exercise 21.4.3. -/
theorem brownianElementaryIntegral_timeSlice_tendsto_of_closureApproximation_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : PredictableSimpleProcessL2Closure ℱ μ}
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs_tendsto :
      Tendsto
        (fun n ↦ predictableSimpleProcessClosure (Hs n) (hHs_mem n))
        atTop (nhds H))
    (t : NNReal) :
    ∃ h_memLpSeq : ∀ n, MemLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t) 2 μ,
      Tendsto
        (fun n ↦ (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t))
        atTop
        (nhds
          (hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H))) := by
  let HsClosure : ℕ → PredictableSimpleProcessL2Closure ℱ μ := fun n ↦
    predictableSimpleProcessClosure (Hs n) (hHs_mem n)
  let cutoffBeforeMap :
      PredictableSimpleProcessL2Closure ℱ μ →L[ℝ]
        PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
  have hCutoffTendsto :
      Tendsto
        (fun n ↦ cutoffBeforeMap (HsClosure n))
        atTop
        (nhds (cutoffBeforeMap H)) := by
    -- Proof comment: deterministic cutoff is continuous on the closure, so it preserves the
    -- simple approximation limit.
    exact (cutoffBeforeMap.continuous.tendsto H).comp hHs_tendsto
  have hLpTendsto :
      Tendsto
        (fun n ↦
          hIto.toContinuousLinearMap
            (cutoffBeforeMap (HsClosure n)))
        atTop
        (nhds
          (hIto.toContinuousLinearMap
            (cutoffBeforeMap H))) := by
    -- Proof comment: apply the Brownian-Itô terminal map to the convergent cutoff approximants.
    let T := hIto.toContinuousLinearMap
    have hMap :
        Tendsto (fun n ↦ T (cutoffBeforeMap (HsClosure n))) atTop
          (nhds (T (cutoffBeforeMap H))) :=
      (T.continuous.tendsto _).comp hCutoffTendsto
    simpa [T] using hMap
  have hSliceAe :
      ∀ n,
        MeasureTheory.brownianElementaryIntegral W (Hs n) t =ᵐ[μ]
          brownianItoIntegralTruncatedProcess W (HsClosure n) t := by
    intro n
    simpa [HsClosure] using
      brownianElementaryIntegral_predictableSimple_ae_eq_truncatedClosure_local
        (Hs n) (hHs_mem n) t
  have h_memLpSeq :
      ∀ n, MemLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t) 2 μ := by
    intro n
    have hTargetMem :
        MemLp (brownianItoIntegralTruncatedProcess W (HsClosure n) t) 2 μ := by
      simpa [HsClosure] using
        brownianItoIntegralTruncatedProcess_memLp_two_local (HsClosure n) t
    exact (MeasureTheory.memLp_congr_ae (hSliceAe n)).2 hTargetMem
  refine ⟨h_memLpSeq, ?_⟩
  have hToLpEq :
      (fun n ↦ (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t)) =
        fun n ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t (HsClosure n)) := by
    funext n
    have hTargetMem :
        MemLp (brownianItoIntegralTruncatedProcess W (HsClosure n) t) 2 μ := by
      simpa [HsClosure] using
        brownianItoIntegralTruncatedProcess_memLp_two_local (HsClosure n) t
    calc
      (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t) =
          hTargetMem.toLp
            (brownianItoIntegralTruncatedProcess W (HsClosure n) t) := by
              exact MeasureTheory.MemLp.toLp_congr
                (h_memLpSeq n)
                hTargetMem
                (hSliceAe n)
      _ =
          hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t (HsClosure n)) := by
              let hCanonical :
                  MemLp (brownianItoIntegralTruncatedProcess W (HsClosure n) t) 2 μ := by
                simpa [HsClosure] using
                  brownianItoIntegralTruncatedProcess_memLp_two_local (HsClosure n) t
              have hCanonicalEq :
                  hCanonical.toLp (brownianItoIntegralTruncatedProcess W (HsClosure n) t) =
                    hIto.toContinuousLinearMap
                      (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
                        (HsClosure n)) := by
                apply Lp.ext
                exact
                  (MeasureTheory.MemLp.coeFn_toLp hCanonical).trans
                    (Filter.EventuallyEq.of_eq rfl)
              exact
                (MeasureTheory.MemLp.toLp_congr hTargetMem hCanonical
                  (Filter.EventuallyEq.of_eq rfl)).trans hCanonicalEq
  -- Proof comment: after identifying each time slice with the corresponding closure-side `Lp`
  -- class, the desired limit is exactly the continuity limit of the cutoff approximants.
  simpa [hToLpEq] using hLpTendsto

/-- Helper for Theorem 25.11: the fixed-time simple approximants converge in `L²` to the concrete
Definition 25.10 truncation slice. -/
theorem brownianElementaryIntegral_timeSlice_tendstoInLp_two_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : PredictableSimpleProcessL2Closure ℱ μ}
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs_tendsto :
      Tendsto
        (fun n ↦ predictableSimpleProcessClosure (Hs n) (hHs_mem n))
        atTop (nhds H))
    (t : NNReal) :
    TendstoInLp 2 μ
      (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
      (brownianItoIntegralTruncatedProcess W H t) := by
  have hSliceLimit :
      ∃ h_memLpSeq : ∀ n, MemLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t) 2 μ,
        Tendsto
          (fun n ↦ (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t))
          atTop
          (nhds
            (hIto.toContinuousLinearMap
              (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H))) := by
    exact
      brownianElementaryIntegral_timeSlice_tendsto_of_closureApproximation_local
        hHs_tendsto t
  rcases hSliceLimit with
    ⟨h_memLpSeq, h_tendsto⟩
  refine ⟨h_memLpSeq, brownianItoIntegralTruncatedProcess_memLp_two_local H t, ?_⟩
  have hTargetToLp :
      (brownianItoIntegralTruncatedProcess_memLp_two_local H t).toLp
          (brownianItoIntegralTruncatedProcess W H t) =
        hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) := by
    apply Lp.ext
    exact
      (MeasureTheory.MemLp.coeFn_toLp
        (brownianItoIntegralTruncatedProcess_memLp_two_local H t)).trans
        (Filter.EventuallyEq.of_eq rfl)
  -- Proof comment: `TendstoInLp` is just the owner packaging of the already proved `Lp`-class
  -- convergence, with the target class rewritten to the concrete truncation slice.
  simpa [brownianItoIntegralTruncatedProcess, hTargetToLp] using h_tendsto

/-- Helper for Theorem 25.11: the fixed-time `L²` convergence above already matches the
`ENNReal.ofReal 2` exponent spelling required by Exercise 21.4.3. -/
private theorem brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : PredictableSimpleProcessL2Closure ℱ μ}
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs_tendsto :
      Tendsto
        (fun n ↦ predictableSimpleProcessClosure (Hs n) (hHs_mem n))
        atTop (nhds H))
    (t : NNReal) :
    letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
    TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
      (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
      (brownianItoIntegralTruncatedProcess W H t) := by
  -- Proof comment: the only change is the exponent's normal form; the underlying `L²` statement
  -- is exactly the previous theorem.
  simpa using
    brownianElementaryIntegral_timeSlice_tendstoInLp_two_local hHs_tendsto t

/-- Helper for Theorem 25.11: deterministic cutoff is contractive on the closure
`\overline{\mathcal E}`. -/
theorem cutoffBefore_norm_le_local
    {μ : Measure Ω} {ℱ : TimeFiltration}
    (t : NNReal) (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ‖MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H‖ ≤ ‖H‖ := by
  -- Proof comment: compare both closure elements in the ambient `L²(μ ⊗ dt)` space, where the
  -- cutoff is the indicator multiplication used in Definition 25.10 and so cannot increase the
  -- `L²` norm.
  change ‖(((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H :
        PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (MeasureTheory.processMeasure μ)))‖ ≤
    ‖((H : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (MeasureTheory.processMeasure μ))‖
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  rw [eLpNorm_congr_ae
      (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn t H)]
  let f : Ω × ℝ → ℝ := fun x ↦
    (((H : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (MeasureTheory.processMeasure μ)) x)
  simpa [f] using
    (eLpNorm_indicator_le f :
      eLpNorm (Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)} f) 2
          (MeasureTheory.processMeasure μ) ≤
        eLpNorm f 2 (MeasureTheory.processMeasure μ))

/-- Helper for Theorem 25.11: the conditional-expectation martingale of the terminal Brownian-Itô
class is available independently of the exported truncation owner. -/
theorem terminalCondExp_martingale_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    Martingale (fun t ↦ μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]) ℱ μ := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  -- Proof comment: once the terminal Itô class is fixed, the standard conditional-expectation
  -- process is the canonical martingale candidate.
  exact MeasureTheory.martingale_condExp (hIto.toContinuousLinearMap H : Ω → ℝ) ℱ μ

/-- Companion API for Theorem 25.11 (2): the source-facing owner for `\tilde I^W(H)` is the
canonical conditional-expectation process of the terminal Brownian-Itô class. The concrete
Definition 25.10 truncation process is identified with it below by almost-sure equality. -/
noncomputable abbrev brownianItoIntegralMartingaleProcess
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) : Process :=
  fun t ↦ μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]

/-- Helper for Theorem 25.11: the concrete truncation process already satisfies the uniform
`L²` bound predicted by the source proof. -/
theorem truncatedProcess_l2_bound_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      eLpNorm (brownianItoIntegralTruncatedProcess W H t) 2 μ ≤ (‖H‖₊ : ℝ≥0∞) := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  intro t
  let hMem : MemLp (brownianItoIntegralTruncatedProcess W H t) 2 μ :=
    brownianItoIntegralTruncatedProcess_memLp_two_local H t
  have hToLp :
      hMem.toLp (brownianItoIntegralTruncatedProcess W H t) =
        hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) := by
    -- Proof comment: the concrete truncation slice is by definition the chosen representative of
    -- the cutoff terminal `Lp` class.
    apply Lp.ext
    exact (MeasureTheory.MemLp.coeFn_toLp hMem).trans (Filter.EventuallyEq.of_eq rfl)
  calc
    eLpNorm (brownianItoIntegralTruncatedProcess W H t) 2 μ =
        ‖hMem.toLp (brownianItoIntegralTruncatedProcess W H t)‖ₑ := by
          symm
          exact Lp.enorm_toLp hMem
    _ =
        ‖hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H)‖ₑ := by
          rw [hToLp]
    _ =
        ENNReal.ofReal
          ‖hIto.toContinuousLinearMap
              (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H)‖ := by
          rw [← ofReal_norm_eq_enorm]
    _ =
        ENNReal.ofReal
          ‖MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H‖ := by
          rw [norm_eq hBrownian hAdapted hIndependentIncrements]
    _ ≤ ENNReal.ofReal ‖H‖ := by
          exact ENNReal.ofReal_le_ofReal (cutoffBefore_norm_le_local t H)
    _ = (‖H‖₊ : ℝ≥0∞) := by
          rw [ofReal_norm_eq_enorm]
          simp [enorm_eq_nnnorm]

/-- Helper for Theorem 25.11: on a predictable simple stage, the closure-side truncation slice is
the conditional expectation of the corresponding terminal Brownian-Itô class. -/
theorem predictableSimpleClosure_truncated_eq_terminalCondExp_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (t : NNReal) :
    brownianItoIntegralTruncatedProcess W (predictableSimpleProcessClosure K hK) t =ᵐ[μ]
      μ[((hIto.toContinuousLinearMap (predictableSimpleProcessClosure K hK) : Ω → ℝ)) | ℱ t] := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let T : NNReal := representation.times (Fin.last representation.n)
  have hRepresentation :
      (K : Process) = representation.toProcess :=
    Classical.choose_spec (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  have hStoppedEq :
      MeasureTheory.brownianElementaryIntegral W K (max t T) =
        MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
    -- Proof comment: once `max t T` is beyond the last partition time of the chosen step
    -- representation, the stopped elementary integral has reached its terminal value.
    calc
      MeasureTheory.brownianElementaryIntegral W K (max t T) =
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral
            representation W (max t T) := by
              simpa [hRepresentation] using
                congrFun (MeasureTheory.brownianElementaryIntegral_spec W K hRepresentation)
                  (max t T)
      _ =
          MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
            representation W := by
              simpa [T] using
                (PredictableStepRepresentation.brownianElementaryIntegral_eq_atInfinity
                  representation W (le_max_right t T))
      _ =
          MeasureTheory.brownianElementaryIntegralAtInfinity W K := by
              simpa [hRepresentation] using
                (MeasureTheory.brownianElementaryIntegralAtInfinity_spec W K hRepresentation).symm
  have hSimpleMart :
      Martingale (MeasureTheory.brownianElementaryIntegral W K) ℱ μ :=
    brownianElementaryIntegral_martingale
      hBrownian hAdapted hIndependentIncrements K
  have hCondElementary :
      μ[MeasureTheory.brownianElementaryIntegralAtInfinity W K | ℱ t] =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegral W K t := by
    -- Proof comment: the simple-stage stopped integral is a martingale, and after the terminal
    -- representation time it is exactly the terminal elementary integral.
    simpa using
      (MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hStoppedEq)).trans
        (hSimpleMart.condExp_ae_eq (le_max_left t T))
  have hTerminalAe :
      ((hIto.toContinuousLinearMap (predictableSimpleProcessClosure K hK) : Lp ℝ 2 μ) :
        Ω → ℝ) =ᵐ[μ]
        MeasureTheory.brownianElementaryIntegralAtInfinity W K :=
    hIto.ae_eq_brownianElementaryIntegralAtInfinity K hK
  -- Proof comment: identify the truncation slice with the simple elementary integral, then
  -- replace the latter by the conditional expectation of the terminal closure-side class.
  exact
    (brownianElementaryIntegral_predictableSimple_ae_eq_truncatedClosure_local
      K hK t).symm.trans <|
      hCondElementary.symm.trans <|
        (MeasureTheory.condExp_congr_ae hTerminalAe).symm

/-- Companion API for Theorem 25.11: each deterministic-time slice of the concrete truncation
process `\tilde I^W(H)` agrees almost surely with the conditional-expectation representative used
to prove the martingale property. -/
theorem truncatedProcess_ae_eq_terminalCondExp
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      brownianItoIntegralTruncatedProcess W H t =ᵐ[μ]
        μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t] := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := fact_iff.2 (by norm_num)
  rcases closurePoint_hasPredictableSimpleApproximation H with ⟨Hs, hHs_mem, hHs_tendsto⟩
  let HsClosure : ℕ → PredictableSimpleProcessL2Closure ℱ μ := fun n ↦
    predictableSimpleProcessClosure (Hs n) (hHs_mem n)
  have hHsClosure_tendsto :
      Tendsto HsClosure atTop (nhds H) := by
    -- Proof comment: the approximation theorem already returns the simple stages in the canonical
    -- closure owner used by Definition 25.10.
    simpa [HsClosure] using hHs_tendsto
  intro t
  let terminalMap := hIto.toContinuousLinearMap
  have hTerminalMapContinuous : Continuous terminalMap := terminalMap.continuous
  have hTerminalLpTendsto :
      Tendsto (fun n ↦ terminalMap (HsClosure n))
        atTop (nhds (terminalMap H)) := by
    -- Proof comment: the terminal Brownian-Itô map is continuous on the closure.
    exact (hTerminalMapContinuous.tendsto H).comp hHsClosure_tendsto
  have hTerminalELpTendsto :
      Tendsto
        (fun n ↦
          eLpNorm
            (((terminalMap (HsClosure n) : Ω → ℝ) - (terminalMap H : Ω → ℝ))) 2 μ)
        atTop (nhds 0) := by
    -- Proof comment: translate the convergence of terminal `Lp` classes into vanishing `L²`
    -- distance of concrete representatives.
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n ↦ (terminalMap (HsClosure n) : Ω → ℝ))
        (fun n ↦ MeasureTheory.Lp.memLp (terminalMap (HsClosure n)))
        (terminalMap H : Ω → ℝ)
        (MeasureTheory.Lp.memLp (terminalMap H))).1 <|
        by simpa using hTerminalLpTendsto
  have hCondMem :
      MemLp (μ[((terminalMap H : Ω → ℝ)) | ℱ t]) 2 μ := by
    exact
      MeasureTheory.MemLp.condExp_of_one_le
        (MeasureTheory.Lp.memLp (terminalMap H))
        (ℱ.le t)
  have hCondMemSeq :
      ∀ n,
        MemLp (μ[((terminalMap (HsClosure n) : Ω → ℝ)) | ℱ t]) 2 μ := by
    intro n
    exact
      MeasureTheory.MemLp.condExp_of_one_le
        (MeasureTheory.Lp.memLp (terminalMap (HsClosure n)))
        (ℱ.le t)
  have hCondToLpTendsto :
      Tendsto
        (fun n ↦
          (hCondMemSeq n).toLp
            (μ[((terminalMap (HsClosure n) : Ω → ℝ)) | ℱ t]))
        atTop
        (nhds
          (hCondMem.toLp
            (μ[((terminalMap H : Ω → ℝ)) | ℱ t]))) := by
    have hCondELpTendsto :
        Tendsto
          (fun n ↦
            eLpNorm
              (μ[((terminalMap (HsClosure n) : Ω → ℝ)) | ℱ t] -
                μ[((terminalMap H : Ω → ℝ)) | ℱ t]) 2 μ)
          atTop (nhds 0) := by
      -- Proof comment: conditional expectation is `L²`-continuous on the probability space.
      exact
        MeasureTheory.tendsto_eLpNorm_condExp_sub_of_tendsto_eLpNorm
          (ℱ.le t)
          (MeasureTheory.Lp.memLp (terminalMap H))
          (fun n ↦ MeasureTheory.Lp.memLp (terminalMap (HsClosure n)))
          hTerminalELpTendsto
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n ↦ μ[((terminalMap (HsClosure n) : Ω → ℝ)) | ℱ t])
        hCondMemSeq
        (μ[((terminalMap H : Ω → ℝ)) | ℱ t])
        hCondMem).2 hCondELpTendsto
  rcases
      @brownianElementaryIntegral_timeSlice_tendsto_of_closureApproximation_local
        Ω mΩ μ ℱ W hIto H Hs hHs_mem hHs_tendsto t with
    ⟨hSliceMemSeq, hSliceLpTendsto⟩
  have hSliceEq :
      (fun n ↦
        (hSliceMemSeq n).toLp
          (MeasureTheory.brownianElementaryIntegral W (Hs n) t)) =
        fun n ↦
          (hCondMemSeq n).toLp
            (μ[((terminalMap (HsClosure n) : Ω → ℝ)) | ℱ t]) := by
    funext n
    apply (MeasureTheory.MemLp.toLp_eq_toLp_iff (hSliceMemSeq n) (hCondMemSeq n)).2
    -- Proof comment: the simple approximants already satisfy the source-side conditional
    -- expectation identity at fixed time `t`.
    exact
      (brownianElementaryIntegral_predictableSimple_ae_eq_truncatedClosure_local
        (Hs n) (hHs_mem n) t).trans <|
        predictableSimpleClosure_truncated_eq_terminalCondExp_local
          hBrownian hAdapted hIndependentIncrements (Hs n) (hHs_mem n) t
  have hSliceToCondTendsto :
      Tendsto
        (fun n ↦
          (hSliceMemSeq n).toLp
            (MeasureTheory.brownianElementaryIntegral W (Hs n) t))
        atTop
        (nhds
          (hCondMem.toLp
            (μ[((terminalMap H : Ω → ℝ)) | ℱ t]))) := by
    -- Proof comment: after the simple-stage identification, the same `Lp` sequence also
    -- converges to the conditional expectation of the terminal Brownian-Itô class.
    rw [hSliceEq]
    exact hCondToLpTendsto
  have hTargetToLp :
      (brownianItoIntegralTruncatedProcess_memLp_two_local H t).toLp
          (brownianItoIntegralTruncatedProcess W H t) =
        terminalMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) := by
    -- Proof comment: the concrete truncation slice is exactly the chosen representative of the
    -- cutoff terminal `Lp` class.
    apply Lp.ext
    exact
      (MeasureTheory.MemLp.coeFn_toLp
        (brownianItoIntegralTruncatedProcess_memLp_two_local H t)).trans
        (Filter.EventuallyEq.of_eq rfl)
  have hLpEq :
      terminalMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) =
        hCondMem.toLp
          (μ[((terminalMap H : Ω → ℝ)) | ℱ t]) :=
    tendsto_nhds_unique hSliceLpTendsto hSliceToCondTendsto
  -- Proof comment: the truncation slice and the conditional expectation realize the same `L²`
  -- class, so they agree almost everywhere.
  exact
    (MeasureTheory.MemLp.toLp_eq_toLp_iff
      (brownianItoIntegralTruncatedProcess_memLp_two_local H t)
      hCondMem).1 (hTargetToLp.trans hLpEq)

/-- Companion API for Theorem 25.11 (2): the concrete Definition 25.10 truncation process and the
source-facing martingale owner `brownianItoIntegralMartingaleProcess W H` agree at every
deterministic time almost surely. -/
theorem brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      (@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) t =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W H t := by
  intro t
  exact (truncatedProcess_ae_eq_terminalCondExp hBrownian hAdapted hIndependentIncrements H t).symm

/-- Companion API for Theorem 25.11 (2): each deterministic-time slice of the concrete Definition
25.10 truncation process `\tilde I_t^W(H) := I^W_∞(H^(t))` lies in `L²(μ)`. The bridge to the
conditional-expectation proof device is recorded by
`truncatedProcess_ae_eq_terminalCondExp`. -/
theorem truncatedProcess_memLp
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal, MemLp (brownianItoIntegralTruncatedProcess W H t) 2 μ := by
  intro t
  -- Proof comment: the public `L²` claim is already available from the local truncation-slice
  -- membership lemma, so no conditional-expectation work is needed here.
  simpa using brownianItoIntegralTruncatedProcess_memLp_two_local H t

/-- Helper for Theorem 25.11: each fixed-time slice of the concrete truncation process is already
almost everywhere strongly measurable with respect to the time-`t` sigma-algebra, via its
conditional-expectation identification. -/
theorem truncatedProcess_aestronglyMeasurable_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      AEStronglyMeasurable[ℱ t] (brownianItoIntegralTruncatedProcess W H t) μ := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  intro t
  -- Proof comment: the conditional expectation is strongly measurable for `ℱ t`, and the
  -- concrete truncation slice is almost everywhere equal to it.
  exact
    ((stronglyMeasurable_condExp : StronglyMeasurable[ℱ t]
        (μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t])).aestronglyMeasurable).congr
      (truncatedProcess_ae_eq_terminalCondExp
        hBrownian hAdapted hIndependentIncrements H t).symm

/-- Companion API for Theorem 25.11 (2): package the uniform `L²` bound together with the
existence of a continuous modification, so the main theorem surface can stay split into a small
number of atomic clauses. -/
def truncatedProcessBoundedContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} (W : Process)
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) : Prop :=
  (∃ C : ℝ≥0,
      ∀ t : NNReal, eLpNorm (brownianItoIntegralTruncatedProcess W H t) 2 μ ≤ (C : ℝ≥0∞)) ∧
    ∃ IwH : Process, IsContinuousModification W H IwH

/-- Companion API for Theorem 25.11 (2): `truncatedProcessBoundedContinuous W H` unfolds to the
uniform `L²`-bound clause together with the continuous-modification clause from the source. -/
theorem truncatedProcessBoundedContinuous_iff
    {μ : Measure Ω} {ℱ : TimeFiltration} (W : Process)
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    truncatedProcessBoundedContinuous W H ↔
      ((∃ C : ℝ≥0,
          ∀ t : NNReal, eLpNorm (brownianItoIntegralTruncatedProcess W H t) 2 μ ≤
            (C : ℝ≥0∞)) ∧
        ∃ IwH : Process, IsContinuousModification W H IwH) :=
  Iff.rfl

/-- Helper for Theorem 25.11: the time-`t` conditional expectation of the terminal Brownian-Itô
class belongs to `L²(μ.trim (ℱ.le t))`. -/
theorem terminalCondExp_memLp_trim_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (t : NNReal) :
    MemLp (μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]) 2 (μ.trim (ℱ.le t)) := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  let condSlice : Ω → ℝ := μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]
  have hCondMem :
      MemLp condSlice 2 μ :=
    MeasureTheory.MemLp.condExp_of_one_le
      (MeasureTheory.Lp.memLp (hIto.toContinuousLinearMap H))
      (ℱ.le t)
  refine ⟨stronglyMeasurable_condExp.aestronglyMeasurable, ?_⟩
  -- Proof comment: trimming to `ℱ t` preserves the `L²` seminorm of an `ℱ t`-strongly
  -- measurable function.
  rw [MeasureTheory.eLpNorm_trim (ℱ.le t) stronglyMeasurable_condExp]
  exact hCondMem.2

/-- Helper for Theorem 25.11: the concrete truncation slice and the terminal conditional
expectation realize the same ambient `L²(μ)` class. -/
theorem truncatedProcess_eq_terminalCondExp_toLp_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (t : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) =
      let condSlice : Ω → ℝ := μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]
      let hCondTrimMem : MemLp condSlice 2 (μ.trim (ℱ.le t)) :=
        terminalCondExp_memLp_trim_local hBrownian H t
      (MeasureTheory.memLp_of_memLp_trim (ℱ.le t) hCondTrimMem).toLp condSlice := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  let condSlice : Ω → ℝ := μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]
  let hCondTrimMem : MemLp condSlice 2 (μ.trim (ℱ.le t)) :=
    terminalCondExp_memLp_trim_local hBrownian H t
  let hCondMem : MemLp condSlice 2 μ :=
    MeasureTheory.memLp_of_memLp_trim (ℱ.le t) hCondTrimMem
  let hSliceMem : MemLp (brownianItoIntegralTruncatedProcess W H t) 2 μ :=
    brownianItoIntegralTruncatedProcess_memLp_two_local H t
  have hSliceToLp :
      hSliceMem.toLp (brownianItoIntegralTruncatedProcess W H t) =
        hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) := by
    -- Proof comment: the concrete truncation slice is exactly the chosen representative of the
    -- cutoff terminal `Lp` class.
    apply Lp.ext
    exact (MeasureTheory.MemLp.coeFn_toLp hSliceMem).trans (Filter.EventuallyEq.of_eq rfl)
  have hSliceAe :
      brownianItoIntegralTruncatedProcess W H t =ᵐ[μ] condSlice :=
    truncatedProcess_ae_eq_terminalCondExp
      hBrownian hAdapted hIndependentIncrements H t
  have hSliceToCondToLp :
      hSliceMem.toLp (brownianItoIntegralTruncatedProcess W H t) =
        hCondMem.toLp condSlice :=
    (MeasureTheory.MemLp.toLp_eq_toLp_iff hSliceMem hCondMem).2 hSliceAe
  -- Proof comment: identify the concrete slice with the conditional-expectation `Lp` class.
  exact hSliceToLp.symm.trans hSliceToCondToLp

/-- Helper for Theorem 25.11: each cutoff terminal `L²(μ)` class belongs to the
`lpMeasSubgroup` for the time-`t` sigma-algebra. This is the stable fixed-time measurability
surface used by the conditional-expectation route. -/
theorem truncatedProcess_slice_memLpMeasSubgroup_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H) ∈
        MeasureTheory.lpMeasSubgroup ℝ (ℱ t) (2 : ℝ≥0∞) μ := by
  intro t
  let condSlice : Ω → ℝ := μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]
  let hCondTrimMem : MemLp condSlice 2 (μ.trim (ℱ.le t)) :=
    terminalCondExp_memLp_trim_local hBrownian H t
  let hCondMem : MemLp condSlice 2 μ :=
    MeasureTheory.memLp_of_memLp_trim (ℱ.le t) hCondTrimMem
  -- Proof comment: rewrite the cutoff terminal class to the `Lp` class of the time-`t`
  -- conditional expectation and then use its `ℱ t`-almost-strong measurability.
  rw [MeasureTheory.mem_lpMeasSubgroup_iff_aestronglyMeasurable]
  rw [truncatedProcess_eq_terminalCondExp_toLp_local
    hBrownian hAdapted hIndependentIncrements H t]
  exact
    stronglyMeasurable_condExp.aestronglyMeasurable.congr
      (MeasureTheory.MemLp.coeFn_toLp hCondMem).symm

/-- Helper for Theorem 25.11: the concrete truncation process satisfies the martingale recurrence
directly against the terminal conditional-expectation martingale. -/
theorem truncatedProcess_condExp_ae_eq_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    {i j : NNReal}
    (hij : i ≤ j) :
    μ[brownianItoIntegralTruncatedProcess W H j | ℱ i] =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W H i := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    infer_instance
  have hTerminalMart :
      Martingale (fun t ↦ μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ t]) ℱ μ :=
    terminalCondExp_martingale_local hBrownian H
  -- Proof comment: rewrite both concrete slices to the same terminal conditional-expectation
  -- martingale and then use its tower-property recurrence.
  calc
    μ[brownianItoIntegralTruncatedProcess W H j | ℱ i] =ᵐ[μ]
        μ[μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ j] | ℱ i] := by
          exact MeasureTheory.condExp_congr_ae
            (truncatedProcess_ae_eq_terminalCondExp
              hBrownian hAdapted hIndependentIncrements H j)
    _ =ᵐ[μ] μ[((hIto.toContinuousLinearMap H : Ω → ℝ)) | ℱ i] := by
          exact hTerminalMart.condExp_ae_eq hij
    _ =ᵐ[μ] brownianItoIntegralTruncatedProcess W H i := by
          exact
            (truncatedProcess_ae_eq_terminalCondExp
              hBrownian hAdapted hIndependentIncrements H i).symm

/-- Helper for Theorem 25.11: the concrete Definition 25.10 truncation process
`\tilde I^W(H)` admits a continuous modification before the final theorem packages the three
source clauses together. The reusable owner for such a realization is
`IsContinuousModification W H IwH`. -/
theorem exists_continuousModification_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ IwH : Process, IsContinuousModification W H IwH := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
  rcases closurePoint_hasPredictableSimpleApproximation H with ⟨Hs, hHs_mem, hHs_tendsto⟩
  let Xtilde : NNReal → MeasureTheory.Lp ℝ (ENNReal.ofReal (2 : ℝ)) μ := fun t ↦
    (brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
      hHs_tendsto t).memLp.toLp
      (brownianItoIntegralTruncatedProcess W H t)
  have hX :
      ∀ n : ℕ, Martingale (MeasureTheory.brownianElementaryIntegral W (Hs n)) ℱ μ := by
    intro n
    -- Proof comment: each predictable simple approximant is already covered by Theorem 25.4.
    exact brownianElementaryIntegral_martingale
      hBrownian hAdapted hIndependentIncrements (Hs n)
  have hcont :
      ∀ n : ℕ,
        HasAlmostSurelyContinuousPaths μ (MeasureTheory.brownianElementaryIntegral W (Hs n)) := by
    intro n
    -- Proof comment: the same Theorem 25.4 package gives almost surely continuous paths on every
    -- simple approximating martingale.
    exact brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
      hBrownian hAdapted hIndependentIncrements (Hs n)
  have hp : 1 < (2 : ℝ) := by
    norm_num
  have hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
        ∃ h_memLpSeq :
            ∀ n, MemLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t)
              (ENNReal.ofReal (2 : ℝ)) μ,
          Tendsto
            (fun n ↦ (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t))
            atTop (nhds (Xtilde t)) := by
    intro t
    let hSlice :
        TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
          (brownianItoIntegralTruncatedProcess W H t) :=
      brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
        hHs_tendsto t
    -- Proof comment: the source-side fixed-time `L²` convergence is already packaged as
    -- `TendstoInLp`, so the Exercise 21.4.3 input is just its owner-level `toLp` formulation.
    refine ⟨hSlice.memLpSeq, ?_⟩
    simpa [Xtilde, hSlice] using hSlice.tendsto_toLp
  rcases exists_continuous_martingale_modification_of_timewise_lp_limit
      hX hcont hp hlimit with
    ⟨Xc, _hXc_martingale, hXc_cont, hXc_repr, _hXc_tendsto⟩
  refine ⟨Xc, ?_⟩
  refine ⟨hXc_cont, ?_⟩
  intro t
  let hSlice :
      TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
        (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
        (brownianItoIntegralTruncatedProcess W H t) :=
    brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
      hHs_tendsto t
  rcases hXc_repr t with ⟨hXc_memLp, hXc_toLp⟩
  have hToLpEq :
      hXc_memLp.toLp (Xc t) =
        hSlice.memLp.toLp (brownianItoIntegralTruncatedProcess W H t) := by
    -- Proof comment: both `Lp` classes are the same fixed-time limit class `Xtilde t`.
    simpa [Xtilde, hSlice] using hXc_toLp
  -- Proof comment: equal fixed-time `L²` classes mean almost-everywhere equal representatives,
  -- which is exactly the `AreModifications` predicate for the concrete truncation process.
  exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hXc_memLp hSlice.memLp).1 hToLpEq

/-- Helper for Theorem 25.11: the source-facing martingale owner inherits the uniform `L²` bound
from the concrete truncation process via deterministic-time almost-sure equality. -/
theorem brownianItoIntegralMartingaleProcess_l2_bound_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ t : NNReal,
      eLpNorm ((@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) t) 2 μ ≤
        (‖H‖₊ : ℝ≥0∞) := by
  intro t
  -- Proof comment: transport the already-proved bound across the deterministic-time almost-sure
  -- identification with the concrete truncation slice.
  rw [eLpNorm_congr_ae
    (brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess
      hBrownian hAdapted hIndependentIncrements H t)]
  exact truncatedProcess_l2_bound_local hBrownian hAdapted hIndependentIncrements H t

/-- Helper for Theorem 25.11: a continuous modification of the concrete truncation process is also
a continuous modification of the source-facing martingale owner. -/
theorem brownianItoIntegralMartingaleProcess_hasContinuousModification_local
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ IwH : Process,
      HasAlmostSurelyContinuousPaths μ IwH ∧
        AreModifications μ IwH
          (@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) := by
  rcases exists_continuousModification_local hBrownian hAdapted hIndependentIncrements H with
    ⟨IwH, hIwH⟩
  rcases isContinuousModification_spec hIwH with ⟨hCont, hMod⟩
  refine ⟨IwH, hCont, ?_⟩
  intro t
  -- Proof comment: compose the modification to the concrete truncation process with the
  -- deterministic-time almost-sure equality between truncation and martingale owners.
  exact
    (hMod t).trans
      (brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess
        hBrownian hAdapted hIndependentIncrements H t).symm

/-- Companion API for Theorem 25.11 (2): package the `L²`-boundedness clause together with the
existence of a continuous modification for the source-facing martingale owner
`brownianItoIntegralMartingaleProcess W H`. -/
def brownianItoIntegralMartingaleProcessBoundedContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) : Prop :=
  (∃ C : ℝ≥0,
      ∀ t : NNReal,
        eLpNorm ((@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) t) 2 μ ≤
          (C : ℝ≥0∞)) ∧
    ∃ IwH : Process,
      HasAlmostSurelyContinuousPaths μ IwH ∧
        AreModifications μ IwH
          (@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H)

/-- Companion API for Theorem 25.11 (2):
`brownianItoIntegralMartingaleProcessBoundedContinuous W H` unfolds to the `L²`-boundedness and
continuous-modification clauses for `brownianItoIntegralMartingaleProcess W H`. -/
theorem brownianItoIntegralMartingaleProcessBoundedContinuous_iff
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    (@brownianItoIntegralMartingaleProcessBoundedContinuous Ω mΩ μ ℱ W hIto H) ↔
      ((∃ C : ℝ≥0,
          ∀ t : NNReal,
            eLpNorm ((@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) t) 2 μ ≤
              (C : ℝ≥0∞)) ∧
        ∃ IwH : Process,
          HasAlmostSurelyContinuousPaths μ IwH ∧
            AreModifications μ IwH
              (@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H)) :=
  Iff.rfl

/-- Theorem 25.11 (2): for every `H ∈ \overline{\mathcal E}`, the source-facing owner
`brownianItoIntegralMartingaleProcess W H` for `\tilde I_t^W(H) := I^W_∞(H^(t))` is an
`L²`-bounded `ℱ`-martingale and has a continuous modification `I^W(H)`. The concrete Definition
25.10 truncation process remains available as `brownianItoIntegralTruncatedProcess W H` and is
identified with this martingale owner by
`brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess`. -/
theorem truncatedProcess_isL2BoundedMartingale
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    Martingale (@brownianItoIntegralMartingaleProcess Ω mΩ μ ℱ W hIto H) ℱ μ ∧
      (@brownianItoIntegralMartingaleProcessBoundedContinuous Ω mΩ μ ℱ W hIto H) := by
  -- Proof comment: the martingale clause is exactly the conditional-expectation martingale, and
  -- the boundedness and continuity clauses are transported from the concrete truncation process.
  refine ⟨terminalCondExp_martingale_local hBrownian H, ?_⟩
  rw [brownianItoIntegralMartingaleProcessBoundedContinuous_iff]
  refine ⟨?_, ?_⟩
  · -- Proof comment: use the source-side norm bound `‖H‖₊` after transporting each time slice.
    exact ⟨‖H‖₊,
      brownianItoIntegralMartingaleProcess_l2_bound_local
        hBrownian hAdapted hIndependentIncrements H⟩
  · -- Proof comment: the continuous modification witness for the truncation process transports
    -- along the same deterministic-time almost-sure equality.
    exact brownianItoIntegralMartingaleProcess_hasContinuousModification_local
      hBrownian hAdapted hIndependentIncrements H

/-- Helper for Theorem 25.11 (2): the concrete Definition 25.10 truncation process
`\tilde I^W(H)` admits a continuous modification. The reusable owner for such a realization is
`IsContinuousModification W H IwH`. -/
theorem exists_continuousModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ IwH : Process, IsContinuousModification W H IwH := by
  -- Proof comment: the public existence theorem is now just the earlier helper, kept below the
  -- target theorem so the later named API can continue to reference it.
  simpa using exists_continuousModification_local
    hBrownian hAdapted hIndependentIncrements H

/-- Helper for Theorem 25.11 (2): the source-facing continuous-modification owner can be chosen
to already be a martingale. -/
theorem exists_continuousModification_martingale
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ IwH : Process, IsContinuousModification W H IwH ∧ Martingale IwH ℱ μ := by
  letI : IsProbabilityMeasure μ := hBrownian.isProbabilityMeasure
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
  rcases closurePoint_hasPredictableSimpleApproximation H with ⟨Hs, hHs_mem, hHs_tendsto⟩
  let Xtilde : NNReal → MeasureTheory.Lp ℝ (ENNReal.ofReal (2 : ℝ)) μ := fun t ↦
    let hSlice :
        TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
          (brownianItoIntegralTruncatedProcess W H t) :=
      brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
        hHs_tendsto t
    hSlice.memLp.toLp (brownianItoIntegralTruncatedProcess W H t)
  have hX :
      ∀ n : ℕ, Martingale (MeasureTheory.brownianElementaryIntegral W (Hs n)) ℱ μ := by
    intro n
    -- Proof comment: each predictable simple approximant already carries the public Theorem 25.4
    -- martingale structure.
    exact brownianElementaryIntegral_martingale
      hBrownian hAdapted hIndependentIncrements (Hs n)
  have hcont :
      ∀ n : ℕ,
        HasAlmostSurelyContinuousPaths μ (MeasureTheory.brownianElementaryIntegral W (Hs n)) := by
    intro n
    -- Proof comment: the same public package gives almost surely continuous paths on every
    -- approximating elementary integral.
    exact brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
      hBrownian hAdapted hIndependentIncrements (Hs n)
  have hp : 1 < (2 : ℝ) := by
    norm_num
  have hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
        ∃ h_memLpSeq :
            ∀ n, MemLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t)
              (ENNReal.ofReal (2 : ℝ)) μ,
          Tendsto
            (fun n ↦ (h_memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) t))
            atTop (nhds (Xtilde t)) := by
    intro t
    let hSlice :
        TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
          (brownianItoIntegralTruncatedProcess W H t) :=
      brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
        hHs_tendsto t
    -- Proof comment: the fixed-time `L²` convergence is already in the exact `toLp` form needed
    -- by Exercise 21.4.3.
    refine ⟨hSlice.memLpSeq, ?_⟩
    simpa [Xtilde, hSlice] using hSlice.tendsto_toLp
  rcases exists_continuous_martingale_modification_of_timewise_lp_limit
      hX hcont hp hlimit with
    ⟨Xc, hXc_martingale, hXc_cont, hXc_repr, _hXc_tendsto⟩
  have hXc_mod :
      AreModifications μ Xc (brownianItoIntegralTruncatedProcess W H) := by
    intro t
    let hSlice :
        TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
          (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) t)
          (brownianItoIntegralTruncatedProcess W H t) :=
      brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
        hHs_tendsto t
    rcases hXc_repr t with ⟨hXc_memLp, hXc_toLp⟩
    have hToLpEq :
        hXc_memLp.toLp (Xc t) =
          hSlice.memLp.toLp (brownianItoIntegralTruncatedProcess W H t) := by
      -- Proof comment: both fixed-time `L²` classes equal the prescribed limit class `Xtilde t`.
      simpa [Xtilde, hSlice] using hXc_toLp
    exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hXc_memLp hSlice.memLp).1 hToLpEq
  exact ⟨Xc, ⟨hXc_cont, hXc_mod⟩, hXc_martingale⟩

/-- Helper for Theorem 25.11 (2): resetting only the time-zero value of a process to `0`. -/
private def pinValueAtZero (X : Process) : Process :=
  fun t ω ↦ if t = 0 then 0 else X t ω

/-- Helper for Theorem 25.11 (2): if a process is almost surely `0` at time `0`, then pinning its
time-zero value preserves the modification relation to any companion process. -/
private lemma areModifications_pinValueAtZero
    {μ : Measure Ω}
    {I J : Process}
    (hI_zero_ae : I 0 =ᵐ[μ] 0)
    (hIJ : AreModifications μ I J) :
    AreModifications μ (pinValueAtZero I) J := by
  intro t
  by_cases ht : t = 0
  · subst ht
    filter_upwards [hI_zero_ae, hIJ 0] with ω hω0 hωmod
    simp [pinValueAtZero, hω0, hωmod.symm]
  · -- Proof comment: away from the initial time, pinning does not change the process at all.
    calc
      pinValueAtZero I t =ᵐ[μ] I t := by
        exact Filter.EventuallyEq.of_eq <| by
          funext ω
          simp [pinValueAtZero, ht]
      _ =ᵐ[μ] J t := hIJ t

/-- Helper for Theorem 25.11 (2): if a process is almost surely `0` at time `0`, then pinning its
time-zero value keeps the almost-sure continuity of sample paths. -/
private lemma hasAlmostSurelyContinuousPaths_pinValueAtZero
    {μ : Measure Ω}
    {I : Process}
    (hI_zero_ae : I 0 =ᵐ[μ] 0)
    (hcont : HasAlmostSurelyContinuousPaths μ I) :
    HasAlmostSurelyContinuousPaths μ (pinValueAtZero I) := by
  filter_upwards [hI_zero_ae, hcont] with ω hω0 hωcont
  have hpath : processPath (pinValueAtZero I) ω = processPath I ω := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp [processPath, pinValueAtZero, hω0]
    · simp [processPath, pinValueAtZero, ht]
  -- Proof comment: on the full-measure event `I 0 = 0`, the pinned path is literally the same
  -- path, so continuity transports without any further stochastic input.
  simpa [HasAlmostSurelyContinuousPaths] using hpath.symm ▸ hωcont

/-- Helper for Theorem 25.11 (2): pinning a strongly adapted process at time `0` preserves strong
adaptedness. -/
private lemma stronglyAdapted_pinValueAtZero
    {ℱ : TimeFiltration}
    {I : Process}
    (hI_strong : StronglyAdapted ℱ I) :
    StronglyAdapted ℱ (pinValueAtZero I) := by
  intro t
  by_cases ht : t = 0
  · subst ht
    -- Proof comment: the pinned time-zero slice is the constant-zero random variable.
    have h0 : pinValueAtZero I 0 = (fun _ : Ω ↦ (0 : ℝ)) := by
      funext ω
      simp [pinValueAtZero]
    rw [h0]
    simpa using
      (stronglyMeasurable_const : StronglyMeasurable[ℱ 0] (fun _ : Ω ↦ (0 : ℝ)))
  · -- Proof comment: for positive times, pinning leaves the slice unchanged.
    have htEq : pinValueAtZero I t = I t := by
      funext ω
      simp [pinValueAtZero, ht]
    rw [htEq]
    exact hI_strong t

/-- Helper for Theorem 25.11 (2): pinning a martingale at time `0` preserves the martingale law
when the original time-zero slice already vanishes almost surely. -/
private lemma martingale_pinValueAtZero
    {μ : Measure Ω} {ℱ : TimeFiltration}
    {I : Process}
    (hI : Martingale I ℱ μ)
    (hI_zero_ae : I 0 =ᵐ[μ] 0) :
    Martingale (pinValueAtZero I) ℱ μ := by
  refine martingale_congr_ae hI (stronglyAdapted_pinValueAtZero hI.stronglyAdapted) ?_
  intro t
  by_cases ht : t = 0
  · subst ht
    filter_upwards [hI_zero_ae] with ω hω0
    simp [pinValueAtZero, hω0]
  · -- Proof comment: once `t ≠ 0`, the pinned process and the original process are identical.
    exact Filter.EventuallyEq.of_eq <| by
      funext ω
      simp [pinValueAtZero, ht]

/-- Helper for Theorem 25.11 (2): every stopped Brownian elementary integral starts exactly from
`0`. -/
private lemma brownianElementaryIntegral_zero
    {ℱ : TimeFiltration} {W : Process}
    (H : MeasureTheory.PredictableSimpleProcess ℱ) :
    MeasureTheory.brownianElementaryIntegral W H 0 = 0 := by
  funext ω
  classical
  -- Proof comment: at time `0`, every truncated Brownian increment is `W 0 - W 0`.
  simp [MeasureTheory.brownianElementaryIntegral,
    MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegral]

/-- Helper for Theorem 25.11 (2): the concrete truncated Brownian-Itô process already vanishes
almost surely at time `0`. -/
private lemma brownianItoIntegralTruncatedProcess_zero_ae
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    brownianItoIntegralTruncatedProcess W H 0 =ᵐ[μ] 0 := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
  rcases closurePoint_hasPredictableSimpleApproximation H with ⟨Hs, _hHs_mem, hHs_tendsto⟩
  let hSlice :
      TendstoInLp (ENNReal.ofReal (2 : ℝ)) μ
        (fun n ↦ MeasureTheory.brownianElementaryIntegral W (Hs n) 0)
        (brownianItoIntegralTruncatedProcess W H 0) := by
    simpa using
      brownianElementaryIntegral_timeSlice_tendstoInLp_ofRealTwo_local
        hHs_tendsto 0
  have hZeroMem : MemLp (fun _ : Ω ↦ (0 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (MemLp.zero' : MemLp (fun _ : Ω ↦ (0 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ)
  have hConst :
      Tendsto
        (fun n ↦ (hSlice.memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) 0))
        atTop
        (nhds (hZeroMem.toLp (fun _ : Ω ↦ (0 : ℝ)))) := by
    -- Proof comment: each approximating elementary integral is exactly `0` at the origin.
    have hSeqEq :
        (fun n ↦ (hSlice.memLpSeq n).toLp (MeasureTheory.brownianElementaryIntegral W (Hs n) 0)) =
          fun _ : ℕ ↦ hZeroMem.toLp (fun _ : Ω ↦ (0 : ℝ)) := by
      funext n
      have hZeroAe :
          MeasureTheory.brownianElementaryIntegral W (Hs n) 0 =ᵐ[μ] fun _ : Ω ↦ (0 : ℝ) := by
        exact Filter.EventuallyEq.of_eq <|
          brownianElementaryIntegral_zero (W := W) (H := Hs n)
      exact (MeasureTheory.MemLp.toLp_eq_toLp_iff (hSlice.memLpSeq n) hZeroMem).2 hZeroAe
    rw [hSeqEq]
    exact tendsto_const_nhds
  have hToLpEq :
      hSlice.memLp.toLp (brownianItoIntegralTruncatedProcess W H 0) =
        hZeroMem.toLp (fun _ : Ω ↦ (0 : ℝ)) :=
    tendsto_nhds_unique hSlice.tendsto_toLp hConst
  -- Proof comment: equality of `L²` classes identifies the time-zero slice with the zero
  -- function almost everywhere.
  exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hSlice.memLp hZeroMem).1 hToLpEq

/-- Helper for Theorem 25.11 (2): the raw chosen continuous-modification witness already starts
from `0` almost surely, so pinning only changes a null set at time `0`. -/
private lemma chooseContinuousModification_zero_ae
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    (Classical.choose
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)) 0 =ᵐ[μ] 0 := by
  let Xc : Process :=
    Classical.choose
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)
  have hMod :
      AreModifications μ Xc (brownianItoIntegralTruncatedProcess W H) :=
    (Classical.choose_spec
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)).1.modifies_truncated
  -- Proof comment: the chosen witness is a modification of the time-zero truncation slice, which
  -- is already zero almost everywhere.
  exact (hMod 0).trans (brownianItoIntegralTruncatedProcess_zero_ae H)

/-- Companion API for Theorem 25.11 (2): `continuousModification hBrownian hAdapted
hIndependentIncrements H` is the named process `I^W(H)` obtained from the Brownian hypotheses and
`H`. -/
noncomputable def continuousModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) : Process :=
  pinValueAtZero <|
    Classical.choose
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)

/-- Companion API for Theorem 25.11 (2): the named owner `continuousModification
hBrownian hAdapted hIndependentIncrements H` realizes the continuous modification predicate. -/
theorem continuousModification_isContinuousModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    IsContinuousModification W H
      (continuousModification hBrownian hAdapted hIndependentIncrements H) := by
  let Xc : Process :=
    Classical.choose
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)
  have hXc_mod :
      AreModifications μ Xc (brownianItoIntegralTruncatedProcess W H) :=
    (Classical.choose_spec
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)).1.modifies_truncated
  have hXc_cont :
      HasAlmostSurelyContinuousPaths μ Xc :=
    (Classical.choose_spec
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)).1.continuous_paths
  have hXc_zero_ae : Xc 0 =ᵐ[μ] 0 :=
    chooseContinuousModification_zero_ae
      hBrownian hAdapted hIndependentIncrements H
  -- Proof comment: the named owner is the chosen witness pinned at time `0`, so continuity and
  -- the modification relation both transport through the pinning lemmas.
  refine ⟨?_, ?_⟩
  · simpa [continuousModification, Xc] using
      hasAlmostSurelyContinuousPaths_pinValueAtZero hXc_zero_ae hXc_cont
  · simpa [continuousModification, Xc] using
      areModifications_pinValueAtZero hXc_zero_ae hXc_mod

/-- Companion API for Theorem 25.11 (2): the named process
`continuousModification hBrownian
hAdapted hIndependentIncrements H` has almost surely continuous paths and is a modification of the
concrete process `brownianItoIntegralTruncatedProcess W H`. -/
theorem continuousModification_spec
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    HasAlmostSurelyContinuousPaths μ
        (continuousModification hBrownian hAdapted hIndependentIncrements H) ∧
      AreModifications μ
        (continuousModification hBrownian hAdapted hIndependentIncrements H)
        (brownianItoIntegralTruncatedProcess W H) := by
  -- Proof comment: reuse the owner-unpacking lemma on the chosen witness.
  exact isContinuousModification_spec
    (continuousModification_isContinuousModification
      hBrownian hAdapted hIndependentIncrements H)

/-- Companion API for Theorem 25.11 (2): the named process
`continuousModification hBrownian hAdapted hIndependentIncrements H` is already a martingale. -/
theorem continuousModification_martingale
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    Martingale
      (continuousModification hBrownian hAdapted hIndependentIncrements H)
      ℱ μ := by
  let Xc : Process :=
    Classical.choose
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)
  have hXc_mart :
      Martingale Xc ℱ μ :=
    (Classical.choose_spec
      (exists_continuousModification_martingale
        hBrownian hAdapted hIndependentIncrements H)).2
  have hXc_zero_ae : Xc 0 =ᵐ[μ] 0 :=
    chooseContinuousModification_zero_ae
      hBrownian hAdapted hIndependentIncrements H
  -- Proof comment: the chosen owner is pinned only at a null time-zero defect, so the
  -- martingale law transfers by almost-everywhere congruence.
  simpa [continuousModification, Xc] using
    martingale_pinValueAtZero hXc_mart hXc_zero_ae

/-- Companion API for Theorem 25.11 (2): the named process
`continuousModification hBrownian hAdapted hIndependentIncrements H` starts exactly from `0`. -/
theorem continuousModification_zero
    {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}
    [BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    continuousModification hBrownian hAdapted hIndependentIncrements H 0 = 0 := by
  -- Proof comment: the named owner was defined by pinning the chosen witness at the origin.
  funext ω
  simp [continuousModification, pinValueAtZero]

end BrownianItoIntegral

end ProbabilityTheory
