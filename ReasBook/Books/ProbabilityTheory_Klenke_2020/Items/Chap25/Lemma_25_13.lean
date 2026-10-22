/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open ENNReal
open scoped ENNReal Topology

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- Helper for Lemma 25.13: cutting off a progressively measurable integrand before a stopping
time preserves progressive measurability. -/
theorem processBeforeStoppingTime_progMeasurable
    {ℱ : TimeFiltration} {H : Process}
    (hH : ProgMeasurable ℱ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    ProgMeasurable ℱ (ProbabilityTheory.processBeforeStoppingTime H τ) := by
  intro i
  letI : MeasurableSpace Ω := ℱ i
  let s : Set (Set.Iic i × Ω) :=
    {p | ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i}
  have hs : MeasurableSet s := by
    -- Proof comment: the stopping strip on `[0, i] × Ω` is cut out by comparing two measurable
    -- time variables.
    refine measurableSet_le ?_ ?_
    · exact continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)
    · exact
        ((hτ.min_const i).measurable_of_le (fun _ ↦ min_le_right _ _)).comp
          (@measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ i))
  have hEq :
      (fun p : Set.Iic i × Ω ↦ ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2) =
        Set.indicator s (fun p : Set.Iic i × Ω ↦ H p.1 p.2) := by
    funext p
    have hp : ((p.1 : NNReal) : ENNReal) ≤ i := by
      exact_mod_cast p.1.2
    by_cases hmem : p ∈ s
    · have hle : ((p.1 : NNReal) : ENNReal) ≤ τ p.2 := by
        have hmin : ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i := by
          simpa [s] using hmem
        exact le_trans hmin (min_le_left _ _)
      -- Proof comment: inside the stopping strip, the cutoff agrees with the original process.
      have hcut :
          ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2 = H p.1 p.2 := by
        simpa [ProbabilityTheory.processBeforeStoppingTime_apply, hle]
      rw [hcut]
      symm
      simp [Set.indicator, hmem]
    · have hnot : ¬ ((p.1 : NNReal) : ENNReal) ≤ τ p.2 := by
        intro hle
        apply hmem
        have hmin : ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i := le_min hle hp
        simpa [s] using hmin
      -- Proof comment: outside the strip, the cutoff vanishes by definition.
      have hcut :
          ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2 = 0 := by
        simpa [ProbabilityTheory.processBeforeStoppingTime_apply, hnot]
      rw [hcut]
      symm
      simp [Set.indicator, hmem]
  rw [hEq]
  -- Proof comment: indicator of a measurable strip preserves the progressive measurability of
  -- the restriction of `H` to `[0, i] × Ω`.
  exact (hH i).indicator hs

/-- Helper for Lemma 25.13: for a stopping time `τ`, the left-endpoint stopping event `{u < τ}`
is measurable at time `u`. -/
theorem measurableSet_lt_stoppingTime
    {ℱ : TimeFiltration} {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) (u : NNReal) :
    MeasurableSet[ℱ u] {ω | (u : ENNReal) < τ ω} := by
  -- Proof comment: `{u < τ}` is the complement of the stopping event `{τ ≤ u}`.
  exact hτ.measurableSet_gt u

/-- Helper for Lemma 25.13: multiplying a coefficient by the stopping event `{u < τ}` preserves
`ℱ u`-measurability. This is the measurability input needed for the dyadic stopped-simple
constructor from the source proof. -/
theorem measurable_mul_indicator_lt_stoppingTime
    {ℱ : TimeFiltration} {τ : Ω → ENNReal} {u : NNReal} {f : Ω → ℝ}
    (hf : Measurable[ℱ u] f)
    (hτ : IsStoppingTime ℱ τ) :
    Measurable[ℱ u]
      (fun ω ↦ f ω * Set.indicator {ω | (u : ENNReal) < τ ω} (fun _ ↦ (1 : ℝ)) ω) := by
  have hEvent : MeasurableSet[ℱ u] {ω | (u : ENNReal) < τ ω} :=
    measurableSet_lt_stoppingTime hτ u
  have hIndicator :
      Measurable[ℱ u]
        (Set.indicator {ω | (u : ENNReal) < τ ω} (fun _ ↦ (1 : ℝ))) := by
    -- Proof comment: the indicator is the piecewise function taking value `1` on the stopping
    -- event and `0` outside it.
    simpa using
      (Measurable.indicator measurable_const hEvent :
        Measurable[ℱ u] ({ω | (u : ENNReal) < τ ω}.indicator (fun _ ↦ (1 : ℝ))))
  -- Proof comment: the indicator of the stopping event is measurable at the same left endpoint,
  -- so the product stays measurable there.
  exact hf.mul hIndicator

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

section GlobalItoRealization

variable {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Process}
variable [hIto : BrownianItoIntegral μ ℱ W]
variable {τ : Ω → ENNReal} {H G : Process}

namespace MeasureTheory

/-- Helper for Lemma 25.13: the time-space realization of the cutoff process is the indicator of
the stopping strip in `Ω × ℝ`. -/
private theorem processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator
    {H : Process} {τ : Ω → ENNReal} :
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime H τ) =
      Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ τ x.1}
        (MeasureTheory.processToTimeSpaceFun H) := by
  funext x
  rcases x with ⟨ω, t⟩
  have ht_eq : (((t.toNNReal : NNReal) : ENNReal)) = ENNReal.ofReal t := by
    by_cases hnonneg : 0 ≤ t
    · rw [Real.toNNReal_of_nonneg hnonneg, ENNReal.ofReal_eq_coe_nnreal]
    · have hnonpos : t ≤ 0 := le_of_not_ge hnonneg
      rw [Real.toNNReal_of_nonpos hnonpos]
      simp [ENNReal.ofReal_eq_zero.mpr hnonpos]
  by_cases ht : ENNReal.ofReal t ≤ τ ω
  · -- Proof comment: on the stopping strip, the cutoff agrees with the original representative.
    have ht' : (((t.toNNReal : NNReal) : ENNReal)) ≤ τ ω := by
      simpa [ht_eq] using ht
    simp [MeasureTheory.processToTimeSpaceFun,
      ProbabilityTheory.processBeforeStoppingTime_apply, ht, ht']
  · -- Proof comment: outside the strip, both the cutoff and the indicator vanish.
    have ht' : ¬ (((t.toNNReal : NNReal) : ENNReal)) ≤ τ ω := by
      simpa [ht_eq] using ht
    simp [MeasureTheory.processToTimeSpaceFun,
      ProbabilityTheory.processBeforeStoppingTime_apply, ht, ht']

/-- Helper for Lemma 25.13: a globally square-integrable predictable simple process defines the
corresponding realized closure point in `PredictableSimpleProcessL2Closure ℱ μ`. -/
noncomputable def predictableSimpleProcessToClosureLocal
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (H : MeasureTheory.PredictableSimpleProcess ℱ)
    (hH :
      MemLp (MeasureTheory.processToTimeSpaceFun ((H : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  let H₂ : MeasureTheory.predictableSimpleProcessL2 ℱ μ :=
    MeasureTheory.predictableSimpleProcessToL2 H hH
  ⟨(H₂ : Lp ℝ 2 (MeasureTheory.processMeasure μ)),
    Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ) H₂.2⟩

/-- Helper for Lemma 25.13: every realized closure point admits a predictable-simple
approximation converging in the closure topology. -/
theorem existsPredictableSimpleApproximationOfClosurePointLocal
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    ∃ Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ,
      ∃ hHs_mem :
        ∀ n,
          MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
            (MeasureTheory.processMeasure μ),
        Filter.Tendsto
          (fun n ↦ MeasureTheory.predictableSimpleProcessToClosureLocal (Hs n) (hHs_mem n))
          Filter.atTop
          (nhds Hbar) := by
  classical
  have hmem :
      ((Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) ∈
        closure
          (MeasureTheory.predictableSimpleProcessL2 ℱ μ :
            Set (Lp ℝ 2 (MeasureTheory.processMeasure μ))) := by
    -- Proof comment: realize the closure point as an ambient `L²(μ ⊗ dt)` limit inside the
    -- topological closure of predictable simple representatives.
    simpa [MeasureTheory.PredictableSimpleProcessL2Closure, Submodule.topologicalClosure_coe] using
      Hbar.2
  rcases mem_closure_iff_seq_limit.mp hmem with ⟨fs, hfs_mem, hfs_tendsto⟩
  let Fs : ℕ → MeasureTheory.predictableSimpleProcessL2 ℱ μ := fun n ↦ ⟨fs n, hfs_mem n⟩
  choose Hs hHs_mem hHs_repr using fun n ↦ (Fs n).2
  refine ⟨Hs, hHs_mem, ?_⟩
  -- Proof comment: repackage the ambient approximants as canonical closure points coming from
  -- actual predictable simple processes.
  refine tendsto_subtype_rng.2 ?_
  convert hfs_tendsto using 1
  funext n
  apply Subtype.ext
  simpa [MeasureTheory.predictableSimpleProcessToClosureLocal] using
    (congrArg Subtype.val (hHs_repr n)).symm

/-- Helper for Lemma 25.13: a process belongs to the canonical `L²(μ ⊗ dt)` closure of
predictable simple integrands when its ambient `Lp` class lies in
`PredictableSimpleProcessL2Closure ℱ μ`. This is the local owner spelling used throughout the
file because importing `Theorem_25_9` would clash with the Definition 25.10 closure API. -/
def MemPredictableStepProcessClosure
    (ℱ : TimeFiltration) (μ : Measure Ω) (H : Process) : Prop :=
  ∃ hH : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ),
    hH.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ

namespace MemPredictableStepProcessClosure

variable {ℱ : TimeFiltration} {μ : Measure Ω} {H : Process}

/-- Helper for Lemma 25.13: a process in the canonical closure is globally square-integrable on
`Ω × [0, ∞)`. -/
theorem memLp (hH : MemPredictableStepProcessClosure ℱ μ H) :
    MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ) :=
  Exists.elim hH fun hH_memLp _ ↦ hH_memLp

/-- Helper for Lemma 25.13: the ambient `L²(μ ⊗ dt)` class of a closure member lies in the
realized closure. -/
theorem toLp_mem_closure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hH.memLp.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨_, hhH⟩ => hhH

/-- Helper for Lemma 25.13: a closure member canonically determines its realized closure point. -/
noncomputable def toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => ⟨hH_memLp.toLp (processToTimeSpaceFun H), hhH⟩

/-- Helper for Lemma 25.13: coercing `hH.toClosure` back to ambient `L²(μ ⊗ dt)` recovers the
represented `Lp` class of `H`. -/
@[simp] theorem coe_toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    ((hH.toClosure : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      hH.memLp.toLp (processToTimeSpaceFun H) :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => rfl

end MemPredictableStepProcessClosure

end MeasureTheory

local notation "MemPredictableStepProcessClosure" =>
  MeasureTheory.MemPredictableStepProcessClosure

/-- Helper for Lemma 25.13: the stopping strip in `Ω × ℝ` attached to a stopping time `τ`. -/
private def stoppingStrip_local (τ : Ω → ENNReal) : Set (Ω × ℝ) :=
  {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ τ x.1}

/-- Helper for Lemma 25.13: the stopping strip of a stopping time is measurable in the ambient
time-space product. -/
private theorem measurableSet_stoppingStrip_local
    (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet (stoppingStrip_local (Ω := Ω) τ) := by
  -- Proof comment: the strip is cut out by comparing the measurable time coordinate with the
  -- measurable stopping time.
  refine measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd) ?_
  exact hτ.measurable'.comp measurable_fst

/-- Helper for Lemma 25.13: multiplying an ambient `L²(μ ⊗ dt)` representative by the stopping
strip indicator keeps it in `L²(μ ⊗ dt)`. -/
private theorem memLp_stoppingStripIndicator_local
    (hτ : IsStoppingTime ℱ τ)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    MemLp
      (Set.indicator (stoppingStrip_local (Ω := Ω) τ) fun x ↦ f x)
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
  (Lp.memLp f).indicator (measurableSet_stoppingStrip_local (Ω := Ω) (ℱ := ℱ) hτ)

/-- Helper for Lemma 25.13: the ambient `L²(μ ⊗ dt)` stopping-strip operator attached to `τ`. -/
private noncomputable def stoppingStripLpFun_local
    (hτ : IsStoppingTime ℱ τ)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) :=
  (memLp_stoppingStripIndicator_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f).toLp
    (Set.indicator (stoppingStrip_local (Ω := Ω) τ) fun x ↦ f x)

/-- Helper for Lemma 25.13: the stopping-strip operator is additive on ambient `L²(μ ⊗ dt)`. -/
private theorem stoppingStripLpFun_add_local
    (hτ : IsStoppingTime ℱ τ)
    (f g : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ (f + g) =
      stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f +
        stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ g := by
  -- Proof comment: as for deterministic cutoffs, compare the two ambient `Lp` classes through
  -- `MemLp.toLp_eq_toLp_iff` and reduce to the pointwise indicator identity.
  rw [stoppingStripLpFun_local, stoppingStripLpFun_local, stoppingStripLpFun_local]
  rw [← MeasureTheory.MemLp.toLp_add
    (memLp_stoppingStripIndicator_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f)
    (memLp_stoppingStripIndicator_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ g)]
  apply (MeasureTheory.MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [Lp.coeFn_add f g] with x hx
  by_cases hxstrip : x ∈ stoppingStrip_local (Ω := Ω) τ
  · simpa [hxstrip] using hx
  · simp [hxstrip]

/-- Helper for Lemma 25.13: the stopping-strip operator commutes with scalar multiplication on
ambient `L²(μ ⊗ dt)`. -/
private theorem stoppingStripLpFun_smul_local
    (hτ : IsStoppingTime ℱ τ)
    (a : ℝ)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ (a • f) =
      a • stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f := by
  -- Proof comment: the stopping strip is fixed, so scalar multiplication commutes with the same
  -- indicator cutoff on the ambient `L²(μ ⊗ dt)` space.
  rw [stoppingStripLpFun_local, stoppingStripLpFun_local]
  rw [← MeasureTheory.MemLp.toLp_const_smul a
    (memLp_stoppingStripIndicator_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f)]
  apply (MeasureTheory.MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [Lp.coeFn_smul a f] with x hx
  by_cases hxstrip : x ∈ stoppingStrip_local (Ω := Ω) τ
  · simp [hxstrip, hx]
  · simp [hxstrip]

/-- Helper for Lemma 25.13: the stopping-strip operator is a contraction on ambient
`L²(μ ⊗ dt)`. -/
private theorem norm_stoppingStripLpFun_le_local
    (hτ : IsStoppingTime ℱ τ)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    ‖stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f‖ ≤ 1 * ‖f‖ := by
  rw [stoppingStripLpFun_local, Lp.norm_toLp, Lp.norm_def]
  simpa [one_mul] using ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le (s := stoppingStrip_local (Ω := Ω) τ) (fun x ↦ f x))

/-- Helper for Lemma 25.13: the stopping-strip cutoff acts continuously on ambient
`L²(μ ⊗ dt)`. -/
private noncomputable def stoppingStripLpMap_local
    (hτ : IsStoppingTime ℱ τ) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) →L[ℝ]
      Lp ℝ 2 (MeasureTheory.processMeasure μ) :=
  LinearMap.mkContinuous
    { toFun := stoppingStripLpFun_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
      map_add' := stoppingStripLpFun_add_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
      map_smul' := stoppingStripLpFun_smul_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ }
    1
    (fun f ↦ by
      simpa using norm_stoppingStripLpFun_le_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ f)

/-- Helper for Lemma 25.13: applying the ambient stopping-strip map to the `L²(μ ⊗ dt)` class
of `H` gives the `L²(μ ⊗ dt)` class of the stopped process `H^(τ)`. -/
private theorem stoppingStripLpMap_apply_toClosure_local
    (hτ : IsStoppingTime ℱ τ)
    {K : Process}
    (hK : MeasureTheory.MemPredictableStepProcessClosure ℱ μ K) :
    stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ hK.toClosure =
      ((by
          let strip : Set (Ω × ℝ) := stoppingStrip_local (Ω := Ω) τ
          have hIndicator :
              MemLp
                (Set.indicator strip (MeasureTheory.processToTimeSpaceFun K))
                (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
            hK.memLp.indicator (measurableSet_stoppingStrip_local (Ω := Ω) (ℱ := ℱ) hτ)
          simpa [strip, stoppingStrip_local,
            MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator] using
            hIndicator : MemLp
              (MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime K τ))
              (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ))).toLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime K τ)) := by
  rcases hK with ⟨hK_memLp, hK_closure⟩
  let strip : Set (Ω × ℝ) := stoppingStrip_local (Ω := Ω) τ
  let hStoppedMem :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime K τ))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
    have hIndicator :
        MemLp
          (Set.indicator strip (MeasureTheory.processToTimeSpaceFun K))
          (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
      hK_memLp.indicator (measurableSet_stoppingStrip_local (Ω := Ω) (ℱ := ℱ) hτ)
    -- Proof comment: rewrite the stopped representative to the common strip indicator and reuse
    -- the inherited `L²` bound from `K`.
    simpa [strip, stoppingStrip_local,
      MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator] using
      hIndicator
  -- Proof comment: after unpacking the closure witness, both sides are `toLp` classes of the
  -- same strip-indicator representative.
  rw [stoppingStripLpFun_local]
  apply (MeasureTheory.MemLp.toLp_eq_toLp_iff _ hStoppedMem).2
  have hLpEq :
      (((hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun K) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun K := by
    simpa using (MeasureTheory.MemLp.coeFn_toLp hK_memLp)
  have hIndicatorEq :
      Set.indicator strip
          (fun x ↦
            (((hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun K) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x)) =ᵐ[MeasureTheory.processMeasure μ]
        Set.indicator strip (MeasureTheory.processToTimeSpaceFun K) := by
    filter_upwards [hLpEq] with x hx
    by_cases hxstrip : x ∈ strip
    · simp [hxstrip, hx]
    · simp [hxstrip]
  exact hIndicatorEq.trans <|
    (Filter.EventuallyEq.of_eq
      (MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator
        (H := K) (τ := τ))).symm

/-- Helper for Lemma 25.13: convergence in the realized closure passes through the fixed stopping
strip because the strip operator is continuous on ambient `L²(μ ⊗ dt)`. -/
theorem processBeforeStoppingTime_toLp_tendsto_of_closureApprox_local
    (hτ : IsStoppingTime ℱ τ)
    {K : Process}
    (hK : MeasureTheory.MemPredictableStepProcessClosure ℱ μ K)
    {Ks : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    (hKs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Ks n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ))
    (hKsStopped :
      ∀ n,
        MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime ((Ks n : Process)) τ))
    (hKs_tendsto :
      Filter.Tendsto
        (fun n ↦ MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n))
        Filter.atTop
        (nhds hK.toClosure)) :
    Filter.Tendsto
      (fun n ↦ (((hKsStopped n).toClosure :
          MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))
      Filter.atTop
      (nhds
        (stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
          (((hK.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ))))) := by
  have hAmbient :
      Filter.Tendsto
        (fun n ↦
          (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))
        Filter.atTop
        (nhds
          (((hK.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
    exact tendsto_subtype_rng.1 hKs_tendsto
  have hStripTendsto :
      Filter.Tendsto
        (fun n ↦
          stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
            (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ))))
        Filter.atTop
        (nhds
          (stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
            (((hK.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))) := by
    -- Proof comment: once the approximation is viewed in ambient `L²(μ ⊗ dt)`, the strip map
    -- preserves the limit by continuity.
    exact
      ((stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ).continuous.tendsto _).comp
        hAmbient
  have hStageEq :
      ∀ n,
        stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
            (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ))) =
          (((hKsStopped n).toClosure :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)) := by
    intro n
    rcases hKsStopped n with ⟨hStoppedMem, hStoppedClosure⟩
    rw [stoppingStripLpFun_local]
    apply (MeasureTheory.MemLp.toLp_eq_toLp_iff _ hStoppedMem).2
    have hLpEq :
        (fun x ↦
          ((((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x)) =ᵐ[MeasureTheory.processMeasure μ]
          MeasureTheory.processToTimeSpaceFun ((Ks n : Process)) := by
      simpa [MeasureTheory.predictableSimpleProcessToClosureLocal,
        MeasureTheory.predictableSimpleProcessToL2_coe] using
        (MeasureTheory.MemLp.coeFn_toLp (hKs_mem n))
    have hIndicatorEq :
        Set.indicator (stoppingStrip_local (Ω := Ω) τ)
            (fun x ↦
              ((((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                      MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                    Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) x)) =ᵐ[MeasureTheory.processMeasure μ]
          Set.indicator (stoppingStrip_local (Ω := Ω) τ)
            (MeasureTheory.processToTimeSpaceFun ((Ks n : Process))) := by
      filter_upwards [hLpEq] with x hx
      by_cases hxstrip : x ∈ stoppingStrip_local (Ω := Ω) τ
      · simp [hxstrip, hx]
      · simp [hxstrip]
    exact hIndicatorEq.trans <|
      (Filter.EventuallyEq.of_eq
        (MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator
          (H := (Ks n : Process)) (τ := τ))).symm
  -- Proof comment: each stopped simple stage is exactly the strip-map image of the ambient
  -- approximant, so the continuity limit is the desired stopped-sequence limit.
  simpa [hStageEq] using hStripTendsto

/-- Helper for Lemma 25.13: a predictable simple stage vanishes after the last time of a chosen
predictable-step representation. -/
private theorem predictableSimpleProcess_eq_zero_of_last_lt_local
    {ℱ : TimeFiltration}
    (K : MeasureTheory.PredictableSimpleProcess ℱ) :
    ∃ T : NNReal, ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → (K : Process) t ω = 0 := by
  classical
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  refine ⟨representation.times (Fin.last representation.n), ?_⟩
  intro t ω ht
  have hRepresentation :
      (K : Process) = representation.toProcess :=
    Classical.choose_spec (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  -- Proof comment: the chosen predictable-step representation is identically zero after its last
  -- partition time, so the original simple stage is zero there as well.
  simpa [hRepresentation] using representation.toProcess_eq_zero_of_last_lt ht ω

/-- Helper for Lemma 25.13: once a process already vanishes after time `T`, stopping at `τ`
agrees with stopping at the bounded time `min τ T`. -/
private theorem processBeforeStoppingTime_eq_min_const_of_vanishesAfter_local
    {H : Process} {τ : Ω → ENNReal} {T : NNReal}
    (hzero : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → H t ω = 0) :
    ProbabilityTheory.processBeforeStoppingTime H τ =
      ProbabilityTheory.processBeforeStoppingTime H (fun ω ↦ min (τ ω) (T : ENNReal)) := by
  funext t ω
  by_cases htT : t ≤ T
  · by_cases hτt : (t : ENNReal) ≤ τ ω
    · have hτmin : (t : ENNReal) ≤ min (τ ω) (T : ENNReal) := by
        refine le_min hτt ?_
        exact_mod_cast htT
      -- Proof comment: before time `T`, the deterministic cap is inactive, so both cutoffs keep
      -- the same value of `H`.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτt, hτmin]
    · have hτmin : ¬ (t : ENNReal) ≤ min (τ ω) (T : ENNReal) := by
        intro h
        exact hτt (le_trans h (min_le_left _ _))
      -- Proof comment: if `t` already lies beyond `τ`, both stopped processes vanish.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτt, hτmin]
  · have htT' : T < t := lt_of_not_ge htT
    have hzero' : H t ω = 0 := hzero htT'
    have hτmin : ¬ (t : ENNReal) ≤ min (τ ω) (T : ENNReal) := by
      intro h
      apply not_le_of_gt htT'
      exact ENNReal.coe_le_coe.mp (le_trans h (min_le_right _ _))
    by_cases hτt : (t : ENNReal) ≤ τ ω
    · -- Proof comment: past time `T`, the process is already zero, so the extra `τ`-branch does
      -- not matter.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτt, hτmin, hzero']
    · -- Proof comment: if `t` is beyond both cutoffs, both stopped processes vanish trivially.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hτt, hτmin]

/-- Helper for Lemma 25.13: stopping a predictable simple stage should already lie in the
realized closure `\overline{\mathcal E}`. -/
private theorem predictableSimpleStopped_memPredictable_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (ProbabilityTheory.processBeforeStoppingTime ((K : Process)) τ) := by
  have hProg :
      ProgMeasurable ℱ
        (ProbabilityTheory.processBeforeStoppingTime ((K : Process)) τ) :=
    processBeforeStoppingTime_progMeasurable
      (Ω := Ω) (ℱ := ℱ) (H := (K : Process))
      K.isPredictable.progMeasurable hτ
  have hStopped_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime ((K : Process)) τ))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
    let strip : Set (Ω × ℝ) := stoppingStrip_local (Ω := Ω) τ
    have hIndicator :
        MemLp
          (Set.indicator strip (MeasureTheory.processToTimeSpaceFun ((K : Process))))
          (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
      hK.indicator (measurableSet_stoppingStrip_local (Ω := Ω) (ℱ := ℱ) (τ := τ) hτ)
    -- Proof comment: the stopped time-space representative is exactly the common strip
    -- indicator of the original predictable simple stage.
    simpa [strip, stoppingStrip_local,
      MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator] using
      hIndicator
  -- Proof comment: the local closure-membership criterion closes the simple-stage stopping lemma
  -- once progressive measurability and the inherited `L²(μ ⊗ dt)` bound are in place.
  exact
    MeasureTheory.progMeasurable_memPredictableStepProcessClosure ℱ μ hProg hStopped_memLp

namespace MeasureTheory.MemPredictableStepProcessClosure

/-- Helper for Lemma 25.13: stopping a closure member preserves the ambient `L²(μ ⊗ dt)` bound
because the stopped time-space representative is a measurable strip indicator of the original
representative. -/
theorem processBeforeStoppingTime_memLp_local
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Process}
    (hH : MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime H τ))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  rcases hH with ⟨hH_memLp, _hhH_closure⟩
  let strip : Set (Ω × ℝ) := {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ τ x.1}
  have hstrip : MeasurableSet strip := by
    -- Proof comment: the stopping strip is measurable because both time coordinates are
    -- measurable on `Ω × ℝ`.
    refine measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd) ?_
    exact hτ.measurable'.comp measurable_fst
  have hIndicator :
      MemLp
        (Set.indicator strip (MeasureTheory.processToTimeSpaceFun H))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    hH_memLp.indicator hstrip
  -- Proof comment: rewrite the stopped time-space representative to the strip indicator and reuse
  -- the inherited `L²` bound.
  simpa [strip, MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator] using
    hIndicator

/-- Helper for Lemma 25.13: deterministic-time cutoff preserves the canonical closure because the
closure-side cutoff operator already acts on ambient `L²(μ ⊗ dt)`. -/
theorem processBeforeStoppingTime_const
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Process}
    (hH : MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) := by
  rcases hH with ⟨hH_memLp, hhH_closure⟩
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    ⟨hH_memLp.toLp (MeasureTheory.processToTimeSpaceFun H), hhH_closure⟩
  let hStopped_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    processBeforeStoppingTime_memLp_local ⟨hH_memLp, hhH_closure⟩
      (isStoppingTime_const ℱ t)
  refine ⟨hStopped_memLp, ?_⟩
  have hEq :
      hStopped_memLp.toLp
          (MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal))) =
        ((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hbar :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) := by
    have hEqAE :
        Filter.EventuallyEq
          (MeasureTheory.ae (MeasureTheory.processMeasure μ))
          (MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)))
          ((((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hbar :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) := by
      -- Proof comment: compare both ambient `L²(μ ⊗ dt)` representatives through the same
      -- deterministic strip indicator on `Ω × ℝ`.
      have hStoppedEq :
          Filter.EventuallyEq
            (MeasureTheory.ae (MeasureTheory.processMeasure μ))
            (MeasureTheory.processToTimeSpaceFun
              (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)))
            (Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ (t : ENNReal)}
              (MeasureTheory.processToTimeSpaceFun H)) := by
        let hEq :
            MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) =
              Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ (t : ENNReal)}
                (MeasureTheory.processToTimeSpaceFun H) :=
          MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator
        exact Filter.EventuallyEq.of_eq hEq
      have hIndicatorEq :
          Filter.EventuallyEq
            (MeasureTheory.ae (MeasureTheory.processMeasure μ))
            (Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ (t : ENNReal)}
              (MeasureTheory.processToTimeSpaceFun H))
            (Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
              (MeasureTheory.processToTimeSpaceFun H)) := by
        exact Filter.EventuallyEq.of_eq <| by
          funext x
          by_cases hxt : x.2 ≤ (t : ℝ)
          · have hxt' : x.2.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hxt
            simp [Set.indicator_of_mem, hxt, hxt', MeasureTheory.processToTimeSpaceFun]
          · have hxt' : ¬ x.2.toNNReal ≤ t := by
              intro hx
              exact hxt (Real.toNNReal_le_iff_le_coe.1 hx)
            simp [Set.indicator_of_notMem, hxt, hxt', MeasureTheory.processToTimeSpaceFun]
      have hLpEq :
          Filter.EventuallyEq
            (MeasureTheory.ae (MeasureTheory.processMeasure μ))
            (Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
              (MeasureTheory.processToTimeSpaceFun H))
            (Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
              (((Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) := by
        filter_upwards [(MeasureTheory.MemLp.coeFn_toLp hH_memLp).symm] with x hx
        by_cases hxt : x.2 ≤ (t : ℝ)
        · simpa [Set.indicator_of_mem, hxt, Hbar] using hx
        · simp [Set.indicator_of_notMem, hxt]
      have hCutEq :
          Filter.EventuallyEq
            (MeasureTheory.ae (MeasureTheory.processMeasure μ))
            (Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
              (((Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ))
            ((((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hbar :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) := by
        exact
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn
            t Hbar).symm
      exact hStoppedEq.trans <| hIndicatorEq.trans <| hLpEq.trans hCutEq
    simpa using
      (MeasureTheory.MemLp.toLp_eq_toLp_iff hStopped_memLp
        (Lp.memLp
          (((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hbar :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))).2 hEqAE
  -- Proof comment: once the deterministic cutoff representative is identified with the stopped
  -- process, closure membership follows from the cutoff operator's codomain.
  exact hEq ▸ (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hbar).2

/-- Helper for Lemma 25.13: deterministic cutoff on the realized closure agrees with the closure
point of the deterministically stopped integrand. -/
theorem cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Process}
    (hH : MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (processBeforeStoppingTime_const hH t) := by
  -- Proof comment: compare both closure points through their ambient `L²(μ ⊗ dt)`
  -- representatives, where both sides are the same deterministic strip cutoff of `H`.
  apply Subtype.ext
  rw [MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure]
  apply Lp.ext
  have hLeftIndicator :
      ((((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t hH.toClosure :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[
            MeasureTheory.processMeasure μ]
        Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
          (fun x ↦
            (((hH.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) x)) :=
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn t hH.toClosure
  have hClosureCoe :
      (fun x ↦
        (((hH.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)) x)) =ᵐ[
          MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun H := by
    simpa [MeasureTheory.MemPredictableStepProcessClosure.toClosure] using
      (MeasureTheory.MemLp.coeFn_toLp hH.memLp)
  have hLeftEq :
      ((((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t hH.toClosure :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[
            MeasureTheory.processMeasure μ]
        Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
          (MeasureTheory.processToTimeSpaceFun H) := by
    refine hLeftIndicator.trans ?_
    filter_upwards [hClosureCoe] with x hx
    by_cases hxt : x.2 ≤ (t : ℝ)
    · simpa [Set.indicator_of_mem, hxt,
        MeasureTheory.MemPredictableStepProcessClosure.toClosure] using hx
    · simp [Set.indicator_of_notMem, hxt]
  have hIndicatorEq :
      Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ (t : ENNReal)}
          (MeasureTheory.processToTimeSpaceFun H) =ᵐ[MeasureTheory.processMeasure μ]
        Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
          (MeasureTheory.processToTimeSpaceFun H) := by
    exact Filter.EventuallyEq.of_eq <| by
      funext x
      by_cases hxt : x.2 ≤ (t : ℝ)
      · have hxt' : x.2.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hxt
        simp [Set.indicator_of_mem, hxt, hxt', MeasureTheory.processToTimeSpaceFun]
      · have hxt' : ¬ x.2.toNNReal ≤ t := by
          intro hx
          exact hxt (Real.toNNReal_le_iff_le_coe.1 hx)
        simp [Set.indicator_of_notMem, hxt, hxt', MeasureTheory.processToTimeSpaceFun]
  have hStoppedEq :
      MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) =ᵐ[
            MeasureTheory.processMeasure μ]
        Set.indicator {x : Ω × ℝ | ENNReal.ofReal x.2 ≤ (t : ENNReal)}
          (MeasureTheory.processToTimeSpaceFun H) :=
    Filter.EventuallyEq.of_eq
      (MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator
        (H := H) (τ := fun _ ↦ (t : ENNReal)))
  have hRightEq :
      Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)}
          (MeasureTheory.processToTimeSpaceFun H) =ᵐ[MeasureTheory.processMeasure μ]
        ((((MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (processBeforeStoppingTime_const hH t) :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) := by
    have hStoppedToLp :
        MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) =ᵐ[
              MeasureTheory.processMeasure μ]
          ((((MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (processBeforeStoppingTime_const hH t) :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) := by
      simpa [MeasureTheory.MemPredictableStepProcessClosure.toClosure] using
        (MeasureTheory.MemLp.coeFn_toLp
          (MeasureTheory.MemPredictableStepProcessClosure.memLp
            (processBeforeStoppingTime_const hH t))).symm
    exact hIndicatorEq.symm.trans <| hStoppedEq.symm.trans hStoppedToLp
  exact hLeftEq.trans hRightEq

/-- Helper for Lemma 25.13: the canonical closure class of an admissible integrand should stay in
`\overline{\mathcal E}` after cutting off the integrand before a stopping time. -/
theorem processBeforeStoppingTime
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Process}
    (hH : MeasureTheory.MemPredictableStepProcessClosure ℱ μ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (ProbabilityTheory.processBeforeStoppingTime H τ) := by
  -- Route correction: after importing the canonical Theorem 25.9 bridge, the stopping proof only
  -- needs to transport a predictable-simple `L²` approximation through the fixed stopping-strip
  -- map in ambient `L²(μ ⊗ dt)`.
  have hStopped_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime H τ))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    processBeforeStoppingTime_memLp_local (Ω := Ω) (ℱ := ℱ) (μ := μ) hH hτ
  refine ⟨hStopped_memLp, ?_⟩
  rcases
      MeasureTheory.existsPredictableSimpleApproximationOfClosurePointLocal
        (Ω := Ω) (ℱ := ℱ) (μ := μ)
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) with
    ⟨Ks, hKs_mem, hKs_tendsto⟩
  have hKsStopped :
      ∀ n,
        MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime ((Ks n : Process)) τ) := by
    intro n
    -- Proof comment: this is the remaining source-facing simple-stage stopping lemma.
    exact
      predictableSimpleStopped_memPredictable_local
        (Ω := Ω) (ℱ := ℱ) (μ := μ) (K := Ks n) (hK := hKs_mem n) (hτ := hτ)
  have hStoppedTendsto :
      Filter.Tendsto
        (fun n ↦ (((MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)) :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)))
        Filter.atTop
        (nhds
          (stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
            (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hH :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))) := by
    -- Proof comment: once the simple stages are stopped inside the closure owner, the ambient
    -- strip operator carries the original approximation to the stopped limit.
    have hAmbient :
        Filter.Tendsto
          (fun n ↦
            (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ))))
          Filter.atTop
          (nhds
            (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hH :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
      exact tendsto_subtype_rng.1 hKs_tendsto
    have hStripTendsto :
        Filter.Tendsto
          (fun n ↦
            stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
              (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                  Lp ℝ 2 (MeasureTheory.processMeasure μ))))
          Filter.atTop
          (nhds
            (stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
              (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hH :
                    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ))))) := by
      exact
        ((stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ).continuous.tendsto _)
          .comp hAmbient
    have hStageEq :
        ∀ n,
          stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
              (((MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n) :
                    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                  Lp ℝ 2 (MeasureTheory.processMeasure μ))) =
            (((MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)) :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)) := by
      intro n
      let hStage :
          MeasureTheory.MemPredictableStepProcessClosure ℱ μ ((Ks n : Process)) :=
        ⟨hKs_mem n, (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)).2⟩
      simpa [hStage, MeasureTheory.MemPredictableStepProcessClosure.toClosure] using
        (stoppingStripLpMap_apply_toClosure_local
          (Ω := Ω) (ℱ := ℱ) (μ := μ) (τ := τ) (hτ := hτ) (hK := hStage))
    simpa [hStageEq] using hStripTendsto
  have hLimitMem :
      stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
          (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hH :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ))) ∈
        MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ := by
    refine
      (Submodule.isClosed_topologicalClosure
        (MeasureTheory.predictableSimpleProcessL2 ℱ μ)).mem_of_tendsto hStoppedTendsto ?_
    exact Filter.Eventually.of_forall fun n ↦
      (((MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)) :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)).2
  have hMapEq :
      stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := τ) hτ
          (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hH :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ))) =
        hStopped_memLp.toLp
          (MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H τ)) := by
    -- Proof comment: the ambient strip map is exactly the `L²(μ ⊗ dt)` class of the stopped
    -- process, so the closed limit above is the desired closure witness.
    simpa [hStopped_memLp] using
      (stoppingStripLpMap_apply_toClosure_local
        (Ω := Ω) (ℱ := ℱ) (μ := μ) (τ := τ) (hτ := hτ) (hK := hH))
  rw [hMapEq] at hLimitMem
  exact hLimitMem

end MeasureTheory.MemPredictableStepProcessClosure

/-- Helper for Lemma 25.13: stopping before a random time `τ` and then before a deterministic
time `t` agrees with performing the two cutoffs in the opposite order. -/
theorem processBeforeStoppingTime_const_comm
    (G : Process) (τ : Ω → ENNReal) (t : NNReal) :
    processBeforeStoppingTime (processBeforeStoppingTime G τ) (fun _ ↦ (t : ENNReal)) =
      processBeforeStoppingTime (processBeforeStoppingTime G fun _ ↦ (t : ENNReal)) τ := by
  -- Proof comment: both sides keep `G s ω` exactly on the region where `s ≤ τ ω` and `s ≤ t`.
  funext s ω
  by_cases hsτ : (s : ENNReal) ≤ τ ω
  · by_cases hst : (s : ENNReal) ≤ (t : ENNReal)
    · simp [processBeforeStoppingTime_apply, hsτ, hst]
    · simp [processBeforeStoppingTime_apply, hsτ, hst]
  · by_cases hst : (s : ENNReal) ≤ (t : ENNReal)
    · simp [processBeforeStoppingTime_apply, hsτ, hst]
    · simp [processBeforeStoppingTime_apply, hsτ, hst]

/-- Helper for Lemma 25.13: applying the same deterministic cutoff twice is idempotent. -/
theorem processBeforeStoppingTime_const_idem
    (G : Process) (t : NNReal) :
    processBeforeStoppingTime
        (processBeforeStoppingTime G fun _ ↦ (t : ENNReal))
        (fun _ ↦ (t : ENNReal)) =
      processBeforeStoppingTime G fun _ ↦ (t : ENNReal) := by
  -- Proof comment: both sides keep `G s ω` exactly on the region `s ≤ t`.
  ext s ω
  by_cases hst : (s : ENNReal) ≤ (t : ENNReal)
  · simp [processBeforeStoppingTime_apply, hst]
  · simp [processBeforeStoppingTime_apply, hst]

/-- Helper for Lemma 25.13: if a random stop stays below the deterministic horizon `T`, then
stopping `H 1_[0,T]` again at that random stop gives the direct stopped integrand. -/
private theorem processBeforeStoppingTime_constStage_eq_randomCutoff_local
    {H : Process} {σ : Ω → ENNReal} {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal)) :
    processBeforeStoppingTime
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        σ =
      processBeforeStoppingTime H σ := by
  -- Proof comment: on the active branch `s ≤ σ ω`, the bound `σ ω ≤ T` forces `s ≤ T`, so the
  -- outer deterministic cutoff does not change the value.
  funext s ω
  by_cases hsσ : (s : ENNReal) ≤ σ ω
  · have hsT : (s : ENNReal) ≤ (T : ENNReal) := le_trans hsσ (hσ_le ω)
    simp [processBeforeStoppingTime_apply, hsσ, hsT]
  · simp [processBeforeStoppingTime_apply, hsσ]

/-- Helper for Lemma 25.13: literal equality of admissible integrands identifies their canonical
closure points. -/
private theorem toClosure_eq_of_process_eq_local
    {H G : Process}
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hEq : H = G) :
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hG := by
  -- Proof comment: compare the two closure points via their ambient `L²(μ ⊗ dt)` classes, where
  -- the process equality is explicit.
  apply Subtype.ext
  change
    hH.memLp.toLp (MeasureTheory.processToTimeSpaceFun H) =
      hG.memLp.toLp (MeasureTheory.processToTimeSpaceFun G)
  exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hH.memLp hG.memLp).2 <|
    Filter.EventuallyEq.of_eq <| by
      simpa [MeasureTheory.processToTimeSpaceFun, hEq]

/-- Helper for Lemma 25.13: time-space almost-everywhere equality identifies the corresponding
canonical closure points. -/
private theorem toClosure_eq_of_timeSpaceFun_aeEq_local
    {H G : Process}
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hEq :
      MeasureTheory.processToTimeSpaceFun H =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun G) :
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hG := by
  -- Proof comment: compare the two closure points directly in the ambient `L²(μ ⊗ dt)` quotient,
  -- where boundary-sensitive cutoff representatives naturally live.
  apply Subtype.ext
  exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hH.memLp hG.memLp).2 hEq

/-- Helper for Lemma 25.13: stopping before the same stopping time preserves time-space
almost-everywhere equality of process representatives. -/
private theorem processBeforeStoppingTime_timeSpaceFun_aeEq_local
    {H G : Process} {τ : Ω → ENNReal}
    (hEq :
      MeasureTheory.processToTimeSpaceFun H =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun G) :
    MeasureTheory.processToTimeSpaceFun (processBeforeStoppingTime H τ) =ᵐ[MeasureTheory.processMeasure μ]
      MeasureTheory.processToTimeSpaceFun (processBeforeStoppingTime G τ) := by
  -- Proof comment: both stopped representatives are cut out by the same stopping strip
  -- indicator, so the common indicator preserves the given almost-everywhere equality.
  rw [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
    MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator]
  filter_upwards [hEq] with x hx
  by_cases hxstrip : ENNReal.ofReal x.2 ≤ τ x.1
  · simp [Set.indicator_of_mem, hxstrip, hx]
  · simp [Set.indicator_of_notMem, hxstrip]

/-- Helper for Lemma 25.13: if a stopping time dominates the deterministic horizon `t` almost
surely, then cutting first at that random stop and then again at `t` gives the same ambient
`L²(μ ⊗ dt)` class as the direct deterministic cutoff `H 1_[0,t]`. -/
private theorem deterministicCutoff_after_randomCutoff_toClosure_eq_of_ae_le_local
    {H : Process} {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    {t : NNReal}
    (hτ_dom : ∀ᵐ ω ∂μ, (t : ENNReal) ≤ τ ω)
    (hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ))
    (hCut : MemPredictableStepProcessClosure ℱ μ
      (processBeforeStoppingTime H fun _ ↦ (t : ENNReal))) :
    MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t)) =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hCut := by
  let B : Set Ω := {ω | ¬ (t : ENNReal) ≤ τ ω}
  have hTimeSpaceEq :
      MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime (processBeforeStoppingTime H τ) fun _ ↦ (t : ENNReal)) =ᵐ[
            MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun
          (processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) := by
    have hB_meas : MeasurableSet B := (hτ.measurableSet_ge t).compl
    have hμB : μ B = 0 := by
      rw [ae_iff] at hτ_dom
      simpa [B] using hτ_dom
    have hBadNull :
        MeasureTheory.processMeasure μ ({x : Ω × ℝ | x.1 ∈ B}) = 0 := by
      have hSetEq : {x : Ω × ℝ | x.1 ∈ B} = B ×ˢ (Set.univ : Set ℝ) := by
        ext x
        simp
      simp [hSetEq, MeasureTheory.processMeasure, hμB, hB_meas]
    have hGood :
        ∀ᵐ x ∂MeasureTheory.processMeasure μ, x.1 ∉ B := by
      rw [ae_iff]
      simpa using hBadNull
    filter_upwards [hGood] with x hxGood
    rcases x with ⟨ω, s⟩
    have hgood : (t : ENNReal) ≤ τ ω := by
      simpa [B] using hxGood
    have hs_eq : (((s.toNNReal : NNReal) : ENNReal)) = ENNReal.ofReal s := by
      by_cases hs_nonneg : 0 ≤ s
      · rw [Real.toNNReal_of_nonneg hs_nonneg, ENNReal.ofReal_eq_coe_nnreal]
      · have hs_nonpos : s ≤ 0 := le_of_not_ge hs_nonneg
        rw [Real.toNNReal_of_nonpos hs_nonpos]
        simp [ENNReal.ofReal_eq_zero.mpr hs_nonpos]
    by_cases hst : ENNReal.ofReal s ≤ (t : ENNReal)
    · have hsτ : ENNReal.ofReal s ≤ τ ω := le_trans hst hgood
      have hst' : (((s.toNNReal : NNReal) : ENNReal)) ≤ (t : ENNReal) := by
        simpa [hs_eq] using hst
      have hsτ' : (((s.toNNReal : NNReal) : ENNReal)) ≤ τ ω := by
        simpa [hs_eq] using hsτ
      -- Proof comment: on the good event `t ≤ τ ω`, the extra random cutoff is inactive on the
      -- whole deterministic strip `{s ≤ t}`.
      simp [MeasureTheory.processToTimeSpaceFun, processBeforeStoppingTime_apply, hst', hsτ']
    · -- Proof comment: outside the deterministic strip `{s ≤ t}`, both cutoffs are already `0`.
      have hst' : ¬ (((s.toNNReal : NNReal) : ENNReal)) ≤ (t : ENNReal) := by
        simpa [hs_eq] using hst
      have hLeftZero :
          MeasureTheory.processToTimeSpaceFun
              (processBeforeStoppingTime (processBeforeStoppingTime H τ) fun _ ↦ (t : ENNReal))
              (ω, s) = 0 := by
        change processBeforeStoppingTime (processBeforeStoppingTime H τ) (fun _ ↦ (t : ENNReal))
            s.toNNReal ω = 0
        simpa [processBeforeStoppingTime_apply, hst']
      have hRightZero :
          MeasureTheory.processToTimeSpaceFun
              (processBeforeStoppingTime H fun _ ↦ (t : ENNReal))
              (ω, s) = 0 := by
        change processBeforeStoppingTime H (fun _ ↦ (t : ENNReal)) s.toNNReal ω = 0
        simpa [processBeforeStoppingTime_apply, hst']
      rw [hLeftZero, hRightZero]
  -- Proof comment: the two closure witnesses represent the same ambient `L²(μ ⊗ dt)` class.
  exact
    toClosure_eq_of_timeSpaceFun_aeEq_local
      (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t))
      hCut
      hTimeSpaceEq

/-- Helper for Lemma 25.13: the Brownian Itô integral up to a stopping time uses the fixed-time
truncated process on `{τ < ∞}` and the terminal Brownian Itô integral on `{τ = ∞}`. -/
noncomputable def brownianItoIntegralStoppedValue
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (τ : Ω → ENNReal) : Ω → ℝ :=
  fun ω ↦
    if τ ω = ∞ then
      hIto.toContinuousLinearMap H ω
    else
      brownianItoIntegralTruncatedProcess W H (τ ω).toNNReal ω

/-- Helper for Lemma 25.13: `brownianItoIntegralStoppedValue` unfolds to the finite/terminal case
split from the source statement. -/
@[simp] theorem brownianItoIntegralStoppedValue_apply
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (τ : Ω → ENNReal) (ω : Ω) :
    brownianItoIntegralStoppedValue W H τ ω =
      if τ ω = ∞ then
        hIto.toContinuousLinearMap H ω
      else
        brownianItoIntegralTruncatedProcess W H (τ ω).toNNReal ω :=
  rfl

/-- Helper for Lemma 25.13: at a deterministic finite time, the stopped Brownian Itô integral is
just the truncated Brownian Itô process value at that time. -/
@[simp] theorem brownianItoIntegralStoppedValue_const
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (t : NNReal) :
    brownianItoIntegralStoppedValue W H (fun _ ↦ (t : ENNReal)) =
      brownianItoIntegralTruncatedProcess W H t := by
  funext ω
  simp [brownianItoIntegralStoppedValue]

/-- Helper for Lemma 25.13: at the terminal stopping time `∞`, the stopped Brownian Itô integral
is the terminal Brownian Itô integral. -/
@[simp] theorem brownianItoIntegralStoppedValue_top
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    brownianItoIntegralStoppedValue W H (fun _ ↦ ∞) =
      hIto.toContinuousLinearMap H := by
  funext ω
  simp [brownianItoIntegralStoppedValue]

/-- Helper for Lemma 25.13: on the finite branch of a stopping time, the raw stopped Brownian
Itô value is just the usual stopped value of the deterministic truncation process. -/
private lemma untopA_eq_toNNReal_of_ne_top_local
    {a : ENNReal} (ha : a ≠ ∞) :
    a.untopA = a.toNNReal := by
  lift a to NNReal using ha with b
  have hne : (b : ENNReal) ≠ ∞ := by
    simp
  rw [WithTop.untopA_eq_untop hne]
  exact ENNReal.coe_inj.mp (WithTop.coe_untop (b : ENNReal) hne)

/-- Helper for Lemma 25.13: on the finite branch of a stopping time, the raw stopped Brownian
Itô value is just the usual stopped value of the deterministic truncation process. -/
private theorem brownianItoIntegralStoppedValue_eq_stoppedValue_of_ne_top_local
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {τ : Ω → ENNReal}
    (hτ_fin : ∀ ω, τ ω ≠ ∞) :
    brownianItoIntegralStoppedValue W H τ =
      MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W H) τ := by
  funext ω
  -- Proof comment: once `τ ω` is finite, both owners evaluate the same truncation slice at the
  -- same `NNReal` time.
  have htime : (τ ω).toNNReal = (τ ω).untopA :=
    (untopA_eq_toNNReal_of_ne_top_local (hτ_fin ω)).symm
  simpa [brownianItoIntegralStoppedValue, MeasureTheory.stoppedValue, hτ_fin ω, htime]

/-- Helper for Lemma 25.13: after capping by a deterministic horizon `T`, the raw stopped
Brownian-Itô owner is exactly the sampled truncation process because the stop is finite. -/
private theorem brownianStoppedValue_eq_stoppedValue_on_boundedMin_local
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal}
    (T : NNReal) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    brownianItoIntegralStoppedValue W Hbar β =
      MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) β := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  -- Proof comment: the deterministic cap by `T` removes the `∞` branch from the raw stopped
  -- value, so both owners sample the same truncation time pointwise.
  exact
    brownianItoIntegralStoppedValue_eq_stoppedValue_of_ne_top_local
      (W := W) (H := Hbar) (τ := β)
      (fun ω ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

/-- Helper for Lemma 25.13: on the finite branch of a stopping time, the sampled martingale owner
is the deterministic martingale slice at the sampled `NNReal` time. -/
private theorem martingaleSampledOwner_apply_eq_martingaleSlice_of_ne_top_local
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (W : Process)
    [BrownianItoIntegral μ ℱ W]
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal} {ω : Ω}
    (hσ_fin : σ ω ≠ ∞) :
    (if σ ω = ∞ then
      hIto.toContinuousLinearMap Hbar ω
    else
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) Hbar)
        σ ω) =
      BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) Hbar (σ ω).toNNReal ω := by
  have htime : (σ ω).toNNReal = (σ ω).untopA :=
    (untopA_eq_toNNReal_of_ne_top_local hσ_fin).symm
  -- Proof comment: once `σ ω` is finite, the sampled martingale owner is just the deterministic
  -- martingale slice at the sampled time `(σ ω).toNNReal`.
  simp [MeasureTheory.stoppedValue, hσ_fin, htime]

/-- Helper for Lemma 25.13: for a deterministic stopping time, the stopped Brownian Itô value is
the terminal Brownian Itô map of the deterministic cutoff closure point. -/
theorem stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    Filter.EventuallyEq
      (MeasureTheory.ae μ)
      (brownianItoIntegralStoppedValue W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH)
        (fun _ ↦ (t : ENNReal)))
      (hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hH t))) := by
  -- Proof comment: normalize the deterministic stopped value to the truncated Brownian-Itô
  -- process, then rewrite the cutoff closure by the deterministic-time owner theorem.
  refine Filter.EventuallyEq.of_eq ?_
  calc
    brownianItoIntegralStoppedValue W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH)
        (fun _ ↦ (t : ENNReal)) =
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t := by
          simpa using brownianItoIntegralStoppedValue_const
            W (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t
    _ =
        hIto.toContinuousLinearMap
          (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH)) := by
            rfl
    _ =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hH t)) := by
            rw [MeasureTheory.MemPredictableStepProcessClosure
              .cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst hH t]

/-- Helper for Lemma 25.13: a bounded stopping time admits dyadic ceiling approximants with
countable range that dominate the stopping time and converge pointwise back to it. -/
private theorem exists_dyadicApproximation_of_boundedStoppingTime
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (T : NNReal)
    (hτ_le : ∀ ω, τ ω ≤ T) :
    ∃ τm : ℕ → Ω → ENNReal,
      (∀ m, IsStoppingTime ℱ (τm m)) ∧
      (∀ m, (Set.range (τm m)).Countable) ∧
      (∀ m ω, τ ω ≤ τm m ω) ∧
      (∀ ω, Filter.Tendsto (fun m ↦ τm m ω) Filter.atTop (nhds (τ ω))) := by
  have hτ_fin : ∀ ω, τ ω ≠ ∞ := fun ω ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hτ_le ω)
  let τNN : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (τ ω)
  have hτ_eq : (fun ω ↦ (τNN ω : ENNReal)) = τ := by
    -- Proof comment: the uniform finite bound lets us recover the `ENNReal` stopping time from
    -- its `NNReal` representative without losing the value at any sample point.
    funext ω
    simp [τNN, ENNReal.coe_toNNReal, hτ_fin ω]
  have hτNN : IsStoppingTime ℱ (fun ω ↦ (τNN ω : ENNReal)) := by
    rw [hτ_eq]
    exact hτ
  let τm : ℕ → Ω → ENNReal := fun m ω ↦ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal)
  refine ⟨τm, ?_, ?_, ?_, ?_⟩
  · intro m
    -- Proof comment: each dyadic ceiling approximation stays inside the stopping-time owner.
    simpa [τm] using dyadicCeilApprox_isStoppingTime hτNN m
  · intro m
    -- Proof comment: every dyadic stage only takes values in one fixed dyadic mesh.
    simpa [τm] using ProbabilityTheory.dyadicCeilApprox_countableRange m τNN
  · intro m ω
    -- Proof comment: dyadic ceilings dominate the original finite stopping time pointwise.
    let c : NNReal := (2 : NNReal) ^ m
    have hc_pos : 0 < c := by
      -- Proof comment: the dyadic scale is strictly positive.
      dsimp [c]
      positivity
    have hceil :
        c * τNN ω ≤ (Nat.ceil (((c * τNN ω : NNReal) : ℝ)) : NNReal) := by
      exact_mod_cast Nat.le_ceil (((c * τNN ω : NNReal) : ℝ))
    have hleNN :
        τNN ω ≤ ProbabilityTheory.dyadicCeilApprox m τNN ω := by
      rw [ProbabilityTheory.dyadicCeilApprox, div_eq_mul_inv]
      rw [le_mul_inv_iff₀ hc_pos]
      simpa [c, mul_assoc, mul_left_comm, mul_comm] using hceil
    have hτ_eqω : (τNN ω : ENNReal) = τ ω := by
      simpa [τNN, hτ_fin ω] using (ENNReal.coe_toNNReal (hτ_fin ω))
    have hle : (τNN ω : ENNReal) ≤ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal) := by
      exact_mod_cast hleNN
    simpa [τm] using le_trans hτ_eqω.symm.le hle
  · intro ω
    -- Proof comment: after passing to the finite `NNReal` representative, the Chapter 21 dyadic
    -- approximation converges back to the original bounded stopping time.
    have hTendsto :
        Filter.Tendsto
          (fun m ↦ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal))
          Filter.atTop
          (nhds ((τNN ω : NNReal) : ENNReal)) :=
      (continuous_coe.tendsto (τNN ω)).comp
        (ProbabilityTheory.dyadicCeilApprox_tendsto τNN ω)
    have hτ_eqω : (τNN ω : ENNReal) = τ ω := by
      simpa [τNN, hτ_fin ω] using (ENNReal.coe_toNNReal (hτ_fin ω))
    simpa [τm, hτ_eqω] using hTendsto

/-- Helper for Lemma 25.13: every finite dyadic ceiling approximation already lies on the dyadic
mesh of level `n`. -/
private theorem dyadicCeilApprox_meshWitness_local
    (n : ℕ) (ρ : Ω → NNReal) (ω : Ω) :
    ∃ k : ℕ,
      ((ProbabilityTheory.dyadicCeilApprox n ρ ω : NNReal) : ENNReal) =
        (((k : NNReal) / ((2 : NNReal) ^ n)) : ENNReal) := by
  -- Proof comment: unfold the dyadic ceiling definition and read off the mesh numerator from the
  -- ceiling integer itself.
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * ρ ω : NNReal) : ℝ), ?_⟩
  simp [ProbabilityTheory.dyadicCeilApprox]

/-- Helper for Lemma 25.13: an arbitrary stopping time admits dyadic ceiling approximants whose
finite branch is the Chapter 21 dyadic ceiling of `ENNReal.toNNReal τ`, while the `∞` branch is
kept fixed. -/
private theorem existsDyadicApproximationOfStoppingTime_local
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    ∃ τm : ℕ → Ω → ENNReal,
      (∀ m, IsStoppingTime ℱ (τm m)) ∧
      (∀ m, (Set.range (τm m)).Countable) ∧
      (∀ m ω, τ ω ≤ τm m ω) ∧
      (∀ m ω, τm m ω = ∞ ↔ τ ω = ∞) ∧
      (∀ m ω, τm m ω = ∞ ∨
        ∃ k : ℕ, τm m ω = (((k : NNReal) / ((2 : NNReal) ^ m)) : ENNReal)) ∧
      (∀ ω, Filter.Tendsto (fun m ↦ τm m ω) Filter.atTop (nhds (τ ω))) := by
  let τNN : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (τ ω)
  let τm : ℕ → Ω → ENNReal := fun m ω ↦
    if htop : τ ω = ∞ then
      ∞
    else
      (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal)
  refine ⟨τm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    intro t
    let q : NNReal :=
      (Nat.floor ((((2 : NNReal) ^ m) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ m)
    have hEvent :
        {ω | τm m ω ≤ t} = {ω | τ ω ≤ q} := by
      ext ω
      by_cases htop : τ ω = ∞
      · -- Proof comment: on the `∞` branch, both stopping events are false at any finite level.
        have hLeft : ¬ τm m ω ≤ t := by
          simp [τm, htop]
        have hRight : ¬ τ ω ≤ q := by
          simpa [htop] using
            (show ¬ ((∞ : ENNReal) ≤ (q : ENNReal)) from by simp)
        simp [hLeft, hRight]
      · have hDyadic :
          ((ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal) ≤ t) ↔
            ((τNN ω : ENNReal) ≤ q) := by
          simpa [Set.mem_setOf_eq, q] using
            congrArg (fun s : Set Ω ↦ ω ∈ s)
              (ProbabilityTheory.dyadicCeilApprox_event_le_eq (Ω := Ω) (n := m) (τ := τNN)
                (t := t))
        have hτ_eqω : (τNN ω : ENNReal) = τ ω := by
          simpa [τNN, htop] using (ENNReal.coe_toNNReal htop)
        -- Proof comment: away from `∞`, converting `τ` to `NNReal` and back loses no
        -- information, so the dyadic event is exactly `{τ ≤ q}`.
        simpa [τm, htop, hτ_eqω] using hDyadic
    simpa [hEvent] using hτ.measurableSet_le q
  · intro m
    have hDyadicCount :
        (Set.range fun ω ↦ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal)).Countable :=
      ProbabilityTheory.dyadicCeilApprox_countableRange m τNN
    refine (hDyadicCount.insert ∞).mono ?_
    rintro _ ⟨ω, rfl⟩
    by_cases htop : τ ω = ∞
    · simp [τm, htop]
    · right
      exact ⟨ω, by simp [τm, htop]⟩
  · intro m ω
    by_cases htop : τ ω = ∞
    · simp [τm, htop]
    · have hceil :
          (2 : NNReal) ^ m * τNN ω ≤
            (Nat.ceil ((((2 : NNReal) ^ m) * τNN ω : NNReal) : ℝ) : NNReal) := by
        exact_mod_cast Nat.le_ceil ((((2 : NNReal) ^ m) * τNN ω : NNReal) : ℝ)
      have hleNN :
          τNN ω ≤ ProbabilityTheory.dyadicCeilApprox m τNN ω := by
        have hpow_pos : 0 < (2 : NNReal) ^ m := by
          positivity
        rw [ProbabilityTheory.dyadicCeilApprox, div_eq_mul_inv]
        rw [le_mul_inv_iff₀ hpow_pos]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hceil
      have hτ_eqω : (τNN ω : ENNReal) = τ ω := by
        simpa [τNN, htop] using (ENNReal.coe_toNNReal htop)
      have hle : (τNN ω : ENNReal) ≤ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal) := by
        exact_mod_cast hleNN
      simpa [τm, htop] using le_trans hτ_eqω.symm.le hle
  · intro m ω
    by_cases htop : τ ω = ∞
    · simp [τm, htop]
    · simp [τm, htop]
  · intro m ω
    by_cases htop : τ ω = ∞
    · -- Proof comment: the top branch is kept fixed by construction.
      left
      simp [τm, htop]
    · -- Proof comment: away from `∞`, the approximant is literally one dyadic mesh point.
      right
      rcases dyadicCeilApprox_meshWitness_local (n := m) (ρ := τNN) ω with ⟨k, hk⟩
      exact ⟨k, by simpa [τm, htop] using hk⟩
  · intro ω
    by_cases htop : τ ω = ∞
    · -- Proof comment: on the `∞` branch, every approximant is literally constant.
      simpa [τm, htop] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (∞ : ENNReal)) Filter.atTop (nhds ∞))
    · have hTendsto :
        Filter.Tendsto
          (fun m ↦ (ProbabilityTheory.dyadicCeilApprox m τNN ω : ENNReal))
          Filter.atTop
          (nhds ((τNN ω : NNReal) : ENNReal)) :=
        (continuous_coe.tendsto (τNN ω)).comp
          (ProbabilityTheory.dyadicCeilApprox_tendsto τNN ω)
      have hτ_eqω : (τNN ω : ENNReal) = τ ω := by
        simpa [τNN, htop] using (ENNReal.coe_toNNReal htop)
      -- Proof comment: off the `∞` branch, the approximants are the ordinary dyadic ceilings of
      -- the finite `NNReal` representative of `τ`.
      simpa [τm, htop, hτ_eqω] using hTendsto

/-- Helper for Lemma 25.13: the continuous modification from Theorem 25.11 agrees almost surely
with the concrete truncated Brownian-Itô process simultaneously on any countable family of
deterministic times. -/
private theorem continuousModification_aeEq_on_countableSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {S : Set NNReal}
    (hS : S.Countable) :
    ∀ᵐ ω ∂μ, ∀ t ∈ S,
      BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar t ω =
        brownianItoIntegralTruncatedProcess W Hbar t ω := by
  let _ : Countable S := hS.to_subtype
  have hAll :
      ∀ᵐ ω ∂μ, ∀ t : S,
        BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar t ω =
          brownianItoIntegralTruncatedProcess W Hbar t ω := by
    -- Proof comment: `continuousModification_spec` gives fixed-time equality, and `ae_all_iff`
    -- packages those countably many equalities into one full-measure event.
    rw [ae_all_iff]
    intro t
    simpa using
      (BrownianItoIntegral.continuousModification_spec
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements Hbar).2 t
  -- Proof comment: unwrap the subtype-valued quantifier back to the original set `S`.
  filter_upwards [hAll] with ω hω t ht
  exact hω ⟨t, ht⟩

/-- Helper for Lemma 25.13: use the sampled continuous modification as a common owner for the
stopped Brownian-Itô value, keeping the `∞` branch explicit. -/
noncomputable def continuousModificationSampledOwner_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (σ : Ω → ENNReal) : Ω → ℝ :=
  fun ω ↦
    if htop : σ ω = ∞ then
      hIto.toContinuousLinearMap Hbar ω
    else
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar)
        σ ω

/-- Helper for Lemma 25.13: keep the countable-range stopping-time owner in the same finite/top
branching form, but sample the source-facing martingale owner from Theorem 25.11 instead of its
continuous modification. -/
private noncomputable def martingaleSampledOwner_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (σ : Ω → ENNReal) : Ω → ℝ :=
  fun ω ↦
    if htop : σ ω = ∞ then
      hIto.toContinuousLinearMap Hbar ω
    else
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar)
        σ ω

/-- Helper for Lemma 25.13: for a finite countable-range stopping time `σ`, the stopped value of
the continuous modification from Theorem 25.11 agrees almost surely with the raw stopped
Brownian-Itô value. -/
private theorem continuousModification_stoppedValue_ae_eq_brownianStoppedValue_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable)
    (hσ_fin : ∀ ω, σ ω ≠ ∞) :
    MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar) σ =ᵐ[μ]
      brownianItoIntegralStoppedValue W Hbar σ := by
  let syncSet : Set NNReal := ENNReal.toNNReal '' Set.range σ
  have hSyncSet_countable : syncSet.Countable := hσ_count.image ENNReal.toNNReal
  have hSync :
      ∀ᵐ ω ∂μ, ∀ t ∈ syncSet,
        BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar t ω =
          brownianItoIntegralTruncatedProcess W Hbar t ω :=
    continuousModification_aeEq_on_countableSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hSyncSet_countable
  filter_upwards [hSync] with ω hω
  have hσ_mem : ENNReal.toNNReal (σ ω) ∈ syncSet := by
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  -- Proof comment: the sampled stopping value only uses the time `(σ ω).toNNReal`, which lies
  -- in the synchronized countable set by construction.
  have hSample :
      BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar (ENNReal.toNNReal (σ ω)) ω =
        brownianItoIntegralTruncatedProcess W Hbar (ENNReal.toNNReal (σ ω)) ω :=
    hω _ hσ_mem
  have htime : (σ ω).toNNReal = (σ ω).untopA :=
    (untopA_eq_toNNReal_of_ne_top_local (hσ_fin ω)).symm
  have hStoppedValueEq :
      MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar) σ ω =
        brownianItoIntegralStoppedValue W Hbar σ ω := by
    -- Proof comment: on the finite branch of `σ`, both owners evaluate the same sampled time.
    simpa [MeasureTheory.stoppedValue, brownianItoIntegralStoppedValue, hσ_fin ω, htime] using
      hSample
  exact hStoppedValueEq

/-- Helper for Lemma 25.13: for a countable-range stopping time `σ`, the sampled continuous
modification owner agrees almost surely with the raw stopped Brownian-Itô value, with the
terminal branch kept explicit. -/
private theorem continuousModification_sampledValue_ae_eq_brownianStoppedValue_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          σ ω) =ᵐ[μ]
      brownianItoIntegralStoppedValue W Hbar σ := by
  let syncSet : Set NNReal := ENNReal.toNNReal '' Set.range σ
  have hSyncSet_countable : syncSet.Countable := hσ_count.image ENNReal.toNNReal
  have hSync :
      ∀ᵐ ω ∂μ, ∀ t ∈ syncSet,
        BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar t ω =
          brownianItoIntegralTruncatedProcess W Hbar t ω :=
    continuousModification_aeEq_on_countableSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hSyncSet_countable
  filter_upwards [hSync] with ω hω
  have hσ_mem : ENNReal.toNNReal (σ ω) ∈ syncSet := by
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hSample :
      BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar (ENNReal.toNNReal (σ ω)) ω =
        brownianItoIntegralTruncatedProcess W Hbar (ENNReal.toNNReal (σ ω)) ω :=
    hω _ hσ_mem
  by_cases htop : σ ω = ∞
  · -- Proof comment: on the terminal branch, both owners are defined by the same terminal
    -- Brownian-Itô map.
    simp [brownianItoIntegralStoppedValue, htop]
  · have htime : (σ ω).toNNReal = (σ ω).untopA :=
      (untopA_eq_toNNReal_of_ne_top_local htop).symm
    -- Proof comment: on the finite branch, the sampled continuous modification and the raw
    -- stopped value both evaluate the same synchronized time `(σ ω).toNNReal`.
    simpa [MeasureTheory.stoppedValue, brownianItoIntegralStoppedValue, htop, htime] using hSample

/-- Helper for Lemma 25.13: on a countable-range stopping time, the sampled continuous
modification owner and the sampled martingale owner agree almost surely because both sample the
same deterministic-time truncation process on a common countable synchronization set. -/
private theorem continuousSampledOwner_ae_eq_martingaleSampledOwner_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          σ ω) =ᵐ[μ]
      fun ω ↦
        if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar)
          σ ω := by
  let syncSet : Set NNReal := ENNReal.toNNReal '' Set.range σ
  have hSyncSet_countable : syncSet.Countable := hσ_count.image ENNReal.toNNReal
  let _ : Countable syncSet := hSyncSet_countable.to_subtype
  have hContSync :
      ∀ᵐ ω ∂μ, ∀ t : syncSet,
        BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar t ω =
          brownianItoIntegralTruncatedProcess W Hbar t ω := by
    -- Proof comment: the sampled continuous owner agrees with the concrete truncation process at
    -- every deterministic time in the countable synchronization set.
    rw [ae_all_iff]
    intro t
    simpa using
      (BrownianItoIntegral.continuousModification_spec
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements Hbar).2 (t : NNReal)
  have hMartSync :
      ∀ᵐ ω ∂μ, ∀ t : syncSet,
        BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar t ω =
          brownianItoIntegralTruncatedProcess W Hbar t ω := by
    -- Proof comment: the source-facing martingale owner from Theorem 25.11 has the same fixed
    -- deterministic-time slices as the truncation process.
    rw [ae_all_iff]
    intro t
    simpa using
      BrownianItoIntegral.brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess
        hBrownian hAdapted hIndependentIncrements Hbar (t : NNReal)
  filter_upwards [hContSync, hMartSync] with ω hωCont hωMart
  have hσ_mem : ENNReal.toNNReal (σ ω) ∈ syncSet := by
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  by_cases htop : σ ω = ∞
  · -- Proof comment: the explicit `∞` branch is identical in the two sampled-owner
    -- definitions, so nothing remains to prove there.
    simp [htop]
  · have hSample :
        BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar (ENNReal.toNNReal (σ ω)) ω =
          BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar
            (ENNReal.toNNReal (σ ω)) ω := by
      exact (hωCont ⟨ENNReal.toNNReal (σ ω), hσ_mem⟩).trans
        (hωMart ⟨ENNReal.toNNReal (σ ω), hσ_mem⟩).symm
    have htime : (σ ω).toNNReal = (σ ω).untopA :=
      (untopA_eq_toNNReal_of_ne_top_local htop).symm
    -- Proof comment: on the finite branch, both sampled owners read off the same sampled time
    -- `(σ ω).toNNReal`, and the synchronized deterministic-time identity identifies those values.
    simpa [MeasureTheory.stoppedValue, htop, htime] using
      hSample

/-- Helper for Lemma 25.13: after transporting through the common countable-range sampled owner,
the sampled martingale owner already agrees almost surely with the raw stopped Brownian-Itô
value. -/
private theorem martingaleSampledOwner_ae_eq_brownianStoppedValue_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar)
          σ ω) =ᵐ[μ]
      brownianItoIntegralStoppedValue W Hbar σ := by
  -- Proof comment: the continuous sampled owner is the common intermediary already synchronized
  -- both with the martingale owner and with the raw stopped value on countable-range stops.
  exact
    (continuousSampledOwner_ae_eq_martingaleSampledOwner_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hσ_count).symm.trans <|
      continuousModification_sampledValue_ae_eq_brownianStoppedValue_of_countableRange_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements Hbar hσ_count

/-- Helper for Lemma 25.13: if an integrand already vanishes after time `T`, then every
deterministic cutoff at a later time `t ≥ T` leaves the process unchanged. -/
private theorem processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local
    {H : Process} {T t : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → H u ω = 0)
    (hTt : T ≤ t) :
    processBeforeStoppingTime H (fun _ ↦ (t : ENNReal)) = H := by
  funext u ω
  by_cases hut : (u : ENNReal) ≤ (t : ENNReal)
  · by_cases huT : u ≤ T
    · -- Proof comment: before `T`, the later cutoff is inactive, so the process is unchanged.
      simp [processBeforeStoppingTime_apply, hut]
    · have hTu : T < u := lt_of_not_ge huT
      have hzero' : H u ω = 0 := hzero hTu
      -- Proof comment: between `T` and `t`, the process is already zero, so the cutoff still
      -- agrees with the original process.
      simp [processBeforeStoppingTime_apply, hut, hzero']
  · have huT : ¬ u ≤ T := by
      intro huT
      have huT' : (u : ENNReal) ≤ (T : ENNReal) := by
        exact_mod_cast huT
      have hTt' : (T : ENNReal) ≤ (t : ENNReal) := by
        exact_mod_cast hTt
      exact hut (le_trans huT' hTt')
    have hTu : T < u := lt_of_not_ge huT
    have hzero' : H u ω = 0 := hzero hTu
    -- Proof comment: past `t ≥ T`, both the cutoff and the original process vanish.
    simp [processBeforeStoppingTime_apply, hut, hzero']

/-- Helper for Lemma 25.13: for a predictable simple stage that vanishes after `T`, the raw
stopped Brownian-Itô value only depends on the bounded stop `min σ T`. -/
private theorem predictableSimple_brownianStoppedValue_eq_min_const_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable)
    {T : NNReal}
    (hzero : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → (K : Process) t ω = 0) :
    brownianItoIntegralStoppedValue W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) σ =ᵐ[μ]
      brownianItoIntegralStoppedValue W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK)
        (fun ω ↦ min (σ ω) (T : ENNReal)) := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let syncSet : Set NNReal := insert T (ENNReal.toNNReal '' Set.range σ)
  have hSyncSet_countable : syncSet.Countable := by
    simpa [syncSet] using (hσ_count.image ENNReal.toNNReal).insert T
  let _ : Countable syncSet := hSyncSet_countable.to_subtype
  have hTruncEq :
      ∀ t : NNReal, T ≤ t →
        brownianItoIntegralTruncatedProcess W Kbar t =ᵐ[μ]
          hIto.toContinuousLinearMap Kbar := by
    intro t hTt
    have hConst :
        brownianItoIntegralTruncatedProcess W Kbar t =ᵐ[μ]
          hIto.toContinuousLinearMap
            ((MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure) := by
      -- Proof comment: deterministic stopping identifies the time-`t` truncation slice with the
      -- terminal Brownian-Itô map of the deterministically cut off integrand.
      simpa [Kbar, hKstage] using
        stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
          (W := W) (hH := hKstage) t
    have hProcessEq :
        processBeforeStoppingTime (K : Process) (fun _ ↦ (t : ENNReal)) = (K : Process) :=
      processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local hzero hTt
    have hClosureEq :
        (MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure = hKstage.toClosure := by
      -- Proof comment: once the later deterministic cutoff leaves `K` unchanged, the two closure
      -- points are literally the same ambient `L²(μ ⊗ dt)` class.
      exact toClosure_eq_of_process_eq_local
        (MeasureTheory.processBeforeStoppingTime_const hKstage t) hKstage hProcessEq
    have hTerminalEq :
        hIto.toContinuousLinearMap ((MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure) =
          hIto.toContinuousLinearMap Kbar := by
      simpa [Kbar, hKstage] using congrArg hIto.toContinuousLinearMap hClosureEq
    exact hConst.trans <| Filter.EventuallyEq.of_eq hTerminalEq
  have hSync :
      ∀ᵐ ω ∂μ, ∀ t : syncSet,
        T ≤ (t : NNReal) →
          brownianItoIntegralTruncatedProcess W Kbar t ω =
            hIto.toContinuousLinearMap Kbar ω := by
    -- Proof comment: only countably many deterministic times from `σ` matter, so we package all
    -- post-`T` truncation-to-terminal identities on one full-measure event.
    rw [ae_all_iff]
    intro t
    by_cases hTt : T ≤ (t : NNReal)
    · filter_upwards [hTruncEq (t : NNReal) hTt] with ω hω
      intro _
      simpa using hω
    · exact Filter.Eventually.of_forall fun ω ht => False.elim (hTt ht)
  filter_upwards [hSync] with ω hω
  by_cases htop : σ ω = ∞
  · have hT_mem : T ∈ syncSet := by simp [syncSet]
    have hAtT :
        brownianItoIntegralTruncatedProcess W Kbar T ω = hIto.toContinuousLinearMap Kbar ω :=
      hω ⟨T, hT_mem⟩ le_rfl
    -- Proof comment: on the `∞` branch, the bounded stop is `T`, and the post-`T` truncation
    -- already equals the terminal Brownian-Itô value.
    simpa [brownianItoIntegralStoppedValue, htop] using hAtT.symm
  · by_cases hσ_le_T : σ ω ≤ (T : ENNReal)
    · have hmin : min (σ ω) (T : ENNReal) = σ ω := min_eq_left hσ_le_T
      -- Proof comment: if `σ ω ≤ T`, the bounded stop does not change the sampled time at all.
      simp [brownianItoIntegralStoppedValue, htop, hmin]
    · have hσ_mem : ENNReal.toNNReal (σ ω) ∈ syncSet := by
        simp [syncSet]
        exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
      have hT_mem : T ∈ syncSet := by simp [syncSet]
      have hTleσ : T ≤ (σ ω).toNNReal := by
        have hTleσ' : (T : ENNReal) ≤ σ ω := le_of_not_ge hσ_le_T
        simpa [ENNReal.coe_toNNReal htop] using hTleσ'
      have hAtσ :
          brownianItoIntegralTruncatedProcess W Kbar (σ ω).toNNReal ω =
            hIto.toContinuousLinearMap Kbar ω :=
        hω ⟨ENNReal.toNNReal (σ ω), hσ_mem⟩ hTleσ
      have hAtT :
          brownianItoIntegralTruncatedProcess W Kbar T ω =
            hIto.toContinuousLinearMap Kbar ω :=
        hω ⟨T, hT_mem⟩ le_rfl
      have hmin : min (σ ω) (T : ENNReal) = (T : ENNReal) := by
        exact min_eq_right (le_of_not_ge hσ_le_T)
      -- Proof comment: once `σ ω > T`, both the original sampled value and the bounded sampled
      -- value collapse to the same terminal Brownian-Itô value.
      simpa [brownianItoIntegralStoppedValue, htop, hmin] using hAtσ.trans hAtT.symm

/-- Helper for Lemma 25.13: capping a countable-range stopping time by a deterministic horizon
keeps the range countable. -/
private theorem countableRange_min_const_local
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable)
    (T : NNReal) :
    (Set.range (fun ω ↦ min (σ ω) (T : ENNReal))).Countable := by
  -- Proof comment: the capped range is the image of the original range under the deterministic
  -- map `a ↦ min a T`.
  let f : Set.range σ → ENNReal := fun a ↦ min a.1 (T : ENNReal)
  have hEq :
      Set.range f = Set.range (fun ω ↦ min (σ ω) (T : ENNReal)) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      have hy' : ∃ ω, σ ω = y := by
        simpa [Set.mem_range] using hy
      rcases hy' with ⟨ω, hω⟩
      refine ⟨ω, ?_⟩
      simp [f, hω]
    · rintro ⟨ω, rfl⟩
      exact ⟨⟨σ ω, ⟨ω, rfl⟩⟩, rfl⟩
  rw [← hEq]
  let _ : Countable (Set.range σ) := hσ_count.to_subtype
  exact Set.countable_range f

/-- Helper for Lemma 25.13: for a predictable simple stage that already vanishes after time `T`,
the countable-range sampled martingale owner only depends on the bounded stop `σ ∧ T`. -/
private theorem predictableSimple_martingaleSampledOwner_eq_min_const_local
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
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ_count : (Set.range σ).Countable)
    {T : NNReal}
    (hzero : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → (K : Process) t ω = 0) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK))
          σ ω) =ᵐ[μ]
      fun ω ↦
        if min (σ ω) (T : ENNReal) = ∞ then
          hIto.toContinuousLinearMap
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
              (MeasureTheory.predictableSimpleProcessToClosureLocal K hK))
            (fun ω ↦ min (σ ω) (T : ENNReal)) ω := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  have hσT_count :
      (Set.range (fun ω ↦ min (σ ω) (T : ENNReal))).Countable :=
    countableRange_min_const_local (Ω := Ω) (σ := σ) hσ_count T
  have hOwnerToRaw :
      (fun ω ↦
        if σ ω = ∞ then
          hIto.toContinuousLinearMap Kbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Kbar)
            σ ω) =ᵐ[μ]
        brownianItoIntegralStoppedValue W Kbar σ :=
    martingaleSampledOwner_ae_eq_brownianStoppedValue_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Kbar hσ_count
  have hRawToMin :
      brownianItoIntegralStoppedValue W Kbar σ =ᵐ[μ]
        brownianItoIntegralStoppedValue W Kbar
          (fun ω ↦ min (σ ω) (T : ENNReal)) :=
    predictableSimple_brownianStoppedValue_eq_min_const_local
      (μ := μ) (ℱ := ℱ) (W := W)
      K hK hσ_count hzero
  have hMinToOwner :
      (fun ω ↦
        if min (σ ω) (T : ENNReal) = ∞ then
          hIto.toContinuousLinearMap Kbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Kbar)
            (fun ω ↦ min (σ ω) (T : ENNReal)) ω) =ᵐ[μ]
        brownianItoIntegralStoppedValue W Kbar
          (fun ω ↦ min (σ ω) (T : ENNReal)) :=
    martingaleSampledOwner_ae_eq_brownianStoppedValue_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Kbar hσT_count
  -- Proof comment: the raw stopped value already has the desired min-const invariance, and the
  -- countable-range sampled martingale owner is synchronized with that raw owner on both sides.
  exact hOwnerToRaw.trans (hRawToMin.trans hMinToOwner.symm)

/-- Helper for Lemma 25.13: on any countable family of deterministic times, the source-facing
martingale owner from Theorem 25.11 already agrees almost surely with the terminal Brownian-Itô
map of the corresponding deterministic cutoff integrands. -/
private theorem martingaleProcess_ae_eq_cutoffTerminal_on_countableSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {S : Set NNReal}
    (hS : S.Countable)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    ∀ᵐ ω ∂μ, ∀ t ∈ S,
      BrownianItoIntegral.brownianItoIntegralMartingaleProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t ω =
        hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hH t).toClosure) ω := by
  let _ : Countable S := hS.to_subtype
  have hAll :
      ∀ᵐ ω ∂μ, ∀ t : S,
        BrownianItoIntegral.brownianItoIntegralMartingaleProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t ω =
          hIto.toContinuousLinearMap
            ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                hH (t : NNReal)).toClosure) ω := by
    rw [ae_all_iff]
    intro t
    have hMart :
        BrownianItoIntegral.brownianItoIntegralMartingaleProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) (t : NNReal) =ᵐ[μ]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) (t : NNReal) :=
      BrownianItoIntegral.brownianItoIntegralMartingaleProcess_ae_eq_truncatedProcess
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) (t : NNReal)
    have hRawConst :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) (t : NNReal) =ᵐ[μ]
          hIto.toContinuousLinearMap
            ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                hH (t : NNReal)).toClosure) := by
      -- Proof comment: the deterministic stopping identity is the fixed-time bridge from the
      -- martingale owner to the terminal map of the deterministic cutoff integrand.
      exact
        (Filter.EventuallyEq.of_eq
          (brownianItoIntegralStoppedValue_const W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) (t : NNReal))).symm.trans <|
          stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
            (W := W) (hH := hH) (t : NNReal)
    exact hMart.trans hRawConst
  -- Proof comment: package the deterministic-time equalities on one full-measure event so later
  -- arguments can evaluate them at the sampled countable synchronization times.
  filter_upwards [hAll] with ω hω t ht
  exact hω ⟨t, ht⟩

/-- Helper for Lemma 25.13: conditioning the deterministic-time truncation slice at a bounding
horizon `T` down to the stopping-time sigma-algebra already gives the stopping-time conditional
expectation of the terminal Brownian-Itô class. -/
private theorem condExp_truncatedAtBound_ae_eq_condExp_stoppingTime_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    μ[brownianItoIntegralTruncatedProcess W hH.toClosure T | hσ.measurableSpace] =ᵐ[μ]
      μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace] := by
  have hTrunc :
      brownianItoIntegralTruncatedProcess W hH.toClosure T =ᵐ[μ]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ T] :=
    BrownianItoIntegral.truncatedProcess_ae_eq_terminalCondExp
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hH.toClosure T
  have hCond :
      μ[brownianItoIntegralTruncatedProcess W hH.toClosure T | hσ.measurableSpace] =ᵐ[μ]
        μ[μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ T] | hσ.measurableSpace] := by
    -- Proof comment: first rewrite the deterministic slice by the Theorem 25.11
    -- conditional-expectation owner, then collapse the resulting tower.
    exact MeasureTheory.condExp_congr_ae hTrunc
  -- Proof comment: the bound `σ ≤ T` puts `σ(σ)` below `ℱ T`, so the tower property finishes
  -- the comparison.
  exact hCond.trans <|
    (MeasureTheory.condExp_condExp_of_le
      (hσ.measurableSpace_le_of_le hσ_le) (ℱ.le T) :
        μ[μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ T] | hσ.measurableSpace] =ᵐ[μ]
          μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace])

/-- Helper for Lemma 25.13: for a bounded countable-range stopping time, the sampled martingale
owner is the conditional expectation of the terminal Brownian-Itô class with respect to the
stopping-time sigma-algebra. -/
private theorem martingaleSampledOwner_ae_eq_condExp_of_boundedCountableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
          σ ω) =ᵐ[μ]
      μ[(hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) : Ω → ℝ)
        | hσ.measurableSpace] := by
  have hσ_fin : ∀ ω, σ ω ≠ ∞ := fun ω ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hσ_le ω)
  have hOwnerEq :
      (fun ω ↦
        if σ ω = ∞ then
          hIto.toContinuousLinearMap hH.toClosure ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure)
            σ ω) =ᵐ[μ]
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure)
          σ := by
    -- Proof comment: under the deterministic bound `σ ≤ T`, the sampled owner never enters the
    -- explicit `∞` branch, so it is just the stopped martingale process at `σ`.
    filter_upwards with ω
    simp [hσ_fin ω]
  have hMart :
      Martingale
        (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure)
        ℱ μ :=
    (BrownianItoIntegral.truncatedProcess_isL2BoundedMartingale
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hH.toClosure).1
  have hStoppedCond :
      MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure)
          σ =ᵐ[μ]
        μ[BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure T |
          hσ.measurableSpace] := by
    -- Proof comment: optional sampling identifies the sampled martingale owner with the
    -- conditional expectation of the deterministic terminal stage at the bounding horizon `T`.
    exact
      hMart.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
        hσ hσ_le hσ_count
  have hTower :
      μ[BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) hH.toClosure T |
          hσ.measurableSpace] =ᵐ[μ]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace] := by
    -- Proof comment: reuse the extracted deterministic-slice tower collapse so the bounded
    -- sampled-owner theorem only records the genuine optional-sampling step.
    simpa [BrownianItoIntegral.brownianItoIntegralMartingaleProcess] using
      condExp_truncatedAtBound_ae_eq_condExp_stoppingTime_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hσ hσ_le hH
  exact hOwnerEq.trans (hStoppedCond.trans hTower)

/-- Helper for Lemma 25.13: on a level set `{σ = t}` of a bounded countable-range stopping time,
the sampled martingale owner already collapses to the deterministic truncation slice at time `t`.
-/
private theorem martingaleSampledOwner_ae_eq_truncatedProcess_on_levelSet_of_boundedCountableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal))
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess
            (W := W)
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
          σ ω) =ᵐ[
          μ.restrict {ω | σ ω = (t : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t := by
  let A : Set Ω := {ω | σ ω = (t : ENNReal)}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  have hOwnerCond :
      martingaleSampledOwner_local
          (μ := μ) (ℱ := ℱ) (W := W)
          hBrownian hAdapted hIndependentIncrements hH.toClosure σ =ᵐ[μ]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace] := by
    -- Proof comment: for bounded countable-range stops, optional sampling already identifies the
    -- sampled owner with the stopping-time conditional expectation of the terminal Itô class.
    simpa [martingaleSampledOwner_local] using
      martingaleSampledOwner_ae_eq_condExp_of_boundedCountableRange_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hσ hσ_count hσ_le hH
  have hCondRestr :
      μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace] =ᵐ[μ.restrict A]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ t] := by
    -- Proof comment: on the atom `{σ = t}`, the stopping-time sigma-algebra reduces to the
    -- deterministic sigma-algebra `ℱ t`.
    simpa [A] using
      (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
        (μ := μ) (ℱ := ℱ)
        (f := (hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ))
        hσ hσ_count t)
  have hTruncCond :
      brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ t] :=
    BrownianItoIntegral.truncatedProcess_ae_eq_terminalCondExp
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hH.toClosure t
  have hOwnerCondRestr :
      martingaleSampledOwner_local
          (μ := μ) (ℱ := ℱ) (W := W)
          hBrownian hAdapted hIndependentIncrements hH.toClosure σ =ᵐ[μ.restrict A]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | hσ.measurableSpace] :=
    hOwnerCond.filter_mono (Measure.restrict_le_self A)
  have hTruncCondRestr :
      brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ.restrict A]
        μ[(hIto.toContinuousLinearMap hH.toClosure : Ω → ℝ) | ℱ t] :=
    hTruncCond.filter_mono (Measure.restrict_le_self A)
  -- Proof comment: after restricting to `{σ = t}`, both descriptions reduce to the same
  -- deterministic-time conditional expectation owner.
  exact hOwnerCondRestr.trans <| hCondRestr.trans hTruncCondRestr.symm

/-- Helper for Lemma 25.13: if an admissible integrand already vanishes after `T`, then the
terminal Brownian-Itô map of the stopped integrand only depends on the bounded stop `σ ∧ T`. -/
private theorem terminalStoppedIntegrand_eq_min_const_of_vanishesAfter_local
    {σ : Ω → ENNReal} {T : NNReal}
    (hzero : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → H t ω = 0)
    (hσ : IsStoppingTime ℱ σ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.processBeforeStoppingTime hσ)) =
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.processBeforeStoppingTime (hσ.min_const T))) := by
  have hProcessEq :
      processBeforeStoppingTime H σ =
        processBeforeStoppingTime H (fun ω ↦ min (σ ω) (T : ENNReal)) :=
    processBeforeStoppingTime_eq_min_const_of_vanishesAfter_local
      (H := H) (τ := σ) (T := T) hzero
  have hClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.processBeforeStoppingTime hσ) =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.processBeforeStoppingTime (hσ.min_const T)) := by
    -- Proof comment: once the two stopped integrands agree pointwise, their realized closure
    -- points are the same ambient `L²(μ ⊗ dt)` class.
    exact
      toClosure_eq_of_process_eq_local
        (hH.processBeforeStoppingTime hσ)
        (hH.processBeforeStoppingTime (hσ.min_const T))
        hProcessEq
  -- Proof comment: apply the terminal Brownian-Itô map to the common closure point.
  exact congrArg hIto.toContinuousLinearMap hClosureEq

/-- Helper for Lemma 25.13: if `σ ≤ T`, then the terminal Brownian-Itô map of the stopped
integrand is already the deterministic truncation at `T` of the stopped integrand itself. -/
private noncomputable def deterministicConstCutoffClosure_local
    (hH : MemPredictableStepProcessClosure ℱ μ H) (t : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
  MeasureTheory.MemPredictableStepProcessClosure.toClosure <|
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
      (Ω := Ω) (ℱ := ℱ) (μ := μ) hH t

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, the raw stopped Brownian-Itô owner already
reduces to the deterministic time-`t` truncation slice. -/
private theorem brownianStoppedValue_ae_eq_truncatedProcess_on_levelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (t : NNReal) :
    brownianItoIntegralStoppedValue W Hbar σ =ᵐ[
        μ.restrict {ω | σ ω = (t : ENNReal)}]
      brownianItoIntegralTruncatedProcess W Hbar t := by
  let A : Set Ω := {ω | σ ω = (t : ENNReal)}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  refine (ae_restrict_iff' hA_meas).2 ?_
  filter_upwards with ω hω
  have hσ_eq : σ ω = (t : ENNReal) := by
    simpa [A] using hω
  have hσ_fin : σ ω ≠ ∞ := by
    rw [hσ_eq]
    exact ENNReal.coe_ne_top
  -- Proof comment: on the atom `{σ = t}`, the explicit finite branch of
  -- `brownianItoIntegralStoppedValue` samples exactly the deterministic slice at `t`.
  simpa [brownianItoIntegralStoppedValue, hσ_eq, hσ_fin]

/-- Helper for Lemma 25.13: on the top atom `{σ = ∞}`, the raw stopped Brownian-Itô owner is
already the terminal Brownian-Itô map. -/
private theorem brownianStoppedValue_ae_eq_self_on_topLevelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    brownianItoIntegralStoppedValue W Hbar σ =ᵐ[
        μ.restrict {ω | σ ω = ∞}]
      hIto.toContinuousLinearMap Hbar := by
  let A : Set Ω := {ω | σ ω = ∞}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  refine (ae_restrict_iff' hA_meas).2 ?_
  filter_upwards with ω hω
  have hσ_top : σ ω = ∞ := by
    simpa [A] using hω
  -- Proof comment: on the top atom, the explicit definition keeps only the terminal branch.
  simpa [brownianItoIntegralStoppedValue, hσ_top]

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}`, the raw stopped Brownian-Itô
owner already collapses to the deterministic truncation slice at time `c`. -/
private theorem brownianStoppedValue_ae_eq_truncatedProcess_on_boundedMinAtom_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {T : NNReal}
    (c : NNReal) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    brownianItoIntegralStoppedValue W Hbar β =ᵐ[μ.restrict A]
      brownianItoIntegralTruncatedProcess W Hbar c := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  -- Proof comment: this is the earlier level-set identity specialized to the bounded stop
  -- `β = σ ∧ T`.
  simpa [β, A] using
    brownianStoppedValue_ae_eq_truncatedProcess_on_levelSet_local
      (μ := μ) (ℱ := ℱ) (W := W) (σ := β) (hσ := hσ.min_const T) Hbar c

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}`, the sampled truncation process is
already the deterministic slice at time `c`. -/
private theorem stoppedValue_ae_eq_truncatedProcess_on_boundedMinAtom_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {T : NNReal}
    (c : NNReal) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) β =ᵐ[μ.restrict A]
      brownianItoIntegralTruncatedProcess W Hbar c := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  have hA_meas : MeasurableSet A :=
    measurableSet_eq_fun (hσ.min_const T).measurable' measurable_const
  refine (ae_restrict_iff' hA_meas).2 ?_
  filter_upwards with ω hω
  have hβ_eq : β ω = (c : ENNReal) := by
    simpa [A] using hω
  have hβ_fin : β ω ≠ ∞ := by
    rw [hβ_eq]
    exact ENNReal.coe_ne_top
  -- Proof comment: on `{β = c}`, the bounded stop samples the deterministic truncation process
  -- exactly at the fixed time `c`.
  simpa [MeasureTheory.stoppedValue, hβ_eq, hβ_fin]

/-- Helper for Lemma 25.13: under `processMeasure (μ.restrict A)`, the time-space variable stays
over the restricted base event `A`. -/
private theorem ae_fst_mem_of_processMeasure_restrict_local
    {A : Set Ω}
    (hA_meas : MeasurableSet A) :
    ∀ᵐ x ∂MeasureTheory.processMeasure (μ.restrict A), x.1 ∈ A := by
  have hNull :
      MeasureTheory.processMeasure (μ.restrict A) {x : Ω × ℝ | x.1 ∉ A} = 0 := by
    have hSetEq : {x : Ω × ℝ | x.1 ∉ A} = Aᶜ ×ˢ (Set.univ : Set ℝ) := by
      ext x
      simp
    -- Proof comment: restricting the base measure to `A` kills the whole complement strip
    -- `Aᶜ × ℝ`.
    simp [hSetEq, MeasureTheory.processMeasure, hA_meas]
  rw [ae_iff]
  simpa using hNull

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, the time-space representative of the randomly
stopped process already agrees with the deterministic cutoff at `t`. -/
private theorem processToTimeSpaceFun_stopped_ae_eq_const_on_levelSet_local
    {H : Process} {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (t : NNReal) :
    MeasureTheory.processToTimeSpaceFun (processBeforeStoppingTime H σ) =ᵐ[
        MeasureTheory.processMeasure (μ.restrict {ω | σ ω = (t : ENNReal)})]
      MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime H fun _ ↦ (t : ENNReal)) := by
  let A : Set Ω := {ω | σ ω = (t : ENNReal)}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  rw [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
    MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator]
  filter_upwards
    [ae_fst_mem_of_processMeasure_restrict_local (Ω := Ω) (μ := μ) hA_meas] with x hxA
  rcases x with ⟨ω, s⟩
  have hσ_eq : σ ω = (t : ENNReal) := by
    simpa [A] using hxA
  by_cases hsσ : ENNReal.ofReal s ≤ σ ω
  · have hst : ENNReal.ofReal s ≤ (t : ENNReal) := by
      simpa [hσ_eq] using hsσ
    -- Proof comment: on the level set `{σ = t}`, both indicator strips keep exactly the same
    -- time-space values.
    have hsle : s ≤ (t : ℝ) := by
      simpa using hst
    simp [hsσ, hsle, MeasureTheory.processToTimeSpaceFun]
  · have hst : ¬ ENNReal.ofReal s ≤ (t : ENNReal) := by
      simpa [hσ_eq] using hsσ
    -- Proof comment: outside the common strip, both stopped representatives vanish.
    have hsle : ¬ s ≤ (t : ℝ) := by
      simpa using hst
    simp [hsσ, hsle, MeasureTheory.processToTimeSpaceFun]

/-- Helper for Lemma 25.13: on the top atom `{σ = ∞}`, the time-space representative of the
randomly stopped process already agrees with the original integrand. -/
private theorem processToTimeSpaceFun_stopped_ae_eq_self_on_topLevelSet_local
    {H : Process} {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ) :
    MeasureTheory.processToTimeSpaceFun (processBeforeStoppingTime H σ) =ᵐ[
        MeasureTheory.processMeasure (μ.restrict {ω | σ ω = ∞})]
      MeasureTheory.processToTimeSpaceFun H := by
  let A : Set Ω := {ω | σ ω = ∞}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  rw [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator]
  filter_upwards
    [ae_fst_mem_of_processMeasure_restrict_local (Ω := Ω) (μ := μ) hA_meas] with x hxA
  rcases x with ⟨ω, s⟩
  have hσ_top : σ ω = ∞ := by
    simpa [A] using hxA
  have hsσ : ENNReal.ofReal s ≤ σ ω := by
    simpa [hσ_top] using (show ENNReal.ofReal s ≤ (∞ : ENNReal) from le_top)
  -- Proof comment: on `{σ = ∞}`, the stopping strip is all of time, so the indicator disappears.
  simp [hsσ]

/-- Helper for Lemma 25.13: if two stage sequences already agree on `A` at every step and both
converge in measure on `μ`, then their limits still agree on `A`. This is the closure-level
subsequence transfer used when atomwise stage identities are lifted to the final integrand. -/
private theorem ae_eq_restrict_of_tendstoInMeasure_of_seq_local
    {A : Set Ω}
    (hA_meas : MeasurableSet A)
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hF : MeasureTheory.TendstoInMeasure μ f Filter.atTop F)
    (hG : MeasureTheory.TendstoInMeasure μ g Filter.atTop G)
    (hEq : ∀ n, f n =ᵐ[μ.restrict A] g n) :
    F =ᵐ[μ.restrict A] G := by
  have hFInd :
      MeasureTheory.TendstoInMeasure μ (fun n ↦ A.indicator (f n)) Filter.atTop
        (A.indicator F) :=
    hF.indicator A
  have hGInd :
      MeasureTheory.TendstoInMeasure μ (fun n ↦ A.indicator (g n)) Filter.atTop
        (A.indicator G) :=
    hG.indicator A
  have hIndEq :
      ∀ n, A.indicator (f n) =ᵐ[μ] A.indicator (g n) := by
    intro n
    exact (ae_eq_restrict_iff_indicator_ae_eq hA_meas).1 (hEq n)
  have hIndLimit : A.indicator F =ᵐ[μ] A.indicator G := by
    obtain ⟨sf, hsf_strictMono, hsf_ae⟩ := hFInd.exists_seq_tendsto_ae
    have hGSub :
        MeasureTheory.TendstoInMeasure μ (fun n ↦ A.indicator (g (sf n))) Filter.atTop
          (A.indicator G) := by
      exact hGInd.comp hsf_strictMono.tendsto_atTop
    obtain ⟨sg, hsg_strictMono, hsg_ae⟩ := hGSub.exists_seq_tendsto_ae
    have hEqAll :
        ∀ᵐ ω ∂μ, ∀ n : ℕ, A.indicator (f (sf (sg n))) ω = A.indicator (g (sf (sg n))) ω := by
      rw [ae_all_iff]
      intro n
      exact hIndEq (sf (sg n))
    filter_upwards [hsf_ae, hsg_ae, hEqAll] with ω hωF hωG hωEq
    have hωF' :
        Filter.Tendsto (fun n ↦ A.indicator (f (sf (sg n))) ω) Filter.atTop
          (nhds (A.indicator F ω)) :=
      hωF.comp hsg_strictMono.tendsto_atTop
    have hωG' :
        Filter.Tendsto (fun n ↦ A.indicator (f (sf (sg n))) ω) Filter.atTop
          (nhds (A.indicator G ω)) := by
      simpa [hωEq] using hωG
    -- Proof comment: the common indicator subsequence has both candidate limits, so uniqueness
    -- of limits in `ℝ` identifies the restricted terminal values.
    exact tendsto_nhds_unique hωF' hωG'
  -- Proof comment: indicator equality on the ambient probability space is equivalent to
  -- equality under the restricted atom measure.
  exact (ae_eq_restrict_iff_indicator_ae_eq hA_meas).2 hIndLimit

/-- Helper for Lemma 25.13: if stopping times `τm` converge pointwise to `τ` from above, then the
canonical closure points of the stopped integrands converge in ambient `L²(μ ⊗ dt)`. This
dependency-ordered copy is extracted early because the bounded-min dyadic block needs it before
the later sampled-owner proofs. -/
private theorem stoppedIntegrandLpTendsto_of_stoppingApprox_local
    {H : Process} {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm : ∀ n, IsStoppingTime ℱ (τm n))
    (hτm_le : ∀ n ω, τ ω ≤ τm n ω)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) (Filter.atTop : Filter ℕ) (nhds (τ ω)))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    Filter.Tendsto
      (fun n : ℕ ↦ (((hH.processBeforeStoppingTime (hτm n)).toClosure :
          MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))
      (Filter.atTop : Filter ℕ)
      (nhds
        (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
          (((hH.processBeforeStoppingTime hτ).toClosure :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
  let hStopped := fun n : ℕ ↦
    (hH.processBeforeStoppingTime (hτm n) :
      MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime H (τm n)))
  let hStoppedLim : MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (ProbabilityTheory.processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  have hLpNorm :
      Filter.Tendsto
        (fun n ↦
          eLpNorm
            (MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
              MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H τ))
            (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ))
        Filter.atTop
        (𝓝 0) := by
    have hTwo_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hTwo_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have hTwo_pos : 0 < ((2 : ℝ≥0∞).toReal) :=
      ENNReal.toReal_pos hTwo_ne_zero hTwo_ne_top
    suffices hIntegral :
        Filter.Tendsto
          (fun n ↦
            ∫⁻ x, ‖(MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                  MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ) ∂
              MeasureTheory.processMeasure μ)
          Filter.atTop
          (𝓝 0) by
      -- Proof comment: for `p = 2`, vanishing of the square integral is exactly ambient
      -- `L²(processMeasure μ)` convergence of the stopped representatives.
      simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hTwo_ne_zero hTwo_ne_top]
      convert continuous_rpow_const.continuousAt.tendsto.comp hIntegral
      simp [zero_rpow_of_pos (_root_.inv_pos.mpr hTwo_pos)]
    have hF_meas :
        ∀ n,
          AEMeasurable
            (fun x ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ))
            (MeasureTheory.processMeasure μ) := by
      intro n
      exact
        ((hStopped n).memLp.aemeasurable.sub hStoppedLim.memLp.aemeasurable).enorm.pow_const
          (2 : ℝ)
    have hBound :
        ∀ n,
          (fun x ↦
            ‖(MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                  MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) ≤ᵐ[
              MeasureTheory.processMeasure μ]
            fun x ↦ ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ) := by
      intro n
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxle : τ x.1 ≤ τm n x.1 := hτm_le n x.1
      by_cases hxτ : ENNReal.ofReal x.2 ≤ τ x.1
      · have hxτm : ENNReal.ofReal x.2 ≤ τm n x.1 := le_trans hxτ hxle
        -- Proof comment: inside the limiting strip, both stopped representatives agree, so the
        -- pointwise difference vanishes.
        simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
          hxτ, hxτm]
      · by_cases hxτm : ENNReal.ofReal x.2 ≤ τm n x.1
        · -- Proof comment: on the shrinking strip difference, the stopped difference is exactly
          -- the original integrand.
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        · -- Proof comment: outside the approximating strip, both stopped representatives vanish.
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
    have hFinite :
        (∫⁻ x, ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ) ∂
            MeasureTheory.processMeasure μ) ≠
          ∞ := by
      exact
        (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hTwo_ne_zero hTwo_ne_top
          hH.memLp.eLpNorm_lt_top).ne
    have hLimit :
        ∀ᵐ x ∂MeasureTheory.processMeasure μ,
          Filter.Tendsto
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ))
            Filter.atTop
            (𝓝 0) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hxτ : ENNReal.ofReal x.2 ≤ τ x.1
      · have hEventuallyEq :
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) =ᶠ[
                Filter.atTop]
              fun _ ↦ 0 := by
          refine Filter.Eventually.of_forall ?_
          intro n
          have hxτm : ENNReal.ofReal x.2 ≤ τm n x.1 := le_trans hxτ (hτm_le n x.1)
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        -- Proof comment: once `x` lies in the limiting strip, every approximating strip keeps
        -- it as well, so the difference is eventually zero.
        exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
      · have hEventuallyLt :
          ∀ᶠ n in Filter.atTop, τm n x.1 < ENNReal.ofReal x.2 :=
          (hτm_tendsto x.1).eventually (Iio_mem_nhds (lt_of_not_ge hxτ))
        have hEventuallyEq :
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) =ᶠ[
                Filter.atTop]
              fun _ ↦ 0 := by
          filter_upwards [hEventuallyLt] with n hn
          have hxτm : ¬ ENNReal.ofReal x.2 ≤ τm n x.1 := not_le_of_gt hn
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        -- Proof comment: once the approximating strip drops below the sampled time level, both
        -- stopped representatives vanish there.
        exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
    -- Proof comment: dominated convergence on the square integrand gives the required vanishing
    -- of the ambient `L²` distance.
    simpa using
      MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (fun x ↦ ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ))
        hF_meas hBound hFinite hLimit
  have hLp :
      Filter.Tendsto
        (fun n ↦
          (hStopped n).memLp.toLp
            (MeasureTheory.processToTimeSpaceFun
              (ProbabilityTheory.processBeforeStoppingTime H (τm n))))
        Filter.atTop
        (nhds
          (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
            hStoppedLim.memLp.toLp
              (MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H τ)))) := by
    -- Proof comment: convert the square-integral convergence of the representatives into
    -- convergence of their ambient `Lp` classes.
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n ↦
          MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H (τm n)))
        (fun n ↦ (hStopped n).memLp)
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime H τ))
        hStoppedLim.memLp).2 hLpNorm
  simpa [hStopped, hStoppedLim] using hLp

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, conditioning with respect to the stopping-time
σ-algebra of `σ` already agrees with conditioning with respect to the deterministic-time
σ-algebra `ℱ t`. -/
private theorem condExp_stoppingTime_ae_eq_fixedTime_on_atom_local
    {f : Ω → ℝ} {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    [SigmaFinite (μ.trim hσ.measurableSpace_le)]
    (t : NNReal) :
    μ[f | hσ.measurableSpace] =ᵐ[μ.restrict {ω | σ ω = (t : ENNReal)}] μ[f | ℱ t] := by
  -- Proof comment: this is exactly the stopping-time atom restriction theorem from mathlib in
  -- the present `ENNReal = WithTop NNReal` setting.
  simpa using
    (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq
      (μ := μ) (ℱ := ℱ) (f := f) hσ t)

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, the bounded stop `σ ∧ T` is the deterministic
value `min t T`. -/
private theorem levelSet_subset_minConstLevelSet_local
    {σ : Ω → ENNReal} (t T : NNReal) :
    {ω | σ ω = (t : ENNReal)} ⊆ {ω | min (σ ω) (T : ENNReal) = (min t T : NNReal)} := by
  intro ω hω
  -- Proof comment: after substituting `σ ω = t`, the bounded stop is just the deterministic
  -- minimum `min t T`.
  simpa using congrArg (fun x : ENNReal ↦ min x (T : ENNReal)) hω

/-- Helper for Lemma 25.13: on the top atom `{σ = ∞}`, the bounded stop `σ ∧ T` is exactly `T`.
-/
private theorem topLevelSet_subset_minConstTopLevelSet_local
    {σ : Ω → ENNReal} (T : NNReal) :
    {ω | σ ω = ∞} ⊆ {ω | min (σ ω) (T : ENNReal) = (T : ENNReal)} := by
  intro ω hω
  -- Proof comment: on `{σ = ∞}`, capping at `T` simply returns the deterministic horizon `T`.
  have hσ_top : σ ω = ∞ := by
    simpa using hω
  simp [hσ_top]

/-- Helper for Lemma 25.13: once a predictable simple stage vanishes after `T`, every
deterministic truncation at time `t ≥ T` already equals the terminal Brownian-Itô map. -/
private theorem predictableSimple_truncatedProcess_eq_terminal_of_supportBound_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {T t : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (hTt : T ≤ t) :
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) t =ᵐ[μ]
      hIto.toContinuousLinearMap
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  have hConst :
      brownianItoIntegralTruncatedProcess W Kbar t =ᵐ[μ]
        hIto.toContinuousLinearMap
          ((MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure) := by
    -- Proof comment: deterministic stopping identifies the time-`t` truncation slice with the
    -- terminal map of the deterministic cutoff integrand.
    simpa [Kbar, hKstage] using
      stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
        (W := W) (hH := hKstage) t
  have hProcessEq :
      processBeforeStoppingTime (K : Process) (fun _ ↦ (t : ENNReal)) = (K : Process) :=
    processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local hzero hTt
  have hClosureEq :
      (MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure = hKstage.toClosure := by
    -- Proof comment: once the cutoff time is beyond the support horizon, deterministic stopping
    -- leaves the predictable simple stage unchanged.
    exact toClosure_eq_of_process_eq_local
      (hH := MeasureTheory.processBeforeStoppingTime_const hKstage t)
      (hG := hKstage) hProcessEq
  have hTerminalEq :
      hIto.toContinuousLinearMap ((MeasureTheory.processBeforeStoppingTime_const hKstage t).toClosure) =
        hIto.toContinuousLinearMap Kbar := by
    simpa [Kbar, hKstage] using congrArg hIto.toContinuousLinearMap hClosureEq
  -- Proof comment: rewrite the deterministic cutoff back to the original predictable simple
  -- stage and transport the terminal identity through that closure equality.
  exact hConst.trans (Filter.EventuallyEq.of_eq hTerminalEq)

/-- Helper for Lemma 25.13: once a predictable simple stage vanishes after `T`, replacing a
deterministic truncation time by `min t T` does not change the Brownian-Itô truncation slice. -/
private theorem predictableSimple_truncatedProcess_eq_min_const_of_vanishesAfter_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (t : NNReal) :
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) (min t T) =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) t := by
  by_cases htt : t ≤ T
  · -- Proof comment: below the support horizon, `min t T` is literally `t`.
    simpa [min_eq_left htt]
  · have hTt : T ≤ t := le_of_not_ge htt
    have hAtMin :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) (min t T) =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) := by
      -- Proof comment: once `t` lies past the support horizon, the bounded minimum is exactly
      -- `T`, so both deterministic slices collapse to the terminal map.
      simpa [min_eq_right hTt] using
        predictableSimple_truncatedProcess_eq_terminal_of_supportBound_local
          (μ := μ) (ℱ := ℱ) (W := W) K hK hzero (t := T) le_rfl
    have hAtT :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) t =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) :=
      predictableSimple_truncatedProcess_eq_terminal_of_supportBound_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hzero hTt
    -- Proof comment: both deterministic slices identify with the same terminal Brownian-Itô map.
    exact hAtMin.trans hAtT.symm

/-- Helper for Lemma 25.13: on one stopping atom `{β = c}`, the terminal Brownian-Itô map of the
random cutoff of a predictable simple stage should agree with the terminal map of the matching
deterministic cutoff stage. -/
private theorem processToTimeSpaceFun_randomCutoff_ae_eq_constRecut_on_stoppingAtom_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {β : Ω → ENNReal}
    (hβ : IsStoppingTime ℱ β)
    (c : NNReal) :
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) =ᵐ[
          MeasureTheory.processMeasure (μ.restrict {ω | β ω = (c : ENNReal)})]
      MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
          (fun _ ↦ (c : ENNReal))) := by
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  have hAtomEq :
      MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) =ᵐ[
            MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            (fun _ ↦ (c : ENNReal))) := by
    -- Proof comment: on `{β = c}`, the random cutoff already matches the deterministic cutoff.
    simpa [A] using
      processToTimeSpaceFun_stopped_ae_eq_const_on_levelSet_local
        (μ := μ) (H := (K : Process)) (σ := β) (hσ := hβ) c
  have hRecutEq :
      MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
            (fun _ ↦ (c : ENNReal))) =ᵐ[
              MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            (fun _ ↦ (c : ENNReal))) := by
    rw [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator]
    filter_upwards [hAtomEq] with x hx
    by_cases hxc : ENNReal.ofReal x.2 ≤ (c : ENNReal)
    · have hxc_real : x.2 ≤ (c : ℝ) := by
        by_cases hx_nonneg : 0 ≤ x.2
        · exact_mod_cast hxc
        · exact le_trans (le_of_not_ge hx_nonneg) (show (0 : ℝ) ≤ (c : ℝ) by exact_mod_cast c.2)
      simpa [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator, hxc,
        hxc_real] using hx
    · have hxc_real : ¬ x.2 ≤ (c : ℝ) := by
        intro hreal
        apply hxc
        by_cases hx_nonneg : 0 ≤ x.2
        · exact_mod_cast hreal
        · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx_nonneg)]
          exact bot_le
      simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator, hxc_real]
  -- Proof comment: both the raw random cutoff and its deterministic recut identify with the
  -- same deterministic cutoff stage on the stopping atom.
  change
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) =ᵐ[
          MeasureTheory.processMeasure (μ.restrict A)]
      MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
          (fun _ ↦ (c : ENNReal)))
  calc
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) =ᵐ[
          MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            (fun _ ↦ (c : ENNReal))) := hAtomEq
    _ =ᵐ[MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
            (fun _ ↦ (c : ENNReal))) := hRecutEq.symm

/-- Helper for Lemma 25.13: on one stopping atom `{β = c}`, the terminal Brownian-Itô map of the
random cutoff of a predictable simple stage should agree with the terminal map of the matching
deterministic cutoff stage. -/
private theorem processToTimeSpaceFun_constRecut_randomCutoff_ae_eq_constCutoff_on_stoppingAtom_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {β : Ω → ENNReal}
    (hβ : IsStoppingTime ℱ β)
    (c : NNReal) :
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
          (fun _ ↦ (c : ENNReal))) =ᵐ[
            MeasureTheory.processMeasure (μ.restrict {ω | β ω = (c : ENNReal)})]
      MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          (fun _ ↦ (c : ENNReal))) := by
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  have hAtomEq :
      MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) =ᵐ[
            MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            (fun _ ↦ (c : ENNReal))) := by
    -- Proof comment: on the atom `{β = c}`, the random stopping strip is already the
    -- deterministic strip at time `c`.
    simpa [A] using
      processToTimeSpaceFun_stopped_ae_eq_const_on_levelSet_local
        (μ := μ) (H := (K : Process)) (σ := β) (hσ := hβ) c
  have hRecutEq :
      MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
            (fun _ ↦ (c : ENNReal))) =ᵐ[
              MeasureTheory.processMeasure (μ.restrict A)]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime (K : Process)
              (fun _ ↦ (c : ENNReal)))
            (fun _ ↦ (c : ENNReal))) := by
    -- Proof comment: deterministically recutting both atomwise-equal stopped representatives by
    -- the same strip preserves the restricted time-space equality.
    filter_upwards [hAtomEq] with x hx
    by_cases hxc : ENNReal.ofReal x.2 ≤ (c : ENNReal)
    · have hxc_real : x.2 ≤ (c : ℝ) := by
        by_cases hx_nonneg : 0 ≤ x.2
        · exact_mod_cast hxc
        · exact le_trans (le_of_not_ge hx_nonneg) (show (0 : ℝ) ≤ (c : ℝ) by exact_mod_cast c.2)
      simpa [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator, hxc,
        hxc_real] using hx
    · have hxc_real : ¬ x.2 ≤ (c : ℝ) := by
        intro hreal
        apply hxc
        by_cases hx_nonneg : 0 ≤ x.2
        · exact_mod_cast hreal
        · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx_nonneg)]
          exact bot_le
      simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator, hxc_real]
  have hIdem :
      ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            (fun _ : Ω ↦ (c : ENNReal)))
          (fun _ : Ω ↦ (c : ENNReal)) =
        ProbabilityTheory.processBeforeStoppingTime (K : Process)
          (fun _ : Ω ↦ (c : ENNReal)) := by
    funext t
    funext ω
    by_cases htc : (t : ENNReal) ≤ (c : ENNReal)
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, htc]
    · simp [ProbabilityTheory.processBeforeStoppingTime_apply, htc]
  -- Proof comment: the deterministic cutoff is idempotent, so the recut right-hand side
  -- collapses to the original deterministic cutoff stage.
  simpa [A] using hRecutEq.trans <|
    Filter.EventuallyEq.of_eq <| by
      simpa using congrArg MeasureTheory.processToTimeSpaceFun hIdem

variable {W : Process}
variable [hIto : BrownianItoIntegral μ ℱ W]

/-- Helper for Lemma 25.13: the terminal map of a deterministic cutoff integrand is exactly the
fixed-time Brownian-Itô truncation slice of the original closure point. -/
theorem deterministicCutoffTerminal_eq_truncated_local
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    hIto.toContinuousLinearMap
        ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            hH t).toClosure) =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t := by
  -- Proof comment: the deterministic stopping theorem already packages the fixed-time terminal
  -- identity, so we record the output-level normalization once for reuse in the stopping-atom
  -- bridges below.
  simpa using
    (((Filter.EventuallyEq.of_eq
        (brownianItoIntegralStoppedValue_const W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t)).symm).trans
      stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
        (W := W) (hH := hH) t).symm

/-- Helper for Lemma 25.13: if an integrand vanishes after `T`, then stopping it before an
arbitrary random time still vanishes after `T`. -/
private theorem processBeforeStoppingTime_vanishesAfter_local
    {H : Process} {σ : Ω → ENNReal} {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → H u ω = 0) :
    ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u →
      ProbabilityTheory.processBeforeStoppingTime H σ u ω = 0 := by
  intro u ω hu
  by_cases huσ : (u : ENNReal) ≤ σ ω
  · -- Proof comment: on the active branch of the random cutoff, the original integrand is
    -- already zero past the support horizon `T`.
    simpa [ProbabilityTheory.processBeforeStoppingTime_apply, huσ] using hzero hu
  · -- Proof comment: outside the stopping region, the random cutoff vanishes by definition.
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, huσ]

/-- Helper for Lemma 25.13: if an admissible integrand vanishes after `T`, then its terminal
Brownian-Itô map already equals the deterministic time-`T` truncation slice. -/
private theorem terminalBrownianIto_eq_truncated_of_vanishesAfter_local
    {H : Process}
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → H u ω = 0) :
    hIto.toContinuousLinearMap (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) T := by
  let hConst :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hH T
  have hDet :
      hIto.toContinuousLinearMap (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) T :=
    deterministicCutoffTerminal_eq_truncated_local
      (μ := μ) (ℱ := ℱ) (W := W) (hH := hH) T
  have hProcessEq :
      ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) = H :=
    processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local hzero le_rfl
  have hClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hH := by
    -- Proof comment: once the deterministic cutoff leaves the integrand unchanged, the two
    -- closure representatives are literally the same ambient `L²(μ ⊗ dt)` class.
    exact toClosure_eq_of_process_eq_local hConst hH hProcessEq
  have hTerminalEq :
      hIto.toContinuousLinearMap (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) =
        hIto.toContinuousLinearMap (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) := by
    exact congrArg hIto.toContinuousLinearMap hClosureEq
  -- Proof comment: rewrite the deterministic terminal map back to the original integrand and use
  -- the fixed-time truncation identity at the support horizon `T`.
  exact (Filter.EventuallyEq.of_eq hTerminalEq).symm.trans hDet

/-- Helper for Lemma 25.13: if `σ ≤ T`, then the terminal Brownian-Itô map of the stopped
integrand is already the deterministic truncation at `T` of the stopped integrand itself. -/
private theorem terminalStoppedIntegrand_ae_eq_truncatedAtBound_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W ((hH.processBeforeStoppingTime hσ).toClosure) T := by
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H σ) :=
    hH.processBeforeStoppingTime hσ
  have hStoppedConstEq :
      processBeforeStoppingTime (processBeforeStoppingTime H σ) (fun _ ↦ (T : ENNReal)) =
        processBeforeStoppingTime H σ := by
    -- Proof comment: because `σ ≤ T`, cutting the already stopped integrand again at the
    -- deterministic horizon `T` leaves the process unchanged.
    calc
      processBeforeStoppingTime (processBeforeStoppingTime H σ) (fun _ ↦ (T : ENNReal)) =
          processBeforeStoppingTime (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) σ := by
            simpa using processBeforeStoppingTime_const_comm (G := H) σ T
      _ = processBeforeStoppingTime H σ := by
            exact
              processBeforeStoppingTime_constStage_eq_randomCutoff_local
                (H := H) (σ := σ) (T := T) hσ_le
  have hClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hStopped T) =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped := by
    -- Proof comment: the deterministic recut and the original stopped integrand represent the
    -- same ambient closure class because their underlying processes coincide.
    exact
      toClosure_eq_of_process_eq_local
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hStopped T)
        hStopped
        hStoppedConstEq
  have hConst :
      brownianItoIntegralStoppedValue W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped)
          (fun _ ↦ (T : ENNReal)) =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hStopped T)) := by
    simpa [hStopped] using
      stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
        (W := W) (hH := hStopped) T
  have hRaw :
      brownianItoIntegralStoppedValue W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped)
          (fun _ ↦ (T : ENNReal)) =
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T :=
    brownianItoIntegralStoppedValue_const W
      (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hStopped T)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
    -- Proof comment: rewrite the deterministic recut closure back to the original stopped
    -- closure before comparing terminal values.
    exact congrArg hIto.toContinuousLinearMap hClosureEq
  have hResult :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T := by
    -- Proof comment: normalize the terminal map through the deterministic stopping theorem
    -- applied to the already stopped integrand.
    exact
      (((Filter.EventuallyEq.of_eq hRaw).trans hConst).trans
        (Filter.EventuallyEq.of_eq hTerminalEq)).symm
  simpa [hStopped] using hResult

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}` with `c ≤ T`, the deterministic
time-`T` recut of the bounded stopped stage agrees pointwise with the deterministic cutoff at
time `c`. -/
private theorem boundedStopped_constCutoff_apply_eq_constCutoff_on_minConstAtom_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {σ : Ω → ENNReal} {T : NNReal} (c : NNReal) (hcT : c ≤ T)
    {ω : Ω}
    (hω : min (σ ω) (T : ENNReal) = (c : ENNReal))
    (s : NNReal) :
    ProbabilityTheory.processBeforeStoppingTime
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          (fun ω ↦ min (σ ω) (T : ENNReal)))
        (fun _ ↦ (T : ENNReal)) s ω =
      ProbabilityTheory.processBeforeStoppingTime (K : Process)
        (fun _ ↦ (c : ENNReal)) s ω := by
  have hβω : min (σ ω) (T : ENNReal) = (c : ENNReal) := hω
  by_cases hsT : (s : ENNReal) ≤ (T : ENNReal)
  · have hsMin : (s : ENNReal) ≤ min (σ ω) (T : ENNReal) ↔ (s : ENNReal) ≤ (c : ENNReal) := by
      simpa [hβω]
    have hsC : (s : ENNReal) ≤ (c : ENNReal) → (s : ENNReal) ≤ (T : ENNReal) := by
      intro hsC
      exact le_trans hsC (by exact_mod_cast hcT)
    by_cases hsβ : (s : ENNReal) ≤ min (σ ω) (T : ENNReal)
    · have hsConst : (s : ENNReal) ≤ (c : ENNReal) := hsMin.mp hsβ
      -- Proof comment: on the active branch of the bounded stop, both deterministic cutoffs keep
      -- exactly the same sample of `K`.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsT, hsβ, hsConst]
    · have hsConst : ¬ (s : ENNReal) ≤ (c : ENNReal) := by
        intro hsConst
        exact hsβ (hsMin.mpr hsConst)
      -- Proof comment: once `s` lies beyond the bounded stopping level `c`, both recut stages
      -- vanish on the atom `{σ ∧ T = c}`.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsT, hsβ, hsConst]
  · have hsConst : ¬ (s : ENNReal) ≤ (c : ENNReal) := by
      intro hsConst
      exact hsT (le_trans hsConst (by exact_mod_cast hcT))
    have hsβ : ¬ (s : ENNReal) ≤ min (σ ω) (T : ENNReal) := by
      intro hsβ
      exact hsT (le_trans hsβ (min_le_right _ _))
    -- Proof comment: if `s > T`, then the time-`T` recut is already `0`, and because `c ≤ T`
    -- the direct deterministic cutoff at `c` also vanishes.
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsT, hsβ, hsConst]

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}` with `c ≤ T`, the time-space
representative of the deterministic time-`T` recut of the bounded stopped stage already agrees
with the deterministic cutoff at time `c`. -/
private theorem boundedStopped_constCutoff_timeSpaceFun_ae_eq_on_minConstAtom_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    {T : NNReal} (c : NNReal) (hcT : c ≤ T) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
          (fun _ ↦ (T : ENNReal))) =ᵐ[
            MeasureTheory.processMeasure (μ.restrict A)]
      MeasureTheory.processToTimeSpaceFun
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          (fun _ ↦ (c : ENNReal))) := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  have hA_meas : MeasurableSet A :=
    measurableSet_eq_fun (hσ.min_const T).measurable' measurable_const
  filter_upwards
    [ae_fst_mem_of_processMeasure_restrict_local (Ω := Ω) (μ := μ) hA_meas] with x hxA
  rcases x with ⟨ω, s⟩
  have hβω : β ω = (c : ENNReal) := by
    simpa [A] using hxA
  -- Proof comment: after unpacking the atom identity `β ω = c`, the two deterministic recuts are
  -- literally the same stopped process at the sampled time `s.toNNReal`.
  change
    ProbabilityTheory.processBeforeStoppingTime
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
        (fun _ ↦ (T : ENNReal)) s.toNNReal ω =
      ProbabilityTheory.processBeforeStoppingTime (K : Process)
        (fun _ ↦ (c : ENNReal)) s.toNNReal ω
  simpa [β] using
    boundedStopped_constCutoff_apply_eq_constCutoff_on_minConstAtom_local
      (K := K) (σ := σ) (T := T) c hcT hβω s.toNNReal

/-- Helper for Lemma 25.13: the dedicated stopped witness for a predictable simple stage has the
same canonical closure point as the generic closure-side stopping construction applied to that
stage. -/
private theorem predictableSimpleStopped_toClosure_eq_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ) :
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (hKstage.processBeforeStoppingTime hσ) =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (predictableSimpleStopped_memPredictable_local
          (μ := μ) (ℱ := ℱ) K hK hσ) := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) σ) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK hσ
  -- Proof comment: both closure witnesses are attached to the very same stopped process, so the
  -- ambient `L²(μ ⊗ dt)` closure owner is identical.
  exact
    toClosure_eq_of_process_eq_local
      (hKstage.processBeforeStoppingTime hσ)
      hStopped
      rfl

/-- Helper for Lemma 25.13: on the exact atom `{βm = c}`, the terminal Brownian-Itô map of the
stopped predictable-simple cutoff stage already agrees with its own deterministic truncation at
the bounding horizon `T`. -/
private theorem stoppedStageTerminal_eq_selfTruncation_on_exactAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (KcutT : MeasureTheory.PredictableSimpleProcess ℱ)
    (hKcut :
      MemLp (MeasureTheory.processToTimeSpaceFun ((KcutT : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {βm : Ω → ENNReal}
    (hβm : IsStoppingTime ℱ βm)
    {T : NNReal}
    (hβm_leT : ∀ ω, βm ω ≤ (T : ENNReal))
    (c : NNReal) :
    let B : Set Ω := {ω | βm ω = (c : ENNReal)}
    let hKcutStage : MemPredictableStepProcessClosure ℱ μ (KcutT : Process) :=
      ⟨hKcut, (MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut).2⟩
    let hStoppedSimple :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (KcutT : Process) βm) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) KcutT hKcut hβm
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) =ᵐ[
          μ.restrict B]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) T := by
  let B : Set Ω := {ω | βm ω = (c : ENNReal)}
  let hKcutStage : MemPredictableStepProcessClosure ℱ μ (KcutT : Process) :=
    ⟨hKcut, (MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut).2⟩
  let hStoppedSimple :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (KcutT : Process) βm) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) KcutT hKcut hβm
  have hStoppedClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hKcutStage.processBeforeStoppingTime hβm) =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple := by
    -- Proof comment: the generic closure-side stopping witness and the dedicated predictable
    -- simple stopped witness package the same stopped stage `KcutT^(βm)`.
    simpa [hKcutStage, hStoppedSimple] using
      predictableSimpleStopped_toClosure_eq_local
        (μ := μ) (ℱ := ℱ) KcutT hKcut hβm
  have hGlobal :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hKcutStage.processBeforeStoppingTime hβm)) =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hKcutStage.processBeforeStoppingTime hβm)) T := by
    -- Proof comment: the bounded stop `βm ≤ T` lets us normalize the terminal stopped stage to
    -- the time-`T` truncation slice of that same stopped integrand.
    exact
      terminalStoppedIntegrand_ae_eq_truncatedAtBound_local
        (μ := μ) (ℱ := ℱ) (W := W)
        (σ := βm) (hσ := hβm) (T := T) (hσ_le := hβm_leT)
        (hH := hKcutStage)
  have hLeftEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hKcutStage.processBeforeStoppingTime hβm)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) := by
    -- Proof comment: rewrite the terminal map through the canonical closure identification of the
    -- two stopped witnesses.
    exact congrArg hIto.toContinuousLinearMap hStoppedClosureEq
  have hRightEq :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hKcutStage.processBeforeStoppingTime hβm)) T =
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) T := by
    -- Proof comment: the same closure identification rewrites the deterministic truncation slice.
    exact
      congrArg
        (fun Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ ↦
          brownianItoIntegralTruncatedProcess W Hbar T)
        hStoppedClosureEq
  -- Proof comment: restrict the global bounded-stop normalization to the exact atom and then
  -- rewrite both sides to the dedicated predictable-simple stopped witness.
  exact
    (((Filter.EventuallyEq.of_eq hLeftEq).symm).trans
      (hGlobal.filter_mono (Measure.restrict_le_self B))).trans
      (Filter.EventuallyEq.of_eq hRightEq)

/-- Helper for Lemma 25.13: for a predictable simple stage that vanishes after `T`, the terminal
Brownian-Itô map of the bounded random cutoff `K^(β)` should collapse on the exact atom
`{β = c}` to the deterministic truncation slice at time `c`. -/
private theorem predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_exactAtom_boundedFinite_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {β : Ω → ENNReal}
    (hβ : IsStoppingTime ℱ β)
    (hβ_finite : (Set.range β).Finite)
    {T : NNReal}
    (hβ_leT : ∀ ω, β ω ≤ (T : ENNReal))
    (c : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK hβ)) =ᵐ[
          μ.restrict {ω | β ω = (c : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) c := by
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK hβ
  let _ := hβ_finite
  by_cases hcT : c ≤ T
  · let βT : Ω → ENNReal := fun ω ↦ min (β ω) (T : ENNReal)
    let hStoppedBounded :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) βT) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) K hK (hβ.min_const T)
    have hSelfTrunc :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[
              μ.restrict A]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T := by
      -- Proof comment: on `{β = c}`, the terminal map of the bounded stopped stage first
      -- normalizes to its own deterministic time-`T` truncation slice.
      simpa [A, hStopped] using
        stoppedStageTerminal_eq_selfTruncation_on_exactAtom_local
          (μ := μ) (ℱ := ℱ) (W := W)
          K hK (βm := β) hβ (T := T) hβ_leT c
    have hProcessEq :
        ProbabilityTheory.processBeforeStoppingTime (K : Process) β =
          ProbabilityTheory.processBeforeStoppingTime (K : Process) βT := by
      funext t ω
      -- Proof comment: the bound `β ≤ T` makes the clipped stop `β ∧ T` equal to `β`
      -- pointwise, so the two stopped processes coincide.
      simp [βT, min_eq_left (hβ_leT ω)]
    have hStoppedClosureEq :
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped =
          MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded := by
      -- Proof comment: once the underlying stopped processes agree, their closure witnesses are
      -- the same ambient `L²(μ ⊗ dt)` class.
      exact
        toClosure_eq_of_process_eq_local
          hStopped hStoppedBounded hProcessEq
    have hTruncEq :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded) T := by
      -- Proof comment: rewrite the deterministic truncation slice through the common stopped
      -- closure point.
      exact
        congrArg
          (fun Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ ↦
            brownianItoIntegralTruncatedProcess W Hbar T)
          hStoppedClosureEq
    have hA_eq :
        {ω | βT ω = (c : ENNReal)} = A := by
      ext ω
      -- Proof comment: the stopping atom for `β ∧ T` is the same as the original atom
      -- because `β ω ≤ T` already holds everywhere.
      simp [A, βT, min_eq_left (hβ_leT ω)]
    have hBoundedTrunc :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded) T =ᵐ[
              μ.restrict A]
          brownianItoIntegralTruncatedProcess W Kbar c := by
      have hRaw :
          brownianItoIntegralTruncatedProcess W
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded) T =ᵐ[
                μ.restrict {ω | βT ω = (c : ENNReal)}]
            brownianItoIntegralTruncatedProcess W Kbar c := by
        -- Proof comment: the existing bounded stopped-truncation theorem already identifies the
        -- time-`T` slice of the clipped stopped stage with the deterministic cutoff at `c`.
        simpa [βT, Kbar, hStoppedBounded] using
          boundedStoppedTruncation_eq_originalTruncation_on_minConstAtom_local
            (μ := μ) (ℱ := ℱ) (W := W)
            K hK (hσ := hβ) (T := T) c hcT
      simpa [hA_eq] using hRaw
    -- Proof comment: chaining the self-truncation normalization with the bounded truncation
    -- comparison gives the desired atomwise identity.
    exact hSelfTrunc.trans <| (Filter.EventuallyEq.of_eq hTruncEq).trans hBoundedTrunc
  · have hA_empty : A = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.2
      intro ω hω
      have hc_le_T : c ≤ T := by
        exact_mod_cast (show (c : ENNReal) ≤ (T : ENNReal) by simpa [A] using hβ_leT ω)
      exact hcT hc_le_T
    -- Proof comment: if `c > T`, then the atom `{β = c}` is empty because the stop is bounded
    -- above by `T`, so the restricted statement is trivial.
    simpa [A, Kbar, hStopped, hA_empty]

/-- Helper for Lemma 25.13: for a predictable simple stage that vanishes after `T`, the terminal
Brownian-Itô map of the random cutoff `K^(β)` reduces to the bounded finite-range exact-atom
core after replacing `β` by `β ∧ T`. -/
private theorem predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_exactAtom_finite_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {β : Ω → ENNReal}
    (hβ : IsStoppingTime ℱ β)
    (hβ_finite : (Set.range β).Finite)
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (c : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK hβ)) =ᵐ[
          μ.restrict {ω | β ω = (c : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) c := by
  let βT : Ω → ENNReal := fun ω ↦ min (β ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let B : Set Ω := {ω | βT ω = (min c T : NNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK hβ
  let hStoppedBounded :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) βT) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hβ.min_const T)
  have hβT_finite :
      (Set.range βT).Finite := by
    let f : ENNReal → ENNReal := fun x ↦ min x (T : ENNReal)
    have hRange :
        Set.range βT = f '' Set.range β := by
      ext x
      constructor
      · rintro ⟨ω, rfl⟩
        exact ⟨β ω, ⟨ω, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨ω, hω⟩, rfl⟩
        exact ⟨ω, by simpa [βT, f] using congrArg (fun z : ENNReal ↦ min z (T : ENNReal)) hω⟩
    rw [hRange]
    exact hβ_finite.image f
  have hSubset : A ⊆ B := by
    intro ω hω
    have hβ_eq : β ω = (c : ENNReal) := by
      simpa [A] using hω
    simpa [B, βT, hβ_eq]
  have hProcessEq :
      ProbabilityTheory.processBeforeStoppingTime (K : Process) β =
        ProbabilityTheory.processBeforeStoppingTime (K : Process) βT := by
    -- Proof comment: because `K` vanishes after `T`, stopping at `β` or at `β ∧ T`
    -- produces the same integrand.
    simpa [βT] using
      processBeforeStoppingTime_eq_min_const_of_vanishesAfter_local
        (H := (K : Process)) (τ := β) (T := T) hzero
  have hStoppedClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded := by
    -- Proof comment: the two stopping witnesses package the same bounded-support process once
    -- the random time is capped by `T`.
    exact
      toClosure_eq_of_process_eq_local
        hStopped hStoppedBounded hProcessEq
  have hLeftEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded) := by
    exact congrArg hIto.toContinuousLinearMap hStoppedClosureEq
  have hBoundedRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedBounded) =ᵐ[
            μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar (min c T) := by
    -- Proof comment: after capping `β` by `T`, only the bounded finite-range exact-atom core
    -- remains.
    simpa [B, Kbar, hStoppedBounded] using
      (predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_exactAtom_boundedFinite_local
        (μ := μ) (ℱ := ℱ) (W := W)
        K hK (hβ := hβ.min_const T) hβT_finite
        (T := T) (hβ_leT := fun ω ↦ min_le_right _ _) (c := min c T)).filter_mono
          (Measure.restrict_mono hSubset)
  have hMinToTarget :
      brownianItoIntegralTruncatedProcess W Kbar (min c T) =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W Kbar c := by
    by_cases hcT : c ≤ T
    · -- Proof comment: if `c ≤ T`, the bounded reduction does not change the deterministic
      -- target time.
      simpa [min_eq_left hcT]
    · have hTc : T ≤ c := le_of_not_ge hcT
      let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
        ⟨hK, Kbar.2⟩
      let hConstT :
          MemPredictableStepProcessClosure ℱ μ
            (ProbabilityTheory.processBeforeStoppingTime (K : Process)
              fun _ ↦ (T : ENNReal)) :=
        MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
      let hConstC :
          MemPredictableStepProcessClosure ℱ μ
            (ProbabilityTheory.processBeforeStoppingTime (K : Process)
              fun _ ↦ (c : ENNReal)) :=
        MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage c
      have hProcessEqT :
          ProbabilityTheory.processBeforeStoppingTime (K : Process) (fun _ ↦ (T : ENNReal)) =
            (K : Process) :=
        processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local hzero le_rfl
      have hProcessEqC :
          ProbabilityTheory.processBeforeStoppingTime (K : Process) (fun _ ↦ (c : ENNReal)) =
            (K : Process) :=
        processBeforeStoppingTime_const_eq_self_of_vanishesAfter_local hzero hTc
      have hClosureEqT :
          MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstT = Kbar := by
        -- Proof comment: once the deterministic cutoff time is at least `T`, the support bound
        -- makes the cutoff stage equal to the original predictable simple stage.
        exact
          toClosure_eq_of_process_eq_local
            hConstT hKstage hProcessEqT
      have hClosureEqC :
          MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstC = Kbar := by
        -- Proof comment: the same support-bound argument applies at the later deterministic time
        -- `c`.
        exact
          toClosure_eq_of_process_eq_local
            hConstC hKstage hProcessEqC
      have hAtT :
          brownianItoIntegralTruncatedProcess W Kbar T =ᵐ[μ]
            hIto.toContinuousLinearMap Kbar := by
        have hDet :
            hIto.toContinuousLinearMap
                (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstT) =ᵐ[μ]
              brownianItoIntegralTruncatedProcess W Kbar T := by
          simpa [Kbar, hKstage, hConstT] using
            deterministicCutoffTerminal_eq_truncated_local
              (μ := μ) (ℱ := ℱ) (W := W) (hH := hKstage) T
        have hTerminalEq :
            hIto.toContinuousLinearMap
                (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstT) =
              hIto.toContinuousLinearMap Kbar := by
          exact congrArg hIto.toContinuousLinearMap hClosureEqT
        exact hDet.symm.trans (Filter.EventuallyEq.of_eq hTerminalEq)
      have hAtC :
          brownianItoIntegralTruncatedProcess W Kbar c =ᵐ[μ]
            hIto.toContinuousLinearMap Kbar := by
        have hDet :
            hIto.toContinuousLinearMap
                (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstC) =ᵐ[μ]
              brownianItoIntegralTruncatedProcess W Kbar c := by
          simpa [Kbar, hKstage, hConstC] using
            deterministicCutoffTerminal_eq_truncated_local
              (μ := μ) (ℱ := ℱ) (W := W) (hH := hKstage) c
        have hTerminalEq :
            hIto.toContinuousLinearMap
                (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConstC) =
              hIto.toContinuousLinearMap Kbar := by
          exact congrArg hIto.toContinuousLinearMap hClosureEqC
        exact hDet.symm.trans (Filter.EventuallyEq.of_eq hTerminalEq)
      -- Proof comment: once `c ≥ T`, both deterministic truncation slices have already reached
      -- the terminal Brownian-Itô map of `K`.
      simpa [min_eq_right hTc] using hAtT.trans hAtC.symm
  -- Proof comment: reduce to the bounded finite-range exact-atom core for `β ∧ T` and then
  -- normalize the deterministic slice back from `min c T` to `c`.
  exact
    (Filter.EventuallyEq.of_eq hLeftEq).trans <|
      hBoundedRestr.trans <| hMinToTarget.filter_mono (Measure.restrict_le_self A)

/-- Helper for Lemma 25.13: on the exact atom `{β = c}`, the time-`T` truncation slice of a
bounded stopped predictable simple stage already agrees with the time-`c` truncation slice of the
underlying predictable simple stage. -/
private theorem stoppedStageTruncation_eq_baseCutoffTruncation_onExactAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {β : Ω → ENNReal}
    (hβ : IsStoppingTime ℱ β)
    (hβ_finite : (Set.range β).Finite)
    {T : NNReal}
    (hβ_leT : ∀ ω, β ω ≤ (T : ENNReal))
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (c : NNReal) :
    let B : Set Ω := {ω | β ω = (c : ENNReal)}
    let hStopped :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) K hK hβ
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[
          μ.restrict B]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) c := by
  let B : Set Ω := {ω | β ω = (c : ENNReal)}
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK hβ
  have hSelfTrunc :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[
            μ.restrict B]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T := by
    -- Proof comment: because the stopped predictable simple stage vanishes after `T`, its
    -- terminal Brownian-Itô map already matches its own time-`T` truncation slice.
    simpa [B, hStopped] using
      stoppedStageTerminal_eq_selfTruncation_on_exactAtom_local
        (μ := μ) (ℱ := ℱ) (W := W)
        K hK hβ (T := T) hβ_leT c
  have hTerminalAtom :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[
            μ.restrict B]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) c := by
    -- Proof comment: this is the exact predictable-simple stopping atom theorem isolated as the
    -- only remaining structural blocker.
    simpa [B, hStopped] using
      predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_exactAtom_finite_local
        (μ := μ) (ℱ := ℱ) (W := W)
        K hK hβ hβ_finite hzero c
  -- Proof comment: compare both truncation slices through the common terminal map of the stopped
  -- predictable simple stage.
  exact hSelfTrunc.symm.trans hTerminalAtom

/-- Helper for Lemma 25.13: the deterministic cutoff stage `K · 1_[0,T]` is still globally
square-integrable on `Ω × [0, ∞)`. -/
private theorem predictableSimpleCutoffBefore_memLp_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        ((ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
            MeasureTheory.PredictableSimpleProcess ℱ) : Process))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  let Kcut :
      MeasureTheory.PredictableSimpleProcess ℱ :=
    ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
  let hCutMem :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
            (K : Process)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    (memLp_congr_ae
      (Filter.EventuallyEq.of_eq
        (ProbabilityTheory.BrownianItoIntegral
          .processToTimeSpaceFun_cutoffBeforeDeterministicTime_local T
          (K : Process)).symm)).mp <|
      MeasureTheory.MemLp.indicator
        (show MeasurableSet ({x : Ω × ℝ | x.2 ≤ (T : ℝ)}) from
          measurableSet_le measurable_snd measurable_const)
        hK
  -- Proof comment: the chosen predictable simple cutoff has the same time-space representative
  -- as the ambient deterministic indicator cutoff of `K`.
  have hEq :
      MeasureTheory.processToTimeSpaceFun ((Kcut : MeasureTheory.PredictableSimpleProcess ℱ) : Process) =ᵐ[
          MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local T
            (K : Process)) :=
    Filter.EventuallyEq.of_eq <| by
      simpa [Kcut] using
        congrArg MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
            K T)
  exact (memLp_congr_ae hEq).mpr hCutMem

/-- Helper for Lemma 25.13: the deterministic cutoff stage `K · 1_[0,T]` vanishes identically
after time `T`. -/
private theorem predictableSimpleCutoffBefore_vanishesAfter_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {T : NNReal} :
    ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u →
      ((ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
          MeasureTheory.PredictableSimpleProcess ℱ) : Process) u ω = 0 := by
  intro u ω hu
  have hnot : ¬ u ≤ T := not_le_of_gt hu
  -- Proof comment: outside the deterministic support horizon, the chosen cutoff representation is
  -- literally the zero branch of
  -- `ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local`.
  simpa [ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local, hnot]
    using congrArg (fun H : Process => H u ω)
      (ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_coe_local
        K T)

/-- Helper for Lemma 25.13: the closure-side deterministic cutoff owner agrees with the canonical
predictable-simple cutoff object from Theorem 25.11. -/
private theorem predictableSimpleCutoffBefore_toClosure_eq_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (T : NNReal)
    (hKcut :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          ((ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T :
              MeasureTheory.PredictableSimpleProcess ℱ) : Process))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ)) :
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    let KcutT : MeasureTheory.PredictableSimpleProcess ℱ :=
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT =
      MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hCutT :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
  let KcutT : MeasureTheory.PredictableSimpleProcess ℱ :=
    ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
  -- Proof comment: both constructions package the same deterministic cutoff `K · 1_[0,T]`,
  -- once through the closure-side cutoff operator and once through the explicit predictable-simple
  -- object produced in Theorem 25.11.
  calc
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT =
        MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore T Kbar := by
          symm
          simpa [Kbar, hKstage, hCutT] using
            MeasureTheory.MemPredictableStepProcessClosure
              .cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst hKstage T
    _ =
        MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut := by
          simpa [Kbar, KcutT, hKcut] using
            ProbabilityTheory.BrownianItoIntegral.cutoffBefore_predictableSimpleClosure_eq_local
              K hK T

/-- Helper for Lemma 25.13: clipping the dyadic ceiling approximants of the bounded stop
`β = σ ∧ T` keeps the stages below `T` and makes each stage deterministic on the atom
`{β = c}`. -/
private theorem boundedMinClippedDyadicApproximation_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    {T c : NNReal}
    (hcT : c ≤ T) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    ∃ βm : ℕ → Ω → ENNReal, ∃ cm : ℕ → NNReal,
      (∀ m, IsStoppingTime ℱ (βm m)) ∧
      (∀ m, (Set.range (βm m)).Finite) ∧
      (∀ m ω, β ω ≤ βm m ω) ∧
      (∀ m ω, βm m ω ≤ (T : ENNReal)) ∧
      (∀ m, c ≤ cm m) ∧
      (∀ m, cm m ≤ T) ∧
      (∀ ω, Filter.Tendsto (fun m ↦ βm m ω) Filter.atTop (nhds (β ω))) ∧
      Filter.Tendsto cm Filter.atTop (nhds c) ∧
      (∀ m, A ⊆ {ω | βm m ω = (cm m : ENNReal)}) := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let βNN : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (β ω)
  let raw : ℕ → Ω → ENNReal := fun m ω ↦ (ProbabilityTheory.dyadicCeilApprox m βNN ω : ENNReal)
  let βm : ℕ → Ω → ENNReal := fun m ω ↦ min (raw m ω) (T : ENNReal)
  let cm : ℕ → NNReal := fun m ↦
    min
      (((Nat.ceil ((((2 : NNReal) ^ m) * c : NNReal) : ℝ)) : NNReal) / ((2 : NNReal) ^ m))
      T
  have hβ_stop : IsStoppingTime ℱ β := hσ.min_const T
  have hβ_fin : ∀ ω, β ω ≠ ∞ := fun ω ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hβNN_stop : IsStoppingTime ℱ (fun ω ↦ (βNN ω : ENNReal)) := by
    have hβ_eq :
        (fun ω ↦ (βNN ω : ENNReal)) = β := by
      funext ω
      simpa [βNN, hβ_fin ω] using (ENNReal.coe_toNNReal (hβ_fin ω))
    simpa [hβ_eq] using hβ_stop
  refine ⟨βm, cm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    -- Proof comment: each clipped dyadic stage is still a stopping time because both the dyadic
    -- ceiling approximant and the deterministic cap preserve stopping times.
    have hRaw_stop : IsStoppingTime ℱ (raw m) := by
      simpa [raw] using ProbabilityTheory.dyadicCeilApprox_isStoppingTime hβNN_stop m
    simpa [βm] using hRaw_stop.min_const T
  · intro m
    -- Proof comment: after clipping at the deterministic horizon `T`, the dyadic stage still
    -- ranges over one finite mesh: the dyadic numerators are bounded by the dyadic ceiling of
    -- `T`, and the extra clipping contributes at most the endpoint `T`.
    let N : ℕ := Nat.ceil ((((2 : NNReal) ^ m) * T : NNReal) : ℝ) + 1
    let grid : Fin N → ENNReal := fun k ↦
      min ((((k : ℕ) : NNReal) / ((2 : NNReal) ^ m) : NNReal) : ENNReal) (T : ENNReal)
    have hGridFinite : (((Finset.univ.image grid : Finset ENNReal) : Set ENNReal)).Finite := by
      exact (Finset.finite_toSet _)
    refine hGridFinite.subset ?_
    rintro _ ⟨ω, rfl⟩
    let k : ℕ := Nat.ceil ((((2 : NNReal) ^ m) * βNN ω : NNReal) : ℝ)
    have hk :
        ((ProbabilityTheory.dyadicCeilApprox m βNN ω : NNReal) : ENNReal) =
          (((k : NNReal) / ((2 : NNReal) ^ m)) : ENNReal) := by
      simp [ProbabilityTheory.dyadicCeilApprox, k]
    have hβ_eqω : (βNN ω : ENNReal) = β ω := by
      simpa [βNN, hβ_fin ω] using (ENNReal.coe_toNNReal (hβ_fin ω))
    have hβNN_leT : βNN ω ≤ T := by
      exact ENNReal.coe_le_coe.mp (hβ_eqω.symm ▸ (min_le_right _ _))
    have hk_le :
        k ≤ Nat.ceil ((((2 : NNReal) ^ m) * T : NNReal) : ℝ) := by
      change Nat.ceil ((((2 : NNReal) ^ m) * βNN ω : NNReal) : ℝ) ≤
        Nat.ceil ((((2 : NNReal) ^ m) * T : NNReal) : ℝ)
      apply Nat.ceil_le.mpr
      exact le_trans
        (by
          exact_mod_cast
            (mul_le_mul_of_nonneg_left hβNN_leT (by positivity : (0 : NNReal) ≤ (2 : NNReal) ^ m)))
        (Nat.le_ceil ((((2 : NNReal) ^ m) * T : NNReal) : ℝ))
    refine Finset.mem_image.2 ?_
    refine ⟨⟨k, Nat.lt_succ_of_le hk_le⟩, Finset.mem_univ _, ?_⟩
    -- Proof comment: the clipped stage value is exactly the clipped dyadic mesh point attached
    -- to the numerator `k`.
    simpa [grid, N, βm, raw] using (congrArg (fun z : ENNReal ↦ min z (T : ENNReal)) hk).symm
  · intro m ω
    have hceil :
        (2 : NNReal) ^ m * βNN ω ≤
          (Nat.ceil ((((2 : NNReal) ^ m) * βNN ω : NNReal) : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil ((((2 : NNReal) ^ m) * βNN ω : NNReal) : ℝ)
    have hleNN :
        βNN ω ≤ ProbabilityTheory.dyadicCeilApprox m βNN ω := by
      have hpow_pos : 0 < (2 : NNReal) ^ m := by
        positivity
      rw [ProbabilityTheory.dyadicCeilApprox, div_eq_mul_inv]
      rw [le_mul_inv_iff₀ hpow_pos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hceil
    have hβ_eqω : (βNN ω : ENNReal) = β ω := by
      simpa [βNN, hβ_fin ω] using (ENNReal.coe_toNNReal (hβ_fin ω))
    have hleRaw : β ω ≤ raw m ω := by
      have hleRaw' :
          (βNN ω : ENNReal) ≤ (ProbabilityTheory.dyadicCeilApprox m βNN ω : ENNReal) := by
        exact_mod_cast hleNN
      simpa [raw] using le_trans hβ_eqω.symm.le hleRaw'
    -- Proof comment: the clipped dyadic stage still dominates the bounded stop because
    -- `β ≤ raw` and `β ≤ T`.
    exact le_min hleRaw (min_le_right _ _)
  · intro m ω
    -- Proof comment: the clipped stages are bounded by the deterministic horizon by
    -- construction.
    exact min_le_right _ _
  · intro m
    have hceil :
        (2 : NNReal) ^ m * c ≤
          (Nat.ceil ((((2 : NNReal) ^ m) * c : NNReal) : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil ((((2 : NNReal) ^ m) * c : NNReal) : ℝ)
    have hleRaw :
        c ≤
          ((Nat.ceil ((((2 : NNReal) ^ m) * c : NNReal) : ℝ) : NNReal) /
            ((2 : NNReal) ^ m)) := by
      have hpow_pos : 0 < (2 : NNReal) ^ m := by
        positivity
      rw [div_eq_mul_inv]
      rw [le_mul_inv_iff₀ hpow_pos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hceil
    -- Proof comment: clipping the dyadic ceiling of the deterministic atom value `c` at the
    -- larger horizon `T` still leaves a stage value above `c`.
    exact le_min hleRaw hcT
  · intro m
    -- Proof comment: the deterministic dyadic stage values are clipped at `T` by definition.
    exact min_le_right _ _
  · intro ω
    have hRawTendsto :
        Filter.Tendsto
          (fun m ↦ (ProbabilityTheory.dyadicCeilApprox m βNN ω : ENNReal))
          Filter.atTop
          (nhds ((βNN ω : NNReal) : ENNReal)) :=
      (continuous_coe.tendsto (βNN ω)).comp
        (ProbabilityTheory.dyadicCeilApprox_tendsto βNN ω)
    have hβ_eqω : (βNN ω : ENNReal) = β ω := by
      simpa [βNN, hβ_fin ω] using (ENNReal.coe_toNNReal (hβ_fin ω))
    have hClipTendsto :
        Filter.Tendsto
          (fun m ↦ min ((ProbabilityTheory.dyadicCeilApprox m βNN ω : NNReal) : ENNReal)
            (T : ENNReal))
          Filter.atTop
          (nhds (min ((βNN ω : NNReal) : ENNReal) (T : ENNReal))) := by
      simpa using
        ((continuous_id.min continuous_const).tendsto ((βNN ω : NNReal) : ENNReal)).comp
          hRawTendsto
    -- Proof comment: clipping the dyadic ceilings by the deterministic horizon preserves the
    -- pointwise convergence to the bounded stop `β = σ ∧ T`.
    simpa [βm, β, raw, hβ_eqω] using hClipTendsto
  · let cConst : Unit → NNReal := fun _ ↦ c
    have hRawTendsto :
        Filter.Tendsto
          (fun m ↦ ProbabilityTheory.dyadicCeilApprox m cConst PUnit.unit)
          Filter.atTop
          (nhds (cConst PUnit.unit)) :=
      ProbabilityTheory.dyadicCeilApprox_tendsto cConst PUnit.unit
    have hClipTendsto :
        Filter.Tendsto
          (fun m ↦ min (ProbabilityTheory.dyadicCeilApprox m cConst PUnit.unit) T)
          Filter.atTop
          (nhds (min (cConst PUnit.unit) T)) := by
      simpa using ((continuous_id.min continuous_const).tendsto c).comp hRawTendsto
    -- Proof comment: the deterministic dyadic atom values are the same clipped dyadic ceilings,
    -- now evaluated at the constant stop `c`.
    simpa [cm, cConst, ProbabilityTheory.dyadicCeilApprox, min_eq_left hcT] using hClipTendsto
  · intro m ω hω
    have hβ_eqω : β ω = (c : ENNReal) := by
      simpa [A] using hω
    have hβNN_eqω : βNN ω = c := by
      apply ENNReal.coe_inj.mp
      simpa [βNN, hβ_eqω, hβ_fin ω] using (ENNReal.coe_toNNReal (hβ_fin ω))
    -- Proof comment: on `{β = c}`, the dyadic ceiling approximant depends only on the
    -- deterministic value `c`, so the clipped stage becomes the deterministic constant `cm m`.
    simp [βm, cm, raw, ProbabilityTheory.dyadicCeilApprox, hβNN_eqω]

/-- Helper for Lemma 25.13: on the exact dyadic atom `{βm = c}`, the terminal Brownian-Itô map
of the deterministically cut off predictable simple stage `K · 1_[0,T]` should already agree
with the deterministic truncation slice at time `c`. -/
private theorem clippedDyadicStage_eq_truncation_on_exactAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {T : NNReal}
    {βm : Ω → ENNReal}
    (hβm : IsStoppingTime ℱ βm)
    (hβm_finite : (Set.range βm).Finite)
    (hβm_leT : ∀ ω, βm ω ≤ (T : ENNReal))
    (c : NNReal) :
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    hIto.toContinuousLinearMap
        ((hCutT.processBeforeStoppingTime hβm).toClosure) =ᵐ[
          μ.restrict {ω | βm ω = (c : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c := by
  -- Route correction: the clipped-dyadic limit transfer is already in place. The only missing
  -- ingredient is this exact-atom bridge for the concrete finite-range dyadic stage coming from
  -- the bounded approximation package, not for an arbitrary closure member.
  let B : Set Ω := {ω | βm ω = (c : ENNReal)}
  by_cases hcT : c ≤ T
  · let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    let KcutT : MeasureTheory.PredictableSimpleProcess ℱ :=
      ProbabilityTheory.BrownianItoIntegral.predictableSimpleProcessCutoffBefore_local K T
    let hKcut :
        MemLp (MeasureTheory.processToTimeSpaceFun ((KcutT : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ) :=
      predictableSimpleCutoffBefore_memLp_local (μ := μ) K hK T
    let hStoppedSimple :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (KcutT : Process) βm) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) KcutT hKcut hβm
    have hKcutZero :
        ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (KcutT : Process) u ω = 0 := by
      -- Proof comment: the deterministic cutoff stage `K · 1_[0,T]` carries the required
      -- support bound for the exact-atom predictable-simple bridge.
      simpa [KcutT] using
        predictableSimpleCutoffBefore_vanishesAfter_local (Ω := Ω) (ℱ := ℱ) K (T := T)
    have hCutTClosureEq :
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT =
          MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut := by
      -- Proof comment: first rewrite the closure-side deterministic cutoff owner to the concrete
      -- predictable-simple cutoff object from Theorem 25.11.
      simpa [Kbar, hKstage, hCutT, KcutT, hKcut] using
        predictableSimpleCutoffBefore_toClosure_eq_local
          (μ := μ) (ℱ := ℱ) K hK T hKcut
    have hStoppedProcessEq :
        ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime (K : Process)
              fun _ ↦ (T : ENNReal))
            βm =
          ProbabilityTheory.processBeforeStoppingTime (KcutT : Process) βm := by
      -- Proof comment: both sides stop the same deterministic cutoff stage before `βm`; the
      -- difference is only whether we spell that stage as a closure-side cutoff or as the
      -- explicit predictable-simple object `KcutT`.
      funext s ω
      by_cases hsβ : (s : ENNReal) ≤ βm ω
      · by_cases hsT : (s : ENNReal) ≤ (T : ENNReal)
        · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsβ, hsT, KcutT,
            ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local]
        · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsβ, hsT, KcutT,
            ProbabilityTheory.BrownianItoIntegral.cutoffBeforeDeterministicTime_local]
      · simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsβ]
    have hStoppedClosureEq :
        ((hCutT.processBeforeStoppingTime hβm).toClosure) =
          MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple := by
      -- Proof comment: after fixing the deterministic cutoff spelling, both stopping
      -- constructions package the same stopped predictable-simple process.
      exact
        toClosure_eq_of_process_eq_local
          (hCutT.processBeforeStoppingTime hβm)
          hStoppedSimple
          hStoppedProcessEq
    have hSelfTrunc :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) =ᵐ[
              μ.restrict B]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) T := by
      -- Proof comment: first normalize the stopped stage to its own deterministic time-`T`
      -- truncation slice; this is the easy half of the exact-atom bridge.
      simpa [B, hStoppedSimple] using
        stoppedStageTerminal_eq_selfTruncation_on_exactAtom_local
          (μ := μ) (ℱ := ℱ) (W := W)
          KcutT hKcut hβm (T := T) hβm_leT c
    have hStageTruncEq :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) T =ᵐ[
              μ.restrict B]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut) c := by
      -- Proof comment: the exact-atom truncation bridge is now isolated in a dedicated
      -- predictable-simple lemma, so the dyadic stage theorem only consumes that API here.
      simpa [B, hStoppedSimple] using
        stoppedStageTruncation_eq_baseCutoffTruncation_onExactAtom_local
          (μ := μ) (ℱ := ℱ) (W := W)
          KcutT hKcut hβm hβm_finite (T := T) hβm_leT hKcutZero c
    have hLeftEq :
        hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime hβm).toClosure) =
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedSimple) := by
      exact congrArg hIto.toContinuousLinearMap hStoppedClosureEq
    have hRightEq :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c =
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal KcutT hKcut) c := by
      exact congrArg (fun Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ ↦
        brownianItoIntegralTruncatedProcess W Hbar c) hCutTClosureEq
    exact
      (Filter.EventuallyEq.of_eq hLeftEq).trans <|
        hSelfTrunc.trans <| hStageTruncEq.trans (Filter.EventuallyEq.of_eq hRightEq).symm
  · have hEmpty : B = ∅ := by
      ext ω
      constructor
      · intro hω
        have hle : (c : ENNReal) ≤ (T : ENNReal) := by
          simpa [B] using (hω ▸ hβm_leT ω)
        exact (hcT <| ENNReal.coe_le_coe.mp hle).elim
      · intro hω
        simp at hω
    -- Proof comment: if `c > T`, the exact atom is empty because the bounded dyadic stages never
    -- exceed the deterministic horizon `T`.
    simp [B, hEmpty]

/-- Helper for Lemma 25.13: once the dyadic stage identity is known on the exact atom
`{βm = c}`, restricting to a smaller target atom is only measure monotonicity. -/
private theorem clippedDyadicStage_eq_truncation_on_targetAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {T : NNReal}
    {βm : Ω → ENNReal}
    (hβm : IsStoppingTime ℱ βm)
    (hβm_finite : (Set.range βm).Finite)
    (hβm_leT : ∀ ω, βm ω ≤ (T : ENNReal))
    (c : NNReal)
    {A : Set Ω}
    (hSubset : A ⊆ {ω | βm ω = (c : ENNReal)}) :
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    hIto.toContinuousLinearMap
        ((hCutT.processBeforeStoppingTime hβm).toClosure) =ᵐ[μ.restrict A]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c := by
  -- Proof comment: the exact-atom bridge already gives the stage identity on the larger level
  -- set `{βm = c}`, so restricting further to `A` is a one-line `filter_mono`.
  exact
    (clippedDyadicStage_eq_truncation_on_exactAtom_local
      (μ := μ) (ℱ := ℱ) (W := W) K hK (T := T) hβm hβm_finite hβm_leT c)
      .filter_mono (Measure.restrict_mono hSubset)

/-- Helper for Lemma 25.13: after stopping at the bounded time `σ ∧ T`, the predictable simple
stage vanishes above the deterministic horizon `T`. -/
private theorem boundedStopped_vanishesAfter_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    {σ : Ω → ENNReal} {T : NNReal} {u : NNReal} {ω : Ω}
    (hu : T < u) :
    ProbabilityTheory.processBeforeStoppingTime
        (K : Process) (fun ω ↦ min (σ ω) (T : ENNReal)) u ω = 0 := by
  by_cases huβ : (u : ENNReal) ≤ min (σ ω) (T : ENNReal)
  · have hβ_le : min (σ ω) (T : ENNReal) ≤ (T : ENNReal) := min_le_right _ _
    have huT : (T : ENNReal) < (u : ENNReal) := by
      exact_mod_cast hu
    exact (False.elim <| (not_lt_of_ge (le_trans huβ hβ_le)) huT)
  · -- Proof comment: once the time parameter lies beyond the bounded stopping level, the stopped
    -- predictable simple stage vanishes by definition.
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, huβ]

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}`, the bounded stopped truncation at
time `T` should already agree with the deterministic truncation slice at time `c`. -/
private theorem boundedStoppedTruncation_eq_terminalStoppedDeterministicCutoff_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    {T : NNReal} :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hStopped :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[μ]
      hIto.toContinuousLinearMap
        ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure) := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  let hCutT :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
  have hDet :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[μ]
        hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hStopped T).toClosure) := by
    -- Proof comment: first rewrite the left truncation slice as the terminal map of the same
    -- integrand cut off deterministically at `T`.
    simpa using
      (deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hStopped) T).symm
  have hProcessEq :
      ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β)
          (fun _ ↦ (T : ENNReal)) =
        ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal))
          β := by
    -- Proof comment: the random cutoff by `β = σ ∧ T` commutes with the outer deterministic
    -- cutoff at `T`.
    simpa [β] using
      processBeforeStoppingTime_const_comm (G := (K : Process)) β T
  have hClosureEq :
      ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hStopped T).toClosure) =
        ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure) := by
    -- Proof comment: once the two recut processes are literally the same, their canonical
    -- closure witnesses coincide as well.
    exact
      toClosure_eq_of_process_eq_local
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hStopped T)
        (hCutT.processBeforeStoppingTime (hσ.min_const T))
        hProcessEq
  have hTerminalEq :
      hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hStopped T).toClosure) =
        hIto.toContinuousLinearMap
          ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure) := by
    -- Proof comment: apply the terminal Brownian-Itô map to the common closure point obtained
    -- from the commutation identity above.
    exact congrArg hIto.toContinuousLinearMap hClosureEq
  exact hDet.trans <| Filter.EventuallyEq.of_eq hTerminalEq

/-- Helper for Lemma 25.13: after cutting `K` deterministically at `T`, any later truncation at
time `c ≤ T` agrees with the original truncation at time `c`. -/
private theorem deterministicCutoffAtBoundTruncation_eq_originalTruncation_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {T : NNReal} (c : NNReal) (hcT : c ≤ T) :
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hCutT :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c =ᵐ[μ]
      brownianItoIntegralTruncatedProcess W Kbar c := by
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hCutT :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
  have hCutDet :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c =ᵐ[μ]
        hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hCutT c).toClosure) := by
    -- Proof comment: rewrite the truncated slice of the already cut off stage as its terminal
    -- Brownian-Itô map at the later deterministic cutoff `c`.
    simpa using
      (deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hCutT) c).symm
  have hBaseDet :
      hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage c).toClosure) =ᵐ[μ]
        brownianItoIntegralTruncatedProcess W Kbar c := by
    -- Proof comment: the original stage has the same deterministic-cutoff normalization at `c`.
    simpa [Kbar] using
      deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hKstage) c
  have hProcessEq :
      ProbabilityTheory.processBeforeStoppingTime
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal))
          (fun _ ↦ (c : ENNReal)) =
        ProbabilityTheory.processBeforeStoppingTime (K : Process)
          (fun _ ↦ (c : ENNReal)) := by
    ext s ω
    by_cases hsC : (s : ENNReal) ≤ (c : ENNReal)
    · have hsT : (s : ENNReal) ≤ (T : ENNReal) := by
        exact le_trans hsC (by exact_mod_cast hcT)
      -- Proof comment: on the active branch `s ≤ c`, the earlier cutoff at `T` is invisible.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsC, hsT]
    · -- Proof comment: once `s > c`, both deterministic cutoffs already vanish.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsC]
  have hClosureEq :
      ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hCutT c).toClosure) =
        ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hKstage c).toClosure) := by
    -- Proof comment: the two deterministic recuts coincide pointwise because `c ≤ T`.
    exact
      toClosure_eq_of_process_eq_local
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hCutT c)
        (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
          hKstage c)
        hProcessEq
  have hTerminalEq :
      hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hCutT c).toClosure) =
        hIto.toContinuousLinearMap
          ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hKstage c).toClosure) := by
    -- Proof comment: apply the terminal map to the common deterministic-cutoff closure point.
    exact congrArg hIto.toContinuousLinearMap hClosureEq
  exact hCutDet.trans <| (Filter.EventuallyEq.of_eq hTerminalEq).trans hBaseDet

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}`, the bounded stopped truncation at
time `T` should already agree with the deterministic truncation slice at time `c`. -/
private theorem boundedStoppedTruncation_eq_originalTruncation_on_minConstAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    {T : NNReal} (c : NNReal) (hcT : c ≤ T) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hStopped :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
      predictableSimpleStopped_memPredictable_local
        (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
    brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[μ.restrict A]
      brownianItoIntegralTruncatedProcess W Kbar c := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  let hCutT :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage T
  have hLeftRestr :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[
            μ.restrict A]
        hIto.toContinuousLinearMap
          ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure) := by
    -- Proof comment: normalize the left-hand truncation slice to the terminal Brownian-Itô map
    -- of the deterministically cut-off stage stopped at the bounded time `β = σ ∧ T`.
    exact
      (boundedStoppedTruncation_eq_terminalStoppedDeterministicCutoff_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hσ (T := T)).filter_mono
        (Measure.restrict_le_self A)
  have hRightRestr :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c =ᵐ[
            μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar c := by
    -- Proof comment: on the right, the earlier deterministic cutoff at `T` is irrelevant once
    -- we truncate again at the bounded time `c ≤ T`.
    exact
      (deterministicCutoffAtBoundTruncation_eq_originalTruncation_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK c hcT).filter_mono
        (Measure.restrict_le_self A)
  have hCore :
      hIto.toContinuousLinearMap
          ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure) =ᵐ[
            μ.restrict A]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c := by
    have hA_meas : MeasurableSet A :=
      measurableSet_eq_fun (hσ.min_const T).measurable' measurable_const
    have hApprox :
        ∃ βm : ℕ → Ω → ENNReal, ∃ cm : ℕ → NNReal,
          (∀ m, IsStoppingTime ℱ (βm m)) ∧
          (∀ m, (Set.range (βm m)).Finite) ∧
          (∀ m ω, β ω ≤ βm m ω) ∧
          (∀ m ω, βm m ω ≤ (T : ENNReal)) ∧
          (∀ m, c ≤ cm m) ∧
          (∀ m, cm m ≤ T) ∧
          (∀ ω, Filter.Tendsto (fun m ↦ βm m ω) Filter.atTop (nhds (β ω))) ∧
          Filter.Tendsto cm Filter.atTop (nhds c) ∧
          (∀ m, A ⊆ {ω | βm m ω = (cm m : ENNReal)}) := by
      simpa [β, A] using
        (boundedMinClippedDyadicApproximation_local
          (Ω := Ω) (ℱ := ℱ) (σ := σ) hσ (T := T) (c := c) hcT)
    rcases hApprox with
      ⟨βm, cm, hβm, hβm_finite, hβ_le, hβm_leT, hcm_ge, hcm_leT, hβm_tendsto, hcm_tendsto,
        hSubset⟩
    have hStageEq :
        ∀ n,
          hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (hβm n)).toClosure) =ᵐ[μ.restrict A]
            brownianItoIntegralTruncatedProcess W
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) (cm n) := by
      intro n
      -- Proof comment: each clipped dyadic stage is first identified on its exact atom
      -- `{βm n = cm n}`, then restricted back to the target atom `A = {β = c}`.
      exact
        clippedDyadicStage_eq_truncation_on_targetAtom_local
          (μ := μ) (ℱ := ℱ) (W := W) K hK (T := T)
          (hβm := hβm n) (hβm_finite := hβm_finite n) (hβm_leT := hβm_leT n) (c := cm n)
          (A := A) (hSubset := hSubset n)
    have hLeftLpTendsto :
        Filter.Tendsto
          (fun n : ℕ ↦ (((hCutT.processBeforeStoppingTime (hβm n)).toClosure :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)))
          Filter.atTop
          (nhds
            (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
              (((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
      -- Proof comment: the clipped dyadic stopping times decrease to the bounded stop
      -- `β = σ ∧ T`, so the stopped closure points converge in ambient `L²(μ ⊗ dt)`.
      simpa [β] using
        stoppedIntegrandLpTendsto_of_stoppingApprox_local
          (μ := μ) (ℱ := ℱ)
          (H := ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal))
          (τ := β) (τm := βm) (hτ := hσ.min_const T) (hτm := hβm) (hτm_le := hβ_le)
          (hτm_tendsto := hβm_tendsto) (hH := hCutT)
    have hLeftTerminalLpTendsto :
        Filter.Tendsto
          (fun n ↦ hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (hβm n)).toClosure))
          Filter.atTop
          (nhds
            (hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure))) := by
      -- Proof comment: apply the terminal Brownian-Itô map to the convergent stopped
      -- approximants.
      exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hLeftLpTendsto
    have hLeftInMeasure :
        MeasureTheory.TendstoInMeasure μ
          (fun n ↦ hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (hβm n)).toClosure))
          Filter.atTop
          (hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (hσ.min_const T)).toClosure)) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLeftTerminalLpTendsto
    have hConstTendsto :
        ∀ ω, Filter.Tendsto (fun n ↦ ((cm n : NNReal) : ENNReal)) Filter.atTop
          (nhds ((c : NNReal) : ENNReal)) := by
      intro ω
      exact (continuous_coe.tendsto c).comp hcm_tendsto
    have hRightLpTendsto :
        Filter.Tendsto
          (fun n : ℕ ↦ (((hCutT.processBeforeStoppingTime
              (isStoppingTime_const ℱ (cm n))).toClosure :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                  Lp ℝ 2 (MeasureTheory.processMeasure μ)))
          Filter.atTop
          (nhds
            (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
              (((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)).toClosure :
                  MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
      -- Proof comment: the deterministic cutoff times `cm n` converge down to `c`, so the
      -- deterministic recuts of `K · 1_[0,T]` converge in the same ambient closure.
      simpa using
        stoppedIntegrandLpTendsto_of_stoppingApprox_local
          (μ := μ) (ℱ := ℱ)
          (H := ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (T : ENNReal))
          (τ := fun _ ↦ (c : ENNReal))
          (τm := fun n _ ↦ (cm n : ENNReal))
          (hτ := isStoppingTime_const ℱ c)
          (hτm := fun n ↦ isStoppingTime_const ℱ (cm n))
          (hτm_le := fun n _ ↦ by exact_mod_cast hcm_ge n)
          (hτm_tendsto := hConstTendsto) (hH := hCutT)
    have hRightTerminalLpTendsto :
        Filter.Tendsto
          (fun n ↦ hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n))).toClosure))
          Filter.atTop
          (nhds
            (hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)).toClosure))) := by
      -- Proof comment: the terminal Brownian-Itô map is continuous on the deterministic recut
      -- closure points as well.
      exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hRightLpTendsto
    have hRightInMeasureRaw :
        MeasureTheory.TendstoInMeasure μ
          (fun n ↦ hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n))).toClosure))
          Filter.atTop
          (hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)).toClosure)) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp hRightTerminalLpTendsto
    have hRightSeqEq :
        ∀ n,
          hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n))).toClosure) =ᵐ[
                μ]
            brownianItoIntegralTruncatedProcess W
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) (cm n) := by
      intro n
      have hClosureEq :
          MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n))) =
            MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                hCutT (cm n)) := by
        -- Proof comment: the generic stopping constructor and the dedicated deterministic cutoff
        -- constructor package the same deterministically recut process.
        exact
          toClosure_eq_of_process_eq_local
            (hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n)))
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hCutT (cm n))
            rfl
      have hTerminalEq :
          hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ (cm n))).toClosure) =
            hIto.toContinuousLinearMap
              ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                  hCutT (cm n)).toClosure) := by
        exact congrArg hIto.toContinuousLinearMap hClosureEq
      exact
        (Filter.EventuallyEq.of_eq hTerminalEq).trans <|
          deterministicCutoffTerminal_eq_truncated_local
            (μ := μ) (ℱ := ℱ) (W := W) (hH := hCutT) (cm n)
    have hRightLimitEq :
        hIto.toContinuousLinearMap
            ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)).toClosure) =ᵐ[μ]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c := by
      have hClosureEq :
          MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)) =
            MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                hCutT c) := by
        -- Proof comment: the same deterministic-cutoff identification is used for the limit
        -- stage at time `c`.
        exact
          toClosure_eq_of_process_eq_local
            (hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c))
            (MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
              hCutT c)
            rfl
      have hTerminalEq :
          hIto.toContinuousLinearMap
              ((hCutT.processBeforeStoppingTime (isStoppingTime_const ℱ c)).toClosure) =
            hIto.toContinuousLinearMap
              ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
                  hCutT c).toClosure) := by
        exact congrArg hIto.toContinuousLinearMap hClosureEq
      exact
        (Filter.EventuallyEq.of_eq hTerminalEq).trans <|
          deterministicCutoffTerminal_eq_truncated_local
            (μ := μ) (ℱ := ℱ) (W := W) (hH := hCutT) c
    have hRightInMeasure :
        MeasureTheory.TendstoInMeasure μ
          (fun n ↦ brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) (cm n))
          Filter.atTop
          (brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hCutT) c) := by
      -- Proof comment: replace the raw deterministic-cutoff terminal sequence and its limit by
      -- the equivalent truncation-slice spelling from Definition 25.10.
      exact
        MeasureTheory.TendstoInMeasure.congr_left hRightSeqEq <|
          MeasureTheory.TendstoInMeasure.congr_right hRightLimitEq hRightInMeasureRaw
    -- Proof comment: the stagewise target-atom identities and the two convergence-in-measure
    -- limits now fit the common restricted unique-limit lemma.
    exact
      ae_eq_restrict_of_tendstoInMeasure_of_seq_local
        (μ := μ) hA_meas hLeftInMeasure hRightInMeasure hStageEq
  exact hLeftRestr.trans (hCore.trans hRightRestr)

/-- Helper for Lemma 25.13: on the bounded atom `{σ ∧ T = c}`, the terminal Brownian-Itô map of
the bounded stopped predictable-simple stage should agree with the terminal map of the
deterministic cutoff stage at time `c`. -/
private theorem predictableSimpleConstRecutTerminal_eq_constCutoff_on_minConstAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    {T : NNReal} (c : NNReal) (hcT : c ≤ T) :
    let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
    let A : Set Ω := {ω | β ω = (c : ENNReal)}
    let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.predictableSimpleProcessToClosureLocal K hK
    let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
      ⟨hK, Kbar.2⟩
    let hStoppedCanonical :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
      hKstage.processBeforeStoppingTime (hσ.min_const T)
    let hConst :
        MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (c : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage c
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical) =ᵐ[μ.restrict A]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  let hStoppedCanonical :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    hKstage.processBeforeStoppingTime (hσ.min_const T)
  let hConst :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (c : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage c
  have hStoppedClosureEq :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped := by
    -- Proof comment: the predictable-simple stopping witness and the generic closure-side
    -- stopping construction are two owners for the same stopped process.
    simpa [β, Kbar, hKstage, hStopped, hStoppedCanonical] using
      predictableSimpleStopped_toClosure_eq_local
        (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  have hCanonicalRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical) =ᵐ[
            μ.restrict A]
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T := by
    have hClosureRewrite :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical) T =
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T := by
      -- Proof comment: rewrite the canonical stopped owner to the dedicated predictable-simple
      -- stopped owner before comparing truncation slices.
      simpa using
        congrArg
          (fun Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ ↦
            brownianItoIntegralTruncatedProcess W Hbar T)
          hStoppedClosureEq
    have hCanonicalGlobal :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical) =ᵐ[μ]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStoppedCanonical) T := by
      -- Proof comment: the bounded stop `β = σ ∧ T` lies below `T`, so the terminal map is the
      -- time-`T` truncation slice of the stopped integrand.
      exact
        terminalStoppedIntegrand_ae_eq_truncatedAtBound_local
          (μ := μ) (ℱ := ℱ) (W := W)
          (σ := β) (hσ := hσ.min_const T) (T := T)
          (hσ_le := fun ω ↦ min_le_right _ _)
          (hH := hKstage)
    exact hCanonicalGlobal.filter_mono (Measure.restrict_le_self A) |>.trans <|
      Filter.EventuallyEq.of_eq hClosureRewrite
  have hTruncRestr :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[
            μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar c := by
    -- Proof comment: this is the bounded-atom truncation core isolated above.
    simpa [β, A, Kbar, hStopped] using
      boundedStoppedTruncation_eq_originalTruncation_on_minConstAtom_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hσ c hcT
  have hConstRestr :
      brownianItoIntegralTruncatedProcess W Kbar c =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) := by
    -- Proof comment: the deterministic cutoff stage at time `c` is globally identified with the
    -- time-`c` truncation slice of the original predictable-simple closure point.
    exact
      (deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hKstage) c).symm.filter_mono
        (Measure.restrict_le_self A)
  -- Proof comment: once the bounded-atom truncation identity is available, the desired terminal
  -- comparison is just the transitivity chain through the two deterministic normalizations.
  exact hCanonicalRestr.trans (hTruncRestr.trans hConstRestr)

/-- Helper for Lemma 25.13: after capping the stop by the support horizon `T`, the only
remaining predictable-simple comparison is the bounded atom theorem on `{σ ∧ T = c}`. -/
theorem predictableSimple_terminalRandomCutoff_eq_constCutoff_on_boundedStoppingAtom_local
    {W : Process} [hIto : BrownianItoIntegral μ ℱ W]
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (c : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) =ᵐ[
          μ.restrict {ω | min (σ ω) (T : ENNReal) = (c : ENNReal)}]
      hIto.toContinuousLinearMap
        ((MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const
            (⟨hK, (MeasureTheory.predictableSimpleProcessToClosureLocal K hK).2⟩) c).toClosure) := by
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  let hConst :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process)
          fun _ ↦ (c : ENNReal)) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage c
  by_cases hcT : c ≤ T
  · have hConstRestr :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W Kbar c :=
      (deterministicCutoffTerminal_eq_truncated_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hKstage) c).filter_mono
        (Measure.restrict_le_self A)
    have hStoppedZero :
        ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u →
          ProbabilityTheory.processBeforeStoppingTime (K : Process) β u ω = 0 := by
      intro u ω hu
      -- Proof comment: the bounded stop is still a stopping of a process that already vanishes
      -- after `T`, so the same support bound persists.
      simpa [β] using
        boundedStopped_vanishesAfter_local (Ω := Ω) (ℱ := ℱ) K (σ := σ) (T := T) hu
    have hStoppedRestr :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T :=
      (terminalBrownianIto_eq_truncated_of_vanishesAfter_local
        (μ := μ) (ℱ := ℱ) (W := W) (hH := hStopped) (T := T) hStoppedZero).filter_mono
        (Measure.restrict_le_self A)
    -- Route correction: the unrestricted atom bridges were stronger than the actual downstream
    -- use. The only remaining gap is now the atom-local comparison between the time-`T`
    -- truncation slice of the bounded stopped stage and the time-`c` truncation slice of `K`.
    have hBoundedAtom :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W Kbar c := by
      have hTruncAtom :
          brownianItoIntegralTruncatedProcess W
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) T =ᵐ[
                μ.restrict A]
            brownianItoIntegralTruncatedProcess W Kbar c := by
        -- Proof comment: the bounded atom comparison has been reduced to one explicit restricted
        -- deterministic-truncation transport lemma.
        simpa [β, A, Kbar, hStopped] using
          boundedStoppedTruncation_eq_originalTruncation_on_minConstAtom_local
            (μ := μ) (ℱ := ℱ) (W := W) K hK hσ c hcT
      exact hStoppedRestr.trans hTruncAtom
    simpa [A, β, Kbar, hKstage, hStopped, hConst] using
      hBoundedAtom.trans hConstRestr.symm
  · have hEmpty : A = ∅ := by
      simpa [A, β] using
        minConstLevelSet_eq_empty_of_lt_local (σ := σ) (T := T) (c := c) (lt_of_not_ge hcT)
    -- Proof comment: if `c > T`, the bounded atom is empty, so the restricted statement is
    -- trivial.
    simp [A, β, hEmpty]

/-- Helper for Lemma 25.13: the bounded atom `{σ ∧ T = c}` is empty when `c > T`. -/
private theorem minConstLevelSet_eq_empty_of_lt_local
    {σ : Ω → ENNReal} {T c : NNReal}
    (hcT : T < c) :
    {ω | min (σ ω) (T : ENNReal) = (c : ENNReal)} = (∅ : Set Ω) := by
  ext ω
  constructor
  · intro hω
    have hle : min (σ ω) (T : ENNReal) ≤ (T : ENNReal) := min_le_right _ _
    have hc_le : c ≤ T := by
      exact_mod_cast (hω ▸ hle)
    exact (not_le_of_gt hcT hc_le).elim
  · intro hω
    simpa using hω

/-- Helper for Lemma 25.13: after capping the stop by the support horizon `T`, the remaining
predictable-simple stage comparison is purely atom-local on `{σ ∧ T = c}`. -/
private theorem predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_boundedMinAtom_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    {T : NNReal}
    (hzero : ∀ ⦃u : NNReal⦄ ⦃ω : Ω⦄, T < u → (K : Process) u ω = 0)
    (c : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) =ᵐ[
          μ.restrict {ω | min (σ ω) (T : ENNReal) = (c : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) c := by
  -- Route correction: the old owner-side sampled-martingale route does not apply here because
  -- this theorem has only the Definition 25.10 closure hypotheses. The bounded atom comparison is
  -- reduced instead to one restricted terminal-map transport lemma.
  let β : Ω → ENNReal := fun ω ↦ min (σ ω) (T : ENNReal)
  let A : Set Ω := {ω | β ω = (c : ENNReal)}
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let hStopped :
      MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime (K : Process) β) :=
    predictableSimpleStopped_memPredictable_local
      (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T)
  by_cases hcT : c ≤ T
  · let hConst :
      MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime (K : Process)
            fun _ ↦ (c : ENNReal)) :=
      MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime_const hKstage c
    have hTerminalEq :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[
              μ.restrict A]
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) :=
      predictableSimple_terminalRandomCutoff_eq_constCutoff_on_boundedStoppingAtom_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hσ hzero c
    have hConstGlobal :
        brownianItoIntegralTruncatedProcess W Kbar c =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) := by
      -- Proof comment: deterministic stopping identifies the time-`c` truncation slice of `K`
      -- with the terminal map of the deterministic cutoff stage.
      simpa [Kbar, hKstage, hConst] using
        (((Filter.EventuallyEq.of_eq
            (brownianItoIntegralStoppedValue_const W Kbar c)).symm).trans
          stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
            (W := W) (hH := hKstage) c)
    have hConstRestr :
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hConst) =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W Kbar c :=
      hConstGlobal.symm.filter_mono (Measure.restrict_le_self A)
    -- Proof comment: after the restricted time-space normalization, only the deterministic
    -- stopping identity remains.
    simpa [A, β, Kbar, hStopped] using hTerminalEq.trans hConstRestr
  · have hEmpty : A = ∅ := by
      simpa [A, β] using
        minConstLevelSet_eq_empty_of_lt_local (σ := σ) (T := T) (c := c) (lt_of_not_ge hcT)
    -- Proof comment: if `c > T`, then the bounded atom is empty because `σ ∧ T` never exceeds
    -- the deterministic horizon `T`.
    simp [A, β, hEmpty]

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, the terminal Brownian-Itô map of a stopped
predictable simple stage should collapse to the deterministic time-`t` truncation slice. -/
private theorem predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_levelSet_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (t : NNReal) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK hσ)) =ᵐ[
          μ.restrict {ω | σ ω = (t : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) t := by
  rcases predictableSimpleProcess_eq_zero_of_last_lt_local (Ω := Ω) K with ⟨T, hzero⟩
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let A : Set Ω := {ω | σ ω = (t : ENNReal)}
  let B : Set Ω := {ω | min (σ ω) (T : ENNReal) = (min t T : NNReal)}
  have hStopEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK hσ)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) :=
    terminalStoppedIntegrand_eq_min_const_of_vanishesAfter_local
      (μ := μ) (ℱ := ℱ) (W := W) (H := (K : Process)) hzero hσ hKstage
  have hStopRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK hσ)) =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) :=
    (Filter.EventuallyEq.of_eq hStopEq).filter_mono (Measure.restrict_le_self A)
  have hSubset : A ⊆ B := by
    simpa [A, B] using levelSet_subset_minConstLevelSet_local (σ := σ) t T
  have hBoundedRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) =ᵐ[μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar (min t T) := by
    simpa [Kbar, A, B] using
      (predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_boundedMinAtom_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hσ hzero (min t T)).filter_mono
          (Measure.restrict_mono hSubset)
  have hMinRestr :
      brownianItoIntegralTruncatedProcess W Kbar (min t T) =ᵐ[μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar t :=
    (predictableSimple_truncatedProcess_eq_min_const_of_vanishesAfter_local
      (μ := μ) (ℱ := ℱ) (W := W) K hK hzero t).filter_mono
        (Measure.restrict_le_self A)
  -- Proof comment: first cap the stop by the support horizon, then restrict the resulting
  -- bounded-min identity back from `{σ ∧ T = min t T}` to the target atom `{σ = t}`.
  exact hStopRestr.trans (hBoundedRestr.trans hMinRestr)

/-- Helper for Lemma 25.13: on the top atom `{σ = ∞}`, stopping a predictable simple stage does
not change its terminal Brownian-Itô map. -/
private theorem predictableSimple_terminalStoppedIntegrand_ae_eq_self_on_topLevelSet_local
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK :
      MemLp (MeasureTheory.processToTimeSpaceFun ((K : Process))) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ) :
    hIto.toContinuousLinearMap
        (MeasureTheory.predictableSimpleProcessToClosureLocal K hK) =ᵐ[
          μ.restrict {ω | σ ω = ∞}]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (predictableSimpleStopped_memPredictable_local
            (μ := μ) (ℱ := ℱ) K hK hσ)) := by
  rcases predictableSimpleProcess_eq_zero_of_last_lt_local (Ω := Ω) K with ⟨T, hzero⟩
  let Kbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.predictableSimpleProcessToClosureLocal K hK
  let hKstage : MemPredictableStepProcessClosure ℱ μ (K : Process) :=
    ⟨hK, Kbar.2⟩
  let A : Set Ω := {ω | σ ω = ∞}
  let B : Set Ω := {ω | min (σ ω) (T : ENNReal) = (T : ENNReal)}
  have hStopEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK hσ)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) :=
    terminalStoppedIntegrand_eq_min_const_of_vanishesAfter_local
      (μ := μ) (ℱ := ℱ) (W := W) (H := (K : Process)) hzero hσ hKstage
  have hStopRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK hσ)) =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) :=
    (Filter.EventuallyEq.of_eq hStopEq).filter_mono (Measure.restrict_le_self A)
  have hSubset : A ⊆ B := by
    simpa [A, B] using topLevelSet_subset_minConstTopLevelSet_local (σ := σ) T
  have hBoundedRestr :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (predictableSimpleStopped_memPredictable_local
              (μ := μ) (ℱ := ℱ) K hK (hσ.min_const T))) =ᵐ[μ.restrict A]
        brownianItoIntegralTruncatedProcess W Kbar T := by
    simpa [Kbar, A, B] using
      (predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_boundedMinAtom_local
        (μ := μ) (ℱ := ℱ) (W := W) K hK hσ hzero T).filter_mono
          (Measure.restrict_mono hSubset)
  have hTerminalRestr :
      brownianItoIntegralTruncatedProcess W Kbar T =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap Kbar :=
    (predictableSimple_truncatedProcess_eq_terminal_of_supportBound_local
      (μ := μ) (ℱ := ℱ) (W := W) K hK hzero le_rfl).filter_mono
        (Measure.restrict_le_self A)
  -- Proof comment: on `{σ = ∞}`, the bounded stop is exactly `T`, and the time-`T` truncation is
  -- already the terminal Brownian-Itô map because the predictable simple stage vanishes after `T`.
  exact (hStopRestr.trans (hBoundedRestr.trans hTerminalRestr)).symm

/-- Helper for Lemma 25.13: on a single stopping-time atom `{σ = s}`, the terminal Brownian-Itô
map of the randomly stopped integrand agrees with the corresponding deterministic reference
branch. -/
private theorem terminalStoppedIntegrand_ae_eq_atomReference_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (s : ENNReal) :
    hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) =ᵐ[
        μ.restrict {ω | σ ω = s}]
      if hs : s = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH)
      else
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH)
          s.toNNReal := by
  -- Route correction: the failed `μ.restrict A` transport theorem was too abstract.
  -- The actual missing bridge is the direct atom comparison, proved by the two predictable-simple
  -- normalization lemmas immediately above and then lifted through the stopping-strip `L²`
  -- continuity API.
  let A : Set Ω := {ω | σ ω = s}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H σ) :=
    hH.processBeforeStoppingTime hσ
  rcases
      MeasureTheory.existsPredictableSimpleApproximationOfClosurePointLocal
        (Ω := Ω) (ℱ := ℱ) (μ := μ) hH.toClosure with
    ⟨Ks, hKs_mem, hKs_tendsto⟩
  have hKsStopped :
      ∀ n,
        MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (ProbabilityTheory.processBeforeStoppingTime ((Ks n : Process)) σ) := by
    intro n
    -- Proof comment: each predictable-simple approximant stays admissible after stopping.
    exact
      predictableSimpleStopped_memPredictable_local
        (Ω := Ω) (ℱ := ℱ) (μ := μ) (K := Ks n) (hK := hKs_mem n) (hτ := hσ)
  have hStoppedLpTendsto :
      Filter.Tendsto
        (fun n ↦ (((hKsStopped n).toClosure :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ)))
        Filter.atTop
        (nhds
          (stoppingStripLpMap_local (Ω := Ω) (μ := μ) (ℱ := ℱ) (τ := σ) hσ
            (((hH.toClosure : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))) := by
    -- Proof comment: the common stopping-strip operator transports the predictable-simple
    -- approximation of `H` to a predictable-simple approximation of `H^(σ)`.
    exact
      processBeforeStoppingTime_toLp_tendsto_of_closureApprox_local
        (Ω := Ω) (ℱ := ℱ) (μ := μ) (τ := σ) hσ hH hKs_mem hKsStopped hKs_tendsto
  have hStoppedTerminalLpTendsto :
      Filter.Tendsto
        (fun n ↦ hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)))
        Filter.atTop
        (nhds (hIto.toContinuousLinearMap hStopped.toClosure)) := by
    -- Proof comment: apply the terminal Brownian-Itô map to the stopped `L²` approximation.
    exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hStoppedLpTendsto
  have hStoppedTerminalInMeasure :
      MeasureTheory.TendstoInMeasure μ
        (fun n ↦ hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)))
        Filter.atTop
        (hIto.toContinuousLinearMap hStopped.toClosure) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hStoppedTerminalLpTendsto
  by_cases hs : s = ∞
  · have hBaseLpTendsto :
        Filter.Tendsto
          (fun n ↦ hIto.toContinuousLinearMap
            (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)))
          Filter.atTop
          (nhds (hIto.toContinuousLinearMap hH.toClosure)) := by
      -- Proof comment: the original predictable-simple approximants converge to `H` in the same
      -- closure topology, so their terminal Brownian-Itô values converge in `L²(μ)`.
      exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hKs_tendsto
    have hBaseInMeasure :
        MeasureTheory.TendstoInMeasure μ
          (fun n ↦ hIto.toContinuousLinearMap
            (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)))
          Filter.atTop
          (hIto.toContinuousLinearMap hH.toClosure) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp hBaseLpTendsto
    have hStageEq :
        ∀ n,
          hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)) =ᵐ[
                μ.restrict A]
            hIto.toContinuousLinearMap
              (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)) := by
      intro n
      -- Proof comment: on the top atom, each stopped predictable-simple stage agrees with its
      -- original terminal Brownian-Itô map by the stage-level normalization theorem.
      simpa [A, hs] using
        (predictableSimple_terminalStoppedIntegrand_ae_eq_self_on_topLevelSet_local
          (μ := μ) (ℱ := ℱ) (W := W) (K := Ks n) (hK := hKs_mem n) hσ).symm
    have hRestrEq :
        hIto.toContinuousLinearMap hStopped.toClosure =ᵐ[μ.restrict A]
          hIto.toContinuousLinearMap hH.toClosure :=
      ae_eq_restrict_of_tendstoInMeasure_of_seq_local
        (μ := μ) hA_meas hStoppedTerminalInMeasure hBaseInMeasure hStageEq
    simpa [hs, hStopped] using hRestrEq
  · let t : NNReal := s.toNNReal
    have hCutLpTendsto :
        Filter.Tendsto
          (fun n ↦
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
              (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)) :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ))
          Filter.atTop
          (nhds
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t hH.toClosure)) := by
      -- Proof comment: deterministic cutoff is a continuous linear operator on the closure, so it
      -- preserves the predictable-simple approximation.
      exact
        ((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore
            (ℱ := ℱ) (μ := μ) t).continuous.tendsto _).comp hKs_tendsto
    have hTruncLpTendsto :
        Filter.Tendsto
          (fun n ↦ brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)) t)
          Filter.atTop
          (nhds (brownianItoIntegralTruncatedProcess W hH.toClosure t)) := by
      -- Proof comment: after deterministic cutoff, apply the same terminal Brownian-Itô map.
      simpa [brownianItoIntegralTruncatedProcess] using
        (hIto.toContinuousLinearMap.continuous.tendsto _).comp hCutLpTendsto
    have hTruncInMeasure :
        MeasureTheory.TendstoInMeasure μ
          (fun n ↦ brownianItoIntegralTruncatedProcess W
            (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)) t)
          Filter.atTop
          (brownianItoIntegralTruncatedProcess W hH.toClosure t) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTruncLpTendsto
    have hStageEq :
        ∀ n,
          hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure (hKsStopped n)) =ᵐ[
                μ.restrict A]
            brownianItoIntegralTruncatedProcess W
              (MeasureTheory.predictableSimpleProcessToClosureLocal (Ks n) (hKs_mem n)) t := by
      intro n
      -- Proof comment: on the finite atom `{σ = s}`, each stopped predictable-simple stage
      -- collapses to the deterministic time-`s.toNNReal` truncation slice.
      simpa [A, hs, t] using
        predictableSimple_terminalStoppedIntegrand_ae_eq_truncatedProcess_on_levelSet_local
          (μ := μ) (ℱ := ℱ) (W := W) (K := Ks n) (hK := hKs_mem n) hσ t
    have hRestrEq :
        hIto.toContinuousLinearMap hStopped.toClosure =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W hH.toClosure t :=
      ae_eq_restrict_of_tendstoInMeasure_of_seq_local
        (μ := μ) hA_meas hStoppedTerminalInMeasure hTruncInMeasure hStageEq
    simpa [hs, hStopped, t] using hRestrEq

/-- Helper for Lemma 25.13: on the atom `{σ = t}`, the terminal map of the random stopped
integrand should collapse to the deterministic time-`t` truncation slice. -/
private theorem terminalStoppedIntegrand_ae_eq_truncatedProcess_on_levelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) =ᵐ[
        μ.restrict {ω | σ ω = (t : ENNReal)}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) t := by
  -- Proof comment: this is the finite branch of the unified atom theorem above.
  simpa [ENNReal.coe_ne_top] using
    terminalStoppedIntegrand_ae_eq_atomReference_local
      (μ := μ) (ℱ := ℱ) (W := W) hσ hH (t : ENNReal)

/-- Helper for Lemma 25.13: on the top atom `{σ = ∞}`, stopping does not change the terminal
Brownian-Itô map. -/
private theorem terminalStoppedIntegrand_ae_eq_self_on_topLevelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) =ᵐ[
          μ.restrict {ω | σ ω = ∞}]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  -- Proof comment: this is the top branch of the unified atom theorem above.
  simpa using
    (terminalStoppedIntegrand_ae_eq_atomReference_local
      (μ := μ) (ℱ := ℱ) (W := W) hσ hH (∞ : ENNReal)).symm

/-- Helper for Lemma 25.13: the unresolved countable-range route is the single core theorem
behind the later `{σ = ∞}` and `{σ = t}` branch corollaries. -/
private theorem martingaleSampledOwner_ae_eq_terminalStoppedIntegrand_of_countableRange_core_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
        else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
          σ ω) =ᵐ[μ]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped :
      MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    (hH.processBeforeStoppingTime hσ).toClosure
  let syncSet : Set NNReal := ENNReal.toNNReal '' Set.range σ
  have hSyncSet_countable : syncSet.Countable := hσ_count.image ENNReal.toNNReal
  let _ : Countable syncSet := hSyncSet_countable.to_subtype
  have hMartAll :
      ∀ᵐ ω ∂μ, ∀ t : syncSet,
        BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar t ω =
          hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) ω := by
    -- Proof comment: package the deterministic-time synchronization on the countable family of
    -- sampled finite values of `σ`.
    simpa [Hbar, syncSet] using
      martingaleProcess_ae_eq_cutoffTerminal_on_countableSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hSyncSet_countable hH
  have hAtomAll :
      ∀ᵐ ω ∂μ, ∀ t : syncSet,
        σ ω = ((t : NNReal) : ENNReal) →
          hIto.toContinuousLinearMap
              (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) ω =
            hIto.toContinuousLinearMap hStopped ω := by
    rw [ae_all_iff]
    intro t
    let A : Set Ω := {ω | σ ω = ((t : NNReal) : ENNReal)}
    have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
    have hDetGlobal :
        brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ]
          hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) := by
      -- Proof comment: the deterministic stopping theorem identifies the time-`t` truncation
      -- slice with the terminal map of the deterministic cutoff integrand.
      simpa [deterministicConstCutoffClosure_local] using
        (((Filter.EventuallyEq.of_eq
            (brownianItoIntegralStoppedValue_const W hH.toClosure t)).symm).trans <|
          stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
            (W := W) (hH := hH) t)
    have hDetRestr :
        brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ.restrict A]
          hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) :=
      hDetGlobal.filter_mono (Measure.restrict_le_self A)
    have hStoppedRestr :
        hIto.toContinuousLinearMap hStopped =ᵐ[μ.restrict A]
          brownianItoIntegralTruncatedProcess W hH.toClosure t := by
      simpa [A, hStopped] using
        terminalStoppedIntegrand_ae_eq_truncatedProcess_on_levelSet_local
          (μ := μ) (ℱ := ℱ) (W := W) hσ hH t
    have hAtomRestr :
        hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) =ᵐ[
              μ.restrict A]
          hIto.toContinuousLinearMap hStopped :=
      hDetRestr.symm.trans hStoppedRestr.symm
    exact (ae_restrict_iff' hA_meas).1 hAtomRestr
  have hTopAll :
      ∀ᵐ ω ∂μ, σ ω = ∞ →
        hIto.toContinuousLinearMap Hbar ω =
          hIto.toContinuousLinearMap hStopped ω := by
    let A : Set Ω := {ω | σ ω = ∞}
    have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
    have hTopRestr :
        hIto.toContinuousLinearMap Hbar =ᵐ[μ.restrict A]
          hIto.toContinuousLinearMap hStopped := by
      simpa [A, Hbar, hStopped] using
        terminalStoppedIntegrand_ae_eq_self_on_topLevelSet_local
          (μ := μ) (ℱ := ℱ) (W := W) hσ hH
    exact (ae_restrict_iff' hA_meas).1 hTopRestr
  filter_upwards [hMartAll, hAtomAll, hTopAll] with ω hωMart hωAtom hωTop
  by_cases hσ_top : σ ω = ∞
  · -- Proof comment: on the top atom, the sampled owner is definitionally the terminal Brownian
    -- Itô map of the unstopped integrand.
    simpa [Hbar, hStopped, hσ_top] using hωTop hσ_top
  · let t : NNReal := (σ ω).toNNReal
    have ht_mem : t ∈ syncSet := by
      refine ⟨σ ω, ⟨ω, rfl⟩, ?_⟩
      simp [t]
    have hσ_eq_t : σ ω = ((t : NNReal) : ENNReal) := by
      simpa [t] using (ENNReal.coe_toNNReal hσ_top).symm
    have hOwnerSlice :
        BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar t ω =
          hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) ω :=
      hωMart ⟨t, ht_mem⟩
    have hAtomSlice :
        hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) ω =
          hIto.toContinuousLinearMap hStopped ω :=
      hωAtom ⟨t, ht_mem⟩ hσ_eq_t
    -- Proof comment: on the finite branch, the sampled owner is the deterministic martingale
    -- slice at the sampled time, and the atomwise deterministic-cutoff comparison closes the gap.
    calc
      (if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W) Hbar)
          σ ω) =
          BrownianItoIntegral.brownianItoIntegralMartingaleProcess W Hbar t ω := by
            simpa [t] using
              martingaleSampledOwner_apply_eq_martingaleSlice_of_ne_top_local
                (W := W) Hbar (ω := ω) hσ_top
      _ =
          hIto.toContinuousLinearMap
            (deterministicConstCutoffClosure_local (μ := μ) (ℱ := ℱ) hH t) ω := by
              exact hOwnerSlice
      _ = hIto.toContinuousLinearMap hStopped ω := by
              exact hAtomSlice

/-- Helper for Lemma 25.13: on a countable-range stopping time `σ`, the sampled martingale owner
from Theorem 25.11 should already agree almost surely with the terminal Brownian-Itô map of the
stopped integrand. -/
private theorem terminalRandomCutoff_eq_self_on_topLevelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) =ᵐ[μ.restrict {ω | σ ω = ∞}]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  -- Proof comment: the top-atom comparison is now a direct restricted branch lemma, so this
  -- downstream alias no longer depends on the unresolved countable-range core.
  simpa using
    terminalStoppedIntegrand_ae_eq_self_on_topLevelSet_local
      (μ := μ) (ℱ := ℱ) (W := W) hσ hH

/-- Helper for Lemma 25.13: on the level set `{σ = t}`, the terminal Brownian-Itô map of the
deterministic cutoff `H^(t)` agrees with the terminal map of the random cutoff `H^(σ)`. -/
private theorem terminalConstCutoff_eq_randomCutoff_on_levelSet_local
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    hIto.toContinuousLinearMap
        (deterministicConstCutoffClosure_local hH t) =ᵐ[
          μ.restrict {ω | σ ω = (t : ENNReal)}]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  let A : Set Ω := {ω | σ ω = (t : ENNReal)}
  have hA_meas : MeasurableSet A := measurableSet_eq_fun hσ.measurable' measurable_const
  have hDetGlobal :
      brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ]
        hIto.toContinuousLinearMap (deterministicConstCutoffClosure_local hH t) := by
    -- Proof comment: the deterministic stopping theorem identifies the time-`t` truncation
    -- slice with the terminal map of the deterministic cutoff integrand.
    simpa [deterministicConstCutoffClosure_local] using
      (((Filter.EventuallyEq.of_eq
          (brownianItoIntegralStoppedValue_const W hH.toClosure t)).symm).trans <|
        stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const
          (W := W) (hH := hH) t)
  have hDetRestr :
      brownianItoIntegralTruncatedProcess W hH.toClosure t =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap (deterministicConstCutoffClosure_local hH t) :=
    hDetGlobal.filter_mono (Measure.restrict_le_self A)
  have hStoppedRestr :
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) =ᵐ[μ.restrict A]
        brownianItoIntegralTruncatedProcess W hH.toClosure t := by
    simpa [A] using
      terminalStoppedIntegrand_ae_eq_truncatedProcess_on_levelSet_local
        (μ := μ) (ℱ := ℱ) (W := W) hσ hH t
  -- Proof comment: both the deterministic cutoff and the random cutoff are identified with the
  -- same deterministic truncation slice on the atom `{σ = t}`.
  exact hDetRestr.symm.trans hStoppedRestr.symm

/-- Helper for Lemma 25.13: on a countable-range stopping time `σ`, the sampled martingale owner
from Theorem 25.11 should already agree almost surely with the terminal Brownian-Itô map of the
stopped integrand. -/
private theorem martingaleSampledOwner_ae_eq_terminalStoppedIntegrand_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    (fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
          σ ω) =ᵐ[μ]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  -- Proof comment: the countable-range work is now concentrated in the core theorem above, so
  -- downstream proofs can continue to use the original helper name unchanged.
  exact
    martingaleSampledOwner_ae_eq_terminalStoppedIntegrand_of_countableRange_core_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hσ hσ_count hH

/-- Helper for Lemma 25.13: on a countable-range stopping time `σ`, the raw stopped Brownian-Itô
value already agrees almost surely with the terminal Brownian-Itô map of the stopped integrand.
-/
private theorem stoppedBrownianIntegral_ae_eq_integral_stoppedIntegrand_of_countableRange_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {σ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    brownianItoIntegralStoppedValue W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) σ =ᵐ[μ]
      hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) := by
  have hOwner :
      (fun ω ↦
        if σ ω = ∞ then
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
            σ ω) =ᵐ[μ]
        hIto.toContinuousLinearMap ((hH.processBeforeStoppingTime hσ).toClosure) :=
    martingaleSampledOwner_ae_eq_terminalStoppedIntegrand_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hσ hσ_count hH
  have hRawToOwner :
      (fun ω ↦
        if σ ω = ∞ then
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.brownianItoIntegralMartingaleProcess (W := W)
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH))
            σ ω) =ᵐ[μ]
        brownianItoIntegralStoppedValue W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hH) σ :=
    martingaleSampledOwner_ae_eq_brownianStoppedValue_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hH.toClosure hσ_count
  -- Proof comment: after normalizing the countable-range stop through the martingale sampled
  -- owner, the raw stopped value theorem is just a transitivity step.
  exact hRawToOwner.symm.trans hOwner

/-- Helper for Lemma 25.13: the sampled continuous-modification owner converges pointwise along a
stopping-time approximation whose `∞` branch is preserved. -/
private theorem continuousModification_sampledValue_tendsto_of_stoppingApprox_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτm_top : ∀ n ω, τm n ω = ∞ ↔ τ ω = ∞)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) Filter.atTop (nhds (τ ω))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n ↦
          if τm n ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω)
        Filter.atTop
        (nhds
          (if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) := by
  have hCont :
      HasAlmostSurelyContinuousPaths μ
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar) :=
    (BrownianItoIntegral.continuousModification_spec
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar).1
  filter_upwards [hCont] with ω hωCont
  by_cases htop : τ ω = ∞
  · have hEventuallyTop :
      ∀ᶠ n in Filter.atTop, τm n ω = ∞ :=
        Filter.Eventually.of_forall fun n ↦ (hτm_top n ω).2 htop
    have hEventuallyEq :
        (fun n ↦
          if τm n ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω) =ᶠ[Filter.atTop]
          fun _ ↦ hIto.toContinuousLinearMap Hbar ω := by
      filter_upwards [hEventuallyTop] with n hn
      simp [hn]
    -- Proof comment: once the approximation stays on the `∞` branch, the sampled owner is
    -- literally constant and converges to the same terminal Brownian-Itô value.
    simpa [htop] using
      Tendsto.congr' hEventuallyEq tendsto_const_nhds
  · have hτm_fin : ∀ n, τm n ω ≠ ∞ := fun n htopm ↦ htop ((hτm_top n ω).1 htopm)
    have hTimeTendsto :
        Filter.Tendsto (fun n ↦ (τm n ω).toNNReal) Filter.atTop (nhds ((τ ω).toNNReal)) := by
      exact (ENNReal.tendsto_toNNReal_iff htop hτm_fin).2 (hτm_tendsto ω)
    have hSampleTendsto :
        Filter.Tendsto
          (fun n ↦
            BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar ((τm n ω).toNNReal) ω)
          Filter.atTop
          (nhds
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar ((τ ω).toNNReal) ω)) := by
      -- Proof comment: on the finite branch, path continuity turns convergence of stopping
      -- levels into convergence of the sampled continuous modification values.
      simpa [ProbabilityTheory.processPath] using
        hωCont.continuousAt.tendsto.comp hTimeTendsto
    -- Proof comment: after simplifying the finite branch of the sampled owner, this is exactly
    -- the pathwise continuity statement above.
    simpa [MeasureTheory.stoppedValue, htop, hτm_fin] using
      hSampleTendsto

/-- Helper for Lemma 25.13: if stopping times `τm` converge pointwise to `τ` from above, then the
canonical closure points of the stopped integrands converge in ambient `L²(μ ⊗ dt)`. -/
private theorem stoppedIntegrand_toClosure_tendsto_of_stoppingApprox_local
    {H : Process} {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm : ∀ n, IsStoppingTime ℱ (τm n))
    (hτm_le : ∀ n ω, τ ω ≤ τm n ω)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) (Filter.atTop : Filter ℕ) (nhds (τ ω)))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    Filter.Tendsto
      (fun n : ℕ ↦ (((hH.processBeforeStoppingTime (hτm n)).toClosure :
          MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))
      (Filter.atTop : Filter ℕ)
      (nhds
        (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
          (((hH.processBeforeStoppingTime hτ).toClosure :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))) := by
  let hStopped := fun n : ℕ ↦
    (hH.processBeforeStoppingTime (hτm n) :
      MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (ProbabilityTheory.processBeforeStoppingTime H (τm n)))
  let hStoppedLim : MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (ProbabilityTheory.processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  have hLpNorm :
      Filter.Tendsto
        (fun n ↦
          eLpNorm
            (MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
              MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H τ))
            (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ))
        Filter.atTop
        (𝓝 0) := by
    have hTwo_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hTwo_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have hTwo_pos : 0 < ((2 : ℝ≥0∞).toReal) :=
      ENNReal.toReal_pos hTwo_ne_zero hTwo_ne_top
    suffices hIntegral :
        Filter.Tendsto
          (fun n ↦
            ∫⁻ x, ‖(MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                  MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ) ∂
              MeasureTheory.processMeasure μ)
          Filter.atTop
          (𝓝 0) by
      -- Proof comment: for `p = 2`, ambient `Lp` convergence is exactly vanishing of the square
      -- integral of the stopped difference.
      simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hTwo_ne_zero hTwo_ne_top]
      convert continuous_rpow_const.continuousAt.tendsto.comp hIntegral
      simp [zero_rpow_of_pos (_root_.inv_pos.mpr hTwo_pos)]
    have hF_meas :
        ∀ n,
          AEMeasurable
            (fun x ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ))
            (MeasureTheory.processMeasure μ) := by
      intro n
      exact
        ((hStopped n).memLp.aemeasurable.sub hStoppedLim.memLp.aemeasurable).enorm.pow_const
          (2 : ℝ)
    have hBound :
        ∀ n,
          (fun x ↦
            ‖(MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                  MeasureTheory.processToTimeSpaceFun
                    (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) ≤ᵐ[MeasureTheory.processMeasure μ]
            fun x ↦ ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ) := by
      intro n
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxle : τ x.1 ≤ τm n x.1 := hτm_le n x.1
      by_cases hxτ : ENNReal.ofReal x.2 ≤ τ x.1
      · have hxτm : ENNReal.ofReal x.2 ≤ τm n x.1 := le_trans hxτ hxle
        -- Proof comment: inside the limiting strip, both stopped representatives agree, so the
        -- pointwise difference vanishes.
        simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
          hxτ, hxτm]
      · by_cases hxτm : ENNReal.ofReal x.2 ≤ τm n x.1
        · -- Proof comment: on the shrinking strip difference, the stopped difference is exactly
          -- the original integrand.
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        · -- Proof comment: outside the approximating strip, both stopped representatives vanish.
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
    have hFinite :
        (∫⁻ x, ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ) ∂
            MeasureTheory.processMeasure μ) ≠
          ∞ := by
      exact
        (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hTwo_ne_zero hTwo_ne_top
          hH.memLp.eLpNorm_lt_top).ne
    have hLimit :
        ∀ᵐ x ∂MeasureTheory.processMeasure μ,
          Filter.Tendsto
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ))
            Filter.atTop
            (𝓝 0) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hxτ : ENNReal.ofReal x.2 ≤ τ x.1
      · -- Proof comment: once `x` is inside the limiting strip, `hτm_le` keeps it inside every
        -- approximating strip as well, so the difference is identically zero.
        have hEventuallyEq :
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) =ᶠ[Filter.atTop]
              fun _ ↦ 0 := by
          refine Filter.Eventually.of_forall ?_
          intro n
          have hxτm : ENNReal.ofReal x.2 ≤ τm n x.1 := le_trans hxτ (hτm_le n x.1)
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
      · have hEventuallyLt :
          ∀ᶠ n in Filter.atTop, τm n x.1 < ENNReal.ofReal x.2 :=
          (hτm_tendsto x.1).eventually (Iio_mem_nhds (lt_of_not_ge hxτ))
        have hEventuallyEq :
            (fun n ↦
              ‖(MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H (τm n)) -
                    MeasureTheory.processToTimeSpaceFun
                      (ProbabilityTheory.processBeforeStoppingTime H τ)) x‖ₑ ^ (2 : ℝ)) =ᶠ[Filter.atTop]
              fun _ ↦ 0 := by
          filter_upwards [hEventuallyLt] with n hn
          have hxτm : ¬ ENNReal.ofReal x.2 ≤ τm n x.1 := not_le_of_gt hn
          simp [MeasureTheory.processToTimeSpaceFun_processBeforeStoppingTime_eq_indicator,
            hxτ, hxτm]
        -- Proof comment: once `τm n x.1` falls below the fixed time level `x.2`, both stopped
        -- representatives vanish at `x`.
        exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
    -- Proof comment: the stopped-strip difference is bounded by the original square-integrable
    -- integrand and tends pointwise to zero, so dominated convergence gives vanishing square
    -- integral.
    simpa using
      MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (fun x ↦ ‖MeasureTheory.processToTimeSpaceFun H x‖ₑ ^ (2 : ℝ))
        hF_meas hBound hFinite hLimit
  have hLp :
      Filter.Tendsto
        (fun n ↦
          (hStopped n).memLp.toLp
            (MeasureTheory.processToTimeSpaceFun
              (ProbabilityTheory.processBeforeStoppingTime H (τm n))))
        Filter.atTop
        (nhds
          (show Lp ℝ 2 (MeasureTheory.processMeasure μ) from
            hStoppedLim.memLp.toLp
              (MeasureTheory.processToTimeSpaceFun
                (ProbabilityTheory.processBeforeStoppingTime H τ)))) := by
    -- Proof comment: once the `L²(processMeasure μ)` seminorm of the stopped difference tends to
    -- zero, the corresponding ambient `Lp` classes converge.
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n ↦
          MeasureTheory.processToTimeSpaceFun
            (ProbabilityTheory.processBeforeStoppingTime H (τm n)))
        (fun n ↦ (hStopped n).memLp)
        (MeasureTheory.processToTimeSpaceFun
          (ProbabilityTheory.processBeforeStoppingTime H τ))
        hStoppedLim.memLp).2 hLpNorm
  simpa [hStopped, hStoppedLim] using hLp

-- Proof sketch: the remaining dyadic-stage normalization is the source proof's countable-range
-- step. The current file already contains the subsequence/continuity limit machinery, so the only
-- missing Lean work is to identify each dyadic stage on the right with the sampled continuous
-- modification owner used on the left.
/-- Helper for Lemma 25.13: each dyadic approximant stage should identify the stopped-integrand
terminal map with the sampled continuous-modification owner at that same dyadic stopping time. -/
private theorem dyadicApproxStageEqSampledOwner_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τm : ℕ → Ω → ENNReal}
    (hτm_stop : ∀ m, IsStoppingTime ℱ (τm m))
    (hτm_count : ∀ m, (Set.range (τm m)).Countable)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (m : ℕ) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime H (τm m)) :=
      hH.processBeforeStoppingTime (hτm_stop m)
    hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) =ᵐ[μ]
      (fun ω ↦
        if τm m ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm m) ω) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ
      (processBeforeStoppingTime H (τm m)) :=
    hH.processBeforeStoppingTime (hτm_stop m)
  have hStoppedStage :
      brownianItoIntegralStoppedValue W Hbar (τm m) =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) :=
    stoppedBrownianIntegral_ae_eq_integral_stoppedIntegrand_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements (hτm_stop m) (hτm_count m) hH
  have hSampledStage :
      (fun ω ↦
        if τm m ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm m) ω) =ᵐ[μ]
        brownianItoIntegralStoppedValue W Hbar (τm m) :=
    continuousModification_sampledValue_ae_eq_brownianStoppedValue_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar (hτm_count m)
  -- Proof comment: once the countable-range martingale owner is identified with the terminal map
  -- of the stopped integrand, the dyadic sampled owner follows by the countable-range sampled
  -- value theorem already proved above.
  exact hStoppedStage.symm.trans hSampledStage.symm

/-- Helper for Lemma 25.13: after the dyadic stages are synchronized with the sampled continuous
modification owner, the usual subsequence-uniqueness argument identifies that sampled owner with
the terminal map of the stopped integrand. -/
private theorem sampledOwner_ae_eq_terminalStoppedIntegrand_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    (fun ω ↦
      if τ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ ω) =ᵐ[μ]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  rcases existsDyadicApproximationOfStoppingTime_local (ℱ := ℱ) (τ := τ) hτ with
    ⟨τm, hτm_stop, hτm_count, hτm_le, hτm_top, _hτm_mesh, hτm_tendsto⟩
  have hStoppedLpTendsto :
      Filter.Tendsto
        (fun m ↦ (((MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m)) :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))
        Filter.atTop
        (nhds
          (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))) :=
    stoppedIntegrand_toClosure_tendsto_of_stoppingApprox_local
      (ℱ := ℱ) (μ := μ) (τ := τ) (τm := τm)
      hτ hτm_stop hτm_le hτm_tendsto hH
  have hTerminalLpTendsto :
      Filter.Tendsto
        (fun m ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m))))
        Filter.atTop
        (nhds (hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped))) := by
    -- Proof comment: the stopped integrands converge in ambient `L²(μ ⊗ dt)`, so the terminal
    -- Brownian-Itô map converges along the same dyadic approximation.
    exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hStoppedLpTendsto
  have hTerminalInMeasure :
      MeasureTheory.TendstoInMeasure μ
        (fun m ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m))))
        Filter.atTop
        (hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTerminalLpTendsto
  rcases hTerminalInMeasure.exists_seq_tendsto_ae with
    ⟨sm, hsm_strictMono, hsm_ae⟩
  let sampledOwner : (Ω → ENNReal) → Ω → ℝ := fun σ ↦
    fun ω ↦
      if σ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          σ ω
  have hSampledSubseqTendsto :
      ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun m ↦ sampledOwner (τm (sm m)) ω)
          Filter.atTop
          (nhds (sampledOwner τ ω)) := by
    -- Proof comment: on the sampled continuous owner, the dyadic subsequence converges pointwise
    -- because the finite branch follows the continuous modification and the `∞` branch is fixed.
    exact
      continuousModification_sampledValue_tendsto_of_stoppingApprox_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements Hbar
        (τ := τ) (τm := fun m ↦ τm (sm m))
        (fun m ω ↦ hτm_top (sm m) ω)
        (fun ω ↦ (hτm_tendsto ω).comp hsm_strictMono.tendsto_atTop)
  have hStageOwner :
      ∀ n,
        hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop n))) =ᵐ[μ]
          sampledOwner (τm n) := by
    intro n
    exact
      dyadicApproxStageEqSampledOwner_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements
        hτm_stop hτm_count hH n
  have hStageOwnerSubseq :
      ∀ᵐ ω ∂μ,
        ∀ m,
          hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (hH.processBeforeStoppingTime (hτm_stop (sm m)))) ω =
            sampledOwner (τm (sm m)) ω := by
    -- Proof comment: gather the countably many dyadic-stage equalities onto one full-measure
    -- event so the subsequence can be compared pointwise.
    rw [ae_all_iff]
    intro m
    exact hStageOwner (sm m)
  filter_upwards [hsm_ae, hSampledSubseqTendsto, hStageOwnerSubseq] with ω hωTerm hωSampled hωStage
  have hωTerm' :
      Filter.Tendsto
        (fun m ↦ sampledOwner (τm (sm m)) ω)
        Filter.atTop
        (nhds (hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) ω)) := by
    -- Proof comment: on the synchronized event, each sampled-owner stage is literally the same
    -- value as the corresponding terminal map of the stopped dyadic integrand.
    refine Tendsto.congr' ?_ hωTerm
    refine Filter.Eventually.of_forall ?_
    intro m
    symm
    exact hωStage m
  -- Proof comment: the sampled-owner subsequence has the same pointwise values as the terminal
  -- subsequence, so uniqueness of limits identifies the limiting sampled owner with the desired
  -- terminal map.
  exact tendsto_nhds_unique hωSampled hωTerm'

-- Proof sketch: before comparing the two finite-branch owners via dyadic approximation, first
-- simplify both restricted expressions to their deterministic stopped-value forms.
/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the raw stopped Brownian-Itô value
already simplifies to the stopped value of the deterministic truncation process. -/
private theorem brownianStoppedValue_ae_eq_stoppedTruncated_on_finiteSet_local
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) τ := by
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  refine (ae_restrict_iff' hAfin_meas).2 ?_
  filter_upwards with ω hω
  have hτ_fin : τ ω ≠ ∞ := by
    simpa [Afin] using hω
  have htime : (τ ω).toNNReal = (τ ω).untopA :=
    (untopA_eq_toNNReal_of_ne_top_local hτ_fin).symm
  -- Proof comment: after restricting to the finite branch, the stopped Brownian-Itô value and
  -- the stopped truncation process evaluate the same deterministic slice.
  simpa [brownianItoIntegralStoppedValue, MeasureTheory.stoppedValue, hτ_fin, htime]

/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the sampled continuous-modification
owner is just the stopped value of the continuous modification. -/
private theorem sampledOwner_ae_eq_stoppedContinuous_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    (fun ω ↦
      if τ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ ω) =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar)
        τ := by
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  refine (ae_restrict_iff' hAfin_meas).2 ?_
  filter_upwards with ω hω
  have hτ_fin : τ ω ≠ ∞ := by
    simpa [Afin] using hω
  -- Proof comment: on the finite branch, the sampled owner never enters its explicit `∞`
  -- branch, so only the stopped value of the continuous modification remains.
  simp [hτ_fin]

/-- Helper for Lemma 25.13: each countable-range dyadic stage already identifies the raw stopped
Brownian-Itô value with the stopped value of the continuous modification on the finite branch of
the limiting stopping time. -/
private theorem dyadicApprox_brownianStoppedValue_ae_eq_stoppedContinuous_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm_top : ∀ n ω, τm n ω = ∞ ↔ τ ω = ∞)
    (hτm_count : ∀ n, (Set.range (τm n)).Countable)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    (n : ℕ) :
    brownianItoIntegralStoppedValue W Hbar (τm n) =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar)
        (τm n) := by
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  have hStage :
      (fun ω ↦
        if τm n ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm n) ω) =ᵐ[μ]
        brownianItoIntegralStoppedValue W Hbar (τm n) :=
    continuousModification_sampledValue_ae_eq_brownianStoppedValue_of_countableRange_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar (hτm_count n)
  refine (ae_restrict_iff' hAfin_meas).2 ?_
  filter_upwards [hStage] with ω hω hωAfin
  have hτ_fin : τ ω ≠ ∞ := by
    simpa [Afin] using hωAfin
  have hτm_fin : τm n ω ≠ ∞ := by
    intro htop
    exact hτ_fin ((hτm_top n ω).1 htop)
  -- Proof comment: on the finite branch of `τ`, every dyadic stage also stays finite, so the
  -- sampled-owner stage theorem collapses to the stopped value of the continuous modification.
  simpa [hτm_fin] using hω.symm

/-- Helper for Lemma 25.13: on the finite branch of the limiting stopping time, the stopped
values of the continuous modification converge pointwise along the dyadic approximation. -/
private theorem dyadicApprox_stoppedContinuous_tendsto_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ)
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm_top : ∀ n ω, τm n ω = ∞ ↔ τ ω = ∞)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) Filter.atTop (nhds (τ ω))) :
    ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
      Filter.Tendsto
        (fun n ↦
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm n) ω)
        Filter.atTop
        (nhds
          (MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω)) := by
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  have hSampled :
      ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n ↦
            if τm n ω = ∞ then
              hIto.toContinuousLinearMap Hbar ω
            else
              MeasureTheory.stoppedValue
                (BrownianItoIntegral.continuousModification
                  hBrownian hAdapted hIndependentIncrements Hbar)
                (τm n) ω)
          Filter.atTop
          (nhds
            (if τ ω = ∞ then
              hIto.toContinuousLinearMap Hbar ω
            else
              MeasureTheory.stoppedValue
                (BrownianItoIntegral.continuousModification
                  hBrownian hAdapted hIndependentIncrements Hbar)
                τ ω)) :=
    continuousModification_sampledValue_tendsto_of_stoppingApprox_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hτm_top hτm_tendsto
  refine (ae_restrict_iff' hAfin_meas).2 ?_
  filter_upwards [hSampled] with ω hω hωAfin
  have hτ_fin : τ ω ≠ ∞ := by
    simpa [Afin] using hωAfin
  have hEventuallyEq :
      (fun n ↦
        if τm n ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm n) ω) =ᶠ[Filter.atTop]
        fun n ↦
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm n) ω := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hτm_fin : τm n ω ≠ ∞ := by
      intro htop
      exact hτ_fin ((hτm_top n ω).1 htop)
    simp [hτm_fin]
  -- Proof comment: once we restrict to `{τ ≠ ∞}`, the dyadic approximation also stays on the
  -- finite branch, so the sampled-owner convergence becomes the convergence of stopped values.
  simpa [hτ_fin] using Tendsto.congr' hEventuallyEq hω

-- Proof sketch: combine the dyadic stage equality on the finite branch with the pointwise
-- continuity limit of the continuous modification at the limiting stopping time.
/-- Helper for Lemma 25.13: on `{τ ≠ ∞}`, the dyadic stopped Brownian-Itô values converge
pointwise to the stopped value of the continuous modification. -/
private theorem dyadicApprox_brownianStoppedValue_tendsto_to_stoppedContinuous_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm_top : ∀ n ω, τm n ω = ∞ ↔ τ ω = ∞)
    (hτm_count : ∀ n, (Set.range (τm n)).Countable)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) Filter.atTop (nhds (τ ω)))
    (Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
    ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
      Filter.Tendsto
        (fun n ↦ brownianItoIntegralStoppedValue W Hbar (τm n) ω)
        Filter.atTop
        (nhds
          (MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω)) := by
  have hStageAll :
      ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
        ∀ n,
          brownianItoIntegralStoppedValue W Hbar (τm n) ω =
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω := by
    -- Proof comment: collect the dyadic finite-branch identifications on one full-measure event
    -- so they can be used pointwise along the whole sequence.
    rw [ae_all_iff]
    intro n
    exact
      dyadicApprox_brownianStoppedValue_ae_eq_stoppedContinuous_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements
        hτ hτm_top hτm_count Hbar n
  have hContTendsto :
      ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
        Filter.Tendsto
          (fun n ↦
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) :=
    dyadicApprox_stoppedContinuous_tendsto_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hτ hτm_top hτm_tendsto
  filter_upwards [hStageAll, hContTendsto] with ω hωStage hωCont
  -- Proof comment: on the synchronized full-measure event, every dyadic raw stage is literally
  -- the same as the corresponding continuous-modification stage.
  refine Tendsto.congr' ?_ hωCont
  exact Filter.Eventually.of_forall hωStage

-- Proof sketch: the stopped dyadic integrands already converge in ambient `L²(μ ⊗ dt)`, so
-- their terminal Brownian-Itô maps admit an a.e.-convergent subsequence. Rewriting each dyadic
-- terminal map by the countable-range stopped-integrand theorem transfers that subsequence
-- convergence to the corresponding raw stopped values on the finite branch.
/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, some dyadic subsequence of the raw
stopped Brownian-Itô values converges pointwise to the terminal Brownian-Itô map of the stopped
integrand. -/
private theorem
    dyadicApprox_brownianStoppedValue_subseq_tendsto_to_terminalStoppedIntegrand_on_finiteSet_local
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm_stop : ∀ n, IsStoppingTime ℱ (τm n))
    (hτm_count : ∀ n, (Set.range (τm n)).Countable)
    (hτm_le : ∀ n ω, τ ω ≤ τm n ω)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) Filter.atTop (nhds (τ ω)))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    ∃ sm : ℕ → ℕ, StrictMono sm ∧
      ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
        Filter.Tendsto
          (fun m ↦ brownianItoIntegralStoppedValue W Hbar (τm (sm m)) ω)
          Filter.atTop
          (nhds
            (hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) ω)) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hStoppedLpTendsto :
      Filter.Tendsto
        (fun m ↦ (((MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m)) :
            MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
              Lp ℝ 2 (MeasureTheory.processMeasure μ))))
        Filter.atTop
        (nhds
          (((MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped :
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
            Lp ℝ 2 (MeasureTheory.processMeasure μ)))) :=
    stoppedIntegrand_toClosure_tendsto_of_stoppingApprox_local
      (ℱ := ℱ) (μ := μ) (τ := τ) (τm := τm)
      hτ hτm_stop hτm_le hτm_tendsto hH
  have hTerminalLpTendsto :
      Filter.Tendsto
        (fun m ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m))))
        Filter.atTop
        (nhds (hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped))) := by
    -- Proof comment: the stopped dyadic integrands converge in ambient `L²(μ ⊗ dt)`, so the
    -- terminal Brownian-Itô map converges along the same dyadic approximation.
    exact (hIto.toContinuousLinearMap.continuous.tendsto _).comp hStoppedLpTendsto
  have hTerminalInMeasure :
      MeasureTheory.TendstoInMeasure μ
        (fun m ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop m))))
        Filter.atTop
        (hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTerminalLpTendsto
  rcases hTerminalInMeasure.exists_seq_tendsto_ae with
    ⟨sm, hsm_strictMono, hsm_ae⟩
  have hStageRaw :
      ∀ n,
        brownianItoIntegralStoppedValue W Hbar (τm n) =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime (hτm_stop n))) := by
    intro n
    exact
      stoppedBrownianIntegral_ae_eq_integral_stoppedIntegrand_of_countableRange_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements (hτm_stop n) (hτm_count n) hH
  have hStageRawSubseq :
      ∀ᵐ ω ∂μ,
        ∀ m,
          brownianItoIntegralStoppedValue W Hbar (τm (sm m)) ω =
            hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (hH.processBeforeStoppingTime (hτm_stop (sm m)))) ω := by
    -- Proof comment: gather the countably many dyadic stage identifications on one full-measure
    -- event so the extracted subsequence can be compared pointwise.
    rw [ae_all_iff]
    intro m
    exact hStageRaw (sm m)
  refine ⟨sm, hsm_strictMono, ?_⟩
  have hTerminalRestr :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun m ↦
            hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (hH.processBeforeStoppingTime (hτm_stop (sm m)))) ω)
          Filter.atTop
          (nhds (hIto.toContinuousLinearMap hStopped.toClosure ω)) :=
    hsm_ae.filter_mono (Measure.restrict_le_self Afin)
  have hStageRestr :
      ∀ᵐ ω ∂μ.restrict Afin,
        ∀ m,
          brownianItoIntegralStoppedValue W Hbar (τm (sm m)) ω =
            hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (hH.processBeforeStoppingTime (hτm_stop (sm m)))) ω :=
    hStageRawSubseq.filter_mono (Measure.restrict_le_self Afin)
  filter_upwards [hTerminalRestr, hStageRestr] with ω hωTerm hωStage
  -- Proof comment: on the synchronized finite-branch event, each dyadic raw stage is literally
  -- the same as the corresponding dyadic terminal map, so the subsequential terminal convergence
  -- transfers directly to the raw stopped values.
  refine Tendsto.congr' ?_ hωTerm
  exact Filter.Eventually.of_forall hωStage

/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the stopped value of the sampled
continuous modification already agrees almost surely with the terminal Brownian-Itô map of the
stopped integrand. -/
private theorem stoppedContinuous_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar)
        τ =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  rcases existsDyadicApproximationOfStoppingTime_local (ℱ := ℱ) (τ := τ) hτ with
    ⟨τm, hτm_stop, hτm_count, hτm_le, hτm_top, _hτm_mesh, hτm_tendsto⟩
  have hDyadicRawTendsto :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun n ↦ brownianItoIntegralStoppedValue W Hbar (τm n) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) := by
    -- Proof comment: on the finite branch, the dyadic raw stages inherit the pointwise limit of
    -- the sampled continuous modification.
    exact
      dyadicApprox_brownianStoppedValue_tendsto_to_stoppedContinuous_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements
        hτ hτm_top hτm_count hτm_tendsto Hbar
  obtain ⟨sm, hsm_strictMono, hDyadicTerminalSubseq⟩ :=
    dyadicApprox_brownianStoppedValue_subseq_tendsto_to_terminalStoppedIntegrand_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hτ hτm_stop hτm_count hτm_le hτm_tendsto hH
  have hDyadicRawSubseqTendsto :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun m ↦ brownianItoIntegralStoppedValue W Hbar (τm (sm m)) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) := by
    filter_upwards [hDyadicRawTendsto] with ω hωRaw
    exact hωRaw.comp hsm_strictMono.tendsto_atTop
  filter_upwards [hDyadicRawSubseqTendsto, hDyadicTerminalSubseq] with ω hωRaw hωTerm
  -- Proof comment: the same dyadic raw subsequence converges both to the sampled continuous
  -- finite branch and to the terminal map of the stopped integrand, so uniqueness identifies the
  -- two candidate limits.
  exact tendsto_nhds_unique hωRaw hωTerm

/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the explicit sampled-owner formula
already collapses to the terminal Brownian-Itô map of the stopped integrand. -/
private theorem sampledOwner_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    (fun ω ↦
      if τ ω = ∞ then
        hIto.toContinuousLinearMap Hbar ω
      else
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ ω) =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  have hSampledFinite :
      (fun ω ↦
        if τ ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω) =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ :=
    sampledOwner_ae_eq_stoppedContinuous_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hτ Hbar
  have hFiniteTerminal :
      MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
        hIto.toContinuousLinearMap hStopped.toClosure :=
    stoppedContinuous_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hτ hH
  -- Proof comment: first discard the vacuous `∞` branch on `{τ ≠ ∞}`, then apply the dyadic
  -- finite-branch terminal comparison.
  exact hSampledFinite.trans hFiniteTerminal

-- Proof sketch: the raw dyadic subsequence theorem already gives convergence of the stopped
-- Brownian-Itô values to the terminal stopped-integrand map. On `{τ ≠ ∞}`, every dyadic stage is
-- also finite, so those raw stages are literally the stopped values of the deterministic
-- truncation process.
/-- Helper for Lemma 25.13: the dyadic subsequence from the raw finite-branch theorem can be
reused verbatim for the stopped values of the deterministic truncation process on `{τ ≠ ∞}`. -/
private theorem
    dyadicApprox_stoppedTruncated_subseq_tendsto_to_terminalStoppedIntegrand_on_finiteSet_local
    {τ : Ω → ENNReal} {τm : ℕ → Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hτm_stop : ∀ n, IsStoppingTime ℱ (τm n))
    (hτm_count : ∀ n, (Set.range (τm n)).Countable)
    (hτm_le : ∀ n ω, τ ω ≤ τm n ω)
    (hτm_top : ∀ n ω, τm n ω = ∞ ↔ τ ω = ∞)
    (hτm_tendsto :
      ∀ ω, Filter.Tendsto (fun n ↦ τm n ω) Filter.atTop (nhds (τ ω)))
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    ∃ sm : ℕ → ℕ, StrictMono sm ∧
      ∀ᵐ ω ∂μ.restrict {ω | τ ω ≠ ∞},
        Filter.Tendsto
          (fun m ↦
            MeasureTheory.stoppedValue
              (brownianItoIntegralTruncatedProcess W Hbar)
              (τm (sm m)) ω)
          Filter.atTop
          (nhds
            (hIto.toContinuousLinearMap
              (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) ω)) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  obtain ⟨sm, hsm_strictMono, hRawSubseq⟩ :=
    dyadicApprox_brownianStoppedValue_subseq_tendsto_to_terminalStoppedIntegrand_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hτ hτm_stop hτm_count hτm_le hτm_tendsto hH
  have hStageFinite :
      ∀ᵐ ω ∂μ.restrict Afin,
        ∀ m,
          MeasureTheory.stoppedValue
              (brownianItoIntegralTruncatedProcess W Hbar)
              (τm (sm m)) ω =
            brownianItoIntegralStoppedValue W Hbar (τm (sm m)) ω := by
    rw [ae_all_iff]
    intro m
    refine (ae_restrict_iff' hAfin_meas).2 ?_
    filter_upwards with ω hω
    have hτ_fin : τ ω ≠ ∞ := by
      simpa [Afin] using hω
    have hτm_fin : τm (sm m) ω ≠ ∞ := by
      intro htop
      exact hτ_fin ((hτm_top (sm m) ω).1 htop)
    have htime : (τm (sm m) ω).toNNReal = (τm (sm m) ω).untopA :=
      (untopA_eq_toNNReal_of_ne_top_local hτm_fin).symm
    -- Proof comment: on `{τ ≠ ∞}`, every dyadic stage also stays finite, so the raw stopped
    -- value is just the stopped value of the deterministic truncation process at that stage.
    simpa [MeasureTheory.stoppedValue, brownianItoIntegralStoppedValue, hτm_fin, htime]
  refine ⟨sm, hsm_strictMono, ?_⟩
  filter_upwards [hRawSubseq, hStageFinite] with ω hωRaw hωStage
  -- Proof comment: after rewriting each dyadic stage on the finite branch, the already extracted
  -- raw subsequence convergence transfers unchanged to the stopped-truncation subsequence.
  refine Tendsto.congr' ?_ hωRaw
  exact Filter.Eventually.of_forall hωStage

/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the stopped value of the
deterministic truncation process agrees almost surely with the stopped value of the sampled
continuous modification. -/
private theorem stoppedTruncated_ae_eq_stoppedContinuous_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) τ =ᵐ[
        μ.restrict {ω | τ ω ≠ ∞}]
      MeasureTheory.stoppedValue
        (BrownianItoIntegral.continuousModification
          hBrownian hAdapted hIndependentIncrements Hbar)
        τ := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAfin_meas : MeasurableSet Afin := by
    simpa [Afin] using (measurableSet_eq_fun hτ.measurable' measurable_const).compl
  rcases existsDyadicApproximationOfStoppingTime_local (ℱ := ℱ) (τ := τ) hτ with
    ⟨τm, hτm_stop, hτm_count, hτm_le, hτm_top, _hτm_mesh, hτm_tendsto⟩
  have hStageAll :
      ∀ᵐ ω ∂μ.restrict Afin,
        ∀ n,
          MeasureTheory.stoppedValue
              (brownianItoIntegralTruncatedProcess W Hbar)
              (τm n) ω =
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω := by
    rw [ae_all_iff]
    intro n
    have hRawStage :
        brownianItoIntegralStoppedValue W Hbar (τm n) =ᵐ[μ.restrict Afin]
          MeasureTheory.stoppedValue
            (brownianItoIntegralTruncatedProcess W Hbar)
            (τm n) := by
      refine (ae_restrict_iff' hAfin_meas).2 ?_
      filter_upwards with ω hω
      have hτ_fin : τ ω ≠ ∞ := by
        simpa [Afin] using hω
      have hτm_fin : τm n ω ≠ ∞ := by
        intro htop
        exact hτ_fin ((hτm_top n ω).1 htop)
      have htime : (τm n ω).toNNReal = (τm n ω).untopA :=
        (untopA_eq_toNNReal_of_ne_top_local hτm_fin).symm
      -- Proof comment: on `{τ ≠ ∞}`, every dyadic stage is also finite, so the raw stopped
      -- owner is just the stopped value of the deterministic truncation process at that stage.
      simpa [brownianItoIntegralStoppedValue, MeasureTheory.stoppedValue, hτm_fin, htime]
    have hContStage :
        brownianItoIntegralStoppedValue W Hbar (τm n) =ᵐ[μ.restrict Afin]
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            (τm n) :=
      dyadicApprox_brownianStoppedValue_ae_eq_stoppedContinuous_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements
        hτ hτm_top hτm_count Hbar n
    -- Proof comment: each dyadic stopped-truncation stage and each dyadic stopped-continuous
    -- stage are already synchronized through the same raw stopped Brownian-Itô value.
    exact hRawStage.symm.trans hContStage
  have hContTendsto :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun n ↦
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              (τm n) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) :=
    dyadicApprox_stoppedContinuous_tendsto_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements Hbar hτ hτm_top hτm_tendsto
  have hTruncTendsto :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun n ↦
            MeasureTheory.stoppedValue
              (brownianItoIntegralTruncatedProcess W Hbar)
              (τm n) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) := by
    filter_upwards [hStageAll, hContTendsto] with ω hωStage hωCont
    -- Proof comment: on the synchronized full-measure event, every dyadic stopped-truncation
    -- stage is literally the same as the corresponding stopped-continuous stage.
    refine Tendsto.congr' ?_ hωCont
    exact Filter.Eventually.of_forall hωStage
  obtain ⟨sm, hsm_strictMono, hTerminalSubseq⟩ :=
    dyadicApprox_stoppedTruncated_subseq_tendsto_to_terminalStoppedIntegrand_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hτ hτm_stop hτm_count hτm_le
      hτm_top hτm_tendsto hH
  have hTruncSubseqTendsto :
      ∀ᵐ ω ∂μ.restrict Afin,
        Filter.Tendsto
          (fun m ↦
            MeasureTheory.stoppedValue
              (brownianItoIntegralTruncatedProcess W Hbar)
              (τm (sm m)) ω)
          Filter.atTop
          (nhds
            (MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω)) := by
    filter_upwards [hTruncTendsto] with ω hωTrunc
    exact hωTrunc.comp hsm_strictMono.tendsto_atTop
  filter_upwards [hTruncSubseqTendsto, hTerminalSubseq] with ω hωTrunc hωTerm
  -- Proof comment: the same dyadic stopped-truncation subsequence converges both to the stopped
  -- continuous modification and to the terminal stopped-integrand map, so uniqueness identifies
  -- those two finite-branch limits.
  exact tendsto_nhds_unique hωTrunc hωTerm

-- Proof sketch: after the dyadic stages are synchronized with the sampled continuous
-- modification owner, the last finite-branch theorem is just one transitivity step through that
-- common stopped continuous process.
/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the raw stopped truncation owner
should agree almost surely with the terminal Brownian-Itô map of the stopped integrand. -/
private theorem rawStoppedTruncated_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) τ =ᵐ[
        μ.restrict {ω | τ ω ≠ ∞}]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  have hTruncContinuous :
      MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) τ =ᵐ[
          μ.restrict {ω | τ ω ≠ ∞}]
        MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ := by
    -- Proof comment: the new dyadic uniqueness bridge identifies the raw stopped truncation with
    -- the stopped continuous modification on the finite branch.
    simpa [Hbar] using
      stoppedTruncated_ae_eq_stoppedContinuous_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hτ hH
  have hContinuousTerminal :
      MeasureTheory.stoppedValue
          (BrownianItoIntegral.continuousModification
            hBrownian hAdapted hIndependentIncrements Hbar)
          τ =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
        hIto.toContinuousLinearMap hStopped.toClosure := by
    -- Proof comment: the stopped continuous finite branch was already synchronized with the
    -- terminal Brownian-Itô map of the stopped integrand.
    simpa [Hbar, hStopped] using
      stoppedContinuous_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hτ hH
  -- Proof comment: both finite-branch descriptions pass through the same stopped continuous
  -- modification, so a single transitivity step closes the raw stopped-truncation theorem.
  exact hTruncContinuous.trans hContinuousTerminal

/-- Helper for Lemma 25.13: on the finite branch `{τ ≠ ∞}`, the raw stopped Brownian-Itô value
should agree almost surely with the sampled continuous-modification owner. -/
private theorem brownianStoppedValue_ae_eq_sampledOwner_on_finiteSet_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ.restrict {ω | τ ω ≠ ∞}]
      (fun ω ↦
        if τ ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hRawFinite :
      brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ.restrict Afin]
        MeasureTheory.stoppedValue
          (brownianItoIntegralTruncatedProcess W Hbar) τ :=
    brownianStoppedValue_ae_eq_stoppedTruncated_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W) hτ Hbar
  have hFiniteTerminal :
      (fun ω ↦
        if τ ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω) =ᵐ[μ.restrict Afin]
        hIto.toContinuousLinearMap hStopped.toClosure :=
    sampledOwner_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hτ hH
  -- Route correction: the general synchronization is now reduced to the genuine analytic finite
  -- branch. The `{τ = ∞}` branch is handled separately by a direct simplification.
  have hRawStoppedTerminal :
      MeasureTheory.stoppedValue (brownianItoIntegralTruncatedProcess W Hbar) τ =ᵐ[μ.restrict Afin]
        hIto.toContinuousLinearMap hStopped.toClosure := by
    simpa [Afin, Hbar, hStopped] using
      rawStoppedTruncated_ae_eq_terminalStoppedIntegrand_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W) hτ hH
  -- Proof comment: after isolating the last raw finite-branch bridge, both sides are compared
  -- through the same terminal Brownian-Itô map of the stopped integrand.
  exact hRawFinite.trans (hRawStoppedTerminal.trans hFiniteTerminal.symm)

/-- Helper for Lemma 25.13: the sampled continuous-modification owner should agree almost surely
with the raw stopped Brownian-Itô value at the limiting stopping time. -/
private theorem brownianStoppedValue_ae_eq_sampledOwner_local
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
      (fun ω ↦
        if τ ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let Ainf : Set Ω := {ω | τ ω = ∞}
  let Afin : Set Ω := {ω | τ ω ≠ ∞}
  have hAinf_meas : MeasurableSet Ainf := measurableSet_eq_fun hτ.measurable' measurable_const
  have hAfin_meas : MeasurableSet Afin := measurableSet_compl hAinf_meas
  have hTop :
      brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ.restrict Ainf]
        (fun ω ↦
          if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω) := by
    refine (ae_restrict_iff' hAinf_meas).2 ?_
    filter_upwards with ω hω
    -- Proof comment: on `{τ = ∞}`, both sides are definitionally the terminal Brownian-Itô map.
    simp [Ainf, hω, brownianItoIntegralStoppedValue]
  have hFinite :
      brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ.restrict Afin]
        (fun ω ↦
          if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω) := by
    simpa [Afin] using
      brownianStoppedValue_ae_eq_sampledOwner_on_finiteSet_local
        (μ := μ) (ℱ := ℱ) (W := W)
        hBrownian hAdapted hIndependentIncrements hτ hH
  have hTopAll :
      ∀ᵐ ω ∂μ, ω ∈ Ainf →
        brownianItoIntegralStoppedValue W Hbar τ ω =
          (if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω) := by
    exact (ae_restrict_iff' hAinf_meas).1 hTop
  have hFiniteAll :
      ∀ᵐ ω ∂μ, ω ∈ Afin →
        brownianItoIntegralStoppedValue W Hbar τ ω =
          (if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω) := by
    exact (ae_restrict_iff' hAfin_meas).1 hFinite
  -- Proof comment: combine the trivial `{τ = ∞}` branch with the finite-branch theorem to
  -- recover the full almost-sure identity.
  filter_upwards [hTopAll, hFiniteAll] with ω hωTop hωFinite
  by_cases hω : τ ω = ∞
  · exact hωTop hω
  · exact hωFinite hω

-- Proof sketch: first prove the identity for predictable simple processes from the defining Itô
-- sums, then pass to `MemPredictableStepProcessClosure ℱ μ H` by `L²` approximation and the
-- continuity of the integral map from Theorem 25.11.
/-- Lemma 25.13 (1): for a stopping time `τ` and an integrand `H` in the `L²`-closure of the
predictable simple processes, the Brownian Itô integral up to `τ` agrees almost surely with the
terminal Brownian Itô integral of the cutoff integrand
`processBeforeStoppingTime H τ`. -/
theorem stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  -- Route correction: after the deterministic cutoff identity, the missing work is now exactly
  -- the countable-range identity for the dyadic approximants plus the final synchronization of
  -- the raw stopped value with the sampled continuous owner.
  have hSampledEqTarget :
      (fun ω ↦
        if τ ω = ∞ then
          hIto.toContinuousLinearMap Hbar ω
        else
          MeasureTheory.stoppedValue
            (BrownianItoIntegral.continuousModification
              hBrownian hAdapted hIndependentIncrements Hbar)
            τ ω) =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) :=
    sampledOwner_ae_eq_terminalStoppedIntegrand_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hτ hH
  have hStoppedSync :
      brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
        (fun ω ↦
          if τ ω = ∞ then
            hIto.toContinuousLinearMap Hbar ω
          else
            MeasureTheory.stoppedValue
              (BrownianItoIntegral.continuousModification
                hBrownian hAdapted hIndependentIncrements Hbar)
              τ ω) :=
    brownianStoppedValue_ae_eq_sampledOwner_local
      (μ := μ) (ℱ := ℱ) (W := W)
      hBrownian hAdapted hIndependentIncrements hτ hH
  -- Proof comment: once the raw stopped value and the sampled continuous-modification owner are
  -- synchronized, the dyadic-stage bridge and unique-limit step identify both sides of the target
  -- theorem.
  exact hStoppedSync.trans hSampledEqTarget

-- Proof sketch: on the event `{τ ≥ t}`, the cutoff integrand satisfies `H^(τ)_s = H_s` for every
-- `s ≤ t`, so the finite-horizon integral identity follows from part (1) applied to `min τ t`.
/-- Lemma 25.13 (2): for each deterministic time `t`, on the event `{τ ≥ t}` the canonical
Brownian Itô process of `H` agrees almost surely with the canonical Brownian Itô process of the
cutoff integrand `processBeforeStoppingTime H τ`. -/
theorem brownianIntegral_ae_eq_integral_stoppedIntegrand_on_event
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let hStopped : MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
      hH.processBeforeStoppingTime hτ
    brownianItoIntegralTruncatedProcess W
        Hbar t =ᵐ[μ.restrict {ω | (t : ENNReal) ≤ τ ω}]
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) t := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let A : Set Ω := {ω | (t : ENNReal) ≤ τ ω}
  let σ : Ω → ENNReal := fun ω ↦ min (τ ω) (t : ENNReal)
  let hσ : IsStoppingTime ℱ σ := hτ.min_const t
  have hA_meas : MeasurableSet A := hτ.measurableSet_ge t
  have hStopped :
      MemPredictableStepProcessClosure ℱ μ (processBeforeStoppingTime H τ) :=
    hH.processBeforeStoppingTime hτ
  have hLeftTerminal :
      brownianItoIntegralTruncatedProcess W Hbar t =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hH.processBeforeStoppingTime hσ)) := by
    have hSigma :
        brownianItoIntegralStoppedValue W Hbar σ =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.processBeforeStoppingTime hσ)) :=
      stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand
        hBrownian hAdapted hIndependentIncrements hσ hH
    -- Proof comment: on `{τ ≥ t}`, the minimum stopping time `min τ t` is the deterministic
    -- time `t`, so the stopped process value becomes the fixed-time truncated process.
    refine (ae_restrict_iff' hA_meas).2 ?_
    filter_upwards [hSigma] with ω hω hωA
    have hσ_eq : σ ω = (t : ENNReal) := by
      exact min_eq_right (by simpa [A] using hωA)
    simpa [A, σ, brownianItoIntegralStoppedValue, hσ_eq] using hω
  have hRightTerminal :
      brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) t =ᵐ[μ.restrict A]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t))) := by
    have hDet :
        brownianItoIntegralTruncatedProcess W
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure hStopped) t =ᵐ[μ]
          hIto.toContinuousLinearMap
            (MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t))) := by
      -- Proof comment: the deterministic branch is already proved separately, so this side does
      -- not depend on the unresolved random-time approximation step.
      simpa using
        stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand_const hStopped t
    exact hDet.filter_mono (Measure.restrict_le_self A)
  have hClosure :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure (hH.processBeforeStoppingTime hσ) =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t)) := by
    -- Proof comment: both closure points are represented by the same doubly cut-off process
    -- `H 1_{s ≤ τ} 1_{s ≤ t}`.
    apply toClosure_eq_of_process_eq_local
    · exact hH.processBeforeStoppingTime hσ
    · exact hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t)
    · funext s ω
      by_cases hsτ : (s : ENNReal) ≤ τ ω
      · by_cases hst : (s : ENNReal) ≤ (t : ENNReal)
        · simp [σ, processBeforeStoppingTime_apply, hsτ, hst]
        · simp [σ, processBeforeStoppingTime_apply, hsτ, hst]
      · by_cases hst : (s : ENNReal) ≤ (t : ENNReal)
        · simp [σ, processBeforeStoppingTime_apply, hsτ, hst]
        · simp [σ, processBeforeStoppingTime_apply, hsτ, hst]
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hH.processBeforeStoppingTime hσ)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hStopped.processBeforeStoppingTime (isStoppingTime_const ℱ t))) := by
    exact congrArg hIto.toContinuousLinearMap hClosure
  -- Proof comment: both eventwise terminal expressions agree, so the fixed-time truncated
  -- processes agree on `{τ ≥ t}`.
  exact hLeftTerminal.trans <| (Filter.EventuallyEq.of_eq hTerminalEq).trans hRightTerminal.symm

-- Proof sketch: if the cutoff integrands agree, apply part (1) to both `H` and `G` and compare
-- the resulting terminal stopped-integrand integrals.
/-- Helper for Lemma 25.13 (3): if two admissible integrands have the same cutoff integrand
before the stopping time `τ`, then their Itô integrals up to `τ` are almost surely equal. -/
theorem stopped_brownianIntegral_congr
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hcutoff : processBeforeStoppingTime H τ = processBeforeStoppingTime G τ) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let Gbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hG
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
      brownianItoIntegralStoppedValue W Gbar τ := by
  let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
  let Gbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure hG
  have hLeft :
      brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hH.processBeforeStoppingTime hτ)) :=
    stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand
      hBrownian hAdapted hIndependentIncrements hτ hH
  have hRight :
      brownianItoIntegralStoppedValue W Gbar τ =ᵐ[μ]
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hG.processBeforeStoppingTime hτ)) :=
    stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand
      hBrownian hAdapted hIndependentIncrements hτ hG
  have hClosure :
      MeasureTheory.MemPredictableStepProcessClosure.toClosure (hH.processBeforeStoppingTime hτ) =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure (hG.processBeforeStoppingTime hτ) := by
    -- Proof comment: identical cutoff integrands represent the same ambient `L²(μ ⊗ dt)` class.
    exact
      toClosure_eq_of_process_eq_local
        (hH.processBeforeStoppingTime hτ)
        (hG.processBeforeStoppingTime hτ)
        hcutoff
  have hTerminalEq :
      hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hH.processBeforeStoppingTime hτ)) =
        hIto.toContinuousLinearMap
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hG.processBeforeStoppingTime hτ)) := by
    exact congrArg hIto.toContinuousLinearMap hClosure
  -- Proof comment: transport both stopped values through the common terminal Brownian-Itô map of
  -- the shared cutoff integrand.
  exact hLeft.trans <| (Filter.EventuallyEq.of_eq hTerminalEq).trans hRight.symm

-- Proof sketch: the textbook hypothesis implies equality of the cutoff integrands by
-- `processBeforeStoppingTime_congr`, so the canonical cutoff-based congruence theorem applies.
/-- Lemma 25.13 (3): if two admissible integrands `H` and `G` agree at all times up to the
stopping time `τ`, then their Itô integrals up to `τ` are almost surely equal. -/
theorem stopped_brownianIntegral_congr_of_forall_le
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndependentIncrements :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hEq : ∀ (t : NNReal) ω, (t : ENNReal) ≤ τ ω → H t ω = G t ω) :
    let Hbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hH
    let Gbar : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hG
    brownianItoIntegralStoppedValue W Hbar τ =ᵐ[μ]
      brownianItoIntegralStoppedValue W Gbar τ := by
  have hcutoff : processBeforeStoppingTime H τ = processBeforeStoppingTime G τ :=
    processBeforeStoppingTime_congr hEq
  -- Proof comment: the source hypothesis is exactly the cutoff-integrand equality needed by the
  -- canonical congruence theorem above.
  exact stopped_brownianIntegral_congr
    hBrownian hAdapted hIndependentIncrements hτ hH hG hcutoff

end GlobalItoRealization

end ProbabilityTheory
