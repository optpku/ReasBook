/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped Topology NNReal ENNReal

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "RealProcess" => NNReal → Ω → ℝ

namespace Adapted

variable {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}

/-- Helper for Theorem 25.8: an adapted left-continuous real-valued process is measurable on each
finite strip `Set.Iic T × Ω`. -/
lemma measurable_strip_of_adapted_leftContinuous
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_left : ∀ ω : Ω, ∀ t : NNReal,
      ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t)
    (T : NNReal) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦ H p.1 p.2 := by
  letI : MeasurableSpace Ω := ℱ T
  let reversed : RealProcess := fun s ω ↦ H (T - min s T) ω
  have hmeas : ∀ s, Measurable (reversed s) := by
    intro s
    -- Proof comment: every reversed time still lies in the past of `T`, so adaptedness upgrades
    -- the time slice to `ℱ T`-measurability.
    simpa [reversed] using
      hH_adapted.measurable_le (i := T - min s T) (j := T) (tsub_le_self)
  have hright : HasRightContinuousPaths reversed := by
    intro ω s
    have hmaps :
        Set.MapsTo (fun r : NNReal ↦ T - min r T) (Set.Ici s) (Set.Iic (T - min s T)) := by
      intro r hr
      exact tsub_le_tsub_left (min_le_min_right T hr) T
    have hg :
        ContinuousWithinAt (fun r : NNReal ↦ T - min r T) (Set.Ici s) s := by
      -- Proof comment: the time-reversal map is continuous, so it transports right-neighborhoods
      -- of `s` to left-neighborhoods of `T - min s T`.
      exact (continuous_const.sub (continuous_id.min continuous_const)).continuousWithinAt
    -- Proof comment: composing the left-continuous path of `H` with the time-reversal map yields
    -- a right-continuous path for the reversed process.
    simpa [reversed, Function.comp] using
      (ContinuousWithinAt.comp
        (g := fun u : NNReal ↦ H u ω)
        (f := fun r : NNReal ↦ T - min r T)
        (s := Set.Ici s)
        (t := Set.Iic (T - min s T))
        (x := s)
        (hH_left ω (T - min s T)) hg hmaps)
  have huncurry : Measurable (Function.uncurry reversed) := by
    -- Proof comment: the reversed process now matches the right-continuous joint measurability
    -- theorem from Exercise 21.1.4.
    exact MeasureTheory.measurable_uncurry_of_measurable_rightContinuous hmeas hright
  have hcoord : Measurable fun p : Set.Iic T × Ω ↦ (T - p.1, p.2) := by
    -- Proof comment: on the strip `[0,T]`, the coordinate change `(t, ω) ↦ (T - t, ω)` is
    -- measurable.
    exact (measurable_const.sub measurable_fst.subtype_val).prodMk measurable_snd
  have hcomp :
      (fun p : Set.Iic T × Ω ↦ H p.1 p.2) =
        Function.uncurry reversed ∘ fun p : Set.Iic T × Ω ↦ (T - p.1, p.2) := by
    -- Proof comment: on `Set.Iic T`, reversing time twice returns the original time coordinate.
    funext p
    simp [Function.uncurry, reversed,
      tsub_tsub_cancel_of_le (show (p.1 : NNReal) ≤ T from p.1.2)]
  rw [hcomp]
  exact huncurry.comp hcoord

/-- Helper for Theorem 25.8: stripwise measurability already implies progressive measurability for
real-valued processes. -/
private theorem progMeasurable_of_measurableOnStrips
    {ℱ : TimeFiltration} {H' : RealProcess}
    (hstrip : ∀ T : NNReal,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ H' p.1 p.2)) :
    ProgMeasurable ℱ H' := by
  intro T
  -- Proof comment: on each strip, ordinary measurability upgrades to strong measurability because
  -- the codomain is `ℝ`.
  exact (hstrip T).stronglyMeasurable

-- Proof sketch: treat the right-continuous and left-continuous cases separately. In the
-- right-continuous case, use the standard approximation of each strip `[0, t] × Ω` by step
-- processes built from times below `t`; in the left-continuous case, use the analogous
-- approximation from the left.
/-- First implication for Theorem 25.8: if an adapted real-valued process is right continuous or
left continuous, then it is progressively measurable. -/
theorem progMeasurable_of_left_or_right_continuous
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_cont :
      HasRightContinuousPaths H ∨
      ∀ ω : Ω, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ProgMeasurable ℱ H := by
  rcases hH_cont with hH_right | hH_left
  · exact hH_adapted.progMeasurable_of_rightContinuous hH_right
  · intro T
    -- Proof comment: for left-continuous paths, first prove strip measurability by reversing time
    -- on `[0,T]`, then upgrade measurability to strong measurability in the real-valued codomain.
    exact (measurable_strip_of_adapted_leftContinuous hH_adapted hH_left T).stronglyMeasurable

/-- Helper for Theorem 25.8: the lower dyadic index stays on or before the target time. -/
def lowerStepIndex (n : ℕ) (t : NNReal) : ℕ :=
  ⌊t * (n + 1 : NNReal)⌋₊

/-- Helper for Theorem 25.8: the lower dyadic time approximation approaches the target time from
the left. -/
def lowerStepTime (n : ℕ) (t : NNReal) : NNReal :=
  ((lowerStepIndex n t : ℕ) : NNReal) / (n + 1)

/-- Helper for Theorem 25.8: the lower dyadic approximation never overshoots the target time. -/
lemma lowerStepTime_le_self (n : ℕ) (t : NNReal) :
    lowerStepTime n t ≤ t := by
  -- Proof comment: multiply by the positive denominator and apply the defining floor inequality.
  have hfloor : (lowerStepIndex n t : ℕ) ≤ t * (n + 1 : NNReal) := by
    simpa [lowerStepIndex] using
      Nat.floor_le (show 0 ≤ t * (n + 1 : NNReal) by positivity)
  rw [lowerStepTime]
  rw [div_le_iff₀]
  · simpa [mul_assoc] using hfloor
  · exact Nat.cast_add_one_pos n

/-- Helper for Theorem 25.8: the lower dyadic approximation misses the target time by at most
`1 / (n + 1)`. -/
lemma self_le_lowerStepTime_add_inv (n : ℕ) (t : NNReal) :
    t ≤ lowerStepTime n t + 1 / (n + 1 : NNReal) := by
  -- Proof comment: the floor is at least one unit below the scaled target, so dividing by the
  -- positive denominator leaves an explicit error bound.
  have hfloor : t * (n + 1 : NNReal) < ((lowerStepIndex n t : ℕ) : NNReal) + 1 := by
    simpa [lowerStepIndex] using Nat.lt_floor_add_one (t * (n + 1 : NNReal))
  rw [lowerStepTime]
  rw [← add_div]
  rw [le_div_iff₀]
  · simpa using hfloor.le
  · exact Nat.cast_add_one_pos n

/-- Helper for Theorem 25.8: the lower dyadic times converge up to the target time. -/
lemma tendsto_lowerStepTime (t : NNReal) :
    Tendsto (fun n ↦ lowerStepTime n t) atTop (𝓝 t) := by
  have hleft :
      Tendsto (fun n : ℕ ↦ t - 1 / (n + 1 : NNReal)) atTop (𝓝 t) := by
    -- Proof comment: the explicit error term `1 / (n + 1)` tends to zero, so the lower barrier
    -- `t - 1 / (n + 1)` tends up to `t`.
    simpa [tsub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : NNReal) / (n + 1)) atTop (𝓝 0)))
  -- Proof comment: the lower dyadic approximation stays between the convergent lower barrier and
  -- the constant upper barrier `t`, so the squeeze theorem gives convergence to `t`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hleft tendsto_const_nhds ?_ ?_
  · intro n
    exact (tsub_le_iff_right).2 (self_le_lowerStepTime_add_inv n t)
  · intro n
    exact lowerStepTime_le_self n t

/-- Helper for Theorem 25.8: lower dyadic approximants are jointly measurable on each finite
strip. -/
private lemma lowerStep_measurableOnStrip
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H) (T : NNReal) (n : ℕ) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦
      H (lowerStepTime n p.1) p.2 := by
  letI : MeasurableSpace Ω := ℱ T
  let g : ℕ × Ω → ℝ := fun q ↦ H (min (((q.1 : ℕ) : NNReal) / (n + 1)) T) q.2
  have hg : Measurable g := by
    -- Proof comment: after clipping the dyadic time by `T`, every slice stays in the past of `T`.
    refine measurable_from_prod_countable_right fun k ↦ ?_
    simpa [g] using
      hH_adapted.measurable_le
        (i := min (((k : ℕ) : NNReal) / (n + 1)) T)
        (j := T)
        (min_le_right _ _)
  have hidx : Measurable fun p : Set.Iic T × Ω ↦ lowerStepIndex n p.1 := by
    -- Proof comment: the lower dyadic index depends measurably only on the time coordinate.
    simpa [lowerStepIndex] using
      ((measurable_fst.subtype_val.mul_const (n + 1 : NNReal)).nat_floor :
        Measurable fun p : Set.Iic T × Ω ↦ ⌊((p.1 : NNReal) * (n + 1 : NNReal))⌋₊)
  have hmap : Measurable fun p : Set.Iic T × Ω ↦ (lowerStepIndex n p.1, p.2) :=
    hidx.prodMk measurable_snd
  have hcomp :
      (fun p : Set.Iic T × Ω ↦ H (lowerStepTime n p.1) p.2) =
        g ∘ fun p : Set.Iic T × Ω ↦ (lowerStepIndex n p.1, p.2) := by
    funext p
    have hmin :
        min (((lowerStepIndex n p.1 : ℕ) : NNReal) / (n + 1)) T =
          (((lowerStepIndex n p.1 : ℕ) : NNReal) / (n + 1)) := by
      apply min_eq_left
      exact (lowerStepTime_le_self n p.1).trans p.1.2
    simp [g, lowerStepTime, hmin]
  rw [hcomp]
  exact hg.comp hmap

/-- Helper for Theorem 25.8: stripwise measurability is enough for progressive measurability in
the real-valued setting. -/
private theorem progMeasurableOfMeasurableOnStrips
    {ℱ : TimeFiltration} {H : RealProcess}
    (hstrip : ∀ T : NNReal,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ H p.1 p.2)) :
    ProgMeasurable ℱ H := by
  intro T
  -- Proof comment: for real-valued strip maps, measurability upgrades to strong measurability.
  exact (hstrip T).stronglyMeasurable

/-- Helper for Theorem 25.8: patching the time-zero slice by `0` preserves strip measurability. -/
private theorem measurableOnStrip_zeroAtOrigin
    {ℱ : TimeFiltration} {T : NNReal} {f : Set.Iic T × Ω → ℝ}
    (hf :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        f) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) = 0 then 0 else f p) := by
  have hzero :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) :=
    measurable_const
  have hzeroSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) = 0} := by
    have htime :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
      measurable_fst.subtype_val
    convert htime (measurableSet_singleton (0 : NNReal)) using 1
  -- Proof comment: only the singleton time-zero slice is changed, so piecewise measurability
  -- applies directly.
  simpa [Set.piecewise] using hzero.piecewise hzeroSet hf

/-- Helper for Theorem 25.8: patching the top slice `{t = T}` by an `ℱ T`-measurable boundary
value preserves strip measurability. -/
private theorem measurableOnStrip_patchTop
    {ℱ : TimeFiltration} {T : NNReal} {f : Set.Iic T × Ω → ℝ} {g : Ω → ℝ}
    (hf :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        f)
    (hg : Measurable[ℱ T] g) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) = T then g p.2 else f p) := by
  have hgStrip :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ g p.2) :=
    hg.comp measurable_snd
  have htopSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) = T} := by
    have htime :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ (p.1 : NNReal)) :=
      measurable_fst.subtype_val
    convert htime (measurableSet_singleton T) using 1
  -- Proof comment: only the singleton top slice is changed, so measurable piecewise patching
  -- applies exactly as in the time-zero case.
  simpa [Set.piecewise] using hgStrip.piecewise htopSet hf

/-- Helper for Theorem 25.8: once a unit-cell process is measurable on `Set.Iic 1 × Ω`, extending
it by `0` outside `(0,1]` preserves strip measurability on larger horizons. -/
private theorem measurableZeroOutsideUnitCellOfMeasurableOnStrip
    {ℱ : TimeFiltration} {G : RealProcess} {T : NNReal}
    (hT : (1 : NNReal) ≤ T)
    (hG :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦ G p.1 p.2)) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ (1 : NNReal) then G p.1 p.2 else 0) := by
  have hG_mono :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦ G p.1 p.2) :=
    hG.mono (by
      exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.mono hT))) le_rfl
  let truncToOne : Set.Iic T × Ω → Set.Iic (1 : NNReal) × Ω :=
    fun p ↦
      (⟨min (p.1 : NNReal) (1 : NNReal),
        show min (p.1 : NNReal) (1 : NNReal) ≤ (1 : NNReal) from min_le_right _ _⟩, p.2)
  have htruncToOne :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T),
        Subtype.instMeasurableSpace.prod (ℱ T)] truncToOne := by
    have hfstBase :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦ min (p.1 : NNReal) (1 : NNReal) := by
      exact measurable_fst.subtype_val.min measurable_const
    have hsnd :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T), ℱ T]
          (fun p : Set.Iic T × Ω ↦ p.2) :=
      measurable_snd
    have hfst :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦
          (⟨min (p.1 : NNReal) (1 : NNReal),
            show min (p.1 : NNReal) (1 : NNReal) ≤ (1 : NNReal) from min_le_right _ _⟩ :
            Set.Iic (1 : NNReal)) :=
      hfstBase.subtype_mk
    exact hfst.prodMk hsnd
  have hbase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2) := by
    -- Proof comment: pull the unit-strip witness back along the measurable truncation
    -- `t ↦ min t 1`.
    simpa [truncToOne] using hG_mono.comp htruncToOne
  have honeSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ (1 : NNReal)} := by
    exact
      (measurable_fst.subtype_val :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ (p.1 : NNReal)))
        (measurableSet_Iic : MeasurableSet (Set.Iic (1 : NNReal)))
  have hpiece :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ (1 : NNReal)}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))) := by
    simpa using hbase.piecewise honeSet measurable_const
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ (1 : NNReal) then G p.1 p.2 else 0) =
        Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ (1 : NNReal)}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) := by
    funext p
    by_cases hp1 : (p.1 : NNReal) ≤ (1 : NNReal)
    · simp [hp1]
    · simp [hp1]
  -- Proof comment: the larger-strip witness agrees with the unit-strip witness on times `≤ 1`
  -- and vanishes afterwards.
  simpa [hrewrite] using hpiece

/-- Helper for Theorem 25.8: freezing an adapted process at time `0` gives a progressively
measurable version of that single slice. -/
private theorem constantAtZeroProgVersion
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H) :
    ∃ G0 : RealProcess, ProgMeasurable ℱ G0 ∧ H 0 =ᵐ[μ] G0 0 := by
  let G0 : RealProcess := fun _ ω ↦ H 0 ω
  have hG0_adapted : Adapted ℱ G0 := by
    intro T
    -- Proof comment: every time slice of the frozen process is the original time-zero slice.
    simpa [G0] using hH_adapted.measurable_le (i := 0) (j := T) (zero_le T)
  refine ⟨G0, ?_, ?_⟩
  · -- Proof comment: constant sample paths are continuous, so adaptedness upgrades to progressive
    -- measurability.
    exact hG0_adapted.stronglyAdapted.progMeasurable_of_continuous
      (fun _ ↦ continuous_const)
  · -- Proof comment: the frozen process agrees with `H` exactly at time zero.
    simp [G0]

/-- Helper for Theorem 25.8: deterministic time translation preserves the monotonicity required to
build a shifted filtration. -/
private theorem translatedFiltration_mono
    (c : NNReal) (ℱ : TimeFiltration) :
    Monotone fun t : NNReal ↦ ℱ (c + t) := by
  intro s t hst
  simpa [add_comm, add_left_comm, add_assoc] using ℱ.mono (add_le_add_left hst c)

/-- Helper for Theorem 25.8: deterministic time translation preserves the ambient measurability
bound for filtrations. -/
private theorem translatedFiltration_le
    (c : NNReal) (ℱ : TimeFiltration) :
    ∀ t : NNReal, ℱ (c + t) ≤ (inferInstance : MeasurableSpace Ω) := by
  intro t
  exact ℱ.le (c + t)

/-- Helper for Theorem 25.8: shift a filtration by a deterministic time offset. -/
private def shiftedFiltration (c : NNReal) (ℱ : TimeFiltration) : TimeFiltration :=
  { seq := fun t ↦ ℱ (c + t)
    mono' := translatedFiltration_mono c ℱ
    le' := translatedFiltration_le c ℱ }

/-- Helper for Theorem 25.8: shift a process by a deterministic time offset. -/
private def shiftedProcess (c : NNReal) (H : RealProcess) : RealProcess :=
  fun t ω ↦ H (c + t) ω

/-- Helper for Theorem 25.8: translating the filtration and the process by the same deterministic
time preserves adaptedness. -/
private theorem adapted_shiftedProcess
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (c : NNReal) :
    Adapted (shiftedFiltration c ℱ) (shiftedProcess c H) := by
  intro t
  -- Proof comment: the shifted slice at time `t` is exactly the original slice at `c + t`.
  simpa [shiftedFiltration, shiftedProcess] using hH_adapted (c + t)

/-- Helper for Theorem 25.8: almost-sure right continuity is stable under deterministic time
translation. -/
private theorem aeRightContinuous_translatedProcess
    {μ : Measure Ω} {H : RealProcess}
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t)
    (c : NNReal) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ContinuousWithinAt (fun s : NNReal ↦ shiftedProcess c H s ω) (Set.Ici t) t := by
  filter_upwards [hH_right] with ω hω
  intro t
  have hmaps :
      Set.MapsTo (fun s : NNReal ↦ c + s) (Set.Ici t) (Set.Ici (c + t)) := by
    intro s hs
    simpa [add_assoc] using add_le_add_left hs c
  have hshift :
      ContinuousWithinAt (fun s : NNReal ↦ c + s) (Set.Ici t) t := by
    -- Proof comment: deterministic translation is continuous on every right neighborhood.
    exact (continuous_const.add continuous_id).continuousWithinAt
  -- Proof comment: compose the right-continuous path of `H` with the time translation `s ↦ c+s`.
  simpa [shiftedProcess, Function.comp, add_assoc] using
    (ContinuousWithinAt.comp
      (g := fun u : NNReal ↦ H u ω)
      (f := fun s : NNReal ↦ c + s)
      (s := Set.Ici t)
      (t := Set.Ici (c + t))
      (x := t)
      (hω (c + t)) hshift hmaps)

/-- Helper for Theorem 25.8: pulling a progressively measurable translated witness back by a
deterministic shift preserves progressive measurability after zero padding. -/
private theorem progMeasurable_shiftBack
    {ℱ : TimeFiltration} {c : NNReal} {Gshift : RealProcess}
    (hGshift : ProgMeasurable (shiftedFiltration c ℱ) Gshift) :
    ProgMeasurable ℱ (fun t ω ↦ if c ≤ t then Gshift (t - c) ω else 0) := by
  intro T
  by_cases hTc : c ≤ T
  · letI : MeasurableSpace Ω := ℱ T
    let shiftMap : Set.Iic T × Ω → Set.Iic (T - c) × Ω :=
      fun p ↦ (⟨(p.1 : NNReal) - c, tsub_le_tsub_right p.1.2 c⟩, p.2)
    have hshiftMap : Measurable shiftMap := by
      -- Proof comment: on the strip `[0, T]`, subtracting the deterministic offset `c` is a
      -- measurable coordinate change into the shorter strip `[0, T - c]`.
      have hfstBase : Measurable fun p : Set.Iic T × Ω ↦ ((p.1 : NNReal) - c) := by
        exact measurable_fst.subtype_val.sub_const c
      have hfst :
          Measurable fun p : Set.Iic T × Ω ↦
            (⟨(p.1 : NNReal) - c, tsub_le_tsub_right p.1.2 c⟩ : Set.Iic (T - c)) :=
        hfstBase.subtype_mk
      exact hfst.prodMk measurable_snd
    have hshiftStrip :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic (T - c) × Ω ↦ Gshift p.1 p.2) := by
      -- Proof comment: after identifying the shifted horizon `T - c`, the translated filtration
      -- becomes exactly the original horizon filtration `ℱ T`.
      exact (hGshift (T - c)).mono <| by
        simp [shiftedFiltration, add_tsub_cancel_of_le hTc]
    have hbase :
        Measurable fun p : Set.Iic T × Ω ↦ Gshift ((p.1 : NNReal) - c) p.2 := by
      exact hshiftStrip.measurable.comp hshiftMap
    have hcut :
        MeasurableSet {p : Set.Iic T × Ω | c ≤ (p.1 : NNReal)} := by
      -- Proof comment: the cutoff region depends only on the time coordinate.
      have htime : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
        measurable_fst.subtype_val
      exact htime measurableSet_Ici
    have hind :
        StronglyMeasurable fun p : Set.Iic T × Ω ↦
          Set.indicator {p : Set.Iic T × Ω | c ≤ (p.1 : NNReal)}
            (fun q : Set.Iic T × Ω ↦ Gshift ((q.1 : NNReal) - c) q.2) p := by
      exact hbase.stronglyMeasurable.indicator hcut
    -- Proof comment: below time `c` the pulled-back process is zero, and above `c` it is exactly
    -- the translated witness evaluated at `t - c`.
    simpa [Set.indicator] using hind
  · have hbelow : ∀ p : Set.Iic T × Ω, ¬ c ≤ (p.1 : NNReal) := by
      intro p hp
      exact hTc (hp.trans p.1.2)
    -- Proof comment: if `T < c`, the whole strip lies before the shift point, so the pullback is
    -- identically zero there.
    simpa [hbelow] using
      (stronglyMeasurable_zero :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)))

/-- Helper for Theorem 25.8: a progressively measurable unit-cell witness for a translated process
pulls back to a witness on the corresponding natural cell. -/
private theorem pullbackUnitCellVersionToNatCell
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {n : ℕ} (hn : 0 < n)
    {Gshift : RealProcess}
    (hGshift_prog :
      ProgMeasurable (shiftedFiltration ((n - 1 : ℕ) : NNReal) ℱ) Gshift)
    (hGshift_mod :
      ∀ t : NNReal, 0 < t → t ≤ 1 →
        shiftedProcess ((n - 1 : ℕ) : NNReal) H t =ᵐ[μ] Gshift t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  let c : NNReal := (k : NNReal)
  let G : RealProcess := fun t ω ↦ if c ≤ t then Gshift (t - c) ω else 0
  refine ⟨G, ?_, ?_⟩
  · -- Proof comment: pull the translated progressively measurable witness back by the
    -- deterministic map `t ↦ t - c`, padding the earlier times with zero.
    simpa [c, G] using
      progMeasurable_shiftBack (ℱ := ℱ) (c := c) (Gshift := Gshift) hGshift_prog
  · intro t htleft htright
    have ht0 : 0 < t - c := tsub_pos_of_lt htleft
    have ht1 : t - c ≤ 1 := by
      rw [tsub_le_iff_right]
      simpa [c, add_comm, add_left_comm, add_assoc] using htright
    have hc_le : c ≤ t := by
      simpa [c, Nat.succ_sub_one] using htleft.le
    -- Proof comment: on the target cell, the backward shift lands inside `(0, 1]`, so the
    -- translated unit-cell modification theorem applies directly.
    filter_upwards [hGshift_mod (t - c) ht0 ht1] with ω hω
    have hGt : G t ω = Gshift (t - c) ω := by
      simp [G, if_pos hc_le]
    rw [hGt]
    simpa only [shiftedProcess, c, Nat.succ_sub_one, add_tsub_cancel_of_le hc_le] using hω

/-- Helper for Theorem 25.8: assemble a family of local versions by choosing the process indexed
by `Nat.ceil t` at time `t`. -/
private def natCeilAssembledVersion (G : ℕ → RealProcess) : RealProcess :=
  fun t ω ↦ G (Nat.ceil t) t ω

/-- Helper for Theorem 25.8: the `Nat.ceil` assembly preserves progressive measurability once each
piece is progressively measurable. -/
private theorem progMeasurable_natCeilAssembledVersion
    {ℱ : TimeFiltration}
    (G : ℕ → RealProcess)
    (hprog : ∀ n : ℕ, ProgMeasurable ℱ (G n)) :
    ProgMeasurable ℱ (natCeilAssembledVersion G) := by
  intro T
  -- Proof comment: on the strip `[0,T]`, only finitely many ceiling indices can occur.
  refine Measurable.stronglyMeasurable ?_
  letI : MeasurableSpace Ω := ℱ T
  let K : Finset ℕ := Finset.Icc 0 (Nat.ceil T)
  let ceilMap : Set.Iic T × Ω → ℕ := fun p ↦ Nat.ceil (p.1 : NNReal)
  let slab : ℕ → Set (Set.Iic T × Ω) := fun n ↦ ceilMap ⁻¹' ({n} : Set ℕ)
  let stripSum : Set.Iic T × Ω → ℝ := fun p ↦
    K.sum (fun n ↦ Set.indicator (slab n) (fun q : Set.Iic T × Ω ↦ G n q.1 q.2) p)
  have hslab : ∀ n : ℕ, MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)] (slab n) := by
    intro n
    -- Proof comment: each slab is the preimage of a singleton under the measurable ceiling map.
    have hceilMap : Measurable ceilMap := by
      fun_prop
    simpa [slab] using hceilMap (measurableSet_singleton n)
  have hsum : Measurable stripSum := by
    -- Proof comment: finitely many measurable slab pieces can be summed directly.
    refine Finset.measurable_sum K ?_
    intro n hn
    exact Measurable.indicator ((hprog n T).measurable) (hslab n)
  have hrewrite :
      stripSum =
      (fun p : Set.Iic T × Ω ↦ natCeilAssembledVersion G p.1 p.2) := by
    funext p
    dsimp [stripSum]
    have hmemK : Nat.ceil (p.1 : NNReal) ∈ K := by
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.ceil_le.mpr (p.1.2.trans (Nat.le_ceil T))⟩
    -- Proof comment: exactly the summand indexed by `Nat.ceil p.1` survives on the strip.
    rw [Finset.sum_eq_single_of_mem (Nat.ceil (p.1 : NNReal)) hmemK]
    · simp [slab, ceilMap, natCeilAssembledVersion]
    · intro b hb hbne
      by_cases hEq : Nat.ceil (p.1 : NNReal) = b
      · exact False.elim (hbne hEq.symm)
      · simp [slab, ceilMap, hEq]
  -- Proof comment: rewrite the finite measurable sum back to the assembled strip map.
  simpa [hrewrite] using hsum

/-- Helper for Theorem 25.8: almost-sure left continuity already yields a global progressively
measurable version by taking the `limsup` of lower dyadic approximants. -/
private theorem existsProgMeasurableVersion_of_aeLeftContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_left :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧ ∀ t : NNReal, H t =ᵐ[μ] G t := by
  let G : RealProcess := fun t ω ↦ limsup (fun n ↦ H (lowerStepTime n t) ω) atTop
  have hG_prog : ProgMeasurable ℱ G := by
    refine progMeasurableOfMeasurableOnStrips (ℱ := ℱ) ?_
    intro T
    letI : MeasurableSpace (Set.Iic T × Ω) := Subtype.instMeasurableSpace.prod (ℱ T)
    let F : ℕ → Set.Iic T × Ω → ℝ := fun n p ↦ H (lowerStepTime n p.1) p.2
    have hF : ∀ n : ℕ, Measurable (F n) := by
      intro n
      -- Proof comment: each lower dyadic approximation stays in the past of the current strip
      -- horizon, so adaptedness makes it jointly measurable on that strip.
      simpa [F] using
        (lowerStep_measurableOnStrip (ℱ := ℱ) (H := H) hH_adapted T n :
          Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦
            H (lowerStepTime n p.1) p.2)
    -- Proof comment: the pointwise `limsup` of the measurable lower dyadic approximants is still
    -- measurable on every strip.
    simpa [G, F] using
      (Measurable.limsup hF :
        Measurable fun p : Set.Iic T × Ω ↦ limsup (fun n ↦ F n p) atTop)
  refine ⟨G, hG_prog, ?_⟩
  intro t
  filter_upwards [hH_left] with ω hω
  have htime_within :
      Tendsto (fun n ↦ lowerStepTime n t) atTop (𝓝[Set.Iic t] t) := by
    -- Proof comment: the lower dyadic times converge to `t` while remaining inside the left
    -- neighborhood filter `Set.Iic t`.
    refine tendsto_inf.2 ⟨tendsto_lowerStepTime t, ?_⟩
    exact tendsto_principal.2 <| Filter.Eventually.of_forall fun n ↦ lowerStepTime_le_self n t
  have hcont :
      Tendsto (fun s : NNReal ↦ H s ω) (𝓝[Set.Iic t] t) (𝓝 (H t ω)) :=
    hω t
  have hlim :
      Tendsto (fun n ↦ H (lowerStepTime n t) ω) atTop (𝓝 (H t ω)) :=
    hcont.comp htime_within
  -- Proof comment: on the almost-sure left continuity event, the `limsup` of the lower dyadic
  -- approximants recovers the original value.
  simpa [G] using hlim.limsup_eq.symm

/-- Helper for Theorem 25.8: truncate a real-valued process at level `n`. -/
private def natTruncProcess (n : ℕ) (H : RealProcess) : RealProcess :=
  fun t ω ↦ max (-(n : ℝ)) (min (H t ω) (n : ℝ))

/-- Helper for Theorem 25.8: truncation preserves adaptedness. -/
private theorem adapted_natTruncProcess
    {ℱ : TimeFiltration} {H : RealProcess}
    (n : ℕ) (hH_adapted : Adapted ℱ H) :
    Adapted ℱ (natTruncProcess n H) := by
  intro t
  -- Proof comment: each time slice is obtained from `H t` by composing with measurable `min`
  -- and `max` against deterministic constants.
  simpa [natTruncProcess] using
    (measurable_const.max ((hH_adapted t).min measurable_const))

/-- Helper for Theorem 25.8: truncating a jointly measurable process preserves joint
measurability. -/
private theorem measurable_uncurry_natTruncProcess
    {H : RealProcess}
    (n : ℕ)
    (hH_meas : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (natTruncProcess n H)) := by
  have hclamp : Measurable (fun x : ℝ ↦ max (-(n : ℝ)) (min x (n : ℝ))) :=
    measurable_const.max (measurable_id.min measurable_const)
  -- Proof comment: truncation is just postcomposition of the jointly measurable map
  -- `Function.uncurry H` with the measurable real clamp `x ↦ max (-n) (min x n)`.
  simpa [Function.uncurry, natTruncProcess] using hclamp.comp hH_meas

/-- Helper for Theorem 25.8: truncation preserves almost-sure right continuity. -/
private theorem aeRightContinuous_truncProcess
    {μ : Measure Ω} {H : RealProcess}
    (n : ℕ)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ContinuousWithinAt (fun s : NNReal ↦ natTruncProcess n H s ω) (Set.Ici t) t := by
  filter_upwards [hH_right] with ω hω
  intro t
  let clamp : ℝ → ℝ := fun x ↦ max (-(n : ℝ)) (min x (n : ℝ))
  have hclamp : Continuous clamp := by
    exact continuous_const.max (continuous_id.min continuous_const)
  -- Proof comment: the truncation map is continuous on `ℝ`, so it preserves right continuity of
  -- the sample paths after composition.
  simpa [natTruncProcess, clamp, Function.comp] using
    hclamp.continuousAt.comp_continuousWithinAt (hω t)

/-- Helper for Theorem 25.8: once a value already lies in `[-n, n]`, truncation does nothing. -/
private theorem natTruncProcess_eq_self_of_abs_le
    {Ω' : Type u}
    {H : NNReal → Ω' → ℝ}
    {n : ℕ} {t : NNReal} {ω : Ω'}
    (hbound : |H t ω| ≤ (n : ℝ)) :
    natTruncProcess n H t ω = H t ω := by
  have hpair : (-(n : ℝ)) ≤ H t ω ∧ H t ω ≤ (n : ℝ) := by
    simpa using (abs_le.mp hbound)
  -- Proof comment: both truncation clamps are inactive inside the admissible range.
  simp [natTruncProcess, min_eq_left hpair.2, max_eq_right hpair.1]

/-- Helper for Theorem 25.8: truncation is uniformly bounded by its cutoff level. -/
private theorem abs_natTruncProcess_le
    {Ω' : Type u}
    {H : NNReal → Ω' → ℝ}
    (n : ℕ) (t : NNReal) (ω : Ω') :
    |natTruncProcess n H t ω| ≤ (n : ℝ) := by
  have hlower : -(n : ℝ) ≤ natTruncProcess n H t ω := by
    exact le_max_left _ _
  have hupper : natTruncProcess n H t ω ≤ (n : ℝ) := by
    refine max_le ?_ ?_
    · exact neg_le_self (show (0 : ℝ) ≤ n by exact_mod_cast Nat.zero_le n)
    · exact min_le_right _ _
  -- Proof comment: the truncation output always stays inside the interval `[-n, n]`.
  simpa using abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Theorem 25.8: each truncation satisfies the bounded unit-cell hypothesis needed by
the auxiliary-process route. -/
private theorem natTruncProcess_boundOnUnitCell
    {Ω' : Type u} {H : NNReal → Ω' → ℝ} (n : ℕ) :
    ∀ t : NNReal, ∀ ω : Ω', 0 < t → t ≤ 1 → |natTruncProcess n H t ω| ≤ (n : ℝ) := by
  intro t ω ht0 ht1
  -- Proof comment: the pointwise truncation bound is uniform in time, so the unit-cell side
  -- conditions are immediate.
  simpa using abs_natTruncProcess_le (H := H) n t ω

/-- Helper for Theorem 25.8: clipping preserves deterministic-time modification on `(0,1]` once
the original process is already bounded there. -/
private theorem clippedProcessUnitCellModification
    {μ : Measure Ω} {H J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1,
      H t =ᵐ[μ] clippedProcess C J t := by
  intro t ht0 ht1
  filter_upwards [hJ_mod t ht0 ht1] with ω hω
  have hJ_bound : |J t ω| ≤ C := by
    simpa [hω] using hbound t ω ht0 ht1
  -- Proof comment: after transporting the bound from `H` to `J`, clipping is inactive.
  calc
    H t ω = J t ω := hω
    _ = clippedProcess C J t ω := by
      symm
      simpa [clippedProcess] using clipRealAt_eq_self_of_abs_le hC_nonneg hJ_bound

/-- Helper for Theorem 25.8: after clipping a bounded auxiliary process, each positive-time
unit-strip section admits an `ℱ 1`-measurable representative. -/
private theorem clippedProcess_unitStripSection_hasMeasurableModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {H J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1,
      ∃ g : Ω → ℝ, Measurable[ℱ 1] g ∧ clippedProcess C J t =ᵐ[μ] g := by
  intro t ht0 ht1
  have hclip_mod :
      H t =ᵐ[μ] clippedProcess C J t :=
    clippedProcessUnitCellModification
      (μ := μ) (H := H) (J := J) (C := C) hC_nonneg hJ_mod hbound t ht0 ht1
  -- Proof comment: the adapted slice `H t` is `ℱ 1`-measurable, and clipping does not change it
  -- on `(0,1]` because the unit-cell bound makes the clip inactive almost everywhere.
  exact ⟨H t, hH_adapted.measurable_le (i := t) (j := 1) ht1, hclip_mod.symm⟩

/-- Helper for Theorem 25.8: a countable `limsup` of progressively measurable real-valued
processes is progressively measurable. -/
private theorem progMeasurable_limsup
    {ℱ : TimeFiltration} {G : ℕ → RealProcess}
    (hG_prog : ∀ n : ℕ, ProgMeasurable ℱ (G n)) :
    ProgMeasurable ℱ (fun t ω ↦ limsup (fun n ↦ G n t ω) atTop) := by
  apply progMeasurableOfMeasurableOnStrips (ℱ := ℱ)
  intro T
  -- Proof comment: on each strip `[0, T] × Ω`, measurability is closed under countable
  -- `limsup`.
  exact Measurable.limsup (fun n ↦ (hG_prog n T).measurable)

/-- Helper for Theorem 25.8: if every truncation agrees almost everywhere with a witness at a
fixed time, then the `limsup` of those witnesses recovers the original value. -/
private theorem fixedTimeAeEq_limsup_of_truncationWitnesses
    {μ : Measure Ω} {H : RealProcess}
    {G : ℕ → RealProcess}
    (t : NNReal)
    (hG : ∀ n : ℕ, natTruncProcess n H t =ᵐ[μ] G n t) :
    H t =ᵐ[μ] fun ω ↦ limsup (fun n ↦ G n t ω) atTop := by
  have hAll :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, natTruncProcess n H t ω = G n t ω := by
    rw [ae_all_iff]
    exact hG
  filter_upwards [hAll] with ω hω
  have hEventuallyEq :
      (fun n : ℕ ↦ G n t ω) =ᶠ[atTop] fun _ : ℕ ↦ H t ω := by
    rcases exists_nat_gt (|H t ω|) with ⟨N, hN⟩
    filter_upwards [Ioi_mem_atTop N] with n hn
    have hbound : |H t ω| ≤ (n : ℝ) := by
      exact le_trans (le_of_lt hN) (by exact_mod_cast le_of_lt hn)
    calc
      G n t ω = natTruncProcess n H t ω := (hω n).symm
      _ = H t ω := natTruncProcess_eq_self_of_abs_le (H := H) hbound
  have hTendsto : Tendsto (fun n : ℕ ↦ G n t ω) atTop (𝓝 (H t ω)) := by
    exact tendsto_const_nhds.congr' hEventuallyEq.symm
  -- Proof comment: once the witness sequence is eventually constant at `H t ω`, its `limsup`
  -- is exactly `H t ω`.
  simpa using hTendsto.limsup_eq.symm

/-- Helper for Theorem 25.8: the `Nat.ceil` assembly preserves the timewise modification property
once time zero and every positive natural cell are controlled. -/
private theorem areModifications_natCeilAssembledVersion_of_natCells
    {μ : Measure Ω} {H : RealProcess}
    (G : ℕ → RealProcess)
    (hzero : H 0 =ᵐ[μ] G 0 0)
    (hcell :
      ∀ n : ℕ, 0 < n → ∀ t : NNReal,
        ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G n t) :
    AreModifications μ H (natCeilAssembledVersion G) := by
  intro t
  by_cases ht : t = 0
  · -- Proof comment: the time-zero slice is handled by the dedicated witness.
    subst t
    change H 0 =ᵐ[μ] G (Nat.ceil 0) 0
    simpa using hzero
  · have hceil_pos : 0 < Nat.ceil t := Nat.ceil_pos.mpr (pos_iff_ne_zero.mpr ht)
    have hleft_nat : Nat.ceil t - 1 < Nat.ceil t := Nat.sub_one_lt_of_lt hceil_pos
    have hleft : (((Nat.ceil t) - 1 : ℕ) : NNReal) < t := Nat.lt_ceil.1 hleft_nat
    -- Proof comment: for positive time, the assembled index `Nat.ceil t` picks exactly the
    -- unique natural cell containing `t`.
    simpa [natCeilAssembledVersion] using
      hcell (Nat.ceil t) hceil_pos t hleft (Nat.le_ceil t)

/-- Helper for Theorem 25.8: once time zero and each positive natural cell admit progressively
measurable witnesses, the `Nat.ceil` assembly yields a single global modification. -/
private theorem existsProgMeasurableModification_fromNatCellVersions
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hzero :
      ∃ G0 : RealProcess, ProgMeasurable ℱ G0 ∧ H 0 =ᵐ[μ] G0 0)
    (hcell :
      ∀ n : ℕ, 0 < n → ∃ G : RealProcess,
        ProgMeasurable ℱ G ∧
        ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  classical
  rcases hzero with ⟨G0, hG0_prog, hG0_zero⟩
  have hcell' :
      ∀ n : {n : ℕ // 0 < n}, ∃ G : RealProcess,
        ProgMeasurable ℱ G ∧
        ∀ t : NNReal, ((n.1 - 1 : ℕ) : NNReal) < t → t ≤ (n.1 : NNReal) → H t =ᵐ[μ] G t := by
    intro n
    exact hcell n.1 n.2
  choose Gpos hGpos_prog hGpos_cell using hcell'
  let G : ℕ → RealProcess := fun n ↦
    if hn : n = 0 then G0 else Gpos ⟨n, Nat.pos_of_ne_zero hn⟩
  refine ⟨natCeilAssembledVersion G, ?_, ?_⟩
  · -- Proof comment: each assembled piece is progressively measurable by construction.
    refine progMeasurable_natCeilAssembledVersion (ℱ := ℱ) G ?_
    intro n
    by_cases hn : n = 0
    · simpa [G, hn] using hG0_prog
    · simpa [G, hn] using hGpos_prog ⟨n, Nat.pos_of_ne_zero hn⟩
  · -- Proof comment: the timewise modification property follows from the same cellwise assembly.
    refine areModifications_natCeilAssembledVersion_of_natCells
      (μ := μ) (H := H) G ?_ ?_
    · simpa [G] using hG0_zero
    · intro n hn t hleft hright
      simpa [G, Nat.ne_zero_iff_zero_lt.mpr hn] using
        hGpos_cell ⟨n, hn⟩ t hleft hright

/-- Helper for Theorem 25.8: if a strip map is measurable on `[0,T] × Ω`, then its zero extension
is measurable on any larger strip `[0,S] × Ω`. -/
private theorem measurable_zeroExtendOfMeasurableOnLargerStrip
    {ℱ : TimeFiltration} {T S : NNReal} (hTS : T ≤ S) {F : Set.Iic T × Ω → ℝ}
    (hF : Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] F) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ S)]
      (fun p : Set.Iic S × Ω ↦
        if h : ((p.1 : NNReal) : NNReal) ≤ T then F (⟨(p.1 : NNReal), h⟩, p.2) else 0) := by
  have htimeMin :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ S)]
        (fun p : Set.Iic S × Ω ↦ min ((p.1 : NNReal) : NNReal) T) :=
    measurable_fst.subtype_val.min measurable_const
  have hsnd :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ S), ℱ T]
        (fun p : Set.Iic S × Ω ↦ p.2) :=
    measurable_snd.mono le_rfl (ℱ.mono hTS)
  let base : Set.Iic S × Ω → ℝ := fun p ↦
    F (⟨min ((p.1 : NNReal) : NNReal) T,
      show min ((p.1 : NNReal) : NNReal) T ≤ T from min_le_right _ _⟩, p.2)
  have hbase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ S)] base := by
    have hmap :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ S),
          Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic S × Ω ↦
            ((⟨min ((p.1 : NNReal) : NNReal) T,
              show min ((p.1 : NNReal) : NNReal) T ≤ T from min_le_right _ _⟩ : Set.Iic T),
              p.2)) :=
      htimeMin.subtype_mk.prodMk hsnd
    -- Proof comment: clamp the larger-strip time coordinate to `T` before evaluating `F`.
    simpa [base] using hF.comp hmap
  have hcut :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ S)]
        {p : Set.Iic S × Ω | ((p.1 : NNReal) : NNReal) ≤ T} := by
    have htime :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ S)]
          (fun p : Set.Iic S × Ω ↦ ((p.1 : NNReal) : NNReal)) :=
      measurable_fst.subtype_val
    exact htime measurableSet_Iic
  have hind :
      StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ S)]
        (fun p : Set.Iic S × Ω ↦
          Set.indicator {p : Set.Iic S × Ω | ((p.1 : NNReal) : NNReal) ≤ T} base p) :=
    hbase.stronglyMeasurable.indicator hcut
  have hrewrite :
      (fun p : Set.Iic S × Ω ↦
        if h : ((p.1 : NNReal) : NNReal) ≤ T then F (⟨(p.1 : NNReal), h⟩, p.2) else 0) =
      (fun p : Set.Iic S × Ω ↦
        Set.indicator {p : Set.Iic S × Ω | ((p.1 : NNReal) : NNReal) ≤ T} base p) := by
    funext p
    by_cases hp : ((p.1 : NNReal) : NNReal) ≤ T
    · simp [base, hp]
    · simp [base, hp]
  -- Proof comment: on the larger strip, the zero extension is the indicator of the measurable
  -- cutoff `{t ≤ T}` applied to the clamped strip map.
  rw [hrewrite]
  exact hind.measurable

/-- Helper for Theorem 25.8: the upper-step `limsup` candidate is measurable on an arbitrary
horizon strip `[0,T] × Ω`. -/
private lemma upperStepLimsup_measurableOnStrip
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H) (T : NNReal) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      fun p : Set.Iic T × Ω ↦
        limsup (fun k ↦ H (upperStepTimeOn T k p.1) p.2) atTop := by
  letI : MeasurableSpace (Set.Iic T × Ω) :=
    Subtype.instMeasurableSpace.prod (ℱ T)
  let F : ℕ → Set.Iic T × Ω → ℝ := fun k p ↦
    H (upperStepTimeOn T k p.1) p.2
  have hF : ∀ k : ℕ, Measurable (F k) := by
    intro k
    -- Proof comment: each upper-step approximation only uses times bounded by the horizon `n`.
    simpa [F] using
      (upperStep_measurableOnStrip (ℱ := ℱ) (X := H) hH_adapted T k :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦
            H (upperStepTimeOn T k p.1) p.2)
  -- Proof comment: the pointwise `limsup` of the measurable upper-step approximants is still
  -- measurable on the strip.
  simpa [F] using
    (Measurable.limsup hF :
      Measurable fun p : Set.Iic T × Ω ↦ limsup (fun k ↦ F k p) atTop)

/-- Helper for Theorem 25.8: on a fixed strip horizon, right continuity identifies the original
process with the upper-step `limsup` candidate at every earlier deterministic time. -/
private lemma aeEq_upperStepLimsup_onStrip
    {μ : Measure Ω} {H : RealProcess} {T t : NNReal}
    (ht : t ≤ T)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ s : NNReal,
        ContinuousWithinAt (fun r : NNReal ↦ H r ω) (Set.Ici s) s) :
    H t =ᵐ[μ] fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn T k t) ω) atTop := by
  filter_upwards [hH_right] with ω hω
  have hlim :
      Tendsto (fun k ↦ H (upperStepTimeOn T k t) ω) atTop (𝓝 (H t ω)) := by
    -- Proof comment: the upper-step times approach `t` from the right while staying inside the
    -- horizon strip `[0,n]`.
    let Xω : NNReal → Unit → ℝ := fun s _ ↦ H s ω
    have hXω_right :
        ∀ (_ : Unit) (s : NNReal),
          ContinuousWithinAt (fun r : NNReal ↦ Xω r () ) (Set.Ici s) s := by
      intro _ s
      simpa [Xω] using hω s
    simpa [Xω] using
      (upperStep_tendstoOnStrip (X := Xω) hXω_right T
        ((⟨t, ht⟩ : Set.Iic T), ()))
  -- Proof comment: a convergent sequence has `limsup` equal to its limit.
  simpa using hlim.limsup_eq.symm

/-- Helper for Theorem 25.8: on the strict overlap `t < S ≤ T`, the upper-step `limsup`
regularizations with horizons `S` and `T` agree exactly. -/
private lemma upperStepLimsup_eq_on_lt_of_le_horizon
    {Ω' : Type u}
    {H : NNReal → Ω' → ℝ} {t S T : NNReal}
    (htS : t < S) (hST : S ≤ T) :
    (fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn T k t) ω) atTop) =
      fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn S k t) ω) atTop := by
  funext ω
  have hEventually :
      ∀ᶠ k : ℕ in atTop, upperStepTime k t < S := by
    -- Proof comment: the untruncated upper-step times converge to `t`, so for `t < S` they
    -- eventually lie strictly below the smaller horizon `S`.
    exact (tendsto_upperStepTime t) (isOpen_Iio.mem_nhds htS)
  have hEventuallyEq :
      ∀ᶠ k : ℕ in atTop,
        H (upperStepTimeOn T k t) ω = H (upperStepTimeOn S k t) ω := by
    filter_upwards [hEventually] with k hk
    have hkT : upperStepTime k t ≤ T := le_trans hk.le hST
    have hkS : upperStepTime k t ≤ S := hk.le
    simp [upperStepTimeOn, min_eq_left hkT, min_eq_left hkS]
  -- Proof comment: eventual equality of the approximating sequences gives equality of their
  -- `limsup` values.
  simpa using Filter.limsup_congr hEventuallyEq

/-- Helper for Theorem 25.8: once both horizons lie strictly to the right of `t`, the upper-step
`limsup` candidate is independent of which horizon is chosen. -/
private lemma upperStepLimsup_eq_of_lt_horizons
    {Ω' : Type u}
    {H : NNReal → Ω' → ℝ} {t q₁ q₂ : NNReal}
    (htq₁ : t < q₁) (htq₂ : t < q₂) :
    (fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn q₁ k t) ω) atTop) =
      fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn q₂ k t) ω) atTop := by
  by_cases hq₁₂ : q₁ ≤ q₂
  · -- Proof comment: compare both horizons through the smaller one `q₁`.
    exact
      (upperStepLimsup_eq_on_lt_of_le_horizon
        (H := H) (t := t) (S := q₁) (T := q₂) htq₁ hq₁₂).symm
  · have hq₂₁ : q₂ ≤ q₁ := le_of_not_ge hq₁₂
    -- Proof comment: the symmetric case compares both horizons through the smaller one `q₂`.
    exact upperStepLimsup_eq_on_lt_of_le_horizon
      (H := H) (t := t) (S := q₂) (T := q₁) htq₂ hq₂₁

/-- Helper for Theorem 25.8: every strict sub-horizon `t < T ≤ 1` is dominated by a rational
unit horizon. -/
private abbrev UnitRatHorizon :=
  {q : ℚ≥0 // (q : NNReal) ≤ 1}

/-- Helper for Theorem 25.8: if two chosen upper-step horizons both lie strictly above a common
strict prefix, then the resulting `limsup` regularizations agree on that prefix. -/
private lemma upperStepOpenPrefix_eq_onStrictPrefix
    {Ω' : Type u}
    {H : NNReal → Ω' → ℝ} {t S T qS qT : NNReal}
    (htS : t < S) (hST : S ≤ T)
    (hSqS : S < qS) (hTqT : T < qT) :
    (fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn qS k t) ω) atTop) =
      fun ω ↦ limsup (fun k ↦ H (upperStepTimeOn qT k t) ω) atTop := by
  have htqS : t < qS := lt_trans htS hSqS
  have htT : t < T := lt_of_lt_of_le htS hST
  have htqT : t < qT := lt_trans htT hTqT
  -- Proof comment: once both horizons lie strictly above the same time `t`, the eventual
  -- upper-step sequence no longer depends on which horizon is used.
  exact upperStepLimsup_eq_of_lt_horizons (H := H) (t := t) htqS htqT

/-- Helper for Theorem 25.8: between `t` and `T ≤ 1` there is a rational horizon from the
countable unit-horizon family. -/
private theorem existsRationalHorizon_between
    {t T : NNReal} (htT : t < T) (hT1 : T ≤ 1) :
    ∃ q : UnitRatHorizon, t < (q : NNReal) ∧ (q : NNReal) ≤ T := by
  rcases (NNReal.lt_iff_exists_rat_btwn t T).1 htT with ⟨q, hq0, htq, hqT⟩
  let q0 : ℚ≥0 := ⟨q, hq0⟩
  have hq0_eq : (q0 : NNReal) = Real.toNNReal q := by
    apply Subtype.ext
    change ((q0 : NNReal) : ℝ) = (Real.toNNReal q : ℝ)
    rw [Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)]
    exact congrArg (fun x : ℚ => (x : ℝ)) (NNRat.coe_mk q hq0)
  refine ⟨⟨q0, ?_⟩, ?_, ?_⟩
  · have hq_real : (q : ℝ) ≤ 1 := by
      simpa [Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT.le.trans hT1
    rw [hq0_eq]
    simpa [Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT.le.trans hT1
  · rw [hq0_eq]
    exact htq
  · rw [hq0_eq]
    exact hqT.le

/-- Helper for Theorem 25.8: a horizon-`q` upper-step `limsup` candidate can be zero-extended to
any larger strip. -/
private lemma upperStepLimsup_zeroExtend_measurableOnStrip
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H) {q T : NNReal} (hqT : q ≤ T) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦
        if ((p.1 : NNReal) : NNReal) ≤ q then
          limsup (fun k ↦ H (upperStepTimeOn q k p.1) p.2) atTop
        else 0) := by
  -- Proof comment: extend the `q`-strip candidate by zero outside `[0, q]` inside the larger
  -- strip `[0, T]`.
  exact measurable_zeroExtendOfMeasurableOnLargerStrip
    (ℱ := ℱ) (T := q) (S := T) hqT
    (upperStepLimsup_measurableOnStrip (ℱ := ℱ) (H := H) hH_adapted q)

/-- Helper for Theorem 25.8: if `0 < T ≤ q`, then the horizon-`q` upper-step `limsup` candidate
on `[0, T] × Ω` becomes measurable after patching the top slice `{t = T}` by an `ℱ T`-measurable
boundary value. -/
private theorem measurableOnStrip_topPatchedUpperStepLimsup
    {ℱ : TimeFiltration} {H : RealProcess} {T q : NNReal} {g : Ω → ℝ}
    (hH_adapted : Adapted ℱ H) (hTq : T ≤ q)
    (hg : Measurable[ℱ T] g) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = T then g p.2
        else limsup (fun k ↦ H (upperStepTimeOn q k p.1) p.2) atTop) := by
  have hbase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦
          limsup (fun k ↦ H (upperStepTimeOn T k p.1) p.2) atTop) :=
    upperStepLimsup_measurableOnStrip (ℱ := ℱ) (H := H) hH_adapted T
  have hpatched :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦
          if (p.1 : NNReal) = T then g p.2
          else limsup (fun k ↦ H (upperStepTimeOn T k p.1) p.2) atTop) :=
    measurableOnStrip_patchTop (ℱ := ℱ) (T := T) hbase hg
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = T then g p.2
        else limsup (fun k ↦ H (upperStepTimeOn q k p.1) p.2) atTop) =
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = T then g p.2
        else limsup (fun k ↦ H (upperStepTimeOn T k p.1) p.2) atTop) := by
    funext p
    by_cases hp : (p.1 : NNReal) = T
    · simp [hp]
    · have hlt : (p.1 : NNReal) < T := lt_of_le_of_ne p.1.2 hp
      have hEq :
          limsup (fun k ↦ H (upperStepTimeOn q k (p.1 : NNReal)) p.2) atTop =
            limsup (fun k ↦ H (upperStepTimeOn T k (p.1 : NNReal)) p.2) atTop :=
        congrFun
          (upperStepLimsup_eq_on_lt_of_le_horizon
            (H := H) (t := (p.1 : NNReal)) (S := T) (T := q) hlt hTq) p.2
      -- Proof comment: away from the singleton top slice, both upper-step candidates use the same
      -- eventual upper-step times because `T ≤ q` and the smaller horizon already lies above `t`.
      simp [hp, hEq]
  rw [hrewrite]
  exact hpatched

/-- Helper for Theorem 25.8: every time `t ∈ (0, 1]` belongs to one reciprocal unit slab. -/
private lemma exists_memReciprocalUnitSlab
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, 1 / (n + 2 : NNReal) < t ∧ t ≤ 1 / (n + 1 : NNReal) := by
  let P : ℕ → Prop := fun m ↦ 1 / (m + 1 : NNReal) < t
  have hP : ∃ m : ℕ, P m := exists_nat_one_div_lt ht0
  let m : ℕ := Nat.find hP
  have hm_spec : P m := Nat.find_spec hP
  have hm_pos : 0 < m := by
    refine Nat.pos_iff_ne_zero.mpr ?_
    intro hm_zero
    have h1t : (1 : NNReal) < t := by
      simpa [P, m, hm_zero] using hm_spec
    exact (not_lt_of_ge ht1) h1t
  refine ⟨m - 1, ?_, ?_⟩
  · have hm_add : m - 1 + 2 = m + 1 := by
      omega
    have hm_add_nnreal : ((m - 1 : ℕ) : NNReal) + 2 = (m : NNReal) + 1 := by
      exact_mod_cast hm_add
    -- Proof comment: the chosen minimal index already gives the lower slab bound.
    rw [hm_add_nnreal]
    simpa [P, m] using hm_spec
  · have hminimal : ¬ P (m - 1) := by
      intro hm_prev
      have hfind_le : m ≤ m - 1 := by
        simpa [m] using (Nat.find_min' hP hm_prev)
      omega
    -- Proof comment: minimality of the chosen index forces the upper slab bound.
    simpa [P, m] using hminimal

/-- Helper for Theorem 25.8: distinct reciprocal unit slabs are disjoint on the time axis. -/
private lemma reciprocalUnitSlab_eq_of_mem
    {t : NNReal} {m n : ℕ}
    (hm : 1 / (m + 2 : NNReal) < t ∧ t ≤ 1 / (m + 1 : NNReal))
    (hn : 1 / (n + 2 : NNReal) < t ∧ t ≤ 1 / (n + 1 : NNReal)) :
    m = n := by
  have hm_right : t ≤ 1 / (((m + 1 : ℕ) : NNReal)) := by
    simpa using hm.2
  have hn_right : t ≤ 1 / (((n + 1 : ℕ) : NNReal)) := by
    simpa using hn.2
  have hmle' : ((m + 1 : ℕ) : NNReal) < n + 2 := by
    exact lt_of_one_div_lt_one_div (a := (n + 2 : NNReal)) (by positivity)
      (lt_of_lt_of_le hn.1 hm_right)
  have hnle' : ((n + 1 : ℕ) : NNReal) < m + 2 := by
    exact lt_of_one_div_lt_one_div (a := (m + 2 : NNReal)) (by positivity)
      (lt_of_lt_of_le hm.1 hn_right)
  have hmle : m ≤ n := by
    have hnat : m + 1 < n + 2 := by
      exact_mod_cast hmle'
    omega
  have hnle : n ≤ m := by
    have hnat : n + 1 < m + 2 := by
      exact_mod_cast hnle'
    omega
  exact le_antisymm hmle hnle

/-- Helper for Theorem 25.8: every interior time `t ∈ (0, 1)` lies in one half-open reciprocal
unit slab. -/
private lemma existsMemStrictReciprocalUnitSlab
    {t : NNReal} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ n : ℕ, 1 / (n + 2 : NNReal) ≤ t ∧ t < 1 / (n + 1 : NNReal) := by
  rcases exists_memReciprocalUnitSlab (t := t) ht0 ht1.le with ⟨n, hn⟩
  by_cases hEq : t = 1 / (n + 1 : NNReal)
  · have hn_pos : 0 < n := by
      refine Nat.pos_iff_ne_zero.mpr ?_
      intro hn0
      have ht_eq_one : t = 1 := by
        simpa [hn0] using hEq
      exact (not_lt_of_ge ht_eq_one.ge) ht1
    refine ⟨n - 1, ?_, ?_⟩
    · have hpred_add : n - 1 + 2 = n + 1 := by
        omega
      have hpred_add_nnreal : ((n - 1 : ℕ) : NNReal) + 2 = (n : NNReal) + 1 := by
        exact_mod_cast hpred_add
      -- Proof comment: if `t` hits the upper endpoint of the closed slab, move one slab upward
      -- so that the same point becomes the left endpoint of a half-open slab.
      rw [hpred_add_nnreal]
      simp [hEq]
    · have hpred : n - 1 + 1 = n := by
        omega
      have hpred_nnreal : ((n - 1 : ℕ) : NNReal) + 1 = (n : NNReal) := by
        exact_mod_cast hpred
      have hn_cast_pos : (0 : NNReal) < n := by
        exact_mod_cast hn_pos
      have hsucc : (n : NNReal) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      have hlt_inv : 1 / (n + 1 : NNReal) < 1 / (n : NNReal) := by
        exact one_div_lt_one_div_of_lt hn_cast_pos hsucc
      -- Proof comment: the predecessor slab has strictly larger right endpoint, so the equality
      -- case becomes a strict upper bound there.
      rw [hpred_nnreal]
      simpa [hEq] using hlt_inv
  · refine ⟨n, hn.1.le, ?_⟩
    -- Proof comment: away from the right endpoint, the original closed slab is already half-open.
    exact lt_of_le_of_ne hn.2 hEq

/-- Helper for Theorem 25.8: distinct half-open reciprocal slabs are disjoint on the time axis. -/
private lemma strictReciprocalUnitSlab_eq_of_mem
    {t : NNReal} {m n : ℕ}
    (hm : 1 / (m + 2 : NNReal) ≤ t ∧ t < 1 / (m + 1 : NNReal))
    (hn : 1 / (n + 2 : NNReal) ≤ t ∧ t < 1 / (n + 1 : NNReal)) :
    m = n := by
  have hnm : n ≤ m := by
    have hlt : 1 / (m + 2 : NNReal) < 1 / (n + 1 : NNReal) :=
      lt_of_le_of_lt hm.1 hn.2
    have hlt' : 1 / (((m + 2 : ℕ) : NNReal)) < 1 / (((n + 1 : ℕ) : NNReal)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hlt
    have horder : ((n + 1 : ℕ) : NNReal) < ((m + 2 : ℕ) : NNReal) := by
      exact lt_of_one_div_lt_one_div
        (a := ((m + 2 : ℕ) : NNReal)) (by positivity) hlt'
    have hnat : n + 1 < m + 2 := by
      exact_mod_cast horder
    omega
  have hmn : m ≤ n := by
    have hlt : 1 / (n + 2 : NNReal) < 1 / (m + 1 : NNReal) :=
      lt_of_le_of_lt hn.1 hm.2
    have hlt' : 1 / (((n + 2 : ℕ) : NNReal)) < 1 / (((m + 1 : ℕ) : NNReal)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hlt
    have horder : ((m + 1 : ℕ) : NNReal) < ((n + 2 : ℕ) : NNReal) := by
      exact lt_of_one_div_lt_one_div
        (a := ((n + 2 : ℕ) : NNReal)) (by positivity) hlt'
    have hnat : m + 1 < n + 2 := by
      exact_mod_cast horder
    omega
  exact le_antisymm hmn hnm

/-- Helper for Theorem 25.8: if `T` lies in the reciprocal slab indexed by `m`, then every later
slab already has right endpoint at or below `T`. -/
private lemma reciprocalUnitSlab_upperEndpoint_le_horizon_of_lt
    {T : NNReal} {m n : ℕ}
    (hT : 1 / (m + 2 : NNReal) < T ∧ T ≤ 1 / (m + 1 : NNReal))
    (hmn : m < n) :
    1 / (n + 1 : NNReal) ≤ T := by
  have hden_nat : m + 2 ≤ n + 1 := by
    omega
  have hden : (m + 2 : NNReal) ≤ n + 1 := by
    exact_mod_cast hden_nat
  have hrecip : 1 / (n + 1 : NNReal) ≤ 1 / (m + 2 : NNReal) := by
    -- Proof comment: reciprocal order reverses on positive denominators, so later slabs move
    -- strictly closer to zero.
    exact one_div_le_one_div_of_le (by positivity : 0 < (m + 2 : NNReal)) hden
  exact hrecip.trans hT.1.le

/-- Helper for Theorem 25.8: if `T` lies in the reciprocal slab indexed by `m`, then every
earlier slab starts at or above `T`. -/
private lemma horizon_le_reciprocalUnitSlab_lowerEndpoint_of_lt
    {T : NNReal} {m n : ℕ}
    (hT : 1 / (m + 2 : NNReal) < T ∧ T ≤ 1 / (m + 1 : NNReal))
    (hnm : n < m) :
    T ≤ 1 / (n + 2 : NNReal) := by
  have hden_nat : n + 2 ≤ m + 1 := by
    omega
  have hden : (n + 2 : NNReal) ≤ m + 1 := by
    exact_mod_cast hden_nat
  have hrecip : 1 / (m + 1 : NNReal) ≤ 1 / (n + 2 : NNReal) := by
    -- Proof comment: earlier slabs have larger endpoints because their reciprocal denominators
    -- are smaller.
    exact one_div_le_one_div_of_le (by positivity : 0 < (n + 2 : NNReal)) hden
  exact hT.2.trans hrecip

/-- Helper for Theorem 25.8: gluing the reciprocal slabs gives one measurable witness on the unit
strip `[0, 1] × Ω`. -/
private theorem existsMeasurableUnitStripVersion_of_aeRightContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) :
    ∃ G1 : Set.Iic 1 × Ω → ℝ,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω) := by
  classical
  letI : MeasurableSpace (Set.Iic (1 : NNReal) × Ω) := Subtype.instMeasurableSpace.prod (ℱ 1)
  let piece : Option ℕ → Set (Set.Iic (1 : NNReal) × Ω)
    | none => {p | (p.1 : NNReal) = 0}
    | some n =>
        {p | 1 / (n + 2 : NNReal) < (p.1 : NNReal) ∧
            (p.1 : NNReal) ≤ 1 / (n + 1 : NNReal)}
  let candidate : Option ℕ → Set.Iic (1 : NNReal) × Ω → ℝ
    | none => fun _ ↦ 0
    | some n => fun p ↦
        if h : (p.1 : NNReal) ≤ 1 / (n + 1 : NNReal) then
          limsup (fun k ↦ H (upperStepTimeOn (1 / (n + 1 : NNReal)) k p.1) p.2) atTop
        else 0
  have hpiece_meas : ∀ i, MeasurableSet (piece i) := by
    intro i
    have htime :
        Measurable fun p : Set.Iic (1 : NNReal) × Ω ↦ (p.1 : NNReal) :=
      measurable_fst.subtype_val
    cases i with
    | none =>
        -- Proof comment: the time-zero piece is the preimage of the singleton `{0}`.
        have hzeroSet :
            MeasurableSet {p : Set.Iic (1 : NNReal) × Ω | (p.1 : NNReal) = 0} := by
          convert htime (measurableSet_singleton (0 : NNReal)) using 1
        simpa [piece] using hzeroSet
    | some n =>
        -- Proof comment: each positive slab is an interval condition on the time coordinate.
        have hslab :
            MeasurableSet
              {p : Set.Iic (1 : NNReal) × Ω |
                1 / (n + 2 : NNReal) < (p.1 : NNReal) ∧
                  (p.1 : NNReal) ≤ 1 / (n + 1 : NNReal)} := by
          exact (measurableSet_Ioi.preimage htime).inter (measurableSet_Iic.preimage htime)
        simpa [piece] using hslab
  have hcandidate_meas : ∀ i, Measurable (candidate i) := by
    intro i
    cases i with
    | none =>
        -- Proof comment: the zero-time piece uses the constant witness `0`.
        simp [candidate]
    | some n =>
        have hq1 : (1 / (n + 1 : NNReal)) ≤ 1 := by
          have hn1 : (1 : NNReal) ≤ (n + 1 : NNReal) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          rw [one_div]
          exact inv_le_one_of_one_le₀ hn1
        -- Proof comment: on each positive slab, zero-extend the fixed-horizon candidate to the
        -- whole unit strip and then restrict back to the slab.
        change
          Measurable
            (fun p : Set.Iic (1 : NNReal) × Ω ↦
              if (p.1 : NNReal) ≤ 1 / (n + 1 : NNReal) then
                limsup (fun k ↦ H (upperStepTimeOn (1 / (n + 1 : NNReal)) k p.1) p.2) atTop
              else 0)
        exact upperStepLimsup_zeroExtend_measurableOnStrip
          (ℱ := ℱ) (H := H) hH_adapted (q := 1 / (n + 1 : NNReal)) (T := 1) hq1
  have hpairwise :
      Pairwise fun i j => Set.EqOn (candidate i) (candidate j) (piece i ∩ piece j) := by
    intro i j hij x hx
    rcases i with _ | m <;> rcases j with _ | n
    · exact (hij rfl).elim
    · rcases (by
        simpa [piece] using hx :
          (((x.1 : NNReal) : NNReal) = 0) ∧
            (1 / (n + 2 : NNReal) < ((x.1 : NNReal) : NNReal) ∧
              ((x.1 : NNReal) : NNReal) ≤ 1 / (n + 1 : NNReal))) with
        ⟨hx0, hxn⟩
      have hnonneg : (0 : NNReal) ≤ 1 / (n + 2 : NNReal) := by
        positivity
      exact False.elim <|
        (not_lt_of_ge (by rw [hx0]; exact hnonneg)) hxn.1
    · rcases (by
        simpa [piece] using hx :
          (1 / (m + 2 : NNReal) < ((x.1 : NNReal) : NNReal) ∧
            ((x.1 : NNReal) : NNReal) ≤ 1 / (m + 1 : NNReal)) ∧
            (((x.1 : NNReal) : NNReal) = 0)) with
        ⟨hxm, hx0⟩
      have hnonneg : (0 : NNReal) ≤ 1 / (m + 2 : NNReal) := by
        positivity
      exact False.elim <|
        (not_lt_of_ge (by rw [hx0]; exact hnonneg)) hxm.1
    · rcases (by
        simpa [piece] using hx :
          (1 / (m + 2 : NNReal) < ((x.1 : NNReal) : NNReal) ∧
            ((x.1 : NNReal) : NNReal) ≤ 1 / (m + 1 : NNReal)) ∧
            (1 / (n + 2 : NNReal) < ((x.1 : NNReal) : NNReal) ∧
              ((x.1 : NNReal) : NNReal) ≤ 1 / (n + 1 : NNReal))) with
        ⟨hm, hn⟩
      have hmn : m = n := reciprocalUnitSlab_eq_of_mem hm hn
      exact (hij (by simp [hmn])).elim
  rcases exists_measurable_piecewise piece hpiece_meas candidate hcandidate_meas hpairwise with
    ⟨G1, hG1_meas, hG1_eq⟩
  refine ⟨G1, hG1_meas, ?_⟩
  intro t ht0 ht1
  rcases exists_memReciprocalUnitSlab ht0 ht1 with ⟨n, hn⟩
  filter_upwards
      [aeEq_upperStepLimsup_onStrip (μ := μ) (H := H) (T := 1 / (n + 1 : NNReal))
        (t := t) hn.2 hH_right] with ω hω
  have hmem : ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ piece (some n) := by
    simpa [piece] using hn
  have hrewrite :
      G1 (⟨t, ht1⟩, ω) =
        limsup (fun k ↦ H (upperStepTimeOn (1 / (n + 1 : NNReal)) k t) ω) atTop := by
    calc
      G1 (⟨t, ht1⟩, ω) = candidate (some n) (⟨t, ht1⟩, ω) := hG1_eq (some n) hmem
      _ = limsup (fun k ↦ H (upperStepTimeOn (1 / (n + 1 : NNReal)) k t) ω) atTop := by
        dsimp [candidate]
        exact if_pos hn.2
  -- Proof comment: after choosing the slab containing `t`, the glued witness is exactly the
  -- fixed-horizon upper-step `limsup` candidate on that slab.
  exact hω.trans hrewrite.symm

/-- Helper for Theorem 25.8: a unit-strip witness measurable for `prod (ℱ 1)` is also measurable
for the ambient product measurable space on `Set.Iic 1 × Ω`. -/
private theorem unitStripWitness_ambientlyMeasurable
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))] G1) :
    Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)] G1 := by
  -- Proof comment: forget the terminal filtration on the second coordinate and view the strip
  -- witness inside the ambient product measurable space.
  exact hG1.mono (by
    refine sup_le_sup le_rfl ?_
    exact MeasurableSpace.comap_mono (ℱ.le (1 : NNReal))) le_rfl

/-- Helper for Theorem 25.8: extend a measurable unit-strip witness to an ambient jointly
measurable process without changing its deterministic-time modification property on `(0,1]`. -/
private theorem unitStripWitnessToProcess
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    {μ : Measure Ω} {H : RealProcess}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))] G1)
    (hG1_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω)) :
    ∃ J : RealProcess, Measurable (Function.uncurry J) ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] J t := by
  let J : RealProcess := fun t ω ↦ if ht1 : t ≤ 1 then G1 (⟨t, ht1⟩, ω) else 0
  refine ⟨J, ?_, ?_⟩
  · have hG1_ambient :
        Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)] G1 :=
      unitStripWitness_ambientlyMeasurable (ℱ := ℱ) hG1
    let base : NNReal × Ω → ℝ := fun p ↦
      G1 (⟨min p.1 (1 : NNReal), by simp⟩, p.2)
    have htrunc :
        Measurable fun p : NNReal × Ω ↦
          ((⟨min p.1 (1 : NNReal), by simp⟩ : Set.Iic (1 : NNReal)), p.2) := by
      have hfstBase : Measurable fun p : NNReal × Ω ↦ min p.1 (1 : NNReal) := by
        exact measurable_fst.min measurable_const
      have hfst :
          Measurable fun p : NNReal × Ω ↦
            (⟨min p.1 (1 : NNReal), by simp⟩ : Set.Iic (1 : NNReal)) :=
        hfstBase.subtype_mk
      exact hfst.prodMk measurable_snd
    have hbase : Measurable base := by
      -- Proof comment: clamp the time coordinate to `[0,1]` before evaluating the strip witness.
      simpa [base] using hG1_ambient.comp htrunc
    have hcut : MeasurableSet {p : NNReal × Ω | p.1 ≤ (1 : NNReal)} := by
      -- Proof comment: the zero-extension cutoff depends only on the time coordinate.
      exact measurable_fst (measurableSet_Iic : MeasurableSet (Set.Iic (1 : NNReal)))
    have hind :
        StronglyMeasurable fun p : NNReal × Ω ↦
          Set.indicator {p : NNReal × Ω | p.1 ≤ (1 : NNReal)} base p := by
      exact hbase.stronglyMeasurable.indicator hcut
    have hrewrite :
        Function.uncurry J =
          (fun p : NNReal × Ω ↦
            Set.indicator {p : NNReal × Ω | p.1 ≤ (1 : NNReal)} base p) := by
      -- Proof comment: the global extension is exactly the indicator of `{t ≤ 1}` applied to the
      -- clamped unit-strip witness.
      funext p
      by_cases hp : p.1 ≤ 1
      · simp [Function.uncurry, J, base, hp]
      · simp [Function.uncurry, J, base, hp]
    rw [hrewrite]
    exact hind.measurable
  · intro t ht0 ht1
    -- Proof comment: on `(0,1]`, the ambient extension agrees with the strip witness by
    -- construction, so the deterministic-time modification statement transfers directly.
    simpa [J, ht1] using hG1_mod t ht0 ht1

/-- Helper for Theorem 25.8: a measurable unit-strip witness plus a unit-cell bound yields a
globally jointly measurable bounded auxiliary process. -/
private theorem existsBoundedJointlyMeasurableUnitCellAux_of_measurableUnitStripWitness
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {G1 : Set.Iic (1 : NNReal) × Ω → ℝ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1)
    (hG1_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ J : RealProcess, Measurable (Function.uncurry J) ∧
      (∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] J t) ∧
      (∀ t : NNReal, ∀ ω : Ω, |J t ω| ≤ C) := by
  rcases unitStripWitnessToProcess (μ := μ) (ℱ := ℱ) (H := H) hG1 hG1_mod with
    ⟨J0, hJ0_meas, hJ0_mod⟩
  let J : RealProcess := clippedProcess C J0
  refine ⟨J, ?_, ?_, ?_⟩
  · -- Proof comment: clipping preserves joint measurability of the ambient auxiliary process.
    simpa [J] using measurable_uncurry_clippedProcess (J := J0) (C := C) hJ0_meas
  · intro t ht0 ht1
    -- Proof comment: on `(0, 1]`, the bound on `H` makes the clipping inactive after
    -- transporting the deterministic-time modification through `J0`.
    simpa [J] using
      clippedProcessUnitCellModification
        (μ := μ) (H := H) (J := J0) hC_nonneg hJ0_mod hbound t ht0 ht1
  · intro t ω
    -- Proof comment: clipping enforces the global pointwise bound needed for the bounded route.
    simpa [J] using abs_clippedProcess_le (J := J0) (C := C) hC_nonneg t ω

/-- Helper for Theorem 25.8: the ambient inclusion `Set.Iic T × Ω ↪ Set.Iic 1 × Ω` is
measurable whenever `T ≤ 1`. -/
private theorem measurableUnitStripInclusionAmbient
    {T : NNReal} (hTle1 : T ≤ 1) :
    Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω),
      Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
      (fun p : Set.Iic T × Ω ↦
        ((⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩ :
          Set.Iic (1 : NNReal)), p.2)) := by
  have hfstBase :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        (fun p : Set.Iic T × Ω ↦ (p.1 : NNReal)) :=
    measurable_fst.subtype_val
  have hfst :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        (fun p : Set.Iic T × Ω ↦
          (⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩ :
            Set.Iic (1 : NNReal))) :=
    hfstBase.subtype_mk
  -- Proof comment: the time coordinate is included into the larger strip, while the sample
  -- coordinate is unchanged in the ambient measurable space.
  exact hfst.prodMk measurable_snd

/-- Helper for Theorem 25.8: a measurable unit-strip witness also restricts to smaller horizons
in the ambient product measurable space. This ambient version is useful for the auxiliary-process
construction. -/
private theorem measurableOnSmallStripOfAmbientUnitStripWitness
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1)
    {T : NNReal} (hTle1 : T ≤ 1) :
    Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
      (fun p : Set.Iic T × Ω ↦
        G1 (⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩, p.2)) := by
  have hG1_ambient :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        G1 :=
    unitStripWitness_ambientlyMeasurable (ℱ := ℱ) hG1
  -- Proof comment: forgetting the filtration removes the backward-transport obstruction, so the
  -- restriction is just composition with the measurable inclusion `Set.Iic T × Ω ↪ Set.Iic 1 × Ω`.
  simpa using hG1_ambient.comp (measurableUnitStripInclusionAmbient (Ω := Ω) hTle1)

/-- Helper for Theorem 25.8: for `T ≤ 1`, the explicit unit-cell candidate built from a
measurable unit-strip witness is still measurable on `Set.Iic T × Ω` for the ambient product
measurable space. This isolates the only part of the small-strip route that does not require the
missing filtered globalization theorem. -/
private theorem measurableOnSmallStripOfUnitCellCandidateAmbient
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1)
    {T : NNReal} (hTle1 : T ≤ 1) :
    Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) := by
  have hsmall :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        (fun p : Set.Iic T × Ω ↦
          G1 (⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩, p.2)) :=
    measurableOnSmallStripOfAmbientUnitStripWitness (ℱ := ℱ) (G1 := G1) hG1 hTle1
  have hzero :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) :=
    measurable_const
  have hzeroSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) = 0} := by
    have htime :
        Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
          (fun p : Set.Iic T × Ω ↦ (p.1 : NNReal)) :=
      measurable_fst.subtype_val
    convert htime (measurableSet_singleton (0 : NNReal)) using 1
  have hpiece :
      Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)]
        (Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) = 0}
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))
          (fun p : Set.Iic T × Ω ↦
            G1 (⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩, p.2))) := by
    simpa using hzero.piecewise hzeroSet hsmall
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) =
        Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) = 0}
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))
          (fun p : Set.Iic T × Ω ↦
            G1 (⟨(p.1 : NNReal), (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1⟩, p.2)) := by
    funext p
    by_cases hp0 : (p.1 : NNReal) = 0
    · simp [hp0]
    · have hp1 : (p.1 : NNReal) ≤ 1 :=
        (show (p.1 : NNReal) ≤ T from p.1.2).trans hTle1
      simp [Set.piecewise, hp0, hp1]
  -- Proof comment: the candidate is just the ambiently measurable restricted witness with the
  -- singleton time-zero slice patched by `0`.
  simpa [hrewrite] using hpiece

/-- Helper for Theorem 25.8: on the unit strip, patching the time-zero slice of a measurable
witness by `0` preserves filtered strip measurability. -/
private theorem measurableOnUnitStripZeroPatchedWitness
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
      (fun p : Set.Iic (1 : NNReal) × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) := by
  have hrewrite :
      (fun p : Set.Iic (1 : NNReal) × Ω ↦ G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) = G1 := by
    funext p
    simp
  have hstrip1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦ G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) := by
    simpa [hrewrite] using hG1
  -- Proof comment: only the singleton slice `{t = 0}` is modified, so the general strip patching
  -- lemma applies directly on the unit strip.
  exact measurableOnStrip_zeroAtOrigin (ℱ := ℱ) hstrip1

/-- Helper for Theorem 25.8: the explicit unit-cell candidate built from a measurable unit-strip
witness is already measurable on the unit strip itself. -/
private theorem measurableOnUnitStripOfUnitCellCandidate
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
      (fun p : Set.Iic (1 : NNReal) × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) := by
  have hpatched :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦
          if (p.1 : NNReal) = 0 then 0
          else G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) :=
    measurableOnUnitStripZeroPatchedWitness (ℱ := ℱ) (G1 := G1) hG1
  -- Proof comment: on `Set.Iic 1`, the extra branch `if h1 : p.1 ≤ 1` is always taken, so the
  -- explicit unit-cell candidate reduces to the zero-patched witness.
  convert hpatched using 1
  ext p
  by_cases hp0 : (p.1 : NNReal) = 0
  · simp [hp0]
  · have hp1 : (p.1 : NNReal) ≤ 1 := p.1.2
    simp [hp0, hp1]

/-- Helper for Theorem 25.8: the explicit unit-cell candidate built from a measurable unit-strip
witness stays measurable on every larger strip `[0, T] × Ω` once it is extended by zero outside
the unit cell. -/
private theorem measurableOnLargeStripOfUnitCellCandidate
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ} {T : NNReal}
    (h1leT : (1 : NNReal) ≤ T)
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) := by
  let G : RealProcess := fun t ω ↦
    if h0 : t = 0 then 0 else if h1 : t ≤ 1 then G1 (⟨t, h1⟩, ω) else 0
  have hstrip1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦ G p.1 p.2) := by
    -- Proof comment: on the unit strip itself, the explicit candidate is already measurable after
    -- patching the singleton time-zero slice.
    simpa [G] using
      measurableOnUnitStripOfUnitCellCandidate (ℱ := ℱ) (G1 := G1) hG1
  have hstripLarge :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) :=
    measurableZeroOutsideUnitCellOfMeasurableOnStrip
      (ℱ := ℱ) (G := G) (T := T) h1leT hstrip1
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) =
        (fun p : Set.Iic T × Ω ↦
          if (p.1 : NNReal) = 0 then 0
          else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) := by
    funext p
    by_cases hp1 : (p.1 : NNReal) ≤ 1
    · by_cases hp0 : (p.1 : NNReal) = 0
      · simp [G, hp0]
      · simp [G, hp1, hp0]
    · have hp0 : ¬ (p.1 : NNReal) = 0 := by
        intro hp0
        exact hp1 (by simp [hp0])
      simp [G, hp1, hp0]
  -- Proof comment: above time `1` the candidate vanishes, so larger-strip measurability follows
  -- from the zero-extension of the already measurable unit-strip witness.
  simpa [hrewrite] using hstripLarge

/-- Helper for Theorem 25.8: on a horizon `T ≥ 1`, the sample coordinate is measurable as a map
into the smaller filtration `ℱ 1`. -/
private theorem measurableSndToUnitFiltration_of_one_le
    {ℱ : TimeFiltration} {T : NNReal}
    (h1leT : (1 : NNReal) ≤ T) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T), ℱ (1 : NNReal)]
      (fun p : Set.Iic T × Ω ↦ p.2) := by
  -- Proof comment: monotonicity of the filtration transports the sample coordinate from
  -- `ℱ T` down to `ℱ 1` whenever `1 ≤ T`.
  exact measurable_snd.mono le_rfl (ℱ.mono h1leT)

/-- Helper for Theorem 25.8: once the unit-strip witness is patched at time zero, extending it by
`0` outside `(0,1]` preserves strip measurability on larger horizons. -/
private theorem measurableZeroOutsideUnitCellOnLargeStrip
    {ℱ : TimeFiltration} {G : RealProcess} {T : NNReal}
    (h1leT : (1 : NNReal) ≤ T)
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        (fun p : Set.Iic (1 : NNReal) × Ω ↦ G p.1 p.2)) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) := by
  let truncToOne : Set.Iic T × Ω → Set.Iic (1 : NNReal) × Ω :=
    fun p ↦ (⟨min (p.1 : NNReal) (1 : NNReal),
      show min (p.1 : NNReal) (1 : NNReal) ≤ (1 : NNReal) from min_le_right _ _⟩, p.2)
  have htruncToOne :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T),
        Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        truncToOne := by
    have hfstBase :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦ min (p.1 : NNReal) (1 : NNReal) := by
      exact measurable_fst.subtype_val.min measurable_const
    have hfst :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          fun p : Set.Iic T × Ω ↦
          (⟨min (p.1 : NNReal) (1 : NNReal),
            show min (p.1 : NNReal) (1 : NNReal) ≤ (1 : NNReal) from min_le_right _ _⟩ :
            Set.Iic (1 : NNReal)) :=
      hfstBase.subtype_mk
    exact hfst.prodMk
      (measurableSndToUnitFiltration_of_one_le (Ω := Ω) (ℱ := ℱ) h1leT)
  have hbase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2) := by
    -- Proof comment: first pull the unit-strip witness back along the measurable truncation
    -- `t ↦ min t 1`.
    simpa [truncToOne] using hG1.comp htruncToOne
  have honeSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1} := by
    exact measurableSet_le measurable_fst.subtype_val measurable_const
  have hpiece :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))) := by
    simpa using hbase.piecewise honeSet measurable_const
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) =
        Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) (1 : NNReal)) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) := by
    funext p
    by_cases hp1 : (p.1 : NNReal) ≤ 1
    · simp [hp1]
    · simp [hp1]
  -- Proof comment: on the larger strip, the extended process agrees with the unit-strip witness
  -- for times `≤ 1` and vanishes afterwards.
  simpa [hrewrite] using hpiece

/-- Helper for Theorem 25.8: the unit-cell candidate is measurable on the degenerate strip
`[0, 0] × Ω`. -/
private theorem measurableOnZeroStripOfUnitCellCandidate
    {ℱ : TimeFiltration} {G1 : Set.Iic (1 : NNReal) × Ω → ℝ} :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ (0 : NNReal))]
      (fun p : Set.Iic (0 : NNReal) × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) := by
  have hrewrite :
      (fun p : Set.Iic (0 : NNReal) × Ω ↦
        if (p.1 : NNReal) = 0 then 0
        else if h1 : (p.1 : NNReal) ≤ 1 then G1 (⟨(p.1 : NNReal), h1⟩, p.2) else 0) =
        (fun _ : Set.Iic (0 : NNReal) × Ω ↦ (0 : ℝ)) := by
    funext p
    have hp0 : (p.1 : NNReal) = 0 := le_antisymm p.1.2 (show (0 : NNReal) ≤ p.1 from zero_le _)
    simp [hp0]
  -- Proof comment: every point of `Set.Iic 0` has time coordinate `0`, so the candidate reduces
  -- to the constant zero function.
  rw [hrewrite]
  exact
    (measurable_const :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (0 : NNReal))]
        (fun _ : Set.Iic (0 : NNReal) × Ω ↦ (0 : ℝ)))

/- The stale local bounded-regularization port below is not needed for Theorem 25.8.
The imported core unit-cell globalization theorem is sufficient in this workspace.
namespace UnitCellBoundedRegularization

/-- Helper for Theorem 25.8: replacing the second coordinate of a strip rectangle by its
`μ.trim (ℱ 1)`-measurable hull does not change any deterministic-time section up to `μ`-a.e.
equality. -/
theorem section_prod_toMeasurable_ae_eq
    {μ : Measure Ω} {ℱ : TimeFiltration} {s : Set (Set.Iic (1 : NNReal))} {u : Set Ω}
    (hu : NullMeasurableSet u (μ.trim (ℱ.le 1)))
    (t : NNReal) (ht1 : t ≤ 1) :
    {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ toMeasurable (μ.trim (ℱ.le 1)) u} =ᵐ[μ]
      {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ u} := by
  exact MeasureTheory.Adapted.section_prod_toMeasurable_ae_eq
    (μ := μ) (ℱ := ℱ) (s := s) (u := u) hu t ht1

/-- Helper for Theorem 25.8: a strip rectangle with a `μ.trim (ℱ 1)`-null-measurable second
coordinate already has a `𝓑([0,1]) ⊗ ℱ 1` measurable event version. -/
theorem existsMeasurableUnitStripRectangleEventVersion
    {μ : Measure Ω} {ℱ : TimeFiltration}
    {s : Set (Set.Iic (1 : NNReal))} (hs : MeasurableSet s) {u : Set Ω}
    (hu : NullMeasurableSet u (μ.trim (ℱ.le 1))) :
    ∃ B : Set (Set.Iic (1 : NNReal) × Ω),
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ 1)] B ∧
      ∀ t : NNReal, ∀ ht1 : t ≤ 1,
        {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B} =ᵐ[μ]
          {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ u} := by
  exact MeasureTheory.Adapted.existsMeasurableUnitStripRectangleEventVersion
    (μ := μ) (ℱ := ℱ) hs hu

/-- Helper for Theorem 25.8: an ambiently measurable strip event whose positive-time sections are
`μ.trim (ℱ 1)`-null measurable admits one `𝓑([0,1]) ⊗ ℱ 1` measurable version with the same
positive-time sections up to `μ`-a.e. equality. -/
theorem existsMeasurableUnitStripEventVersion
    {μ : Measure Ω} {ℱ : TimeFiltration}
    {A : Set (Set.Iic (1 : NNReal) × Ω)}
    (hA_meas : MeasurableSet[Subtype.instMeasurableSpace.prod inferInstance] A)
    (hA_section :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        NullMeasurableSet {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ A} (μ.trim (ℱ.le 1))) :
    ∃ B : Set (Set.Iic (1 : NNReal) × Ω),
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ 1)] B ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B} =ᵐ[μ]
          {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ A} := by
  exact MeasureTheory.Adapted.existsMeasurableUnitStripEventVersion
    (μ := μ) (ℱ := ℱ) hA_meas hA_section

/-- Helper for Theorem 25.8: once positive-time strip events admit measurable versions, the same
holds for finite-range strip maps by regularizing each value fiber and summing the resulting
indicators. -/
theorem existsMeasurableFiniteRangeUnitStripVersion_of_eventBridge
    {μ : Measure Ω} {ℱ : TimeFiltration}
    (hEvent :
      ∀ {A : Set (Set.Iic (1 : NNReal) × Ω)},
        MeasurableSet[Subtype.instMeasurableSpace.prod inferInstance] A →
        (∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
          NullMeasurableSet {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ A} (μ.trim (ℱ.le 1))) →
        ∃ B : Set (Set.Iic (1 : NNReal) × Ω),
          MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ 1)] B ∧
          ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
            {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B} =ᵐ[μ]
              {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ A})
    {S : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hS_finite : Finite (Set.range S))
    (hS_meas : Measurable[Subtype.instMeasurableSpace.prod inferInstance] S)
    (hS_section_aemeas :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        AEMeasurable[ℱ 1] (fun ω ↦ S (⟨t, ht1⟩, ω)) μ) :
    ∃ G1 : Set.Iic (1 : NNReal) × Ω → ℝ,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        (fun ω ↦ S (⟨t, ht1⟩, ω)) =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω) := by
  exact MeasureTheory.Adapted.existsMeasurableFiniteRangeUnitStripVersion_of_eventBridge
    (μ := μ) (ℱ := ℱ) hEvent hS_finite hS_meas hS_section_aemeas

/-- Helper for Theorem 25.8: a bounded ambiently measurable strip map whose deterministic-time
sections are `ℱ 1`-a.e.-measurable admits one `𝓑([0,1]) ⊗ ℱ 1` measurable version. -/
theorem existsMeasurableUnitStripVersion_of_boundedStripAEMeasurableSections
    {μ : Measure Ω} {ℱ : TimeFiltration}
    {J : Set.Iic (1 : NNReal) × Ω → ℝ} {C : ℝ}
    (hJ_meas : Measurable[Subtype.instMeasurableSpace.prod inferInstance] J)
    (hJ_section_aemeas :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        AEMeasurable[ℱ 1] (fun ω ↦ J (⟨t, ht1⟩, ω)) μ)
    (hJ_bound : ∀ p : Set.Iic (1 : NNReal) × Ω, |J p| ≤ C) :
    ∃ G1 : Set.Iic (1 : NNReal) × Ω → ℝ,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        (fun ω ↦ J (⟨t, ht1⟩, ω)) =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω) := by
  exact MeasureTheory.Adapted.existsMeasurableUnitStripVersion_of_boundedStripAEMeasurableSections
    (μ := μ) (ℱ := ℱ) hJ_meas hJ_section_aemeas hJ_bound

/-- Helper for Theorem 25.8: a bounded jointly measurable auxiliary process on `(0, 1]` first
regularizes to one measurable witness on the unit strip. -/
theorem existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableDirect
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hJ_meas : Measurable (Function.uncurry J))
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G1 : Set.Iic 1 × Ω → ℝ,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω) := by
  exact MeasureTheory.Adapted.existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableDirect
    (μ := μ) (ℱ := ℱ) (H := H) (J := J) hC_nonneg hH_adapted hJ_meas hJ_mod hbound

/-- Helper for Theorem 25.8: the bounded jointly measurable auxiliary process on `(0, 1]`
globalizes by first producing one measurable unit-strip witness and then applying the existing
unit-cell core theorem. -/
theorem existsProgMeasurableVersionOnUnitCell_of_boundedJointlyMeasurableAux
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hJ_meas : Measurable (Function.uncurry J))
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  exact MeasureTheory.Adapted.existsProgMeasurableVersionOnUnitCell_of_boundedJointlyMeasurableAux
    (μ := μ) (ℱ := ℱ) (H := H) (J := J) hC_nonneg hH_adapted hJ_meas hJ_mod hbound

end UnitCellBoundedRegularization
-/

/-- Helper for Theorem 25.8: a coherent family of finite-horizon strip representatives on
`(0, 1]` globalizes to one progressively measurable unit-cell version. -/
private theorem progMeasurableVersionOnUnitCell_ofCoherentBoundaryVersions
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {K : NNReal → RealProcess}
    (hstrip : ∀ T : NNReal, 0 < T → T ≤ 1 →
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ K T p.1 p.2))
    (hcoh : ∀ {S T : NNReal}, 0 < S → S ≤ T → T ≤ 1 →
      ∀ t : NNReal, t ≤ S → K T t = K S t)
    (htop : ∀ T : NNReal, 0 < T → T ≤ 1 → H T =ᵐ[μ] K T T) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  let G : RealProcess := fun t ω ↦ if t = 0 then 0 else if t ≤ 1 then K 1 t ω else 0
  let G1 : Set.Iic (1 : NNReal) × Ω → ℝ := fun p ↦ K 1 p.1 p.2
  refine ⟨G, ?_, ?_⟩
  · -- Proof comment: on small strips use the horizon-`T` representative via coherence; on large
    -- strips reuse the horizon-`1` representative and extend it by zero outside `(0, 1]`.
    apply progMeasurableOfMeasurableOnStrips (ℱ := ℱ)
    intro T
    by_cases hT0 : T = 0
    · subst hT0
      simpa [G, G1] using
        (measurableOnZeroStripOfUnitCellCandidate (Ω := Ω) (ℱ := ℱ) (G1 := G1))
    · by_cases hTle1 : T ≤ 1
      · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
        have hKT :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦ K T p.1 p.2) :=
          hstrip T hTpos hTle1
        have hpatched :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦
                if (p.1 : NNReal) = 0 then 0 else K T p.1 p.2) :=
          measurableOnStrip_zeroAtOrigin (ℱ := ℱ) hKT
        have hrewrite :
            (fun p : Set.Iic T × Ω ↦ G p.1 p.2) =
              (fun p : Set.Iic T × Ω ↦
                if (p.1 : NNReal) = 0 then 0 else K T p.1 p.2) := by
          funext p
          by_cases hp0 : (p.1 : NNReal) = 0
          · simp [G, hp0]
          · have hKeq :
              K 1 (p.1 : NNReal) p.2 = K T (p.1 : NNReal) p.2 := by
              have hbase :
                  K 1 (p.1 : NNReal) = K T (p.1 : NNReal) :=
                MeasureTheory.Adapted.unitCellBoundaryVersionPrefixCoherent
                  (K := K) hcoh (S := T) (T := 1) hTpos hTle1 le_rfl p.1.2
              exact congrArg (fun f : Ω → ℝ ↦ f p.2) hbase
            have hp1 : (p.1 : NNReal) ≤ 1 := p.1.2.trans hTle1
            simp [G, hp0, hp1, hKeq]
        simpa [hrewrite] using hpatched
      · have h1leT : (1 : NNReal) ≤ T := le_of_not_ge hTle1
        have hG1 :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
              G1 :=
          hstrip 1 zero_lt_one le_rfl
        simpa [G, G1] using
          measurableOnLargeStripOfUnitCellCandidate
            (Ω := Ω) (ℱ := ℱ) (G1 := G1) h1leT hG1
  · -- Proof comment: for `0 < t ≤ 1`, the horizon-`1` representative agrees with the horizon-`t`
    -- top slice by coherence, and the top slice matches `H t` almost everywhere by assumption.
    intro t ht0 ht1
    have htop' : H t =ᵐ[μ] K t t :=
      htop t ht0 ht1
    have hcoh' : K 1 t = K t t :=
      MeasureTheory.Adapted.unitCellBoundaryVersionPrefixCoherent
        (K := K) hcoh (S := t) (T := 1) ht0 ht1 le_rfl le_rfl
    refine htop'.trans ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp [G, ht0.ne', ht1, hcoh'.symm]

/-- Helper for Theorem 25.8: a measurable witness on the unit strip globalizes to a
progressively measurable process on the unit cell. -/
private theorem existsProgMeasurableUnitCellVersion_of_measurableUnitStripVersion
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {G1 : Set.Iic (1 : NNReal) × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ (1 : NNReal))]
        G1)
    (hG1_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω)) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  rcases unitStripWitnessToProcess (μ := μ) (ℱ := ℱ) (H := H) hG1 hG1_mod with
    ⟨J, hJ_meas, hJ_mod⟩
  let K : NNReal → RealProcess := fun _ ↦ J
  have hstrip :
      ∀ T : NNReal, 0 < T → T ≤ 1 →
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ K T p.1 p.2) := by
    intro T hTpos hTle1
    simpa [K] using
      (measurableOnStrip_of_productMeasurable (H := J) hJ_meas T :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ J p.1 p.2))
  have hcoh :
      ∀ {S T : NNReal}, 0 < S → S ≤ T → T ≤ 1 →
        ∀ t : NNReal, t ≤ S → K T t = K S t := by
    intro S T hSpos hST hTle1 t htS
    rfl
  have htop :
      ∀ T : NNReal, 0 < T → T ≤ 1 → H T =ᵐ[μ] K T T := by
    intro T hTpos hTle1
    simpa [K] using hJ_mod T hTpos hTle1
  -- Proof comment: the jointly measurable extension supplies one constant coherent family of
  -- finite-horizon strip representatives, and the coherent-family globalization theorem turns
  -- that family into the desired progressively measurable unit-cell version.
  exact progMeasurableVersionOnUnitCell_ofCoherentBoundaryVersions
    (μ := μ) (ℱ := ℱ) (H := H) hstrip hcoh htop

/-- Helper for Theorem 25.8: adaptedness makes every deterministic-time unit-cell slice
`ℱ 1`-measurable. -/
private theorem adapted_unitStripSection_measurable
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    {t : NNReal} (ht1 : t ≤ 1) :
    Measurable[ℱ 1] (H t) := by
  -- Proof comment: the slice `H t` is `ℱ t`-measurable by adaptedness, and the filtration is
  -- monotone on the unit cell.
  simpa using hH_adapted.measurable_le (i := t) (j := 1) ht1

/-- Helper for Theorem 25.8: deterministic-time modifications of adapted unit-cell slices admit
an `ℱ 1`-measurable representative. -/
private theorem unitStripSection_has_measurableModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {H J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ g : Ω → ℝ, Measurable[ℱ 1] g ∧ J t =ᵐ[μ] g := by
  -- Proof comment: reuse the adapted slice `H t` itself as the measurable representative and
  -- transport along the deterministic-time almost-everywhere equality.
  refine ⟨H t, adapted_unitStripSection_measurable (ℱ := ℱ) (H := H) hH_adapted ht1, ?_⟩
  exact (hJ_mod t ht0 ht1).symm

/-- Helper for Theorem 25.8: deterministic-time modifications of adapted unit-cell slices admit a
representative that is both `ℱ 1`-measurable and ambiently measurable. -/
private theorem unitStripSection_has_ambientlyMeasurableModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {H J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ g : Ω → ℝ, Measurable[ℱ 1] g ∧ Measurable g ∧ J t =ᵐ[μ] g := by
  rcases unitStripSection_has_measurableModification
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hH_adapted hJ_mod ht0 ht1 with
    ⟨g, hg, hEq⟩
  -- Proof comment: the adapted slice `H t` supplies an `ℱ 1`-measurable representative, and
  -- forgetting the filtration keeps the same representative ambiently measurable.
  exact ⟨g, hg, hg.mono (ℱ.le 1) le_rfl, hEq⟩

/-- Helper for Theorem 25.8: deterministic-time modifications of adapted unit-cell slices are
ambiently almost everywhere measurable. -/
private theorem unitStripSection_ambientAEMeasurableOfModification
    {μ : Measure Ω} {ℱ : TimeFiltration} {H J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ _ : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    AEMeasurable (J t) μ := by
  rcases unitStripSection_has_ambientlyMeasurableModification
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hH_adapted hJ_mod ht0 ht1 with
    ⟨g, _hg, hgAmbient, hEq⟩
  -- Proof comment: the same measurable representative is still measurable for the ambient sample
  -- space, so the time slice is ambiently a.e. measurable.
  exact hgAmbient.aemeasurable.congr hEq.symm

/-- Helper for Theorem 25.8: each truncated almost-surely right-continuous process admits a
progressively measurable unit-cell version. -/
private theorem existsProgMeasurableUnitCellVersion_of_aeRightContinuousNatTrunc
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (n : ℕ)
    (hH_adapted : Adapted ℱ H)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → natTruncProcess n H t =ᵐ[μ] G t := by
  have hHn_adapted :
      Adapted ℱ (natTruncProcess n H) :=
    adapted_natTruncProcess (ℱ := ℱ) (H := H) n hH_adapted
  have hHn_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ natTruncProcess n H s ω) (Set.Ici t) t :=
    aeRightContinuous_truncProcess (H := H) n hH_right
  -- Route correction: stop after the measurable unit-strip witness and globalize it through the
  -- bounded auxiliary-process interface already built in this file; the compiled import does not
  -- expose the later Remark 25.7 unit-strip globalization theorem names.
  rcases existsMeasurableUnitStripVersion_of_aeRightContinuous
      (μ := μ) (ℱ := ℱ) (H := natTruncProcess n H) hHn_adapted hHn_right with
    ⟨G1, hG1_meas, hG1_mod⟩
  -- Proof comment: the measurable strip witness is combined with the truncation bound on `(0,1]`
  -- to enter the bounded auxiliary-process route.
  exact existsProgMeasurableUnitCellVersion_of_measurableUnitStripVersion
    (μ := μ) (ℱ := ℱ) (H := natTruncProcess n H) hG1_meas hG1_mod

/-- Helper for Theorem 25.8: on the unit cell `(0,1]`, the right-continuous branch is the only
remaining analytic regularization problem. -/
private theorem existsProgMeasurableUnitCellVersion_of_aeRightContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  have hTrunc :
      ∀ n : ℕ, ∃ G : RealProcess, ProgMeasurable ℱ G ∧
        ∀ t : NNReal, 0 < t → t ≤ 1 → natTruncProcess n H t =ᵐ[μ] G t := by
    intro n
    -- Proof comment: for each bounded truncation, replace the failed open-prefix route by the
    -- canonical bounded auxiliary-process theorem from Remark 25.7.
    exact existsProgMeasurableUnitCellVersion_of_aeRightContinuousNatTrunc
      (μ := μ) (ℱ := ℱ) (H := H) n hH_adapted hH_right
  choose G hG_prog hG_mod using hTrunc
  refine ⟨fun t ω ↦ limsup (fun n ↦ G n t ω) atTop, ?_, ?_⟩
  · -- Proof comment: package the bounded unit-cell witnesses into one progressively measurable
    -- process by taking the stripwise measurable `limsup`.
    exact progMeasurable_limsup (ℱ := ℱ) hG_prog
  · intro t ht0 ht1
    -- Proof comment: for fixed `t`, the truncations eventually stabilize to `H t`, so the
    -- `limsup` of the bounded witnesses recovers the original process almost everywhere.
    exact fixedTimeAeEq_limsup_of_truncationWitnesses (μ := μ) (H := H) t
      (fun n ↦ hG_mod n t ht0 ht1)

/-- Helper for Theorem 25.8: translating the unit-cell right-continuous regularization theorem to
the natural cell `((n - 1), n]` yields the witness shape used in the final assembly. -/
private theorem existsProgMeasurableNatCellVersion_of_aeRightContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    {n : ℕ} (hn : 0 < n)
    (hH_adapted : Adapted ℱ H)
    (hH_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
  let c : NNReal := ((n - 1 : ℕ) : NNReal)
  let ℱshift : TimeFiltration := shiftedFiltration c ℱ
  let Hshift : RealProcess := shiftedProcess c H
  have hHshift_adapted : Adapted ℱshift Hshift := by
    -- Proof comment: translate both the filtration and the process by the same deterministic
    -- offset before applying the unit-cell theorem.
    simpa [ℱshift, Hshift] using
      adapted_shiftedProcess (ℱ := ℱ) (H := H) hH_adapted c
  have hHshift_right :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ Hshift s ω) (Set.Ici t) t := by
    -- Proof comment: the almost-sure right-continuity hypothesis is stable under translation.
    simpa [Hshift] using
      aeRightContinuous_translatedProcess (μ := μ) (H := H) hH_right c
  rcases existsProgMeasurableUnitCellVersion_of_aeRightContinuous
      (μ := μ) (ℱ := ℱshift) (H := Hshift) hHshift_adapted hHshift_right with
    ⟨Gshift, hGshift_prog, hGshift_mod⟩
  -- Proof comment: pull the translated unit-cell witness back through the deterministic shift to
  -- obtain the desired witness on `((n - 1), n]`.
  exact pullbackUnitCellVersionToNatCell
    (μ := μ) (ℱ := ℱ) (H := H) hn hGshift_prog hGshift_mod

/-- Helper for Theorem 25.8: on the unit cell `(0,1]`, almost-sure left continuity should yield a
progressively measurable witness via lower dyadic approximants. -/
private theorem existsProgMeasurableUnitCellVersion_of_aeLeftContinuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_left :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  rcases existsProgMeasurableVersion_of_aeLeftContinuous
      (μ := μ) (ℱ := ℱ) (H := H) hH_adapted hH_left with
    ⟨G, hG_prog, hG_mod⟩
  refine ⟨G, hG_prog, ?_⟩
  intro t ht0 ht1
  exact hG_mod t

-- Proof sketch: in the almost-surely right-continuous or left-continuous case, modify the process
-- on each finite strip by a one-sided dyadic approximation argument that stays inside the strip.
-- The remaining blocker is turning those local strip constructions into one global progressively
-- measurable version while preserving the timewise almost-sure modification statement.
/-- Theorem 25.8 (2): if an adapted real-valued process is almost surely right continuous or
almost surely left continuous, then it admits a progressively measurable version. -/
theorem exists_progMeasurable_modification_of_ae_left_or_right_continuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_ae_cont :
      (∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) ∨
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  -- Route correction: the direct null-set patch route is wrong because an ambient measurable
  -- exceptional set need not preserve adaptedness. The viable route is strip-local one-sided
  -- approximation plus a global assembly step.
  have hzero :
      ∃ G0 : RealProcess, ProgMeasurable ℱ G0 ∧ H 0 =ᵐ[μ] G0 0 :=
    constantAtZeroProgVersion (μ := μ) (ℱ := ℱ) (H := H) hH_adapted
  rcases hH_ae_cont with hH_right | hH_left
  · have hcell :
        ∀ n : ℕ, 0 < n → ∃ G : RealProcess,
          ProgMeasurable ℱ G ∧
          ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
      intro n hn
      exact existsProgMeasurableNatCellVersion_of_aeRightContinuous
        (μ := μ) (ℱ := ℱ) (H := H) hn hH_adapted hH_right
    -- Proof comment: once time zero and every positive natural cell are regularized, the local
    -- `Nat.ceil` assembly theorem produces the global progressively measurable version.
    exact existsProgMeasurableModification_fromNatCellVersions
      (μ := μ) (ℱ := ℱ) (H := H) hzero hcell
  · -- Proof comment: the left-continuous branch closes directly because the lower dyadic
    -- approximants stay in the past of each time and therefore already define a global
    -- progressively measurable modification.
    exact existsProgMeasurableVersion_of_aeLeftContinuous
      (μ := μ) (ℱ := ℱ) (H := H) hH_adapted hH_left

end Adapted
end MeasureTheory

/- Theorem 25.8 (3): in particular, every predictable process is progressively measurable. This is
exactly the canonical theorem `MeasureTheory.IsPredictable.progMeasurable`. -/
recall IsPredictable.progMeasurable
