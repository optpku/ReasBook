/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Filter

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "RealProcess" => NNReal → Ω → ℝ

variable {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}

namespace ProgMeasurable

/-- Helper for Remark 25.7: the progressively measurable restriction of `H` to the strip
`[0, n] × Ω` is measurable for the ambient product measurable space. -/
theorem measurableOnNatStrip
    (hH : ProgMeasurable ℱ H) (n : ℕ) :
    Measurable (fun p : Set.Iic (n : NNReal) × Ω ↦ H p.1 p.2) := by
  -- Proof comment: enlarge the `Ω`-measurable space from `ℱ n` to the ambient measurable space.
  simpa using
    (hH (n : NNReal)).mono
      (show Subtype.instMeasurableSpace.prod (ℱ (n : NNReal)) ≤
          Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω) from by
        exact sup_le_sup le_rfl (ℱ.le (n : NNReal))).measurable

/-- Helper for Remark 25.7: the strips `[0, n] × Ω` cover all of `ℝ≥0 × Ω`. -/
theorem natStripCover_univ :
    (⋃ n : ℕ, (((Set.Iic (n : NNReal)) : Set NNReal) ×ˢ (Set.univ : Set Ω))) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    rcases exists_nat_ge x.1 with ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨n, ?_⟩
    simp [hn]

/-- Helper for Remark 25.7: every progressively measurable real-valued process is product
measurable. -/
-- Proof sketch: for each deterministic horizon `t`, progressive measurability gives measurability
-- of the restriction of `H` to the strip `Set.Iic t × Ω` with respect to `𝓑([0,t]) ⊗ ℱ t`;
-- since `ℱ t ≤ inferInstance`, these restrictions are jointly measurable for the ambient product
-- measurable space, and one patches the stripwise statements over the increasing cover
-- `[0,∞) = ⋃ n, [0,n]`.
theorem measurable_uncurry
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {H : NNReal → Ω → ℝ}
    (hH : ProgMeasurable ℱ H) :
    Measurable (Function.uncurry H) := by
  let S : ℕ → Set (NNReal × Ω) := fun n ↦
    (((Set.Iic (n : NNReal)) : Set NNReal) ×ˢ (Set.univ : Set Ω))
  let f := fun n (p : S n) ↦ H p.1.1 p.1.2
  have hSm : ∀ n, MeasurableSet (S n) := by
    intro n
    -- Proof comment: each strip is measurable because `[0, n]` is a measurable interval.
    exact measurableSet_Iic.prod MeasurableSet.univ
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    -- Proof comment: stripwise progressive measurability becomes ambient strip measurability.
    simpa [f, S] using hH.measurableOnNatStrip n
  have hcompat :
      ∀ i j x hxi hxj, f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rfl
  -- Proof comment: glue the measurable strip restrictions over the countable strip cover.
  simpa [Function.uncurry, f, S, natStripCover_univ] using
    measurable_liftCover S hSm f hfm hcompat natStripCover_univ

/-- A progressively measurable real-valued process is adapted to the underlying filtration. -/
-- Proof sketch: `ProgMeasurable.stronglyAdapted` upgrades `H` to a strongly adapted process, and
-- for real-valued processes strong adaptedness implies ordinary adaptedness.
theorem adapted
    (hH : ProgMeasurable ℱ H) :
    Adapted ℱ H :=
  hH.stronglyAdapted.adapted

end ProgMeasurable

namespace Adapted

/-- Helper for Remark 25.7: joint measurability immediately gives strip measurability for the
ambient product measurable space. -/
theorem measurableOnStrip_of_productMeasurable
    (hH_prod : Measurable (Function.uncurry H))
    (T : NNReal) :
    Measurable[Subtype.instMeasurableSpace.prod inferInstance]
      (fun p : Set.Iic T × Ω ↦ H p.1 p.2) := by
  -- Proof comment: restrict the jointly measurable map `Function.uncurry H` to the strip
  -- inclusion `Set.Iic T × Ω ↪ NNReal × Ω`.
  simpa [Function.uncurry] using
    hH_prod.comp_measurable (by
      fun_prop)

/-- Helper for Remark 25.7: stripwise measurability of a version is enough to conclude
progressive measurability, since the codomain is `ℝ`. -/
theorem progMeasurable_of_measurableOnStrips
    {H' : RealProcess}
    (hstrip : ∀ T : NNReal,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ H' p.1 p.2)) :
    ProgMeasurable ℱ H' := by
  intro T
  -- Proof comment: for real-valued strip maps, ordinary measurability upgrades to strong
  -- measurability by the standard second-countable codomain theorem.
  exact (hstrip T).stronglyMeasurable

/-- Helper for Remark 25.7: a stripwise measurable modification can be upgraded to a
progressively measurable modification without changing the witness. -/
theorem existsProgMeasurableModification_of_existsStripwiseMeasurableModification
    (hstrip :
      ∃ H' : RealProcess,
        (∀ T : NNReal,
          Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
            (fun p : Set.Iic T × Ω ↦ H' p.1 p.2)) ∧
        AreModifications μ H H') :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  rcases hstrip with ⟨H', hH'_strip, hH'_mod⟩
  -- Proof comment: reuse the stripwise witness and upgrade its measurability via the
  -- real-valued `progMeasurable_of_measurableOnStrips` bridge.
  refine ⟨H', progMeasurable_of_measurableOnStrips (ℱ := ℱ) hH'_strip, hH'_mod⟩

/-- Helper for Remark 25.7: the time-zero slice already gives a progressively measurable
version. -/
theorem zeroTimeProgVersion
    (hH_adapted : Adapted ℱ H) :
    ∃ G0 : RealProcess, ProgMeasurable ℱ G0 ∧ H 0 =ᵐ[μ] G0 0 := by
  let G0 : RealProcess := fun _ ω ↦ H 0 ω
  have hG0_adapted : Adapted ℱ G0 := by
    intro T
    -- Proof comment: the constant-in-time version uses only the time-zero random variable.
    simpa [G0] using hH_adapted.measurable_le (i := 0) (j := T) (zero_le T)
  refine ⟨G0, ?_, ?_⟩
  · -- Proof comment: constant paths are continuous, so strong adaptedness upgrades to
    -- progressive measurability.
    exact hG0_adapted.stronglyAdapted.progMeasurable_of_continuous
      (fun _ ↦ continuous_const)
  · -- Proof comment: at time zero this version coincides with the original process exactly.
    simpa [G0]

/-- Helper for Remark 25.7: shift a filtration by a deterministic time `c`. -/
def translatedFiltration (c : NNReal) (ℱ : TimeFiltration) : TimeFiltration where
  seq t := ℱ (c + t)
  mono' := by
    intro s t hst
    exact ℱ.mono (by simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hst c)
  le' := by
    intro t
    exact ℱ.le (c + t)

/-- Helper for Remark 25.7: shift a process by a deterministic time `c`. -/
def translatedProcess (c : NNReal) (H : RealProcess) : RealProcess :=
  fun t ω ↦ H (c + t) ω

/-- Helper for Remark 25.7: deterministic time translation preserves adaptedness once the
filtration is shifted by the same amount. -/
theorem adapted_translatedProcess
    (hH_adapted : Adapted ℱ H)
    (c : NNReal) :
    Adapted (translatedFiltration c ℱ) (translatedProcess c H) := by
  intro t
  -- Proof comment: at translated time `t`, the shifted process is exactly the original slice at
  -- time `c + t`, and the shifted filtration uses the same σ-algebra.
  simpa [translatedFiltration, translatedProcess] using hH_adapted (c + t)

/-- Helper for Remark 25.7: deterministic time translation preserves joint measurability. -/
theorem measurable_uncurry_translatedProcess
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {H : NNReal → Ω → ℝ}
    (hH_prod : Measurable (Function.uncurry H))
    (c : NNReal) :
    Measurable (Function.uncurry (translatedProcess c H)) := by
  have hshift :
      Measurable (fun p : NNReal × Ω ↦ (c + p.1, p.2)) := by
    -- Proof comment: translate only the time coordinate and leave the sample point unchanged.
    exact (measurable_const.add measurable_fst).prodMk measurable_snd
  -- Proof comment: the translated process is the original jointly measurable map precomposed with
  -- the measurable affine time-shift.
  simpa [Function.uncurry, translatedProcess] using hH_prod.comp hshift

/-- Helper for Remark 25.7: translating the unit cell `(0,1]` by `n - 1` lands in the natural
cell `((n - 1), n]`. -/
theorem add_pred_mem_natCell
    {n : ℕ} (hn : 0 < n) {t : NNReal}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (((n - 1 : ℕ) : NNReal) < ((n - 1 : ℕ) : NNReal) + t) ∧
      ((n - 1 : ℕ) : NNReal) + t ≤ (n : NNReal) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  constructor
  · -- Proof comment: adding a positive time increment moves strictly inside the translated cell.
    simpa using lt_add_of_pos_right (k : NNReal) ht0
  · -- Proof comment: the upper endpoint is exactly one unit above the left endpoint.
    simpa [add_assoc] using add_le_add_left ht1 (k : NNReal)

/-- Helper for Remark 25.7: truncate a real-valued process at level `n`. -/
def truncProcess (n : ℕ) (H : RealProcess) : RealProcess :=
  fun t ω ↦ max (-(n : ℝ)) (min (H t ω) (n : ℝ))

/-- Helper for Remark 25.7: truncation preserves adaptedness. -/
theorem adapted_truncProcess
    (n : ℕ) (hH_adapted : Adapted ℱ H) :
    Adapted ℱ (truncProcess n H) := by
  intro t
  -- Proof comment: each time slice is obtained from `H t` by composing with measurable `min`
  -- and `max` against deterministic constants.
  simpa [truncProcess] using
    (measurable_const.max ((hH_adapted t).min measurable_const))

/-- Helper for Remark 25.7: truncation preserves joint measurability. -/
theorem measurable_uncurry_truncProcess
    (n : ℕ) (hH_prod : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (truncProcess n H)) := by
  have hclamp : Measurable (fun x : ℝ ↦ max (-(n : ℝ)) (min x (n : ℝ))) :=
    measurable_const.max (measurable_id.min measurable_const)
  -- Proof comment: the jointly measurable map is postcomposed with the measurable real clamp
  -- `x ↦ max (-n) (min x n)`.
  simpa [Function.uncurry, truncProcess] using hclamp.comp hH_prod

/-- Helper for Remark 25.7: every truncation is uniformly bounded by its cutoff level. -/
theorem abs_truncProcess_le
    (n : ℕ) (t : NNReal) (ω : Ω) :
    |truncProcess n H t ω| ≤ (n : ℝ) := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Proof comment: the lower clamp enforces the bound from below.
    exact le_max_left _ _
  · -- Proof comment: the upper clamp enforces the bound from above.
    refine max_le_iff.mpr ⟨?_, min_le_right _ _⟩
    nlinarith

/-- Helper for Remark 25.7: once a value already lies in `[-n, n]`, truncation does nothing. -/
theorem truncProcess_eq_self_of_abs_le
    {n : ℕ} {t : NNReal} {ω : Ω}
    (hbound : |H t ω| ≤ (n : ℝ)) :
    truncProcess n H t ω = H t ω := by
  have hpair : (-(n : ℝ)) ≤ H t ω ∧ H t ω ≤ (n : ℝ) := by
    simpa using (abs_le.mp hbound)
  -- Proof comment: the lower and upper clamps are both inactive inside the truncation range.
  have hmin : min (H t ω) (n : ℝ) = H t ω := min_eq_left hpair.2
  calc
    truncProcess n H t ω = max (-(n : ℝ)) (min (H t ω) (n : ℝ)) := by
      rfl
    _ = max (-(n : ℝ)) (H t ω) := by rw [hmin]
    _ = H t ω := max_eq_right hpair.1

/-- Helper for Remark 25.7: progressive measurability already gives the strip measurability needed
for the unit-cell family interface. -/
theorem measurableOnStrip_of_progMeasurableUnitCell
    {G : RealProcess}
    (hG_prog : ProgMeasurable ℱ G)
    (T : NNReal) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ G p.1 p.2) := by
  -- Proof comment: for real-valued processes, progressive measurability is stronger than the
  -- ordinary strip measurability used by the family-shaped helper theorems.
  exact (hG_prog T).measurable

/-- Helper for Remark 25.7: patching the time-zero slice by a constant preserves strip
measurability. -/
theorem measurableOnStrip_zeroAtOrigin
    {G : RealProcess} {T : NNReal}
    (hG :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ G p.1 p.2)) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) = 0 then 0 else G p.1 p.2) := by
  have hzero :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) :=
    measurable_const
  have hzeroSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) = 0} := by
    have htime : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
      measurable_fst.subtype_val
    simpa using htime measurableSet_singleton
  -- Proof comment: only the time-zero slice is replaced; outside that measurable singleton,
  -- the original strip witness is unchanged.
  simpa [Set.piecewise] using hzero.piecewise hzeroSet hG

/-- Helper for Remark 25.7: once the unit strip witness is measurable and already patched at time
zero, extending it by `0` outside `(0,1]` preserves strip measurability on larger horizons. -/
theorem measurableZeroOutsideUnitCell_of_measurableOnStrip
    {G : RealProcess} {T : NNReal}
    (hT : 1 ≤ T)
    (hG :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)]
        (fun p : Set.Iic 1 × Ω ↦ G p.1 p.2)) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) := by
  have hG_mono :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic 1 × Ω ↦ G p.1 p.2) :=
    hG.mono <| by
      exact sup_le_sup le_rfl (ℱ.mono hT)
  let truncToOne : Set.Iic T × Ω → Set.Iic 1 × Ω :=
    fun p ↦ (⟨min (p.1 : NNReal) 1, min_le_right _ _⟩, p.2)
  have htruncToOne : Measurable truncToOne := by
    have hfstBase : Measurable fun p : Set.Iic T × Ω ↦ min (p.1 : NNReal) 1 := by
      exact measurable_fst.subtype_val.min measurable_const
    have hfst :
        Measurable fun p : Set.Iic T × Ω ↦
          (⟨min (p.1 : NNReal) 1, min_le_right _ _⟩ : Set.Iic 1) :=
      hfstBase.subtype_mk
    exact hfst.prodMk measurable_snd
  have hbase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) 1) p.2) := by
    -- Proof comment: pull the horizon-`1` strip witness back along the measurable truncation
    -- `t ↦ min t 1`.
    simpa [truncToOne] using hG_mono.comp_measurable htruncToOne
  have honeSet :
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
        {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1} := by
    have htime : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
      measurable_fst.subtype_val
    simpa using htime measurableSet_Iic
  have hpiece :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) 1) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))) := by
    simpa using hbase.piecewise honeSet measurable_const
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) =
        Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) ≤ 1}
          (fun p : Set.Iic T × Ω ↦ G (min (p.1 : NNReal) 1) p.2)
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) := by
    funext p
    by_cases hp1 : (p.1 : NNReal) ≤ 1
    · simp [hp1, min_eq_left hp1]
    · simp [hp1]
  -- Proof comment: the larger-strip witness agrees with the unit-strip witness on times `≤ 1`
  -- and vanishes afterwards.
  simpa [hrewrite] using hpiece

/-- Helper for Remark 25.7: restricting a horizon-`1` strip witness to a smaller strip preserves
measurability. -/
theorem measurableOnSmallStripOfUnitStripWitnessCore
    {G1 : Set.Iic 1 × Ω → ℝ}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1)
    {T : NNReal} (hTle1 : T ≤ 1) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ G1 (⟨(p.1 : NNReal), hTle1.trans p.1.2⟩, p.2)) := by
  have hsnd :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T), ℱ 1]
        (fun p : Set.Iic T × Ω ↦ p.2) :=
    measurable_snd.mono le_rfl (ℱ.mono hTle1)
  have hfstBase :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ (p.1 : NNReal)) :=
    measurable_fst.subtype_val
  have hmap :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ T),
        Subtype.instMeasurableSpace.prod (ℱ 1)]
        (fun p : Set.Iic T × Ω ↦
          ((⟨(p.1 : NNReal), hTle1.trans p.1.2⟩ : Set.Iic 1), p.2)) :=
    hfstBase.subtype_mk.prodMk hsnd
  -- Proof comment: restrict the unit-strip witness along the measurable inclusion
  -- `Set.Iic T × Ω ↪ Set.Iic 1 × Ω`.
  simpa using hG1.comp hmap

/-- Helper for Remark 25.7: a measurable witness on the unit strip globalizes to a progressively
measurable process by patching time zero and extending by zero outside `(0,1]`. -/
theorem existsProgMeasurableVersionOnUnitCellOfMeasurableUnitStripVersionCore
    {G1 : Set.Iic 1 × Ω → ℝ}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1)
    (hG1_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω)) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  let G : RealProcess := fun t ω ↦
    if h0 : t = 0 then 0 else if h1 : t ≤ 1 then G1 (⟨t, h1⟩, ω) else 0
  refine ⟨G, ?_, ?_⟩
  · -- Proof comment: measurability on each strip is obtained by restricting the unit-strip
    -- witness, patching the singleton time slice `{0}`, and extending by zero beyond time `1`.
    apply progMeasurable_of_measurableOnStrips (ℱ := ℱ)
    intro T
    by_cases hT0 : T = 0
    · -- Proof comment: on the degenerate strip `[0,0]`, the candidate is identically zero.
      simp [G, hT0]
    · by_cases hTle1 : T ≤ 1
      · have hsmall :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦ G1 (⟨(p.1 : NNReal), hTle1.trans p.1.2⟩, p.2)) :=
          measurableOnSmallStripOfUnitStripWitnessCore (ℱ := ℱ) hG1 hTle1
        have hpatched :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦
                if (p.1 : NNReal) = 0 then 0
                else G1 (⟨(p.1 : NNReal), hTle1.trans p.1.2⟩, p.2)) :=
          measurableOnStrip_zeroAtOrigin (ℱ := ℱ) hsmall
        have hrewrite :
            (fun p : Set.Iic T × Ω ↦ G p.1 p.2) =
              (fun p : Set.Iic T × Ω ↦
                if (p.1 : NNReal) = 0 then 0
                else G1 (⟨(p.1 : NNReal), hTle1.trans p.1.2⟩, p.2)) := by
          funext p
          by_cases hp0 : (p.1 : NNReal) = 0
          · simp [G, hp0]
          · have hp1 : (p.1 : NNReal) ≤ 1 := hTle1.trans p.1.2
            simp [G, hp0, hp1]
        simpa [hrewrite] using hpatched
      · have h1leT : (1 : NNReal) ≤ T := le_of_not_ge hTle1
        have hstrip1small :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)]
              (fun p : Set.Iic 1 × Ω ↦ G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) := by
          simpa using
            measurableOnSmallStripOfUnitStripWitnessCore (ℱ := ℱ) hG1 le_rfl
        have hstrip1 :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)]
              (fun p : Set.Iic 1 × Ω ↦ if (p.1 : NNReal) = 0 then 0 else G p.1 p.2) := by
          have hpatched :
              Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)]
                (fun p : Set.Iic 1 × Ω ↦
                  if (p.1 : NNReal) = 0 then 0
                  else G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) :=
            measurableOnStrip_zeroAtOrigin (ℱ := ℱ) hstrip1small
          have hrewrite :
              (fun p : Set.Iic 1 × Ω ↦ if (p.1 : NNReal) = 0 then 0 else G p.1 p.2) =
                (fun p : Set.Iic 1 × Ω ↦
                  if (p.1 : NNReal) = 0 then 0
                  else G1 (⟨(p.1 : NNReal), p.1.2⟩, p.2)) := by
            funext p
            by_cases hp0 : (p.1 : NNReal) = 0
            · simp [hp0, G]
            · have hp1 : (p.1 : NNReal) ≤ 1 := p.1.2
              simp [G, hp0, hp1]
          simpa [hrewrite] using hpatched
        have hstripLarge :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) :=
          measurableZeroOutsideUnitCell_of_measurableOnStrip (ℱ := ℱ) h1leT hstrip1
        have hrewrite :
            (fun p : Set.Iic T × Ω ↦ G p.1 p.2) =
              (fun p : Set.Iic T × Ω ↦ if (p.1 : NNReal) ≤ 1 then G p.1 p.2 else 0) := by
          funext p
          by_cases hp1 : (p.1 : NNReal) ≤ 1
          · simp [G, hp1]
          · simp [G, hp1]
        simpa [hrewrite] using hstripLarge
  · intro t ht0 ht1
    -- Proof comment: on `(0,1]`, the globalized process agrees with the unit-strip witness by
    -- construction, so the fixed-time modification statement transfers directly.
    simpa [G, ht0.ne', ht1] using hG1_mod t ht0 ht1

/-- Helper for Remark 25.7: if `H` is already progressively measurable on the unit cell, then it
is its own progressively measurable version there. -/
theorem existsProgMeasurableVersionOnUnitCell_of_selfProgMeasurable
    (hH_prog : ProgMeasurable ℱ H) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  -- Proof comment: reuse `H` itself as the unit-cell witness.
  refine ⟨H, hH_prog, ?_⟩
  intro t ht0 ht1
  -- Proof comment: the witness agrees with the original process pointwise, hence almost
  -- everywhere, on every deterministic time slice.
  exact Filter.EventuallyEq.rfl

/-- Helper for Remark 25.7: on the unit strip, adaptedness upgrades every fixed-time slice to the
terminal sigma-algebra `ℱ 1`. -/
theorem measurable_unitStripSection
    (hH_adapted : Adapted ℱ H)
    {t : NNReal} (ht1 : t ≤ 1) :
    Measurable[ℱ 1] (H t) := by
  -- Proof comment: `H t` is `ℱ t`-measurable by adaptedness, and `ℱ t ≤ ℱ 1` on the unit cell.
  simpa using hH_adapted.measurable_le (i := t) (j := 1) ht1

/-- Helper for Remark 25.7: a fixed-time modification of an adapted unit-cell slice is
`ℱ 1`-a.e.-measurable. -/
theorem aemeasurable_unitStripSection_of_modification
    {J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    AEMeasurable[ℱ 1] (J t) μ := by
  -- Proof comment: transfer the `ℱ 1`-measurability of the adapted slice `H t` across the
  -- deterministic-time almost-everywhere equality with `J t`.
  refine (measurable_unitStripSection (ℱ := ℱ) (H := H) hH_adapted ht1).aemeasurable.congr ?_
  exact (hJ_mod t ht0 ht1).symm

/-- Helper for Remark 25.7: clip a real value to the interval `[-C, C]`. -/
def clipRealAt (C : ℝ) (x : ℝ) : ℝ :=
  max (-C) (min x C)

/-- Helper for Remark 25.7: clipping a real value is measurable. -/
theorem measurable_clipRealAt (C : ℝ) :
    Measurable (clipRealAt C) := by
  -- Proof comment: `clipRealAt` is built from measurable `min` and `max` against constants.
  simpa [clipRealAt] using
    (measurable_const.max (measurable_id.min measurable_const))

/-- Helper for Remark 25.7: clipping to `[-C, C]` is uniformly bounded by `C`. -/
theorem abs_clipRealAt_le
    {C : ℝ} (hC_nonneg : 0 ≤ C) (x : ℝ) :
    |clipRealAt C x| ≤ C := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Proof comment: the lower clamp forces `clipRealAt C x` to stay above `-C`.
    simpa [clipRealAt] using (le_max_left (-C) (min x C))
  · -- Proof comment: the upper clamp forces `clipRealAt C x` to stay below `C`.
    refine max_le_iff.mpr ⟨?_, min_le_right _ _⟩
    linarith

/-- Helper for Remark 25.7: clipping does nothing to values already in `[-C, C]`. -/
theorem clipRealAt_eq_self_of_abs_le
    {C : ℝ} (hC_nonneg : 0 ≤ C) {x : ℝ}
    (hx : |x| ≤ C) :
    clipRealAt C x = x := by
  rcases abs_le.mp hx with ⟨hx_lower, hx_upper⟩
  -- Proof comment: once both one-sided bounds are known, both clamps are inactive.
  calc
    clipRealAt C x = max (-C) (min x C) := by
      rfl
    _ = max (-C) x := by
      rw [min_eq_left hx_upper]
    _ = x := by
      rw [max_eq_right hx_lower]

/-- Helper for Remark 25.7: clip a real-valued process pointwise to `[-C, C]`. -/
def clippedProcess (C : ℝ) (J : RealProcess) : RealProcess :=
  fun t ω ↦ clipRealAt C (J t ω)

/-- Helper for Remark 25.7: pointwise clipping preserves joint measurability. -/
theorem measurable_uncurry_clippedProcess
    {J : RealProcess} {C : ℝ}
    (hJ_meas : Measurable (Function.uncurry J)) :
    Measurable (Function.uncurry (clippedProcess C J)) := by
  -- Proof comment: postcompose the jointly measurable process with the measurable clip map.
  simpa [Function.uncurry, clippedProcess] using
    (measurable_clipRealAt C).comp hJ_meas

/-- Helper for Remark 25.7: clipped processes are pointwise bounded by their clipping level. -/
theorem abs_clippedProcess_le
    {J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C) (t : NNReal) (ω : Ω) :
    |clippedProcess C J t ω| ≤ C := by
  -- Proof comment: apply the scalar clipping bound pointwise.
  simpa [clippedProcess] using abs_clipRealAt_le hC_nonneg (J t ω)

/-- Helper for Remark 25.7: clipping preserves the deterministic-time modification on `(0,1]`
because the original process already stays in `[-C, C]` there. -/
theorem clippedProcess_unitCell_modification
    {J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] clippedProcess C J t := by
  intro t ht0 ht1
  filter_upwards [hJ_mod t ht0 ht1] with ω hω
  have hJ_bound : |J t ω| ≤ C := by
    simpa [hω] using hbound t ω ht0 ht1
  -- Proof comment: after transporting the pointwise bound from `H` to `J`, the clip is inactive.
  calc
    H t ω = J t ω := hω
    _ = clippedProcess C J t ω := by
      symm
      simpa [clippedProcess] using clipRealAt_eq_self_of_abs_le hC_nonneg hJ_bound

/-- Helper for Remark 25.7: strict sublevel sections of a modified unit-strip process are
`μ`-null measurable with respect to `ℱ 1`. -/
theorem nullMeasurableSet_lt_unitStripSection_of_modification
    {J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) (q : ℝ) :
    NullMeasurableSet {ω | J t ω < q} (μ.trim (ℱ.le 1)) := by
  -- Proof comment: the fixed-time slice is `ℱ 1`-a.e.-measurable, so every open sublevel set is
  -- null measurable for the trimmed terminal measure.
  exact
    (aemeasurable_unitStripSection_of_modification
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hH_adapted hJ_mod ht0 ht1)
      .nullMeasurableSet_preimage measurableSet_Iio

/-- Helper for Remark 25.7: singleton fibers of a modified unit-strip process are `μ`-null
measurable with respect to `ℱ 1`. -/
theorem nullMeasurableSet_eq_unitStripSection_of_modification
    {J : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    {t : NNReal} (ht0 : 0 < t) (ht1 : t ≤ 1) (a : ℝ) :
    NullMeasurableSet {ω | J t ω = a} (μ.trim (ℱ.le 1)) := by
  -- Proof comment: equality fibers are preimages of measurable singletons under the same
  -- `ℱ 1`-a.e.-measurable time slice.
  exact
    (aemeasurable_unitStripSection_of_modification
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hH_adapted hJ_mod ht0 ht1)
      .nullMeasurableSet_preimage measurableSet_singleton

/-- Helper for Remark 25.7: replacing the second coordinate of a strip rectangle by its
`μ.trim (ℱ 1)`-measurable hull does not change any deterministic-time section up to `μ`-a.e.
equality. -/
theorem section_prod_toMeasurable_ae_eq
    {s : Set (Set.Iic (1 : NNReal))} {u : Set Ω}
    (hu : NullMeasurableSet u (μ.trim (ℱ.le 1)))
    (t : NNReal) (ht1 : t ≤ 1) :
    {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ toMeasurable (μ.trim (ℱ.le 1)) u} =ᵐ[μ]
      {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ u} := by
  by_cases hs : (⟨t, ht1⟩ : Set.Iic (1 : NNReal)) ∈ s
  · have htrim :
        {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ toMeasurable (μ.trim (ℱ.le 1)) u}
            =ᵐ[μ.trim (ℱ.le 1)]
          {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ u} := by
      -- Proof comment: once the time point lies in the rectangle base, the section is exactly
      -- the measurable hull of `u`, so the claim is `hu.toMeasurable_ae_eq`.
      simpa [hs] using hu.toMeasurable_ae_eq
    -- Proof comment: pass the section equality from the trimmed terminal measure back to `μ`.
    exact ae_of_ae_trim (ℱ.le 1) htrim
  · -- Proof comment: if the time point misses the rectangle base, both sections are literally
    -- empty.
    simp [hs]

/-- Helper for Remark 25.7: a strip rectangle with a `μ.trim (ℱ 1)`-null-measurable second
coordinate already has a `𝓑([0,1]) ⊗ ℱ 1` measurable event version. -/
theorem existsMeasurableUnitStripRectangleEventVersion
    {s : Set (Set.Iic (1 : NNReal))} (hs : MeasurableSet s) {u : Set Ω}
    (hu : NullMeasurableSet u (μ.trim (ℱ.le 1))) :
    ∃ B : Set (Set.Iic (1 : NNReal) × Ω),
      MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ 1)] B ∧
      ∀ t : NNReal, ∀ ht1 : t ≤ 1,
        {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B} =ᵐ[μ]
          {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ s ×ˢ u} := by
  refine ⟨s ×ˢ toMeasurable (μ.trim (ℱ.le 1)) u, hs.prod (measurableSet_toMeasurable _ _), ?_⟩
  intro t ht1
  -- Proof comment: the measurable rectangle keeps the same deterministic-time section because the
  -- second coordinate was only replaced by its measurable hull.
  exact section_prod_toMeasurable_ae_eq (μ := μ) (ℱ := ℱ) hu t ht1

/-- Helper for Remark 25.7: an ambiently measurable strip event whose positive-time sections are
`μ.trim (ℱ 1)`-null measurable admits one `𝓑([0,1]) ⊗ ℱ 1` measurable version with the same
positive-time sections up to `μ`-a.e. equality. -/
theorem existsMeasurableUnitStripEventVersion
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
  let C :
      ∀ S : Set (Set.Iic (1 : NNReal) × Ω),
        MeasurableSet[Subtype.instMeasurableSpace.prod inferInstance] S → Prop :=
    fun S _ ↦
      ∃ B : Set (Set.Iic (1 : NNReal) × Ω),
        MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ 1)] B ∧
        ∀ t : NNReal, ∀ ht1 : t ≤ 1,
          {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B} =ᵐ[μ]
            {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ S}
  have hC :
      ∀ S : Set (Set.Iic (1 : NNReal) × Ω),
        ∀ hS_meas : MeasurableSet[Subtype.instMeasurableSpace.prod inferInstance] S, C S hS_meas := by
    refine
      MeasurableSpace.induction_on_inter
        (C := C) generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · refine ⟨∅, .empty, ?_⟩
      intro t ht1
      -- Proof comment: the empty strip event has empty deterministic-time sections.
      simp
    · intro S hS
      rcases hS with ⟨s, hs, u, hu, rfl⟩
      -- Proof comment: rectangles are handled by replacing the second coordinate with its
      -- `μ.trim (ℱ 1)`-measurable hull.
      exact existsMeasurableUnitStripRectangleEventVersion
        (μ := μ) (ℱ := ℱ) hs hu.nullMeasurableSet
    · intro S hS_meas hS_version
      rcases hS_version with ⟨B, hB_meas, hB_sec⟩
      refine ⟨Bᶜ, hB_meas.compl, ?_⟩
      intro t ht1
      -- Proof comment: sectionwise almost-everywhere equality is preserved by taking complements.
      filter_upwards [hB_sec t ht1] with ω hω
      exact not_congr hω
    · intro f hfd hfm hf
      choose B hB_meas hB_sec using hf
      refine ⟨⋃ n, B n, MeasurableSet.iUnion hB_meas, ?_⟩
      intro t ht1
      have hAll :
          ∀ᵐ ω ∂μ, ∀ n : ℕ,
            (((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B n ↔
              ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ f n) := by
        rw [ae_all_iff]
        intro n
        exact hB_sec n t ht1
      -- Proof comment: synchronize the countably many section equalities and then rewrite the
      -- section of the union pointwise.
      filter_upwards [hAll] with ω hω
      change
        ((((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ ⋃ n, B n) ↔
          (((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ ⋃ n, f n))
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, (hω n).1 hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, (hω n).2 hn⟩
  rcases hC A hA_meas with ⟨B, hB_meas, hB_sec⟩
  refine ⟨B, hB_meas, ?_⟩
  intro t ht0 ht1
  -- Proof comment: the induction already proves sectionwise equality for every `t ≤ 1`, so the
  -- positive-time consumer statement is immediate.
  exact hB_sec t ht1

/-- Helper for Remark 25.7: once positive-time strip events admit measurable versions, the same
holds for finite-range strip maps by regularizing each value fiber and summing the resulting
indicators. -/
theorem existsMeasurableFiniteRangeUnitStripVersion_of_eventBridge
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
  classical
  let R : Finset ℝ := hS_finite.toFinset
  let A : ℝ → Set (Set.Iic (1 : NNReal) × Ω) := fun a ↦ {p | S p = a}
  have hA_meas :
      ∀ a : ℝ, MeasurableSet[Subtype.instMeasurableSpace.prod inferInstance] (A a) := by
    intro a
    -- Proof comment: each value fiber is an ambiently measurable singleton preimage.
    simpa [A] using hS_meas measurableSet_singleton
  have hA_section :
      ∀ a : ℝ, ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        NullMeasurableSet {ω | ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ A a} (μ.trim (ℱ.le 1)) := by
    intro a t ht0 ht1
    -- Proof comment: every deterministic-time value fiber is null measurable because the section
    -- itself is `ℱ 1`-a.e.-measurable.
    simpa [A] using
      (hS_section_aemeas t ht0 ht1).nullMeasurableSet_preimage measurableSet_singleton
  choose B hB_meas hB_sec using fun a : ℝ ↦
    hEvent (A := A a) (hA_meas a) (hA_section a)
  let G1 : Set.Iic (1 : NNReal) × Ω → ℝ := fun p ↦ R.sum fun a ↦ (B a).indicator (fun _ ↦ a) p
  have hG1_meas :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 := by
    -- Proof comment: the finite sum is measurable because each indicator uses an `ℱ 1`-measurable
    -- strip event produced by the event bridge.
    refine Finset.measurable_fun_sum R ?_
    intro a ha
    exact measurable_const.indicator (hB_meas a)
  refine ⟨G1, hG1_meas, ?_⟩
  intro t ht0 ht1
  have hAll :
      ∀ᵐ ω ∂μ, ∀ a : R,
        (((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) ∈ B a.1 ↔
          S ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω) = a.1) := by
    -- Proof comment: the finite range lets us synchronize all fiberwise a.e. equalities on one
    -- full-measure set.
    refine ae_all_iff.2 ?_
    intro a
    simpa [A] using hB_sec a.1 t ht0 ht1
  filter_upwards [hAll] with ω hω
  let p : Set.Iic (1 : NNReal) × Ω := ((⟨t, ht1⟩ : Set.Iic (1 : NNReal)), ω)
  have hp_mem : S p ∈ R := by
    simpa [R, p] using hS_finite.mem_toFinset.mpr ⟨p, rfl⟩
  have hpB : p ∈ B (S p) := by
    exact (hω ⟨S p, hp_mem⟩).2 rfl
  -- Proof comment: on the synchronized full-measure set, the regularized fibers reproduce the
  -- original finite partition, so the indicator sum collapses to the unique active value.
  calc
    G1 (⟨t, ht1⟩, ω) = R.sum (fun a ↦ (B a).indicator (fun _ ↦ a) p) := by
      rfl
    _ = S p := by
      refine Finset.sum_eq_single_of_mem (S p) hp_mem ?_
      intro b hb hb_ne
      have hp_not_mem : p ∉ B b := by
        intro hp_mem_b
        have : S p = b := (hω ⟨b, hb⟩).1 hp_mem_b
        exact hb_ne this.symm
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hpB, hp_not_mem]
    _ = S (⟨t, ht1⟩, ω) := by
      rfl

/-- Helper for Remark 25.7: a bounded ambiently measurable strip map whose deterministic-time
sections are `ℱ 1`-a.e.-measurable admits one `𝓑([0,1]) ⊗ ℱ 1` measurable version. -/
theorem existsMeasurableUnitStripVersion_of_boundedStripAEMeasurableSections
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
  classical
  let φ : ℕ → ℝ →ₛ ℝ := fun n ↦
    SimpleFunc.approxOn (fun x : ℝ ↦ x) measurable_id (Set.range J ∪ {0}) 0 (by simp) n
  let S : ℕ → Set.Iic (1 : NNReal) × Ω →ₛ ℝ := fun n ↦ (φ n).comp J hJ_meas
  have hφ_tendsto :
      ∀ p : Set.Iic (1 : NNReal) × Ω,
        Tendsto (fun n ↦ φ n (J p)) atTop (𝓝 (J p)) := by
    intro p
    -- Proof comment: approximate the scalar identity on `Set.range J ∪ {0}` and evaluate at the
    -- actual value `J p`.
    exact SimpleFunc.tendsto_approxOn measurable_id (by simp)
      (subset_closure <| Or.inl ⟨p, rfl⟩)
  have hS_section_aemeas :
      ∀ n : ℕ, ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        AEMeasurable[ℱ 1] (fun ω ↦ S n (⟨t, ht1⟩, ω)) μ := by
    intro n t ht0 ht1
    -- Proof comment: composing each section of `J` with the measurable scalar simple function
    -- preserves `ℱ 1`-a.e. measurability.
    simpa [S] using ((φ n).measurable.comp_aemeasurable (hJ_section_aemeas t ht0 ht1))
  choose G hG_meas hG_sec using
    fun n : ℕ ↦
      existsMeasurableFiniteRangeUnitStripVersion_of_eventBridge
        (μ := μ) (ℱ := ℱ)
        (hEvent := fun {A} hA_meas hA_section ↦
          existsMeasurableUnitStripEventVersion (μ := μ) (ℱ := ℱ) hA_meas hA_section)
        (S := S n) (hS_finite := (S n).finite_range) (hS_meas := (S n).measurable)
        (hS_section_aemeas := hS_section_aemeas n)
  let G1 : Set.Iic (1 : NNReal) × Ω → ℝ := fun p ↦ limsup (fun n ↦ G n p) atTop
  refine ⟨G1, ?_, ?_⟩
  · -- Proof comment: the pointwise `limsup` of countably many strip-measurable functions is again
    -- strip measurable.
    exact Measurable.limsup hG_meas
  · intro t ht0 ht1
    have hAll :
        ∀ᵐ ω ∂μ, ∀ n : ℕ, G n (⟨t, ht1⟩, ω) = φ n (J (⟨t, ht1⟩, ω)) := by
      rw [ae_all_iff]
      intro n
      -- Proof comment: synchronize the finite-range measurable versions with the scalar simple
      -- approximants on one deterministic-time section.
      simpa [S] using (hG_sec n t ht0 ht1).symm
    filter_upwards [hAll] with ω hω
    have hTendsto :
        Tendsto (fun n ↦ G n (⟨t, ht1⟩, ω)) atTop (𝓝 (J (⟨t, ht1⟩, ω))) := by
      -- Proof comment: on the synchronized full-measure set, the measurable versions coincide
      -- termwise with the scalar approximants of `J`.
      exact (hφ_tendsto (⟨t, ht1⟩, ω)).congr'
        (Filter.Eventually.of_forall fun n ↦ (hω n).symm)
    -- Proof comment: once the sequence converges pointwise on this full-measure set, its `limsup`
    -- is exactly the target section value.
    simpa [G1, hTendsto.limsup_eq]

/-- Helper for Remark 25.7: the bounded auxiliary jointly measurable pair on `(0, 1]` should be
first regularized into one measurable witness on the unit strip `[0,1] × Ω`. -/
theorem existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableDirect
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
  let Jc : RealProcess := clippedProcess C J
  have hJc_meas :
      Measurable[Subtype.instMeasurableSpace.prod inferInstance]
        (fun p : Set.Iic 1 × Ω ↦ Jc p.1 p.2) := by
    -- Proof comment: first clip the auxiliary process so the strip witness becomes pointwise
    -- bounded before any approximation step.
    simpa [Jc] using
      measurableOnStrip_of_productMeasurable (H := Jc)
        (measurable_uncurry_clippedProcess (J := J) (C := C) hJ_meas) 1
  have hJc_mod :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] Jc t := by
    -- Proof comment: on `(0,1]`, the bound on `H` makes the clipping inactive along the
    -- deterministic-time modification `H t = J t` almost everywhere.
    exact clippedProcess_unitCell_modification
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hC_nonneg hJ_mod hbound
  have hJc_section_aemeas :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, AEMeasurable[ℱ 1] (Jc t) μ := by
    intro t ht0 ht1
    -- Proof comment: each deterministic-time section is almost everywhere equal to the adapted
    -- slice `H t`, hence inherits `ℱ 1`-a.e.-measurability.
    exact aemeasurable_unitStripSection_of_modification
      (μ := μ) (ℱ := ℱ) (H := H) (J := Jc) hH_adapted hJc_mod ht0 ht1
  have hJc_bound :
      ∀ t : NNReal, ∀ ω : Ω, |Jc t ω| ≤ C := by
    intro t ω
    -- Proof comment: the clipped process is bounded everywhere, so later simple-function
    -- approximations can work with a genuine pointwise range bound.
    exact abs_clippedProcess_le (J := J) (C := C) hC_nonneg t ω
  rcases existsMeasurableUnitStripVersion_of_boundedStripAEMeasurableSections
      (μ := μ) (ℱ := ℱ) (J := fun p ↦ Jc p.1 p.2) (C := C)
      hJc_meas hJc_section_aemeas (fun p ↦ hJc_bound p.1 p.2) with
    ⟨G1, hG1_meas, hG1_mod⟩
  refine ⟨G1, hG1_meas, ?_⟩
  intro t ht0 ht1
  -- Proof comment: first compare `H t` with the clipped process `Jc t`, then transport the
  -- sectionwise regularization of the clipped strip map.
  exact (hJc_mod t ht0 ht1).trans (hG1_mod t ht0 ht1)

/-- Helper for Remark 25.7: the bounded auxiliary jointly measurable pair on `(0, 1]` is
regularized by first building one measurable unit-strip witness and then globalizing it. -/
theorem existsProgMeasurableVersionOnUnitCell_of_boundedJointlyMeasurableAux
    {J : RealProcess} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hJ_meas : Measurable (Function.uncurry J))
    (hJ_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1, H t =ᵐ[μ] J t)
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  rcases existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableDirect
      (μ := μ) (ℱ := ℱ) (H := H) (J := J) hC_nonneg hH_adapted hJ_meas hJ_mod hbound with
    ⟨G1, hG1_meas, hG1_mod⟩
  -- Proof comment: once the measurable strip witness exists, the earlier unit-cell globalization
  -- theorem upgrades it to a progressively measurable witness without changing the fixed-time
  -- modification data.
  exact existsProgMeasurableVersionOnUnitCellOfMeasurableUnitStripVersionCore
    (μ := μ) (ℱ := ℱ) (H := H) hG1_meas hG1_mod

/-- Helper for Remark 25.7: the bounded owner theorem may first regularize through an auxiliary
jointly measurable process `J` before returning a measurable witness on the unit strip. -/
theorem existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableAux
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
  -- Proof comment: this is now just the canonical direct unit-strip witness theorem, without
  -- detouring through the progressively measurable wrapper.
  exact existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableDirect
    (μ := μ) (ℱ := ℱ) (H := H) (J := J) hC_nonneg hH_adapted hJ_meas hJ_mod hbound

/-- Helper for Remark 25.7: the bounded unit-cell route only needs one measurable witness on the
unit strip `[0, 1] × Ω` with deterministic-time almost-everywhere agreement. -/
theorem existsMeasurableUnitStripVersion_of_boundedJointlyMeasurable
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G1 : Set.Iic 1 × Ω → ℝ,
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1 ∧
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω) := by
  -- Proof comment: instantiate the generalized bounded owner theorem with the original jointly
  -- measurable process `H`, so the only remaining frontier is the strip regularization itself.
  simpa using
    existsMeasurableUnitStripVersion_of_boundedJointlyMeasurableAux
      (μ := μ) (ℱ := ℱ) (H := H) (J := H) hC_nonneg hH_adapted hH_prod
      (fun t ht0 ht1 ↦ Filter.EventuallyEq.rfl) hbound

/-- Helper for Remark 25.7: extend a measurable unit-strip witness to a globally jointly
measurable process without changing its deterministic-time modification property on `(0, 1]`. -/
theorem unitStripWitnessToProcess
    {G1 : Set.Iic 1 × Ω → ℝ}
    (hG1 :
      Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1)
    (hG1_mod :
      ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
        H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω)) :
    ∃ J : RealProcess, Measurable (Function.uncurry J) ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] J t := by
  let J : RealProcess := fun t ω ↦ if ht1 : t ≤ 1 then G1 (⟨t, ht1⟩, ω) else 0
  refine ⟨J, ?_, ?_⟩
  · have hG1_ambient : Measurable G1 := by
      -- Proof comment: forget the terminal filtration on the second coordinate and view the unit
      -- strip witness as measurable for the ambient product measurable space.
      change Measurable[Subtype.instMeasurableSpace.prod (inferInstance : MeasurableSpace Ω)] G1
      exact hG1.mono (by
        refine sup_le_sup le_rfl ?_
        exact MeasurableSpace.comap_mono (ℱ.le 1)) le_rfl
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
      -- Proof comment: clamp the time coordinate to `[0, 1]` before evaluating the strip witness.
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
      · simp [Function.uncurry, J, base, hp, min_eq_left hp]
      · simp [Function.uncurry, J, base, hp]
    rw [hrewrite]
    exact hind.measurable
  · intro t ht0 ht1
    -- Proof comment: on `(0, 1]`, the global extension agrees with the strip witness by
    -- construction, so the deterministic-time modification statement transfers directly.
    simpa [J, ht1] using hG1_mod t ht0 ht1

/-- Helper for Remark 25.7: restricting a horizon-`1` strip witness to a smaller strip preserves
measurability. -/
theorem measurableOnSmallStrip_of_unitStripWitness
    {G1 : Set.Iic 1 × Ω → ℝ}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1)
    {T : NNReal} (hTle1 : T ≤ 1) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω ↦ G1 (⟨(p.1 : NNReal), hTle1.trans p.1.2⟩, p.2)) := by
  -- Proof comment: reuse the earlier core strip-restriction interface.
  exact measurableOnSmallStripOfUnitStripWitnessCore (ℱ := ℱ) hG1 hTle1

/-- Helper for Remark 25.7: a measurable witness on the unit strip globalizes to a progressively
measurable process by patching time zero and extending by zero outside `(0,1]`. -/
theorem existsProgMeasurableVersionOnUnitCell_of_measurableUnitStripVersion
    {G1 : Set.Iic 1 × Ω → ℝ}
    (hG1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ 1)] G1)
    (hG1_mod : ∀ t : NNReal, 0 < t → ∀ ht1 : t ≤ 1,
      H t =ᵐ[μ] fun ω ↦ G1 (⟨t, ht1⟩, ω)) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  -- Proof comment: reuse the earlier core unit-cell globalization interface.
  exact existsProgMeasurableVersionOnUnitCellOfMeasurableUnitStripVersionCore
    (μ := μ) (ℱ := ℱ) hG1 hG1_mod

/-- Helper for Remark 25.7: the only analytic frontier is a single progressively measurable
unit-cell witness with deterministic-time almost-everywhere agreement. -/
theorem existsProgMeasurableVersionOnUnitCell_of_boundedCore
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  -- Route correction: the bounded-core consumer should call the direct progressively measurable
  -- owner theorem, and the strip-valued theorem now sits downstream as an adapter only.
  exact existsProgMeasurableVersionOnUnitCell_of_boundedJointlyMeasurableAux
    (μ := μ) (ℱ := ℱ) (H := H) (J := H) hC_nonneg hH_adapted hH_prod
    (fun t ht0 ht1 ↦ Filter.EventuallyEq.rfl) hbound

/-- Helper for Remark 25.7: once the owner theorem returns one progressively measurable unit-cell
witness, every small strip `(0, T]` is measurable by direct projection. -/
theorem existsStripwiseMeasurableVersionOnUnitCellLocal_of_bounded
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess,
      (∀ T : NNReal, 0 < T → T ≤ 1 →
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ G p.1 p.2)) ∧
      (∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t) := by
  rcases existsProgMeasurableVersionOnUnitCell_of_boundedCore
      (μ := μ) (ℱ := ℱ) (H := H) hC_nonneg hH_adapted hH_prod hbound with
    ⟨G, hG_prog, hmod⟩
  refine ⟨G, ?_, hmod⟩
  intro T hTpos hTle1
  -- Proof comment: progressive measurability already contains the strip measurability required by
  -- the local bounded interface.
  simpa using measurableOnStrip_of_progMeasurableUnitCell (ℱ := ℱ) hG_prog T

/-- Helper for Remark 25.7: once the owner theorem returns one progressively measurable unit-cell
witness, the global stripwise interface is the same witness read on every horizon. -/
theorem existsStripwiseMeasurableVersionOnUnitCell_of_bounded
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess,
      (∀ T : NNReal,
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ G p.1 p.2)) ∧
      (∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t) := by
  rcases existsProgMeasurableVersionOnUnitCell_of_boundedCore
      (μ := μ) (ℱ := ℱ) (H := H) hC_nonneg hH_adapted hH_prod hbound with
    ⟨G, hG_prog, hmod⟩
  refine ⟨G, ?_, hmod⟩
  intro T
  -- Proof comment: the global stripwise theorem is now just the owner witness viewed on an
  -- arbitrary horizon, so no zero-patching or outer extension is needed.
  simpa using measurableOnStrip_of_progMeasurableUnitCell (ℱ := ℱ) hG_prog T

/-- Helper for Remark 25.7: one direct progressively measurable unit-cell witness yields the
coherent family interface by keeping the same witness at every horizon. -/
theorem coherentBoundaryVersionsOfProgUnitCellWitness
    {G : RealProcess}
    (hG_prog : ProgMeasurable ℱ G)
    (hG_mod : ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t) :
    ∃ K : NNReal → RealProcess,
      (∀ T : NNReal, 0 < T → T ≤ 1 →
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ K T p.1 p.2)) ∧
      (∀ {S T : NNReal}, 0 < S → S ≤ T → T ≤ 1 →
        ∀ t : NNReal, t ≤ S → K T t = K S t) ∧
      (∀ T : NNReal, 0 < T → T ≤ 1 → H T =ᵐ[μ] K T T) := by
  refine ⟨fun _ ↦ G, ?_, ?_, ?_⟩
  · intro T hTpos hTle1
    -- Proof comment: every horizon sees the same progressively measurable strip witness.
    simpa using measurableOnStrip_of_progMeasurableUnitCell (ℱ := ℱ) hG_prog T
  · intro S T hSpos hST hTle1 t htS
    -- Proof comment: a constant horizon family is automatically prefix coherent.
    rfl
  · intro T hTpos hTle1
    -- Proof comment: the top-slice clause is exactly the deterministic-time modification
    -- property of the direct unit-cell witness.
    simpa using hG_mod T hTpos hTle1

/-- Helper for Remark 25.7: the bounded unit-cell frontier is best packaged as a coherent family
of finite-horizon strip representatives with exact top-slice agreement. -/
theorem existsCoherentUnitCellBoundaryVersionsOfBounded
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ K : NNReal → RealProcess,
      (∀ T : NNReal, 0 < T → T ≤ 1 →
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ K T p.1 p.2)) ∧
      (∀ {S T : NNReal}, 0 < S → S ≤ T → T ≤ 1 →
        ∀ t : NNReal, t ≤ S → K T t = K S t) ∧
      (∀ T : NNReal, 0 < T → T ≤ 1 → H T =ᵐ[μ] K T T) := by
  -- Route correction: the coherent family is now a corollary of one direct bounded unit-cell
  -- witness, so exact prefix coherence is handled by a constant family instead of analytic gluing.
  rcases existsProgMeasurableVersionOnUnitCell_of_boundedCore
      (μ := μ) (ℱ := ℱ) (H := H) hC_nonneg hH_adapted hH_prod hbound with
    ⟨G, hG_prog, hG_mod⟩
  -- Proof comment: reuse the same witness at every horizon; the family obligations are then
  -- purely formal.
  exact coherentBoundaryVersionsOfProgUnitCellWitness
    (μ := μ) (ℱ := ℱ) (H := H) hG_prog hG_mod

/-- Helper for Remark 25.7: the coherent-family theorem exports deterministic-time equality only
at the horizon slice. -/
theorem unitCellBoundaryVersionTopAeEq
    {K : NNReal → RealProcess}
    (htop : ∀ T : NNReal, 0 < T → T ≤ 1 → H T =ᵐ[μ] K T T)
    {T : NNReal} (hTpos : 0 < T) (hTle1 : T ≤ 1) :
    H T =ᵐ[μ] K T T :=
  htop T hTpos hTle1

/-- Helper for Remark 25.7: the coherent-family theorem exports exact prefix agreement between
nested horizons. -/
theorem unitCellBoundaryVersionPrefixCoherent
    {K : NNReal → RealProcess}
    (hcoh : ∀ {S T : NNReal}, 0 < S → S ≤ T → T ≤ 1 →
      ∀ t : NNReal, t ≤ S → K T t = K S t)
    {S T t : NNReal} (hSpos : 0 < S) (hST : S ≤ T) (hTle1 : T ≤ 1) (htS : t ≤ S) :
    K T t = K S t :=
  hcoh hSpos hST hTle1 t htS

/-- Helper for Remark 25.7: a coherent finite-horizon family already yields the bounded unit-cell
progressive version. -/
theorem progMeasurableVersionOnUnitCell_of_coherentBoundaryVersions
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
  refine ⟨G, ?_, ?_⟩
  · -- Proof comment: use the horizon-`1` representative on `(0,1]`, patch time `0` by zero, and
    -- keep the process zero afterwards; coherence transfers the small-strip measurability.
    apply progMeasurable_of_measurableOnStrips (ℱ := ℱ)
    intro T
    by_cases hT0 : T = 0
    · -- Proof comment: the degenerate strip `[0,0]` only sees the zero value.
      simp [G, hT0]
    · by_cases hTle1 : T ≤ 1
      · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
        have hKT :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦ K T p.1 p.2) :=
          hstrip T hTpos hTle1
        have hzero :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) :=
          measurable_const
        have hzeroSet :
            MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
              {p : Set.Iic T × Ω | (p.1 : NNReal) = 0} := by
          have htime : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
            measurable_fst.subtype_val
          simpa using htime measurableSet_singleton
        have hpiece :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) = 0}
                (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))
                (fun p : Set.Iic T × Ω ↦ K T p.1 p.2)) := by
          simpa using hzero.piecewise hzeroSet hKT
        have hrewrite :
            (fun p : Set.Iic T × Ω ↦ G p.1 p.2) =
              Set.piecewise {p : Set.Iic T × Ω | (p.1 : NNReal) = 0}
                (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))
                (fun p : Set.Iic T × Ω ↦ K T p.1 p.2) := by
          funext p
          by_cases hp0 : (p.1 : NNReal) = 0
          · simp [G, hp0]
          · have hKeq :
              K 1 (p.1 : NNReal) p.2 = K T (p.1 : NNReal) p.2 := by
              have hbase :
                  K 1 (p.1 : NNReal) = K T (p.1 : NNReal) :=
                unitCellBoundaryVersionPrefixCoherent (K := K) hcoh
                  (S := T) (T := 1) hTpos hTle1 le_rfl (p.1.2)
              exact congrArg (fun f : Ω → ℝ ↦ f p.2) hbase
            have hp1 : (p.1 : NNReal) ≤ 1 := p.1.2.trans hTle1
            simp [G, hp0, hp1, hKeq]
        simpa [hrewrite] using hpiece
      · have h1ltT : (1 : NNReal) < T := lt_of_not_ge hTle1
        have hstrip1 :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic 1 × Ω ↦ K 1 p.1 p.2) := by
          exact (hstrip 1 zero_lt_one le_rfl).mono <| by
            exact sup_le_sup le_rfl (ℱ.mono (le_of_lt h1ltT))
        let truncToOne : Set.Iic T × Ω → Set.Iic 1 × Ω :=
          fun p ↦ (⟨min (p.1 : NNReal) 1, min_le_right _ _⟩, p.2)
        have htruncToOne : Measurable truncToOne := by
          have hfstBase : Measurable fun p : Set.Iic T × Ω ↦ min (p.1 : NNReal) 1 := by
            exact measurable_fst.subtype_val.min measurable_const
          have hfst :
              Measurable fun p : Set.Iic T × Ω ↦
                (⟨min (p.1 : NNReal) 1, min_le_right _ _⟩ : Set.Iic 1) :=
            hfstBase.subtype_mk
          exact hfst.prodMk measurable_snd
        have hbase :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (fun p : Set.Iic T × Ω ↦ K 1 (min (p.1 : NNReal) 1) p.2) := by
          simpa [truncToOne] using hstrip1.comp_measurable htruncToOne
        have honeSet :
            MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
              {p : Set.Iic T × Ω | 0 < (p.1 : NNReal) ∧ (p.1 : NNReal) ≤ 1} := by
          have htime : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
            measurable_fst.subtype_val
          exact (htime measurableSet_Ioi).inter (htime measurableSet_Iic)
        have hpiece :
            Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
              (Set.piecewise {p : Set.Iic T × Ω | 0 < (p.1 : NNReal) ∧ (p.1 : NNReal) ≤ 1}
                (fun p : Set.Iic T × Ω ↦ K 1 (min (p.1 : NNReal) 1) p.2)
                (fun _ : Set.Iic T × Ω ↦ (0 : ℝ))) := by
          simpa using hbase.piecewise honeSet measurable_const
        have hrewrite :
            (fun p : Set.Iic T × Ω ↦ G p.1 p.2) =
              Set.piecewise {p : Set.Iic T × Ω | 0 < (p.1 : NNReal) ∧ (p.1 : NNReal) ≤ 1}
                (fun p : Set.Iic T × Ω ↦ K 1 (min (p.1 : NNReal) 1) p.2)
                (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)) := by
          funext p
          by_cases hpos : 0 < (p.1 : NNReal)
          · by_cases hp1 : (p.1 : NNReal) ≤ 1
            · simp [G, hpos.ne', hp1, hpos, hp1, min_eq_left hp1]
            · simp [G, hpos.ne', hp1, hpos, hp1]
          · have hp0 : (p.1 : NNReal) = 0 := le_antisymm (le_of_not_gt hpos) bot_le
            simp [G, hp0, hpos]
        simpa [hrewrite] using hpiece
  · intro t ht0 ht1
    -- Proof comment: for `0 < t ≤ 1`, the boundary value of the horizon-`t` representative agrees
    -- with the horizon-`1` representative by coherence, so the timewise modification follows.
    have htop' : H t =ᵐ[μ] K t t :=
      unitCellBoundaryVersionTopAeEq (K := K) htop ht0 ht1
    have hcoh' : K 1 t = K t t :=
      unitCellBoundaryVersionPrefixCoherent (K := K) hcoh
        (S := t) (T := 1) ht0 ht1 le_rfl le_rfl
    refine htop'.trans ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp [G, ht0.ne', ht1, hcoh'.symm]

/-- Helper for Remark 25.7: a bounded adapted jointly measurable process on `(0, 1]` admits a
progressively measurable version with deterministic-time almost-everywhere agreement. -/
theorem existsProgMeasurableVersionOnUnitCell_of_bounded
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H))
    (hbound : ∀ t : NNReal, ∀ ω : Ω, 0 < t → t ≤ 1 → |H t ω| ≤ C) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  -- Proof comment: the bounded wrapper now forwards directly to the true analytic frontier.
  exact existsProgMeasurableVersionOnUnitCell_of_boundedCore
    (μ := μ) (ℱ := ℱ) (H := H) hC_nonneg hH_adapted hH_prod hbound

/-- Helper for Remark 25.7: a countable `limsup` of progressively measurable real-valued
processes is progressively measurable. -/
theorem progMeasurable_limsup
    {G : ℕ → RealProcess}
    (hG_prog : ∀ n : ℕ, ProgMeasurable ℱ (G n)) :
    ProgMeasurable ℱ (fun t ω ↦ limsup (fun n ↦ G n t ω) atTop) := by
  -- Proof comment: on each strip `[0, T] × Ω`, progressive measurability gives ordinary
  -- measurability of every `G n`, and measurability is closed under countable `limsup`.
  apply progMeasurable_of_measurableOnStrips (ℱ := ℱ)
  intro T
  exact Measurable.limsup (fun n ↦ (hG_prog n T).measurable)

/-- Helper for Remark 25.7: if every truncation of `H t` agrees almost everywhere with a witness,
then the `limsup` of those witnesses recovers `H t` almost everywhere. -/
theorem fixedTimeAeEq_limsup_of_truncationWitnesses
    {G : ℕ → RealProcess}
    (t : NNReal)
    (hG : ∀ n : ℕ, truncProcess n H t =ᵐ[μ] G n t) :
    H t =ᵐ[μ] fun ω ↦ limsup (fun n ↦ G n t ω) atTop := by
  have hAll :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, truncProcess n H t ω = G n t ω := by
    rw [ae_all_iff]
    exact hG
  filter_upwards [hAll] with ω hω
  have hEventuallyEq :
      (fun n : ℕ => G n t ω) =ᶠ[atTop] fun _ : ℕ => H t ω := by
    rcases exists_nat_gt (|H t ω|) with ⟨N, hN⟩
    filter_upwards [Ioi_mem_atTop N] with n hn
    have hbound : |H t ω| ≤ (n : ℝ) := by
      exact le_trans (le_of_lt hN) (by exact_mod_cast le_of_lt hn)
    calc
      G n t ω = truncProcess n H t ω := (hω n).symm
      _ = H t ω := truncProcess_eq_self_of_abs_le (H := H) hbound
  have hTendsto : Tendsto (fun n : ℕ => G n t ω) atTop (𝓝 (H t ω)) := by
    exact tendsto_const_nhds.congr' hEventuallyEq.symm
  -- Proof comment: once the witness sequence is eventually constant at `H t ω`, its `limsup`
  -- is exactly `H t ω`.
  simpa using hTendsto.limsup_eq.symm

/-- Helper for Remark 25.7: the direct unit-cell regularization theorem is the only remaining
analytic frontier. -/
theorem existsProgMeasurableVersionOnUnitCell
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, 0 < t → t ≤ 1 → H t =ᵐ[μ] G t := by
  have hTrunc :
      ∀ n : ℕ, ∃ G : RealProcess, ProgMeasurable ℱ G ∧
        ∀ t : NNReal, 0 < t → t ≤ 1 → truncProcess n H t =ᵐ[μ] G t := by
    intro n
    -- Proof comment: each truncation is uniformly bounded by `n`, so the bounded-core theorem
    -- applies directly to the truncated process on the unit cell.
    refine existsProgMeasurableVersionOnUnitCell_of_bounded
      (μ := μ) (ℱ := ℱ) (H := truncProcess n H) (C := n) ?_ ?_ ?_ ?_
    · exact_mod_cast Nat.zero_le n
    · exact adapted_truncProcess (ℱ := ℱ) (H := H) n hH_adapted
    · exact measurable_uncurry_truncProcess (H := H) n hH_prod
    · intro t ω ht0 ht1
      simpa using abs_truncProcess_le (H := H) n t ω
  choose G hG_prog hG_mod using hTrunc
  refine ⟨fun t ω ↦ limsup (fun n ↦ G n t ω) atTop, ?_, ?_⟩
  · -- Proof comment: package the truncation witnesses into one progressively measurable process by
    -- taking the stripwise measurable `limsup`.
    exact progMeasurable_limsup (ℱ := ℱ) hG_prog
  · intro t ht0 ht1
    -- Proof comment: for fixed `t`, the truncations stabilize pointwise in `n`, so the `limsup`
    -- of the bounded witnesses recovers `H t` almost everywhere.
    exact fixedTimeAeEq_limsup_of_truncationWitnesses (μ := μ) (H := H) t
      (fun n ↦ hG_mod n t ht0 ht1)

/-- Helper for Remark 25.7: shifting a progressively measurable process back by a deterministic
time stays progressively measurable after zero-padding the earlier times. -/
theorem progMeasurable_shiftBack
    {c : NNReal} {Gshift : RealProcess}
    (hGshift : ProgMeasurable (translatedFiltration c ℱ) Gshift) :
    ProgMeasurable ℱ (fun t ω ↦ if c ≤ t then Gshift (t - c) ω else 0) := by
  intro T
  by_cases hTc : c ≤ T
  · let shiftMap : Set.Iic T × Ω → Set.Iic (T - c) × Ω :=
      fun p ↦ (⟨(p.1 : NNReal) - c, tsub_le_tsub_right p.1.2⟩, p.2)
    have hshiftMap : Measurable shiftMap := by
      -- Proof comment: on the strip `[0, T]`, subtracting the deterministic offset `c` is a
      -- measurable coordinate change into the shorter strip `[0, T - c]`.
      have hfstBase : Measurable fun p : Set.Iic T × Ω ↦ ((p.1 : NNReal) - c) := by
        exact measurable_fst.subtype_val.sub_const c
      have hfst :
          Measurable fun p : Set.Iic T × Ω ↦
            (⟨(p.1 : NNReal) - c, tsub_le_tsub_right p.1.2⟩ : Set.Iic (T - c)) :=
        hfstBase.subtype_mk
      exact hfst.prodMk measurable_snd
    have hbase :
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ Gshift ((p.1 : NNReal) - c) p.2) := by
      -- Proof comment: when `c ≤ T`, the shifted filtration at horizon `T - c` is exactly `ℱ T`.
      simpa [translatedFiltration, add_tsub_cancel_of_le hTc] using
        (hGshift (T - c)).measurable.comp_measurable hshiftMap
    have hcut :
        MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
          {p : Set.Iic T × Ω | c ≤ (p.1 : NNReal)} := by
      -- Proof comment: the cutoff region depends only on the time coordinate.
      have : Measurable fun p : Set.Iic T × Ω ↦ (p.1 : NNReal) :=
        measurable_fst.subtype_val
      exact this (measurableSet_Ici c)
    -- Proof comment: below time `c` the pulled-back process is zero, and above `c` it is exactly
    -- the translated witness evaluated at `t - c`.
    simpa [Set.piecewise] using
      (hbase.stronglyMeasurable.piecewise hcut stronglyMeasurable_zero)
  · have hbelow : ∀ p : Set.Iic T × Ω, ¬ c ≤ (p.1 : NNReal) := by
      intro p hp
      exact hTc (hp.trans p.1.2)
    -- Proof comment: if `T < c`, the whole strip lies before the shift point, so the pullback is
    -- identically zero there.
    simpa [hbelow] using
      (stronglyMeasurable_zero :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun _ : Set.Iic T × Ω ↦ (0 : ℝ)))

/-- Helper for Remark 25.7: a progressively measurable unit-cell witness for the translated process
pulls back to a witness on the natural cell `((n - 1), n]`. -/
theorem pullbackUnitCellWitnessToNatCell
    {n : ℕ} (hn : 0 < n)
    {Gshift : RealProcess}
    (hGshift_prog :
      ProgMeasurable (translatedFiltration ((n - 1 : ℕ) : NNReal) ℱ) Gshift)
    (hGshift_mod :
      ∀ t : NNReal, 0 < t → t ≤ 1 →
        translatedProcess ((n - 1 : ℕ) : NNReal) H t =ᵐ[μ] Gshift t) :
    ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  let c : NNReal := (k : NNReal)
  let G : RealProcess := fun t ω ↦ if c ≤ t then Gshift (t - c) ω else 0
  refine ⟨G, ?_, ?_⟩
  · -- Proof comment: pull the translated progressively measurable witness back by the
    -- deterministic map `t ↦ t - c`, padding the earlier times with zero.
    simpa [c, G] using
      progMeasurable_shiftBack (μ := μ) (ℱ := ℱ)
        (c := c) (Gshift := Gshift) hGshift_prog
  · intro t htleft htright
    have ht0 : 0 < t - c := tsub_pos_of_lt htleft
    have ht1 : t - c ≤ 1 := by
      rw [tsub_le_iff_right]
      simpa [c, add_comm, add_left_comm, add_assoc] using htright
    -- Proof comment: on the target cell, the backward shift lands inside `(0, 1]`, so the
    -- translated unit-cell modification theorem applies directly.
    simpa [translatedProcess, G, c, if_pos htleft.le, add_tsub_cancel_of_le htleft.le] using
      hGshift_mod (t - c) ht0 ht1

/-- Helper for Remark 25.7: a direct unit-cell regularization theorem on `(0,1]` transports
to witnesses on every positive natural cell. -/
theorem existsProgMeasurableNatCellWitnesses
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∀ n : ℕ, 0 < n → ∃ G : RealProcess, ProgMeasurable ℱ G ∧
      ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
  intro n hn
  let c : NNReal := ((n - 1 : ℕ) : NNReal)
  let ℱshift : TimeFiltration := translatedFiltration c ℱ
  let Hshift : RealProcess := translatedProcess c H
  have hHshift_adapted : Adapted ℱshift Hshift := by
    -- Proof comment: deterministic translation preserves adaptedness after shifting the
    -- filtration by the same amount.
    simpa [ℱshift, Hshift] using adapted_translatedProcess (ℱ := ℱ) (H := H) hH_adapted c
  have hHshift_prod : Measurable (Function.uncurry Hshift) := by
    -- Proof comment: joint measurability is preserved by the same time translation.
    simpa [Hshift] using measurable_uncurry_translatedProcess (H := H) hH_prod c
  rcases existsProgMeasurableVersionOnUnitCell
      (μ := μ) (ℱ := ℱshift) (H := Hshift) hHshift_adapted hHshift_prod with
    ⟨Gshift, hGshift_prog, hGshift_mod⟩
  -- Proof comment: once the translated process has a progressively measurable witness on `(0, 1]`,
  -- pull it back through the deterministic translation to obtain the witness on `((n - 1), n]`.
  exact pullbackUnitCellWitnessToNatCell
    (μ := μ) (ℱ := ℱ) (H := H) hn hGshift_prog hGshift_mod

/-- Helper for Remark 25.7: assemble a family of natural-horizon versions by choosing the witness
indexed by `Nat.ceil t` at time `t`. -/
def natHorizonAssembledVersion (G : ℕ → RealProcess) : RealProcess :=
  fun t ω ↦ G (Nat.ceil t) t ω

/-- Helper for Remark 25.7: a `Nat.ceil`-assembled family is progressively measurable once each
member is progressively measurable. -/
theorem progMeasurable_natHorizonAssembledVersion
    (G : ℕ → RealProcess)
    (hprog : ∀ n : ℕ, ProgMeasurable ℱ (G n)) :
    ProgMeasurable ℱ (natHorizonAssembledVersion G) := by
  intro T
  -- Proof comment: on the strip `[0,T]`, only finitely many ceiling indices can occur.
  refine Measurable.stronglyMeasurable ?_
  let K : Finset ℕ := Finset.Icc 0 (Nat.ceil T)
  let slab : ℕ → Set (Set.Iic T × Ω) := fun n ↦ {p | Nat.ceil (p.1 : NNReal) = n}
  have hslab : ∀ n : ℕ, MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)] (slab n) := by
    intro n
    -- Proof comment: each slab is the preimage of a singleton under the measurable ceiling map.
    let ceilMap : Set.Iic T × Ω → ℕ := fun p ↦ Nat.ceil (p.1 : NNReal)
    have hceilMap : Measurable ceilMap := by
      fun_prop
    simpa [ceilMap, slab] using hceilMap (measurableSet_singleton n)
  have hsum :
      Measurable (fun p : Set.Iic T × Ω ↦
        K.sum (fun n ↦ Set.indicator (slab n) (fun q : Set.Iic T × Ω ↦ G n q.1 q.2) p)) := by
    -- Proof comment: finitely many measurable slab pieces can be summed directly.
    refine Finset.measurable_fun_sum K ?_
    intro n hn
    exact Measurable.indicator ((hprog n T).measurable) (hslab n)
  have hrewrite :
      (fun p : Set.Iic T × Ω ↦
        K.sum (fun n ↦ Set.indicator (slab n) (fun q : Set.Iic T × Ω ↦ G n q.1 q.2) p)) =
      (fun p : Set.Iic T × Ω ↦ natHorizonAssembledVersion G p.1 p.2) := by
    funext p
    have hmemK : Nat.ceil (p.1 : NNReal) ∈ K := by
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.ceil_le.mpr (p.1.2.trans (Nat.le_ceil T))⟩
    -- Proof comment: exactly the summand indexed by `Nat.ceil p.1` survives on the strip.
    rw [Finset.sum_eq_single_of_mem (Nat.ceil (p.1 : NNReal)) hmemK]
    · simp [K, slab, natHorizonAssembledVersion]
    · intro b hb hbne
      simp [slab, hbne]
  -- Proof comment: rewrite the finite measurable sum back to the assembled strip map.
  convert hsum using 1
  ext p
  exact (congrFun hrewrite p).symm

/-- Helper for Remark 25.7: the `Nat.ceil` assembly preserves the timewise modification property
coming from each finite horizon. -/
theorem areModifications_natHorizonAssembledVersion
    (G : ℕ → RealProcess)
    (hmod : ∀ n : ℕ, ∀ t : NNReal, t ≤ (n : NNReal) → H t =ᵐ[μ] G n t) :
    AreModifications μ H (natHorizonAssembledVersion G) := by
  intro t
  -- Proof comment: at time `t`, choose the horizon `Nat.ceil t`, which always dominates `t`.
  simpa [natHorizonAssembledVersion] using hmod (Nat.ceil t) t (Nat.le_ceil t)

/-- Helper for Remark 25.7: the `Nat.ceil` assembly only needs one-cell modification witnesses,
plus a separate time-zero witness. -/
theorem areModifications_natHorizonAssembledVersion_of_natCells
    (G : ℕ → RealProcess)
    (hzero : H 0 =ᵐ[μ] G 0 0)
    (hcell :
      ∀ n : ℕ, 0 < n → ∀ t : NNReal,
        ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G n t) :
    AreModifications μ H (natHorizonAssembledVersion G) := by
  intro t
  by_cases ht : t = 0
  · -- Proof comment: the zero-time slice is handled by the dedicated witness.
    simpa [natHorizonAssembledVersion, ht, Nat.ceil_zero] using hzero
  · have hceil_pos : 0 < Nat.ceil t := Nat.ceil_pos.mpr (pos_iff_ne_zero.mpr ht)
    have hleft_nat : Nat.ceil t - 1 < Nat.ceil t := Nat.sub_one_lt_of_lt hceil_pos
    have hleft : (((Nat.ceil t) - 1 : ℕ) : NNReal) < t := Nat.lt_ceil.1 hleft_nat
    -- Proof comment: for `t > 0`, the relevant assembled index is exactly the single cell
    -- containing `t`.
    simpa [natHorizonAssembledVersion] using
      hcell (Nat.ceil t) hceil_pos t hleft (Nat.le_ceil t)

/-- Helper for Remark 25.7: once each natural horizon admits one progressively measurable
representative, the `Nat.ceil` assembly yields a single progressively measurable modification. -/
theorem existsProgMeasurableModification_of_natHorizonVersions
    (hVersions : ∀ n : ℕ, ∃ G : RealProcess,
      ProgMeasurable ℱ G ∧
      ∀ t : NNReal, t ≤ (n : NNReal) → H t =ᵐ[μ] G t) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  classical
  -- Proof comment: choose one witness on each natural horizon and then apply the existing
  -- `Nat.ceil` gluing lemmas to assemble a global progressively measurable version.
  choose G hG using hVersions
  refine ⟨natHorizonAssembledVersion G, ?_, ?_⟩
  · -- Proof comment: progressive measurability is preserved by the `Nat.ceil` assembly.
    exact progMeasurable_natHorizonAssembledVersion (ℱ := ℱ) G (fun n ↦ (hG n).1)
  · -- Proof comment: the timewise almost-sure equalities survive the same assembly.
    exact areModifications_natHorizonAssembledVersion
      (μ := μ) (ℱ := ℱ) (H := H) G (fun n ↦ (hG n).2)

/-- Helper for Remark 25.7: once each positive nat-cell has one progressively measurable
representative and time zero is treated separately, the same `Nat.ceil` assembly yields a global
progressively measurable modification. -/
theorem existsProgMeasurableModification_of_natCellVersions
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
  refine ⟨natHorizonAssembledVersion G, ?_, ?_⟩
  · -- Proof comment: each assembled piece is progressively measurable by construction.
    refine progMeasurable_natHorizonAssembledVersion (ℱ := ℱ) G ?_
    intro n
    by_cases hn : n = 0
    · simpa [G, hn] using hG0_prog
    · simpa [G, hn] using hGpos_prog ⟨n, Nat.pos_of_ne_zero hn⟩
  · -- Proof comment: apply the nat-cell modification theorem to the chosen family.
    refine areModifications_natHorizonAssembledVersion_of_natCells
      (μ := μ) (ℱ := ℱ) (H := H) G ?_ ?_
    · simpa [G] using hG0_zero
    · intro n hn t hleft hright
      simpa [G, Nat.ne_zero_iff_zero_lt.mpr hn] using
        hGpos_cell ⟨n, hn⟩ t hleft hright

/-- Helper for Remark 25.7: an adapted jointly measurable real-valued process admits a
progressively measurable modification. -/
theorem existsProgMeasurableModificationOfJointlyMeasurable
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  -- Route correction: the downstream API only needs time zero plus one witness on each positive
  -- natural cell `((n - 1), n]`, so the main theorem now reduces directly to that assembly step.
  have hzero :
      ∃ G0 : RealProcess, ProgMeasurable ℱ G0 ∧ H 0 =ᵐ[μ] G0 0 :=
    zeroTimeProgVersion (μ := μ) (ℱ := ℱ) (H := H) hH_adapted
  have hcell :
      ∀ n : ℕ, 0 < n → ∃ G : RealProcess,
        ProgMeasurable ℱ G ∧
        ∀ t : NNReal, ((n - 1 : ℕ) : NNReal) < t → t ≤ (n : NNReal) → H t =ᵐ[μ] G t :=
    existsProgMeasurableNatCellWitnesses (μ := μ) (ℱ := ℱ) (H := H) hH_adapted hH_prod
  -- Proof comment: the already-proved nat-cell assembly theorem turns these local witnesses into
  -- one global progressively measurable modification.
  exact existsProgMeasurableModification_of_natCellVersions
    (μ := μ) (ℱ := ℱ) (H := H) hzero hcell

/-- Helper for Remark 25.7: the only genuine missing step is finite-horizon regularization.
For a fixed natural horizon, build one globally progressively measurable version that agrees with
`H` almost everywhere at all earlier times. -/
theorem existsProgMeasurableVersionUpToNatHorizon
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∀ n : ℕ, ∃ G : RealProcess,
      ProgMeasurable ℱ G ∧
      ∀ t : NNReal, t ≤ (n : NNReal) → H t =ᵐ[μ] G t := by
  intro n
  -- Proof comment: once a global progressively measurable modification exists, the same witness
  -- works on every finite horizon without any new strip construction.
  rcases existsProgMeasurableModificationOfJointlyMeasurable
      (μ := μ) (ℱ := ℱ) (H := H) hH_adapted hH_prod with ⟨G, hG_prog, hG_mod⟩
  refine ⟨G, hG_prog, ?_⟩
  intro t ht
  -- Proof comment: the modification relation already gives timewise almost-sure equality for all
  -- deterministic times, so the horizon bound is unused.
  exact hG_mod t

/-- Helper for Remark 25.7: it is enough to regularize into a stripwise measurable version; the
usual `ProgMeasurable` statement then follows automatically. -/
theorem existsStripwiseMeasurableModificationOfJointlyMeasurable
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ H' : RealProcess,
      (∀ T : NNReal,
        Measurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ H' p.1 p.2)) ∧
      AreModifications μ H H' := by
  -- Proof comment: use the global progressively measurable modification directly and read off
  -- strip measurability from its definition.
  rcases existsProgMeasurableModificationOfJointlyMeasurable
      (μ := μ) (ℱ := ℱ) (H := H) hH_adapted hH_prod with ⟨H', hH'_prog, hH'_mod⟩
  refine ⟨H', ?_, hH'_mod⟩
  · intro T
    -- Proof comment: progressive measurability is exactly stripwise strong measurability, and for
    -- real-valued processes strong measurability implies measurability.
    exact (hH'_prog T).measurable

/-- Helper for Remark 25.7: a coherent finite-horizon family of progressively measurable
representatives would supply the missing converse direction. -/
theorem existsCoherentFiniteHorizonProgressiveVersions
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ G : NNReal → RealProcess,
      (∀ T : NNReal,
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
          (fun p : Set.Iic T × Ω ↦ G T p.1 p.2)) ∧
      (∀ {S T : NNReal}, S ≤ T → ∀ t : NNReal, t ≤ S → G T t = G S t) ∧
      (∀ T : NNReal, ∀ t : NNReal, t ≤ T → H t =ᵐ[μ] G T t) := by
  -- Route correction: instead of gluing unrelated stripwise representatives, first build one
  -- global progressively measurable modification and then reuse it at every horizon.
  rcases existsProgMeasurableModificationOfJointlyMeasurable (μ := μ) (ℱ := ℱ) (H := H)
      hH_adapted hH_prod with ⟨H', hprog, hmod⟩
  refine ⟨fun _ ↦ H', ?_, ?_, ?_⟩
  · intro T
    -- Proof comment: the constant horizon family inherits each strip measurability from `H'`.
    simpa using hprog T
  · intro S T hST t htS
    -- Proof comment: constant horizon families agree on overlaps by reflexivity.
    rfl
  · intro T t htT
    -- Proof comment: the modification relation is already timewise, so the horizon index is irrelevant.
    simpa using hmod t

/-- Helper for Remark 25.7: take the diagonal value from a coherent finite-horizon family. -/
def diagFiniteHorizonVersion (G : NNReal → RealProcess) : RealProcess :=
  fun t ω ↦ G t t ω

/-- Helper for Remark 25.7: the diagonal process coincides with the horizon-`T` representative on
the strip `[0,T] × Ω` when the family is coherent on nested horizons. -/
theorem diagFiniteHorizonVersion_eq_on_strip
    (G : NNReal → RealProcess)
    (hcoh : ∀ {S T : NNReal}, S ≤ T → ∀ t : NNReal, t ≤ S → G T t = G S t)
    (T : NNReal) :
    (fun p : Set.Iic T × Ω ↦ diagFiniteHorizonVersion G p.1 p.2) =
      (fun p : Set.Iic T × Ω ↦ G T p.1 p.2) := by
  -- Proof comment: on the strip `[0,T]`, coherence lets us replace the diagonal horizon `p.1`
  -- with the ambient horizon `T`.
  funext p
  simpa [diagFiniteHorizonVersion] using
    congrArg (fun f : Ω → ℝ => f p.2) (hcoh p.1.2 (p.1 : NNReal) le_rfl).symm

/-- Helper for Remark 25.7: stripwise strong measurability of a coherent family yields a
progressively measurable diagonal process. -/
theorem diagFiniteHorizonVersion_progMeasurable
    (G : NNReal → RealProcess)
    (hsm : ∀ T : NNReal,
      StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ G T p.1 p.2))
    (hcoh : ∀ {S T : NNReal}, S ≤ T → ∀ t : NNReal, t ≤ S → G T t = G S t) :
    ProgMeasurable ℱ (diagFiniteHorizonVersion G) := by
  intro T
  -- Proof comment: rewrite the strip restriction of the diagonal process to the already
  -- measurable strip map coming from the horizon-`T` representative.
  simpa [diagFiniteHorizonVersion_eq_on_strip (G := G) hcoh T] using hsm T

/-- Helper for Remark 25.7: the diagonal process is a modification of the original process once
each horizon representative matches the original process at all earlier times. -/
theorem diagFiniteHorizonVersion_areModifications
    (G : NNReal → RealProcess)
    (hae : ∀ T : NNReal, ∀ t : NNReal, t ≤ T → H t =ᵐ[μ] G T t) :
    AreModifications μ H (diagFiniteHorizonVersion G) := by
  intro t
  -- Proof comment: choose the horizon `T = t`, where the diagonal process is exactly `G t t`.
  simpa [diagFiniteHorizonVersion] using hae t t le_rfl

/-- Remark 25.7: an adapted product-measurable real-valued process admits a progressively
measurable modification. -/
-- Proof sketch: use the standard regularization theorem for jointly measurable adapted processes
-- to build a version `H'` whose restriction to every strip `[0,t] × Ω` is measurable for
-- `𝓑([0,t]) ⊗ ℱ t`; by construction `H'` agrees with `H` almost surely at each deterministic time,
-- so `H'` is a progressively measurable modification of `H`.
theorem exists_progMeasurable_modification_of_productMeasurable
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := by
  -- Route correction: the source-facing theorem should now expose the direct regularization result,
  -- while the coherent-family and diagonal lemmas remain available as internal wrappers.
  exact existsProgMeasurableModificationOfJointlyMeasurable (μ := μ) (ℱ := ℱ) (H := H)
    hH_adapted hH_prod

end Adapted

end MeasureTheory
