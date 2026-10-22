/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Remark_16_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_6

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The first time at which the Brownian path `t ↦ B t ω` hits the level `b`. -/
def brownianLevelHittingTime (B : NNReal → Ω → ℝ) (b : ℝ) : Ω → ENNReal :=
  hittingAfter B ({b} : Set ℝ) (0 : NNReal)

omit [MeasurableSpace Ω] in
/-- Expanding `brownianLevelHittingTime` gives the canonical owner `hittingAfter` for the
Brownian path at level `b`. -/
theorem brownianLevelHittingTime_eq_hittingAfter
    (B : NNReal → Ω → ℝ) (b : ℝ) :
    brownianLevelHittingTime B b =
      hittingAfter B ({b} : Set ℝ) (0 : NNReal) := by
  rfl

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 21.2.5: one-sided hitting is the zero-slope specialization of the affine
boundary hitting time from Exercise 21.2.6. -/
theorem brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero
    (B : NNReal → Ω → ℝ) (b : ℝ) :
    brownianLevelHittingTime B b = brownianAffineBoundaryHittingTime B 0 b := by
  ext ω
  rw [brownianLevelHittingTime_eq_hittingAfter, brownianAffineBoundaryHittingTime_eq_hittingAfter]
  simp

/-- Helper for Exercise 21.2.5: finite Brownian level hitting time is equivalent to the existence
of an actual hit at some time. -/
theorem brownianLevelHittingTime_ne_top_iff_exists_eq
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω} :
    brownianLevelHittingTime B b ω ≠ ⊤ ↔ ∃ t : NNReal, B t ω = b := by
  simpa [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
    (brownianAffineBoundaryHittingTime_ne_top_iff_exists_eq
      (B := B) (a := 0) (b := b) (ω := ω))

/-- Helper for Exercise 21.2.5: an explicit hit at time `t` bounds the hitting time by `t`. -/
theorem brownianLevelHittingTime_le_of_eq
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω} {t : NNReal}
    (ht : B t ω = b) :
    brownianLevelHittingTime B b ω ≤ t := by
  simpa [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
    (brownianAffineBoundaryHittingTime_le_of_eq
      (B := B) (a := 0) (b := b) (ω := ω) (t := t) (by simpa using ht))

/-- Helper for Exercise 21.2.5: for measurable time slices and continuous paths, the level hitting
time is a stopping time for the natural filtration. -/
theorem brownianLevelHittingTime_isStoppingTime
    {B : NNReal → Ω → ℝ}
    (hBsm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t ↦ B t ω)
    (b : ℝ) :
    IsStoppingTime (Filtration.natural B hBsm) (brownianLevelHittingTime B b) := by
  -- Proof comment: specialize the affine-boundary stopping-time theorem to slope `a = 0`.
  simpa [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
    (brownianAffineBoundaryHittingTime_isStoppingTime
      (B := B) (a := 0) (b := b) hBsm (fun ω ↦ by simpa using hcont ω))

/-- Helper for Exercise 21.2.5: once the level-hit time is finite, the stopped Brownian value is
exactly the level `b`. -/
theorem brownianLevelHittingTime_stoppedValue_eq_level
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (hcont : Continuous fun t ↦ B t ω)
    (hτ : brownianLevelHittingTime B b ω ≠ ⊤) :
    stoppedValue B (brownianLevelHittingTime B b) ω = b := by
  have hτ_lt : brownianAffineBoundaryHittingTime B 0 b ω < ⊤ := by
    simpa [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
      (lt_top_iff_ne_top.mpr hτ)
  -- Proof comment: the affine-boundary stopped-value identity at slope `0` is exactly the
  -- one-sided stopped Brownian value.
  simpa [stoppedValue,
    brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
    (driftedBrownian_value_eq_boundary_at_hittingTime
      (B := B) (a := 0) (b := b) (ω := ω) (by simpa using hcont) hτ_lt)

/-- Helper for Exercise 21.2.5: the real-valued hitting-time clock is almost everywhere
measurable. -/
theorem aemeasurable_brownianLevelHittingTime_toReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (b : ℝ) :
    AEMeasurable (fun ω ↦ (brownianLevelHittingTime B b ω).toReal) μ := by
  simpa [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
    (aemeasurable_brownianAffineBoundaryHittingTime_toReal (μ := μ) (B := B) hB 0 b)

/-- Helper for Exercise 21.2.5: for a positive level, Brownian motion hits that level in finite
time almost surely. -/
theorem brownianLevelHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    {b : ℝ}
    (hb : 0 < b) :
    ∀ᵐ ω ∂μ, brownianLevelHittingTime B b ω ≠ ⊤ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let s : Set Ω := {ω | brownianAffineBoundaryHittingTime B 0 b ω < ⊤}
  have hs_ae :
      s =ᵐ[μ] {ω | 0 < (brownianAffineBoundaryHittingTime B 0 b ω).toReal} := by
    filter_upwards [hB.continuous_paths] with ω hωcont
    have hcont : Continuous fun t : NNReal ↦ B t ω := by
      simpa [processPath] using hωcont
    apply propext
    constructor
    · intro hω
      have hτ_ne : brownianAffineBoundaryHittingTime B 0 b ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      have hτ_not_le_zero : ¬ brownianAffineBoundaryHittingTime B 0 b ω ≤ 0 := by
        intro hτ_zero
        rcases
            (brownianAffineBoundaryHittingTime_le_iff_exists_eq_of_continuous
              (B := B) (a := 0) (b := b) (ω := ω) (by simpa using hcont) (T := 0)).1 hτ_zero
          with ⟨t, ht_mem, ht_eq⟩
        have ht_zero : t = 0 := by
          exact le_antisymm ht_mem.2 (by simp)
        have hB0 : B 0 ω = b := by
          simpa [ht_zero] using ht_eq
        have hzeroω : B 0 ω = 0 := by
          simpa using congrFun hB.zero ω
        have : (0 : ℝ) = b := by
          linarith
        linarith
      have hτ_pos : 0 < brownianAffineBoundaryHittingTime B 0 b ω := lt_of_not_ge hτ_not_le_zero
      exact ENNReal.toReal_pos hτ_pos.ne' hτ_ne
    · intro hω
      exact (ENNReal.toReal_pos_iff.1 hω).2
  have hs_null : NullMeasurableSet s μ := by
    have hrhs :
        NullMeasurableSet {ω | 0 < (brownianAffineBoundaryHittingTime B 0 b ω).toReal} μ :=
      by
        let hmeas :=
          aemeasurable_brownianAffineBoundaryHittingTime_toReal (μ := μ) (B := B) hB 0 b
        exact hmeas.nullMeasurableSet_preimage measurableSet_Ioi
    exact hrhs.congr hs_ae.symm
  have hs_prob : μ s = 1 := by
    simpa [s] using
      (brownianAffineBoundaryHittingTime_lt_top_prob (μ := μ) (B := B) hB (a := 0) (b := b) hb)
  have hs_mem_ae : s ∈ ae μ := (MeasureTheory.mem_ae_iff_prob_eq_one₀ hs_null).2 hs_prob
  simpa [s, brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b),
    lt_top_iff_ne_top] using hs_mem_ae

/-- The law of the real-valued Brownian level-hitting time `τ_b.toReal`. -/
def brownianLevelHittingTimeLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (b : ℝ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (aemeasurable_brownianLevelHittingTime_toReal (μ := μ) (B := B) hB b)

/-- Coercing `brownianLevelHittingTimeLaw hB b` to `Measure ℝ` recovers the corresponding
pushforward law of `τ_b.toReal`. -/
theorem brownianLevelHittingTimeLaw_toMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (b : ℝ) :
    (brownianLevelHittingTimeLaw hB b : Measure ℝ) =
      Measure.map (fun ω ↦ (brownianLevelHittingTime B b ω).toReal) μ := by
  rfl

/-- The candidate Brownian hitting-time density appearing in Exercise 21.2.5. -/
def brownianLevelHittingTimeDensity (b : ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then
    0
  else
    (b / Real.sqrt (2 * Real.pi)) * Real.exp (-(b ^ (2 : ℕ)) / (2 * x)) *
      Real.rpow x (-(3 : ℝ) / 2)

/-- Exercise 21.2.5: item (i), for `b > 0`, the Laplace transform of the Brownian first hitting
time is `exp (-b * sqrt (2 * λ))`. -/
theorem brownianLevelHittingTime_laplaceTransform
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    {b : ℝ}
    (hb : 0 < b)
    (l : NNReal) :
    ∫ x : ℝ, Real.exp (-((l : ℝ) * x)) ∂(brownianLevelHittingTimeLaw hB b : Measure ℝ) =
      Real.exp (-b * Real.sqrt (2 * (l : ℝ))) := by
  let τ : Ω → ENNReal := brownianLevelHittingTime B b
  have hKernel :
      AEStronglyMeasurable
        (fun x : ℝ ↦ Real.exp (-((l : ℝ) * x)))
        (brownianLevelHittingTimeLaw hB b : Measure ℝ) := by
    have hCont : Continuous (fun x : ℝ ↦ Real.exp (-((l : ℝ) * x))) := by
      fun_prop
    exact hCont.aestronglyMeasurable
  calc
    ∫ x : ℝ, Real.exp (-((l : ℝ) * x)) ∂(brownianLevelHittingTimeLaw hB b : Measure ℝ)
        = ∫ ω, Real.exp (-((l : ℝ) * (τ ω).toReal)) ∂μ := by
            rw [brownianLevelHittingTimeLaw_toMeasure]
            exact MeasureTheory.integral_map
              (aemeasurable_brownianLevelHittingTime_toReal (μ := μ) (B := B) hB b)
              hKernel
    _ = ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B 0 b (l : ℝ) ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [brownianLevelHittingTime_ae_ne_top (μ := μ) (B := B) hB hb] with ω hω
          have hω_lt : brownianAffineBoundaryHittingTime B 0 b ω < ⊤ := by
            simpa
              [brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b)] using
              (lt_top_iff_ne_top.mpr hω)
          -- Proof comment: on the almost-sure finite-hit event, the affine Laplace weight at
          -- slope `0` is just `exp (-λ τ_b)`.
          simp [τ, brownianAffineBoundaryHittingTimeLaplaceWeight_def,
            brownianLevelHittingTime_eq_affineBoundaryHittingTime_zero (B := B) (b := b), hω_lt]
    _ = Real.exp (-b * Real.sqrt (2 * (l : ℝ))) := by
          simpa using
            (brownianAffineBoundaryHittingTime_laplaceTransform
              (μ := μ) (B := B) hB (a := 0) (b := b) (lam := (l : ℝ)) hb
              (by positivity))

end ProbabilityTheory
