/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open MeasureTheory
open scoped MeasureTheory Topology NNReal ENNReal

noncomputable section

universe u v

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
variable {X : ℝ≥0 → Ω → E}

/-- Helper for Exercise 21.1.4: the `n`-th upper dyadic index for the time `t`. -/
def upperStepIndex (n : ℕ) (t : ℝ≥0) : ℕ :=
  ⌈t * (n + 1 : ℝ≥0)⌉₊

/-- Helper for Exercise 21.1.4: the `n`-th upper dyadic time approximation of `t`. -/
def upperStepTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ((upperStepIndex n t : ℕ) : ℝ≥0) / (n + 1)

/-- Helper for Exercise 21.1.4: the upper dyadic approximation truncated at the horizon `T`. -/
def upperStepTimeOn (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  min (upperStepTime n t) T

/-- Helper for Exercise 21.1.4: the upper dyadic approximation stays to the right of `t`. -/
lemma self_le_upperStepTime (n : ℕ) (t : ℝ≥0) : t ≤ upperStepTime n t := by
  -- Multiply by the positive denominator to compare with the defining ceiling inequality.
  have hceil : t * (n + 1 : ℝ≥0) ≤ (upperStepIndex n t : ℕ) := by
    simpa [upperStepIndex] using Nat.le_ceil (t * (n + 1 : ℝ≥0))
  rw [upperStepTime]
  rw [le_div_iff₀]
  · simpa [mul_assoc] using hceil
  · exact Nat.cast_add_one_pos n

/-- Helper for Exercise 21.1.4: the upper dyadic approximation overshoots by at most
`1 / (n + 1)`. -/
lemma upperStepTime_le_add_inv (n : ℕ) (t : ℝ≥0) :
    upperStepTime n t ≤ t + 1 / (n + 1 : ℝ≥0) := by
  -- The defining ceiling is at most one unit above `t * (n + 1)`.
  have hceil : (upperStepIndex n t : ℕ) ≤ t * (n + 1 : ℝ≥0) + 1 := by
    simpa [upperStepIndex] using
      (Nat.ceil_lt_add_one (show 0 ≤ t * (n + 1 : ℝ≥0) by positivity)).le
  rw [upperStepTime]
  rw [div_le_iff₀]
  · refine hceil.trans ?_
    rw [add_mul, div_eq_mul_inv, one_mul, inv_mul_cancel₀]
    exact Nat.cast_add_one_ne_zero n
  · exact Nat.cast_add_one_pos n

/-- Helper for Exercise 21.1.4: the upper dyadic times converge down to `t`. -/
lemma tendsto_upperStepTime (t : ℝ≥0) :
    Tendsto (fun n ↦ upperStepTime n t) atTop (𝓝 t) := by
  -- Squeeze the approximants between the constant sequence `t` and the explicit error bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n ↦ upperStepTime n t)
    (g := fun _ : ℕ ↦ t)
    (h := fun n ↦ t + 1 / (n + 1 : ℝ≥0))
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t)) ?_ ?_ ?_
  · simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
          (fun n : ℕ ↦ (1 : ℝ≥0) / (n + 1 : ℝ≥0)) atTop (𝓝 0))
  · exact Filter.Eventually.of_forall fun n ↦ self_le_upperStepTime n t
  · exact Filter.Eventually.of_forall fun n ↦ upperStepTime_le_add_inv n t

/-- Helper for Exercise 21.1.4: on a fixed horizon strip, each upper-step approximation is jointly
measurable with respect to `ℱ T`. -/
lemma upperStep_measurableOnStrip
    {ℱ : Filtration ℝ≥0 inferInstance} {X : ℝ≥0 → Ω → E}
    (hX_adapted : Adapted ℱ X) (T : ℝ≥0) (n : ℕ) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦
      X (upperStepTimeOn T n p.1) p.2 := by
  letI : MeasurableSpace Ω := ℱ T
  let g : ℕ × Ω → E := fun q ↦ X (min (((q.1 : ℕ) : ℝ≥0) / (n + 1)) T) q.2
  have hg : Measurable g := by
    -- The approximation uses only times bounded by `T`, so each slice is `ℱ T`-measurable.
    refine measurable_from_prod_countable_right fun k ↦ ?_
    simpa [g] using
      hX_adapted.measurable_le
        (i := min (((k : ℕ) : ℝ≥0) / (n + 1)) T)
        (j := T)
        (min_le_right _ _)
  have hidx : Measurable fun p : Set.Iic T × Ω ↦ upperStepIndex n p.1 := by
    -- Only the time coordinate matters for the index.
    simpa [upperStepIndex] using
      ((measurable_fst.subtype_val.mul_const (n + 1 : ℝ≥0)).nat_ceil :
        Measurable fun p : Set.Iic T × Ω ↦ ⌈((p.1 : ℝ≥0) * (n + 1 : ℝ≥0))⌉₊)
  have hmap : Measurable fun p : Set.Iic T × Ω ↦ (upperStepIndex n p.1, p.2) :=
    hidx.prodMk measurable_snd
  have hcomp :
      (fun p : Set.Iic T × Ω ↦ X (upperStepTimeOn T n p.1) p.2) =
        g ∘ fun p : Set.Iic T × Ω ↦ (upperStepIndex n p.1, p.2) := by
    rfl
  rw [hcomp]
  exact hg.comp hmap

/-- Helper for Exercise 21.1.4: on a fixed horizon strip, the upper-step approximations converge
pointwise to the original process. -/
lemma upperStep_tendstoOnStrip
    {X : ℝ≥0 → Ω → E}
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t)
    (T : ℝ≥0) (p : Set.Iic T × Ω) :
    Tendsto (fun n ↦ X (upperStepTimeOn T n p.1) p.2) atTop (𝓝 (X p.1 p.2)) := by
  have htime_tendsto : Tendsto (fun n ↦ upperStepTimeOn T n p.1) atTop (𝓝 (p.1 : ℝ≥0)) := by
    -- Truncation preserves the squeeze to `p.1` because `p.1 ≤ T`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (p.1 : ℝ≥0)) atTop (𝓝 (p.1 : ℝ≥0)))
      (tendsto_upperStepTime p.1) ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦ le_min (self_le_upperStepTime n p.1) p.1.2
    · exact Filter.Eventually.of_forall fun n ↦ min_le_left _ _
  have htime_within :
      Tendsto (fun n ↦ upperStepTimeOn T n p.1) atTop (𝓝[Set.Ici (p.1 : ℝ≥0)] p.1) := by
    -- The approximants stay inside the right-neighborhood filter required by right continuity.
    refine tendsto_inf.2 ⟨htime_tendsto, ?_⟩
    exact tendsto_principal.2 <| Filter.Eventually.of_forall fun n ↦
      le_min (self_le_upperStepTime n p.1) p.1.2
  -- Compose the pathwise right continuity with the convergent approximation times.
  have hcont : Tendsto (fun s : ℝ≥0 ↦ X s p.2) (𝓝[Set.Ici (p.1 : ℝ≥0)] p.1) (𝓝 (X p.1 p.2)) :=
    hX_right_cont p.2 p.1
  exact hcont.comp htime_within

/-- Helper for Exercise 21.1.4: an adapted right-continuous process is measurable on every finite
strip `Set.Iic T × Ω` with respect to the σ-algebra `Subtype.instMeasurableSpace.prod (ℱ T)`. -/
lemma measurable_strip_of_adapted_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance} {X : ℝ≥0 → Ω → E}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t)
    (T : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦ X p.1 p.2 := by
  letI : MeasurableSpace (Set.Iic T × Ω) := Subtype.instMeasurableSpace.prod (ℱ T)
  -- The strip map is the pointwise limit of measurable upper-step approximations.
  refine measurable_of_tendsto_metrizable
    (f := fun n ↦ fun p : Set.Iic T × Ω ↦ X (upperStepTimeOn T n p.1) p.2)
    (fun n ↦ by
      simpa using
        (upperStep_measurableOnStrip hX_adapted T n :
          Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦
            X (upperStepTimeOn T n p.1) p.2))
    ?_
  rw [tendsto_pi_nhds]
  intro p
  simpa using upperStep_tendstoOnStrip hX_right_cont T p

/-- Exercise 21.1.4 (1): if each time slice `X t` is measurable and every sample path is right
continuous on `[0, ∞)`, then the process is jointly measurable as a map on time and sample space.
-/
-- Proof sketch: approximate each path on `[0, ∞)` by right-step processes built from rational or
-- dyadic times. Each approximant is jointly measurable because it is piecewise constant in time
-- with measurable coefficients `X q`, and the right-continuity of the paths identifies `X` as the
-- pointwise limit of these approximants.
theorem measurable_uncurry_of_measurable_rightContinuous
    (hX_meas : ∀ t, Measurable (X t))
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    Measurable (Function.uncurry X) := by
  let ℱ : Filtration ℝ≥0 inferInstance :=
    Filtration.const (ι := ℝ≥0) (m := (inferInstance : MeasurableSpace Ω))
      (inferInstance : MeasurableSpace Ω) le_rfl
  have hX_adapted : Adapted ℱ X := by
    intro t
    simpa [ℱ, Filtration.const_apply] using hX_meas t
  let strip : ℕ → Set (ℝ≥0 × Ω) := fun n ↦ { p | p.1 ≤ (n : ℝ≥0) }
  let stripMap : ∀ n, strip n → E := fun n p ↦ X p.1.1 p.1.2
  have hstrip_meas :
      ∀ n, Measurable (stripMap n) := by
    intro n
    have hbase :
        Measurable fun q : Set.Iic (n : ℝ≥0) × Ω ↦ X q.1 q.2 := by
      -- On each finite strip, use the strip measurability lemma with the constant filtration.
      simpa [ℱ, Filtration.const_apply] using
        measurable_strip_of_adapted_rightContinuous hX_adapted hX_right_cont (n : ℝ≥0)
    have hcoord :
        Measurable fun p : strip n ↦ ((⟨p.1.1, p.2⟩ : Set.Iic (n : ℝ≥0)), p.1.2) := by
      -- Repackage the subtype `{p | p.1 ≤ n}` as the product `Set.Iic n × Ω`.
      exact (measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd
    have hcomp :
        stripMap n = (fun q : Set.Iic (n : ℝ≥0) × Ω ↦ X q.1 q.2) ∘
          fun p : strip n ↦ ((⟨p.1.1, p.2⟩ : Set.Iic (n : ℝ≥0)), p.1.2) := by
      rfl
    rw [hcomp]
    exact hbase.comp hcoord
  have hstrip_eq :
      ∀ (i j) (p : ℝ≥0 × Ω) (hpi : p ∈ strip i) (hpj : p ∈ strip j),
        stripMap i ⟨p, hpi⟩ = stripMap j ⟨p, hpj⟩ := by
    intro i j p hpi hpj
    rfl
  have hcover : ⋃ n, strip n = Set.univ := by
    ext p
    constructor
    · intro _
      simp
    · intro _
      rcases exists_nat_ge p.1 with ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  let glued : ℝ≥0 × Ω → E := Set.liftCover strip stripMap hstrip_eq hcover
  have hglued_meas : Measurable glued :=
    measurable_liftCover strip
      (fun n ↦ by
        change MeasurableSet (Prod.fst ⁻¹' Set.Iic (n : ℝ≥0))
        exact measurableSet_Iic.preimage measurable_fst)
      stripMap hstrip_meas hstrip_eq hcover
  have hglued_eq : glued = Function.uncurry X := by
    funext p
    rcases exists_nat_ge p.1 with ⟨n, hn⟩
    simpa [glued, stripMap] using
      (Set.liftCover_of_mem (S := strip) (f := stripMap) (hf := hstrip_eq) (hS := hcover) hn)
  rw [← hglued_eq]
  exact hglued_meas

namespace Adapted

/-- Exercise 21.1.4 (2): an adapted right-continuous process on a Polish state space is
progressively measurable. -/
-- Proof sketch: for each deterministic horizon `t`, restrict the process to `[0, t]`. Adaptedness
-- makes every time section measurable with respect to `ℱ t`, and right-continuity lets one again
-- approximate the restriction by step processes using only times in `[0, t]`, yielding the
-- required measurability on `Set.Iic t × Ω`.
theorem progMeasurable_of_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance}
    {X : ℝ≥0 → Ω → E}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    ProgMeasurable ℱ X := by
  intro T
  -- The strip measurability lemma matches the definition of progressive measurability.
  exact (measurable_strip_of_adapted_rightContinuous hX_adapted hX_right_cont T).stronglyMeasurable

end Adapted

/-- Exercise 21.1.4 (3): evaluating an adapted right-continuous process at a finite stopping time
is measurable with respect to the stopping-time σ-algebra. -/
-- Proof sketch: part (2) gives progressive measurability. Identify `ω ↦ X (τ ω) ω` with the
-- stopped value of `X` at the finite stopping time `τ`, and then apply the standard theorem that
-- the stopped value of a progressively measurable process is measurable for `𝓕_τ`.
theorem measurable_stoppedValue_of_adapted_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance} {τ : Ω → ℝ≥0}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0)) :
    Measurable[hτ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  simpa [stoppedValue] using
    measurable_stoppedValue (hX_adapted.progMeasurable_of_rightContinuous hX_right_cont) hτ

end MeasureTheory
