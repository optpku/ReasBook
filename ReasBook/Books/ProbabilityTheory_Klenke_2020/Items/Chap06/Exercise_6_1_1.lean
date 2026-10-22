/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Mathlib.MeasureTheory.Measure.Dirac

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E]

-- Proof sketch: restrict the convergence-in-measure statement to the singleton `{ω}`. The
-- restricted measure is `μ {ω} • Measure.dirac ω`, so if `μ {ω} ≠ 0`, then every deviation event
-- containing `ω` has restricted measure exactly `μ {ω}`. Since the restricted deviation measures
-- tend to `0`, eventually `ω` cannot lie in any `ε`-deviation set.
private theorem tendsto_at_of_tendstoInMeasure_of_singleton_ne_zero
    (μ : Measure Ω) [IsFiniteMeasure μ] {fSeq : ℕ → Ω → E} {f : Ω → E} {ω : Ω}
    (h_tendsto : TendstoInMeasure μ fSeq atTop f)
    (hω : μ {ω} ≠ 0) :
    Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  have h_restrict : TendstoInMeasure (μ.restrict {ω}) fSeq atTop f := by
    rw [tendstoInMeasure_iff_dist] at h_tendsto ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h_tendsto ε hε)
      (fun _ ↦ zero_le _) ?_
    intro n
    exact Measure.restrict_apply_le {ω} {x | ε ≤ dist (fSeq n x) (f x)}
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 ((tendstoInMeasure_iff_dist.1 h_restrict) ε hε))
    (μ {ω} / 2) (ENNReal.half_pos hω)
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra hdist
  have hmem : ω ∈ {x | ε ≤ dist (fSeq n x) (f x)} := by
    simpa [Set.mem_setOf_eq, not_lt] using hdist
  have hdirac :
      (Measure.dirac ω) {x | ε ≤ dist (fSeq n x) (f x)} = 1 :=
    Measure.dirac_apply_of_mem hmem
  have h_le : μ {ω} ≤ μ {ω} / 2 := by
    simpa [Measure.restrict_singleton, hdirac, smul_eq_mul] using hN n hn
  exact not_le_of_gt (ENNReal.half_lt_self hω (measure_ne_top μ {ω})) h_le

-- Proof sketch: use `ae_iff_of_countable` to reduce almost-everywhere convergence on the
-- countable space `Ω` to pointwise convergence at those `ω` with `P {ω} ≠ 0`, then apply the
-- preceding singleton-mass lemma.
/-- Exercise 6.1.1: On a countable probability space, convergence in probability implies
almost-everywhere convergence. -/
theorem tendsto_ae_of_tendstoInMeasure_of_countable
    [Countable Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_tendsto : TendstoInMeasure P fSeq atTop f) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  rw [ae_iff_of_countable]
  intro ω hω
  exact tendsto_at_of_tendstoInMeasure_of_singleton_ne_zero P h_tendsto hω
