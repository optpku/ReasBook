/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Exercise 6.1.3: a source-facing complement-set reformulation of
`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'` for real-valued measurable functions on a finite
measure space. It produces a measurable set on which the convergence is uniform and whose
complement has arbitrarily small measure. -/
-- Proof sketch: apply mathlib's finite-measure Egorov theorem to the sequence `fSeq` and limit
-- `f`, using measurable-to-strongly-measurable for real-valued functions. Run the theorem with
-- tolerance `ε / 2`, then replace the exceptional set `t` by `A := tᶜ` so that
-- `μ (Aᶜ) = μ t < ε`.
theorem exists_measurableSet_tendstoUniformlyOn_of_ae_tendsto
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hf : ∀ n, Measurable (fSeq n)) (hg : Measurable f)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧
      μ Aᶜ < ENNReal.ofReal ε ∧ TendstoUniformlyOn fSeq f atTop A := by
  obtain ⟨t, ht_meas, ht_small, ht_uniform⟩ :=
    tendstoUniformlyOn_of_ae_tendsto'
      (fun n ↦ (hf n).stronglyMeasurable) hg.stronglyMeasurable h_tendsto (half_pos hε)
  refine ⟨tᶜ, ht_meas.compl, ?_, by simpa using ht_uniform⟩
  simpa using
    (lt_of_le_of_lt ht_small <| (ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))
