/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- Lemma 13.5: every finite measure on a Polish space is tight in the sense that for each
positive real `ε` there is a compact set whose complement has `μ`-mass smaller than `ε`. -/
-- Proof sketch: use the canonical singleton-tightness theorem
-- `MeasureTheory.isTightMeasureSet_singleton`, then apply
-- `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` to `ε / 2`.
lemma exists_isCompact_measure_compl_lt (μ : Measure E) [IsFiniteMeasure μ] {ε : ℝ}
    (hε : 0 < ε) : ∃ K : Set E, IsCompact K ∧ μ (Kᶜ) < ENNReal.ofReal ε := by
  have hμ : IsTightMeasureSet ({μ} : Set (Measure E)) := isTightMeasureSet_singleton
  have hε' : 0 < ENNReal.ofReal (ε / 2) := by
    positivity
  obtain ⟨K, hK, hKμ⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ) (ENNReal.ofReal (ε / 2)) hε'
  exact ⟨K, hK, (hKμ μ (by simp)).trans_lt <| ENNReal.ofReal_lt_ofReal_iff hε |>.2 (by nlinarith)⟩
