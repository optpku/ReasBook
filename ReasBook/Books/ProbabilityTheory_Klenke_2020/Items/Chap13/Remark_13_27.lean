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

/- Remark 13.27 (1): for a Polish space, singleton families of finite Borel measures are tight by
the canonical owner theorem `MeasureTheory.isTightMeasureSet_singleton`. -/
recall MeasureTheory.isTightMeasureSet_singleton

-- Proof sketch: every singleton subfamily is tight by Remark 13.27 (1), and
-- `IsTightMeasureSet` is stable under finite unions. Induct on the finite set `S` to obtain
-- tightness of the whole family.
/-- Remark 13.27 (2): if `E` is Polish, then every finite family of finite measures on `E` is a
tight set of measures. -/
theorem isTightMeasureSet_of_finite_finiteMeasureFamily {S : Set (FiniteMeasure E)}
    (hS : S.Finite) :
    IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' S) := by
  refine Set.Finite.induction_on S hS ?_ ?_
  ·
      rw [Set.image_empty]
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      exact fun ε hε ↦ ⟨∅, isCompact_empty, by simp⟩
  · intro μ S _ _ ih
    have hμ : IsTightMeasureSet ({(μ : Measure E)} : Set (Measure E)) :=
      isTightMeasureSet_singleton
    simpa [Set.image_insert_eq] using hμ.union ih
