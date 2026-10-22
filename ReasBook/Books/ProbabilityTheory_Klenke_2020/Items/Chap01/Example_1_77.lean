/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory MeasurableSpace

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/- Example 1.77 (1): The identity map on a measurable space is measurable. -/
recall measurable_id' : Measurable (fun ω : Ω ↦ ω)

variable {Ω' : Type v} [MeasurableSpace Ω']

-- Proof sketch: if the source measurable space is `⊤`, apply `measurable_from_top`; if the
-- target measurable space is `⊥`, only the measurable sets `∅` and `univ` in the codomain need to
-- be checked.
/-- Example 1.77 (2): If the source measurable space is discrete or the target measurable space is
trivial, then every map is measurable. -/
theorem measurable_any_map_of_source_top_or_target_bot (X : Ω → Ω')
    (h : ‹MeasurableSpace Ω› = ⊤ ∨ ‹MeasurableSpace Ω'› = ⊥) :
    Measurable X := by
  rcases h with hΩ | hΩ'
  · subst hΩ
    simpa using (measurable_from_top : Measurable[⊤] X)
  · subst hΩ'
    intro s hs
    rcases measurableSet_bot_iff.mp hs with rfl | rfl <;> simp

-- Proof sketch: apply `measurable_indicator_const_iff` with the nonzero value `1 : Fin 2`; the
-- type `Fin 2` carries the discrete measurable structure corresponding to the full sigma-algebra
-- on a two-point space.
/-- Example 1.77 (3): The indicator of a set, valued in the discrete two-point space `Fin 2`, is
measurable if and only if the set itself is measurable. -/
theorem measurable_indicator_fin2_iff (A : Set Ω) :
    Measurable (A.indicator (fun _ : Ω ↦ (1 : Fin 2))) ↔ MeasurableSet A := by
  constructor
  · intro hA
    convert hA (MeasurableSet.singleton (0 : Fin 2)).compl using 1
    ext ω
    simp
  · intro hA
    exact measurable_const.indicator hA
