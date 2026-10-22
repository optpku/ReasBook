/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped NNReal ENNReal Topology

universe u

variable {E : Type u} [TopologicalSpace E]

/- Definition 23.6 (1): A rate function on `E` is exactly a lower semicontinuous map
`E → [0, ∞]`, modeled in Lean as `LowerSemicontinuous I` for `I : E → ℝ≥0∞`. -/
recall LowerSemicontinuous

/-- A good rate function in Definition 23.6 is a rate function whose finite sublevel sets
`I ⁻¹' ([0, a])` are compact for every `a ∈ [0, ∞)`, written in Lean as
`I ⁻¹' Iic (a : ℝ≥0∞)` for `a : ℝ≥0`. -/
class IsGoodRateFunction (I : E → ℝ≥0∞) : Prop where
  /-- A good rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- Every finite sublevel set of a good rate function is compact. -/
  isCompact_sublevel : ∀ a : ℝ≥0, IsCompact (I ⁻¹' Iic (a : ℝ≥0∞))

/-- Definition 23.6: `IsGoodRateFunction I` means that `I` is lower semicontinuous and every
finite sublevel set `I ⁻¹' Iic (a : ℝ≥0∞)` is compact. -/
theorem isGoodRateFunction_iff (I : E → ℝ≥0∞) :
    IsGoodRateFunction I ↔
      LowerSemicontinuous I ∧ ∀ a : ℝ≥0, IsCompact (I ⁻¹' Iic (a : ℝ≥0∞)) := by
  constructor
  · intro hI
    exact ⟨hI.lowerSemicontinuous, hI.isCompact_sublevel⟩
  · rintro ⟨hI_lsc, hI_compact⟩
    exact ⟨hI_lsc, hI_compact⟩

attribute [instance] IsGoodRateFunction.lowerSemicontinuous
