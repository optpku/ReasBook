/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

open scoped ENNReal

universe u

namespace MeasureTheory
namespace FiniteMeasure

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E]

/- Definition 13.26: the owner notion of tightness is `MeasureTheory.IsTightMeasureSet`; for a
family of finite measures, it is applied to the image of the family under the canonical map
`FiniteMeasure.toMeasure`. -/
#check (IsTightMeasureSet : Set (Measure E) → Prop)

/- The compact-control formulation is the canonical theorem
`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
recall isTightMeasureSet_iff_exists_isCompact_measure_compl_le

/-- Definition 13.26: a family of finite measures is tight exactly when compact sets control the
mass of complements uniformly over the family. -/
-- Proof sketch: apply
-- `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` to the image of `ℱ` in `Measure E`,
-- and convert the resulting `≤`-estimate in `ℝ≥0∞` to the textbook's strict bound
-- `< ENNReal.ofReal ε` by shrinking `ε`.
theorem tight_family_iff_forall_exists_isCompact_measure_compl_lt (ℱ : Set (FiniteMeasure E)) :
    IsTightMeasureSet (toMeasure '' ℱ) ↔
      ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
        ∀ μ ∈ ℱ, toMeasure μ Kᶜ < ENNReal.ofReal ε := by
  constructor
  · intro hℱ ε hε
    have hε' : 0 < ENNReal.ofReal (ε / 2) := by
      positivity
    obtain ⟨K, hK, hKℱ⟩ :=
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hℱ) (ENNReal.ofReal (ε / 2)) hε'
    refine ⟨K, hK, fun μ hμ ↦ ?_⟩
    exact (hKℱ (toMeasure μ) ⟨μ, hμ, rfl⟩).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith))
  · intro hℱ
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hε_top : ε = ∞
    · refine ⟨∅, isCompact_empty, fun μ hμ ↦ ?_⟩
      simp [hε_top]
    · have hε_toReal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      obtain ⟨K, hK, hKℱ⟩ := hℱ ε.toReal hε_toReal
      refine ⟨K, hK, fun μ hμ ↦ ?_⟩
      rcases hμ with ⟨ν, hν, rfl⟩
      exact (hKℱ ν hν).le.trans_eq (ENNReal.ofReal_toReal hε_top)

end FiniteMeasure
end MeasureTheory
