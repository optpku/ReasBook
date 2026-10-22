/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory TopologicalSpace

universe u v w

variable {ι : Type u} [Preorder ι]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [MeasurableSpace E]
variable {u : ι → Ω → E}

-- Proof sketch: unfold `MeasureTheory.Adapted` and the order on filtrations. The forward
-- direction shows that each generator `MeasurableSpace.comap (u j)` lies in `f i` whenever
-- `j ≤ i`, and the reverse direction uses the canonical inclusion
-- `MeasurableSpace.comap (u i) _ ≤ generatedFiltration u hu i`.
/-- Remark 9.11: a process is adapted to a filtration exactly when its generated filtration is
smaller than that filtration; in particular, the generated filtration is the smallest filtration
to which the process is adapted. -/
theorem adapted_iff_generatedFiltration_le (hu : ∀ i, Measurable (u i))
    {f : Filtration ι mΩ} :
    Adapted f u ↔ generatedFiltration u hu ≤ f := by
  constructor
  · intro hadapted i
    refine iSup₂_le fun j hij ↦ ?_
    exact measurable_iff_comap_le.1 (hadapted.measurable_le hij)
  · intro huf i
    have hcomap : MeasurableSpace.comap (u i) ‹MeasurableSpace E› ≤ generatedFiltration u hu i := by
      rw [generatedFiltration_apply]
      exact le_iSup₂_of_le i le_rfl le_rfl
    exact measurable_iff_comap_le.2 (hcomap.trans (huf i))

section

variable [TopologicalSpace E]
variable [MetrizableSpace E]
variable [BorelSpace E]

local instance : ∀ _ : ι, TopologicalSpace E := fun _ ↦ inferInstance
local instance : ∀ _ : ι, MetrizableSpace E := fun _ ↦ inferInstance
local instance : ∀ _ : ι, MeasurableSpace E := fun _ ↦ inferInstance
local instance : ∀ _ : ι, BorelSpace E := fun _ ↦ inferInstance

/-- Under the usual Borel regularity assumptions, Remark 9.11 specializes to mathlib's natural
filtration. -/
theorem adapted_iff_natural_le (hum : ∀ i, StronglyMeasurable (u i)) {f : Filtration ι mΩ} :
    Adapted f u ↔ Filtration.natural u hum ≤ f := by
  let hu : ∀ i, Measurable (u i) := fun i ↦ (hum i).measurable
  simpa [generatedFiltration_eq_natural u hum] using adapted_iff_generatedFiltration_le hu

end
