/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E1 : Type u} [MeasurableSpace E1]
variable {E2 : Type v} [MeasurableSpace E2]

/-- Definition 17.53: a probability measure `μ` on `E₁ × E₂` is a coupling of `μ₁` and `μ₂` if
its first and second coordinate marginals are `μ₁` and `μ₂`, respectively. -/
def IsCoupling (μ : ProbabilityMeasure (E1 × E2))
    (μ1 : ProbabilityMeasure E1) (μ2 : ProbabilityMeasure E2) : Prop :=
  (μ : Measure (E1 × E2)).fst = (μ1 : Measure E1) ∧
    (μ : Measure (E1 × E2)).snd = (μ2 : Measure E2)

-- Proof sketch: `Measure.fst` and `Measure.snd` are by definition the pushforwards along
-- `Prod.fst` and `Prod.snd`; compare probability measures by coercing to measures.
/-- A coupling is equivalently characterized by its pushforwards along `Prod.fst` and `Prod.snd`.
-/
theorem isCoupling_iff
    (μ : ProbabilityMeasure (E1 × E2)) (μ1 : ProbabilityMeasure E1)
    (μ2 : ProbabilityMeasure E2) :
    IsCoupling μ μ1 μ2 ↔
      μ.map measurable_fst.aemeasurable = μ1 ∧
        μ.map measurable_snd.aemeasurable = μ2 := by
  constructor
  · rintro ⟨hfst, hsnd⟩
    constructor
    · apply ProbabilityMeasure.toMeasure_injective
      simpa [IsCoupling, Measure.fst] using hfst
    · apply ProbabilityMeasure.toMeasure_injective
      simpa [IsCoupling, Measure.snd] using hsnd
  · rintro ⟨hfst, hsnd⟩
    constructor
    · simpa [IsCoupling, Measure.fst] using
        congrArg (fun ν : ProbabilityMeasure E1 ↦ (ν : Measure E1)) hfst
    · simpa [IsCoupling, Measure.snd] using
        congrArg (fun ν : ProbabilityMeasure E2 ↦ (ν : Measure E2)) hsnd

-- Proof sketch: the product probability measure has the prescribed marginals by the canonical
-- lemmas `ProbabilityMeasure.map_fst_prod` and `ProbabilityMeasure.map_snd_prod`.
/-- The product probability measure `μ₁.prod μ₂` is a coupling of `μ₁` and `μ₂`. -/
theorem isCoupling_prod (μ1 : ProbabilityMeasure E1) (μ2 : ProbabilityMeasure E2) :
    IsCoupling (μ1.prod μ2) μ1 μ2 := by
  simp [IsCoupling]

end ProbabilityTheory
