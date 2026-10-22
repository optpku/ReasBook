/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The intensity measure of a random measure `X`, modeled as a kernel, is the averaged measure
obtained by composing `X` with the ambient probability measure `P`. A random measure is
integrable exactly when this measure is finite. -/
abbrev intensityMeasure (P : ProbabilityMeasure Ω) (X : Kernel Ω E) : Measure E :=
  X ∘ₘ (P : Measure Ω)

-- Proof sketch: `intensityMeasure P X` is definitionally the kernel-measure composition
-- `X ∘ₘ (P : Measure Ω)`, so the claimed formula is the standard application rule
-- `Measure.bind_apply` on measurable sets.
/-- Theorem 24.4: the set function `A ↦ 𝔼[X(A)]` is the measure `intensityMeasure P X`, called the
intensity measure of the random measure `X`; on measurable sets it is given by the averaged
evaluations of the kernel `X`. -/
theorem intensityMeasure_apply
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) {A : Set E} (hA : MeasurableSet A) :
    intensityMeasure P X A = ∫⁻ ω, X ω A ∂(P : Measure Ω) := by
  -- Route correction: the Lean target already packages the intensity as a composed measure.
  -- Unfold that composition so the standard kernel-measure evaluation lemma applies.
  rw [intensityMeasure]
  -- Evaluate the composed measure on the measurable set `A` using `Measure.bind_apply`.
  simpa using (Measure.bind_apply hA (Kernel.aemeasurable X : AEMeasurable X (P : Measure Ω)))
