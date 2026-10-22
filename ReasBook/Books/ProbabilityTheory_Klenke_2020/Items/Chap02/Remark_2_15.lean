/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {Ω : Type u} {ι : Type v}
variable [MeasurableSpace Ω]
variable {m : ι → MeasurableSpace Ω} {β : ι → Type w}
variable [∀ i, MeasurableSpace (β i)]

/- Remark 2.15 (1): a family of random variables is independent exactly when every finite subfamily
satisfies the usual product formula for measurable preimages. This is the canonical theorem
`ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul`. -/
recall ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul

/-- Remark 2.15 (2): if a family of `σ`-algebras is independent and each `X i` is measurable with
respect to the corresponding `σ`-algebra, then the family `X` is independent. -/
theorem iIndepFun_of_measurable_of_iIndep (μ : Measure Ω) {X : ∀ i, Ω → β i}
    (hm : iIndep m μ) (hX : ∀ i, Measurable[m i] (X i)) :
    iIndepFun X μ := by
  rw [iIndepFun_iff_iIndep]
  exact iIndep_of_iIndep_of_le hm fun i ↦ (hX i).comap_le

/- Remark 2.15 (3): measurable postcomposition preserves independence. This is the canonical lemma
`ProbabilityTheory.iIndepFun.comp`. -/
recall ProbabilityTheory.iIndepFun.comp
