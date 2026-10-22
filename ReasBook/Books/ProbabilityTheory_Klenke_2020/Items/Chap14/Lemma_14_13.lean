/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section ProductSections

variable {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-
Lemma 14.13 is a `source-facing` item in the product-measurability domain. The owner abstraction
is the measurable partial-evaluation map on a product:
`measurable_prodMk_left`, `measurable_prodMk_right`, and for function sections the derived owner
theorems `Measurable.of_uncurry_left` and `Measurable.of_uncurry_right`.

The primitive data is just measurability of partial evaluation; measurable sections of sets and
functions are derived API obtained from `MeasurableSet.preimage` and `Measurable.comp`.
-/

/-- Lemma 14.13 (1): for a measurable set in a product measurable space, every section obtained by
fixing the first coordinate is measurable in the second space. -/
theorem measurableSet_prod_section_left
    {A : Set (Ω₁ × Ω₂)} (hA : MeasurableSet A) (ω₁ : Ω₁) :
    MeasurableSet {ω₂ : Ω₂ | (ω₁, ω₂) ∈ A} := by
  simpa only [Set.mem_setOf_eq] using hA.preimage measurable_prodMk_left

/-- Lemma 14.13 (2): for a measurable set in a product measurable space, every section obtained by
fixing the second coordinate is measurable in the first space. -/
theorem measurableSet_prod_section_right
    {A : Set (Ω₁ × Ω₂)} (hA : MeasurableSet A) (ω₂ : Ω₂) :
    MeasurableSet {ω₁ : Ω₁ | (ω₁, ω₂) ∈ A} := by
  simpa only [Set.mem_setOf_eq] using hA.preimage measurable_prodMk_right

/-- Lemma 14.13 (3): if `f : Ω₁ × Ω₂ → EReal` is measurable, then every section obtained by
fixing the first coordinate is a measurable `EReal`-valued map on the second space. -/
theorem measurable_prod_section_left
    {f : Ω₁ × Ω₂ → EReal} (hf : Measurable f) (ω₁ : Ω₁) :
    Measurable (fun ω₂ : Ω₂ ↦ f (ω₁, ω₂)) := by
  let g : Ω₁ → Ω₂ → EReal := Function.curry f
  have hg : Measurable (Function.uncurry g) := by
    simpa [g] using hf
  have hgω₁ : Measurable (g ω₁) := hg.of_uncurry_left
  simpa [g] using hgω₁

/-- Lemma 14.13 (4): if `f : Ω₁ × Ω₂ → EReal` is measurable, then every section obtained by
fixing the second coordinate is a measurable `EReal`-valued map on the first space. -/
theorem measurable_prod_section_right
    {f : Ω₁ × Ω₂ → EReal} (hf : Measurable f) (ω₂ : Ω₂) :
    Measurable (fun ω₁ : Ω₁ ↦ f (ω₁, ω₂)) := by
  let g : Ω₁ → Ω₂ → EReal := Function.curry f
  have hg : Measurable (Function.uncurry g) := by
    simpa [g] using hf
  have hgω₂ : Measurable fun ω₁ : Ω₁ ↦ g ω₁ ω₂ := hg.of_uncurry_right
  simpa [g] using hgω₂

end ProductSections
