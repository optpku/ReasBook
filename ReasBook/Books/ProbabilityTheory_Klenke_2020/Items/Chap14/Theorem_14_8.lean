/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section CountableProduct

variable {I : Type u} {Ω : I → Type v}
variable [Countable I] [∀ i, TopologicalSpace (Ω i)] [∀ i, MeasurableSpace (Ω i)]
variable [∀ i, PolishSpace (Ω i)] [∀ i, BorelSpace (Ω i)]

-- Proof sketch: use the countable-product Polish-space instance for `∀ i, Ω i` and the
-- measurable-space instance `Pi.borelSpace`; then conclude the equality of measurable spaces from
-- `BorelSpace.measurable_eq`.
/-- Theorem 14.8: A countable product of Polish spaces is Polish, and its Borel
σ-algebra agrees with the product σ-algebra. -/
theorem countable_polish_product_polish_and_borel_eq_pi
    : PolishSpace (∀ i, Ω i) ∧ borel (∀ i, Ω i) = MeasurableSpace.pi :=
  ⟨inferInstance, BorelSpace.measurable_eq.symm⟩

end CountableProduct
