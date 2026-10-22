/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

/-- A family `X : Fin n → Ω → ℝ` under a measure `P` realizes the laws `μ` when each coordinate is
measurable, has law `μ i`, the family is independent, and `P` is a probability measure. -/
structure IndependentRealLawFamily {Ω : Type} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure ℝ) (P : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  hasLaw : ∀ i, HasLaw (X i) (μ i) P
  indep : iIndepFun X P
  isProbabilityMeasure : IsProbabilityMeasure P

/-- Corollary 2.23: Any finite family of probability measures on `ℝ` can be realized as the laws of
an independent family of real-valued random variables on a common probability space. -/
-- Proof sketch: specialize `ProbabilityTheory.exists_hasLaw_indepFun` to the finite index type
-- `Fin n` and the constant target space `ℝ`, then package the resulting measurability, law,
-- independence, and probability-space properties into `IndependentRealLawFamily`.
theorem exists_independent_real_random_variables_with_given_laws
    (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : Fin n → Ω → ℝ,
      IndependentRealLawFamily n μ P X := by
  -- The product-space existence theorem supplies a common probability space and coordinate maps
  -- with the prescribed laws and mutual independence.
  obtain ⟨Ω, mΩ, P, X, hMeasurable, hHasLaw, hIndep, hProb⟩ :=
    ProbabilityTheory.exists_hasLaw_indepFun (ι := Fin n) (𝓧 := fun _ : Fin n => ℝ) μ
  -- Repackage those four properties into the structure required by this corollary.
  exact ⟨Ω, mΩ, P, X, ⟨hMeasurable, hHasLaw, hIndep, hProb⟩⟩
