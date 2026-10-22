/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {E : Type u} [MeasurableSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]

section

variable [CompleteSpace F] [BorelSpace F]

/-- Definition 13.9: a family `𝒞` of measurable test maps separates a family `ℱ` of measures if
equality of the integrals of every common integrable test function in `𝒞` forces the two measures
to be equal. The textbook instance is the real-valued specialization `F = ℝ`. -/
def IsSeparatingFamilyFor (ℱ : Set (Measure E)) (𝒞 : Set (E → F)) : Prop :=
  (∀ ⦃f : E → F⦄, f ∈ 𝒞 → Measurable f) ∧
    ∀ ⦃μ ν : Measure E⦄, μ ∈ ℱ → ν ∈ ℱ →
      (∀ ⦃f : E → F⦄, f ∈ 𝒞 → Integrable f μ → Integrable f ν →
        ∫ x, f x ∂μ = ∫ x, f x ∂ν) →
      μ = ν

end

attribute [irreducible] IsSeparatingFamilyFor

-- Proof sketch: extract the measurability component from the defining conjunction of
-- `IsSeparatingFamilyFor`.
/-- Every test function in a separating family is measurable. -/
theorem IsSeparatingFamilyFor.measurable
    {ℱ : Set (Measure E)} {𝒞 : Set (E → F)} (h𝒞 : IsSeparatingFamilyFor ℱ 𝒞)
    {f : E → F} (hf : f ∈ 𝒞) :
    Measurable f := by
  unfold IsSeparatingFamilyFor at h𝒞
  exact h𝒞.1 hf

-- Proof sketch: apply the separation clause in the definition of `IsSeparatingFamilyFor` to the
-- two measures `μ` and `ν`.
/-- A separating family identifies two measures in `ℱ` once all common integrable test functions in
`𝒞` have the same integrals against them. -/
theorem IsSeparatingFamilyFor.eq_of_forall_integral_eq
    {ℱ : Set (Measure E)} {𝒞 : Set (E → F)} (h𝒞 : IsSeparatingFamilyFor ℱ 𝒞)
    {μ ν : Measure E} (hμ : μ ∈ ℱ) (hν : ν ∈ ℱ)
    (h_int :
      ∀ ⦃f : E → F⦄, f ∈ 𝒞 → Integrable f μ → Integrable f ν →
        ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  unfold IsSeparatingFamilyFor at h𝒞
  exact h𝒞.2 hμ hν h_int
