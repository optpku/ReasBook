/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory
namespace SignedMeasure

variable {Ω : Type u} [MeasurableSpace Ω]

open VectorMeasure

-- Proof sketch: this is exactly `VectorMeasure.AbsolutelyContinuous.ennrealToMeasure` specialized
-- to `μ.toENNRealVectorMeasure`, together with `ennrealToMeasure_toENNRealVectorMeasure`.
private theorem absolutelyContinuous_iff_forall_apply_eq_zero (φ : SignedMeasure Ω)
    (μ : Measure Ω) :
    φ ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ A : Set Ω, μ A = 0 → φ A = 0 := by
  simpa [ennrealToMeasure_toENNRealVectorMeasure] using
    (AbsolutelyContinuous.ennrealToMeasure :
      (∀ ⦃s : Set Ω⦄, (μ.toENNRealVectorMeasure).ennrealToMeasure s = 0 → φ s = 0) ↔
        φ ≪ᵥ μ.toENNRealVectorMeasure).symm

-- Proof sketch: for the forward direction use the canonical Radon--Nikodym witness `φ.rnDeriv μ`
-- and `SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`; for the reverse
-- direction, `Measure.withDensityᵥ_absolutelyContinuous` gives the absolute continuity.
/-- Exercise 7.5.1: For a `σ`-finite measure `μ`, a signed measure `φ` is absolutely continuous
with respect to `μ` if and only if there is an integrable real-valued density `f` with
`φ = μ.withDensityᵥ f`. -/
theorem absolutelyContinuous_iff_exists_integrable_density (μ : Measure Ω) [SigmaFinite μ]
    (φ : SignedMeasure Ω) :
    φ ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∃ f : Ω → ℝ, Integrable f μ ∧ μ.withDensityᵥ f = φ := by
  constructor
  · intro hφ
    refine ⟨φ.rnDeriv μ, integrable_rnDeriv φ μ, ?_⟩
    exact (absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq φ μ).mp hφ
  · rintro ⟨f, hf, rfl⟩
    exact Measure.withDensityᵥ_absolutelyContinuous μ f

-- Proof sketch: rewrite the right-hand side using
-- `absolutelyContinuous_iff_exists_integrable_density`; the remaining equivalence is exactly
-- `absolutelyContinuous_iff_forall_apply_eq_zero`.
/-- Exercise 7.5.1 in textbook wording: for a `σ`-finite measure `μ`, a signed measure `φ`
vanishes on every `μ`-null set if and only if there is an integrable real-valued density `f`
with `φ = μ.withDensityᵥ f`. -/
theorem vanishes_on_null_iff_exists_integrable_density (μ : Measure Ω) [SigmaFinite μ]
    (φ : SignedMeasure Ω) :
    (∀ A : Set Ω, μ A = 0 → φ A = 0) ↔
      ∃ f : Ω → ℝ, Integrable f μ ∧ μ.withDensityᵥ f = φ := by
  rw [← absolutelyContinuous_iff_exists_integrable_density μ φ]
  exact (absolutelyContinuous_iff_forall_apply_eq_zero φ μ).symm

/- The canonical density witness for an absolutely continuous signed measure is `φ.rnDeriv μ`. -/
recall absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (φ : SignedMeasure Ω) (μ : Measure Ω)
    [SigmaFinite μ] :
  φ ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (φ.rnDeriv μ) = φ

end SignedMeasure
end MeasureTheory
