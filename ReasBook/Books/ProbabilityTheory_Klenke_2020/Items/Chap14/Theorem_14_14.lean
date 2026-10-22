/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped BigOperators

noncomputable section

universe u

/- In the homogeneous finite-product case, the textbook product measure `μ₀^{⊗ n}` is the
canonical owner object `Measure.pi (fun _ : Fin n ↦ μ₀)`. -/
recall Measure.pi

/- On measurable rectangles, finite product measures are characterized by the canonical rectangle
formula `Measure.pi_pi`. -/
recall Measure.pi_pi

/- Agreement on measurable rectangles identifies a finite product measure with the canonical owner
object `Measure.pi`. -/
recall Measure.pi_eq

-- Proof sketch: use `Measure.pi μs` for existence, `Measure.pi.sigmaFinite` for σ-finiteness,
-- `Measure.pi_pi` for the rectangle formula, and `Measure.pi_eq` for uniqueness.
/-- Theorem 14.14: For a finite family of measurable spaces equipped with σ-finite measures,
there exists a unique σ-finite measure on the product measurable space whose value on each
measurable rectangle is the product of the factor masses. -/
theorem existsUnique_sigmaFinite_product_measure
    {n : ℕ} {Ω : Fin n → Type u} [∀ i, MeasurableSpace (Ω i)]
    (μs : ∀ i, Measure (Ω i)) (hμs : ∀ i, SigmaFinite (μs i)) :
    ∃! μ : Measure ((i : Fin n) → Ω i),
      SigmaFinite μ ∧
        ∀ s : ∀ i, Set (Ω i), (∀ i, MeasurableSet (s i)) →
          μ (univ.pi s) = ∏ i, μs i (s i) := by
  letI : ∀ i, SigmaFinite (μs i) := hμs
  refine ⟨Measure.pi μs, ⟨inferInstance, ?_⟩, ?_⟩
  · intro s _
    exact Measure.pi_pi μs s
  intro ν hν
  rcases hν with ⟨_, hν_rect⟩
  simpa using (Measure.pi_eq hν_rect).symm
