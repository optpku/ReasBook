/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_5
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u}
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Helper for Example 19.4: the boundary datum extended by the first-entrance expectation on
`Aᶜ`. This is the owner-level encoding of the piecewise formula in (19.1). -/
def firstEntranceBoundaryExtension
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : E → ℝ) : E → ℝ :=
  fun x ↦
    if x ∈ A then
      g x
    else
      ∫ ω, g (stoppedValue X (hittingAfter X A 1) ω) ∂(P x : Measure Ω)

/-- Helper for Example 19.4: the first-entrance boundary extension agrees with the prescribed
boundary datum on `A`. -/
theorem firstEntranceBoundaryExtension_eq_boundary
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : E → ℝ)
    {x : E} (hx : x ∈ A) :
    firstEntranceBoundaryExtension P X A g x = g x := by
  -- Proof comment: on the boundary the owner definition selects the boundary branch.
  simp [firstEntranceBoundaryExtension, hx]

/-- Helper for Example 19.4: away from the boundary, the extension unfolds to the first-entrance
expectation. -/
theorem firstEntranceBoundaryExtension_eq_expectation_of_not_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : E → ℝ)
    {x : E} (hx : x ∉ A) :
    firstEntranceBoundaryExtension P X A g x =
      ∫ ω, g (stoppedValue X (hittingAfter X A 1) ω) ∂(P x : Measure Ω) := by
  -- Proof comment: off the boundary the owner definition selects the expectation branch.
  simp [firstEntranceBoundaryExtension, hx]

/-- Helper for Example 19.4: the first-entrance boundary extension matches the boundary datum on
`A` as a set-theoretic equality-on statement. -/
theorem firstEntranceBoundaryExtension_eqOn_boundary
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : E → ℝ) :
    Set.EqOn (firstEntranceBoundaryExtension P X A g) g A := by
  intro x hx
  exact firstEntranceBoundaryExtension_eq_boundary P X A g hx

/-- Example 19.4: if the first-entrance value function satisfies the one-step averaging identity
at every point of `E \ A`, then it is harmonic there. -/
theorem firstEntranceValueFunction_isHarmonicOutside
    [MeasurableSpace E] {κ : Kernel E E}
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : E → ℝ)
    (hfirstStep :
      ∀ ⦃x : E⦄, x ∉ A →
        Integrable (firstEntranceBoundaryExtension P X A g) (κ x) ∧
          firstEntranceBoundaryExtension P X A g x =
            ∫ y, firstEntranceBoundaryExtension P X A g y ∂κ x) :
    IsHarmonicOutside κ A (firstEntranceBoundaryExtension P X A g) := by
  -- Proof comment: the supplied first-step identity is exactly the owner definition of
  -- harmonicity outside `A`.
  intro x hx
  exact hfirstStep hx

end ProbabilityTheory
