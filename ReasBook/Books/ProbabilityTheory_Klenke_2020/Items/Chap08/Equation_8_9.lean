/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

/- Equation (8.9): if `X : Ω → E` and `Z : Ω → ℝ` is measurable with respect to the
pullback σ-algebra `mE.comap X = σ(X)`, then the Doob-Dynkin factorization theorem
`Measurable.exists_eq_measurable_comp` provides a measurable map `φ : E → ℝ` such that
`Z = φ ∘ X`, equivalently `φ (X ω) = Z ω` for all `ω`. -/
recall Measurable.exists_eq_measurable_comp

variable {Ω : Type u} {E : Type v} [mE : MeasurableSpace E]
variable {X : Ω → E} {Z : Ω → ℝ}

/-- Equation (8.9) as a source-facing pointwise bridge: if `Z` is measurable with respect to
`σ(X)`, then the canonical factorization theorem yields a measurable `φ : E → ℝ` with
`φ (X ω) = Z ω` for all `ω`. -/
theorem exists_measurable_eq_comp_apply
    (hZ : Measurable[mE.comap X] Z) :
    ∃ φ : E → ℝ, Measurable φ ∧ ∀ ω, φ (X ω) = Z ω := by
  rcases hZ.exists_eq_measurable_comp with ⟨φ, hφ_meas, rfl⟩
  exact ⟨φ, hφ_meas, fun _ ↦ rfl⟩
