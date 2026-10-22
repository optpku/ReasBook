/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

-- Proof sketch: apply `measurable_pi_iff` to the map `f : Ω → Fin n → ℝ`, viewing `ℝ^n` as the
-- finite product `Fin n → ℝ` with its product measurable space.
/-- Theorem 1.90: a map `f : Ω → ℝ^n`, represented in Lean as `Ω → Fin n → ℝ`, is measurable
if and only if each coordinate map `ω ↦ f ω i` is measurable. -/
theorem measurable_fin_real_iff {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {f : Ω → Fin n → ℝ} :
    Measurable f ↔ ∀ i : Fin n, Measurable fun ω ↦ f ω i := by
  -- The product measurable structure on `Fin n → ℝ` is characterized by coordinate maps.
  simpa using
    (measurable_pi_iff : Measurable f ↔ ∀ i : Fin n, Measurable fun ω ↦ f ω i)

-- Proof sketch: use the same finite-product measurability criterion `measurable_pi_iff`, now for
-- the codomain `EReal`.
/-- The extended-real analogue of coordinatewise measurability for maps into `EReal^n`. -/
theorem measurable_fin_ereal_iff {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    {f : Ω → Fin n → EReal} :
    Measurable f ↔ ∀ i : Fin n, Measurable fun ω ↦ f ω i := by
  -- The same coordinatewise criterion applies to the finite product `Fin n → EReal`.
  simpa using
    (measurable_pi_iff : Measurable f ↔ ∀ i : Fin n, Measurable fun ω ↦ f ω i)
