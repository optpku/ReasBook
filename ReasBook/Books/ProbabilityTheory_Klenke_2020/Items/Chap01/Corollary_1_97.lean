/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped MeasureTheory

variable {Ω : Type u} {Ω' : Type v}
variable [Nonempty Ω] [mΩ' : MeasurableSpace Ω']

-- Proof sketch: for the forward implication, apply
-- `Measurable.exists_eq_measurable_comp` to the map `g` viewed as measurable on the pullback
-- measurable space `mΩ'.comap f`. For the converse, compose the measurable factor `φ` with the
-- pullback-measurable map `f` using `Measurable.comp`.
/-- Corollary 1.97: A map `g : Ω → EReal` is `σ(f)`-measurable, meaning measurable for the
pullback `σ`-algebra `mΩ'.comap f`, if and only if there is a measurable map `φ : Ω' → EReal`
such that `g = φ ∘ f`. -/
theorem measurable_iff_exists_measurable_comp_of_comap {f : Ω → Ω'} {g : Ω → EReal} :
    Measurable[mΩ'.comap f] g ↔ ∃ φ : Ω' → EReal, Measurable φ ∧ g = φ ∘ f := by
  constructor
  · intro hg
    -- The forward direction is exactly the factorization theorem for pullback measurability.
    simpa [Function.comp] using hg.exists_eq_measurable_comp (f := f)
  · rintro ⟨φ, hφ, rfl⟩
    -- The converse uses that `f` is measurable from the pullback `σ`-algebra by construction.
    exact hφ.comp (comap_measurable f)
