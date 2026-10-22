/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

/-- The Section 7 owner vocabulary for a basis letter together with its exponent sign. -/
abbrev SignedLetter (X : Type u) := X × Bool

namespace SignedLetter

variable {X : Type u}

/-- Inverting a signed letter toggles its sign. -/
def inv (x : SignedLetter X) : SignedLetter X :=
  (x.1, !x.2)

instance : Inv (SignedLetter X) :=
  ⟨inv⟩

@[simp] theorem inv_def (x : SignedLetter X) : x⁻¹ = (x.1, !x.2) :=
  rfl

@[simp] theorem inv_inv (x : SignedLetter X) : x⁻¹⁻¹ = x := by
  cases x
  simp

end SignedLetter
