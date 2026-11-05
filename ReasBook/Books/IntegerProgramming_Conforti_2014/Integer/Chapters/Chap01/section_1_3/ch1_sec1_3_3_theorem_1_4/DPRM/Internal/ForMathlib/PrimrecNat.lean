/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import Mathlib.Computability.Primrec.Basic

/-!
# Natural-number exponentiation is primitive recursive

A companion one-liner to issue #36, kept in a separate file so the integer layer stays
exactly what it says it is.

`Mathlib/Computability/Primrec/Basic.lean` lifts `Nat.Primrec.add`, `.sub` and `.mul` to
`Primrec₂` as `Primrec.nat_add`, `Primrec.nat_sub`, `Primrec.nat_mul`, but never lifts
`Nat.Primrec.pow`, which is proved right beside them. This is that missing lemma.
-/

@[expose] public section

namespace Primrec

/-- Exponentiation of naturals is primitive recursive. -/
theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

end Primrec
