/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

-- Declarations for this item will be appended below by the statement pipeline.

/-- The integral group ring of the free group on `X`. -/
abbrev FreeGroupRing (X : Type u) := MonoidAlgebra ℤ (FreeGroup X)

variable {X : Type u}

section

local notation "R" => FreeGroupRing X
local notation "ε" => Bialgebra.counitAlgHom ℤ R

/-- Definition 1-10-4: a Fox derivation of the integral group ring of the free group on `X` is a
`ℤ`-linear endomorphism satisfying the Fox product rule
`D (u * v) = ε(v) • D u + u * D v` for all `u` and `v`, where `ε` is the augmentation morphism of
the group ring. This rule already forces `D 1 = 0`; see `IsFoxDerivation.map_one_eq_zero`. -/
def IsFoxDerivation (D : Module.End ℤ (FreeGroupRing X)) : Prop :=
  ∀ u v : R, D (u * v) = ε v • D u + u * D v

namespace IsFoxDerivation

/-- A Fox derivation annihilates the multiplicative unit. -/
theorem map_one_eq_zero {D : Module.End ℤ (FreeGroupRing X)} (hD : IsFoxDerivation D) :
    D 1 = 0 :=
  by
    have h : D 1 + D 1 = D 1 + 0 := by
      simpa [add_comm] using (hD 1 1).symm
    exact add_left_cancel h

end IsFoxDerivation

end
