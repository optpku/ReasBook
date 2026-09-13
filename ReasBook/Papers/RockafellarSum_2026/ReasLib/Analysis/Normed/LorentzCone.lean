/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Lorentz energy

This module defines the Lorentz energy in positive and negative coordinates.
-/

@[expose] public section

universe u

namespace Lorentz

/-- The Lorentz energy `P ^ 2 - ‖N‖ ^ 2` of a point `(P, N)`. -/
def energy {H0 : Type u} [Norm H0] (x : ℝ × H0) : ℝ :=
  x.1 ^ 2 - ‖x.2‖ ^ 2

/-- The Lorentz energy in product coordinates. -/
theorem energy_apply {H0 : Type u} [Norm H0] (P : ℝ) (N : H0) :
    energy (P, N) = P ^ 2 - ‖N‖ ^ 2 := by
  -- Product projections reduce the energy to its coordinate formula.
  rfl

end Lorentz
