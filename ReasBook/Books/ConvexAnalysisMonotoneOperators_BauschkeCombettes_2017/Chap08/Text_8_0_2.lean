/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {H : Type u} [SMul ℝ H]

/-- Text 8.0.2: the Minkowski gauge of a subset `C` is the `]-∞,+∞]`-valued function sending
`x` to the infimum of the positive real numbers `ξ` such that `x ∈ ξ C`. -/
noncomputable def minkowskiGauge (C : Set H) : H → EReal :=
  fun x ↦ sInf (Real.toEReal '' {ξ : ℝ | 0 < ξ ∧ x ∈ ξ • C})

notation "m[" C "]" => minkowskiGauge C

/-- The textbook Minkowski gauge is the infimum of the positive real scalings that contain the
point. -/
-- Proof sketch: unfold `minkowskiGauge`; the statement is exactly its defining equation.
theorem minkowskiGauge_eq_sInf (C : Set H) (x : H) :
    m[C] x = sInf (Real.toEReal '' {ξ : ℝ | 0 < ξ ∧ x ∈ ξ • C}) := by
  -- The notation `m[C]` is just `minkowskiGauge C`.
  -- Unfolding the definition yields exactly the claimed infimum formula.
  rfl

end
