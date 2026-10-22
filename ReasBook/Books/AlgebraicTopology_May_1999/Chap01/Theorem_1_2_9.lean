/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

noncomputable section

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Theorem 1.2.9: `π₁(X, x) = Path.Homotopic.Quotient x x` carries the group structure induced by
path composition, with unit the constant loop class and inverse given by path reversal. -/
instance loop_homotopy_group (x : X) : Group (Path.Homotopic.Quotient x x) := by
  change Group (FundamentalGroup X x)
  infer_instance

/-- Group multiplication on loop classes is induced by path composition. -/
theorem loop_homotopy_mul_eq_trans (γ δ : Path.Homotopic.Quotient x x) :
    γ * δ = δ.trans γ := rfl

/-- The identity element in the loop-class group is the constant loop class. -/
theorem loop_homotopy_one_eq_refl :
    (1 : Path.Homotopic.Quotient x x) = refl x := rfl

/-- Inversion in the loop-class group is induced by reversing paths. -/
theorem loop_homotopy_inv_eq_symm (γ : Path.Homotopic.Quotient x x) :
    γ⁻¹ = γ.symm := rfl
