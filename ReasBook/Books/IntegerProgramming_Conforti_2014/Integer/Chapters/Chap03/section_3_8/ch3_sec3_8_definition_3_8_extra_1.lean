/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

open scoped Matrix

/-- Definition 3.8-extra-1. A linear inequality `c ⬝ᵥ x ≤ δ` is valid for `P` if it holds for
every `x ∈ P`. -/
def is_valid_inequality {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (c : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ ⦃x : ι → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ

/-- `is_valid_inequality` unfolds to the pointwise validity condition on `P`. -/
theorem is_valid_inequality_iff
    {ι : Type*} [Fintype ι] {P : Set (ι → ℝ)} {c : ι → ℝ} {δ : ℝ} :
    is_valid_inequality P c δ ↔ ∀ ⦃x : ι → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ := by
  rfl
