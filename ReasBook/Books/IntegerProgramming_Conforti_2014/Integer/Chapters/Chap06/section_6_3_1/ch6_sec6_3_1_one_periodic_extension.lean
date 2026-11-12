/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.Field.Periodic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean

/-- Extend a function on the fundamental interval `[0, 1)` to a `1`-periodic function on `ℝ`
by precomposing with `Int.fract`. -/
noncomputable def onePeriodicExtension {α : Type*} (φ : ℝ → α) : ℝ → α :=
  φ ∘ Int.fract

/-- Unfolding formula for `onePeriodicExtension`. -/
@[simp] theorem onePeriodicExtension_apply {α : Type*} (φ : ℝ → α) (r : ℝ) :
    onePeriodicExtension φ r = φ (Int.fract r) :=
  rfl

/-- On the fundamental interval `[0, 1)`, `onePeriodicExtension φ` agrees with `φ`. -/
theorem onePeriodicExtension_eq_on_Ico {α : Type*} (φ : ℝ → α) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    onePeriodicExtension φ u = φ u := by
  simp [Int.fract_eq_self.2 ⟨hu0, hu1⟩]

/-- The function `onePeriodicExtension φ` has period `1`. -/
theorem onePeriodicExtension_periodic {α : Type*} (φ : ℝ → α) :
    Function.Periodic (onePeriodicExtension φ) 1 :=
  (Int.fract_periodic ℝ).comp φ
