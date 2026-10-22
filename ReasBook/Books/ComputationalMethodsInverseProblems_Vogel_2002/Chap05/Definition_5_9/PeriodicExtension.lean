/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_4.PeriodicExtension
public import Mathlib.Data.Matrix.Basic

public section

open scoped Matrix

universe u

namespace Matrix

variable {α : Type u}

/-- A two-dimensional integer-indexed array is `(n_x, n_y)`-periodic when each coordinate is
periodic with the corresponding period. -/
def IsPeriodic (n_x n_y : ℕ) (t : ℤ → ℤ → α) : Prop :=
  (∀ j, Function.Periodic (fun i ↦ t i j) (n_x : ℤ)) ∧
    ∀ i, Function.Periodic (t i) (n_y : ℤ)

/-- `Matrix.IsPeriodic n_x n_y t` means periodicity in each coordinate with the matching
side length. -/
theorem isPeriodic_iff {n_x n_y : ℕ} {t : ℤ → ℤ → α} :
    IsPeriodic n_x n_y t ↔
      (∀ j, Function.Periodic (fun i ↦ t i j) (n_x : ℤ)) ∧
        ∀ i, Function.Periodic (t i) (n_y : ℤ) := by
  rfl

/-- The first-coordinate periodicity extracted from `Matrix.IsPeriodic`. -/
theorem periodicX {n_x n_y : ℕ} {t : ℤ → ℤ → α} (h : IsPeriodic n_x n_y t) :
    ∀ j, Function.Periodic (fun i ↦ t i j) (n_x : ℤ) :=
  isPeriodic_iff.mp h |>.1

/-- The second-coordinate periodicity extracted from `Matrix.IsPeriodic`. -/
theorem periodicY {n_x n_y : ℕ} {t : ℤ → ℤ → α} (h : IsPeriodic n_x n_y t) :
    ∀ i, Function.Periodic (t i) (n_y : ℤ) :=
  isPeriodic_iff.mp h |>.2

/-- The periodic extension of a finite `n_x × n_y` array to integer indices. -/
def periodicExtension {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (t : Matrix (Fin n_x) (Fin n_y) α) :
    ℤ → ℤ → α :=
  fun i j ↦ t (DiscreteSignal.periodicIndex n_x h_x i) (DiscreteSignal.periodicIndex n_y h_y j)

/-- The `[NeZero]` entry point for `Matrix.periodicExtension`, hiding the positivity witnesses. -/
abbrev periodicExtensionOfNeZero {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (t : Matrix (Fin n_x) (Fin n_y) α) : ℤ → ℤ → α :=
  periodicExtension n_x.pos_of_neZero n_y.pos_of_neZero t

/-- The defining reduced-index formula for `Matrix.periodicExtension`. -/
theorem periodicExtension_apply {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (t : Matrix (Fin n_x) (Fin n_y) α)
    (i j : ℤ) :
    periodicExtension h_x h_y t i j =
      t (DiscreteSignal.periodicIndex n_x h_x i) (DiscreteSignal.periodicIndex n_y h_y j) := by
  simp [periodicExtension]

/-- The periodic extension agrees with the original array on the base `Fin n_x × Fin n_y`
window. -/
theorem periodicExtension_apply_natCast {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (t : Matrix (Fin n_x) (Fin n_y) α)
    (i : Fin n_x) (j : Fin n_y) :
    periodicExtension h_x h_y t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) = t i j := by
  simp [periodicExtension, DiscreteSignal.periodicIndex_natCast h_x i,
    DiscreteSignal.periodicIndex_natCast h_y j]

/-- The reduced-index formula for `Matrix.periodicExtensionOfNeZero`. -/
theorem periodicExtensionOfNeZero_apply {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (t : Matrix (Fin n_x) (Fin n_y) α) (i j : ℤ) :
    periodicExtensionOfNeZero t i j =
      t (DiscreteSignal.periodicIndexOfNeZero i) (DiscreteSignal.periodicIndexOfNeZero j) := by
  simpa [periodicExtensionOfNeZero, DiscreteSignal.periodicIndexOfNeZero] using
    periodicExtension_apply n_x.pos_of_neZero n_y.pos_of_neZero t i j

/-- The `[NeZero]` periodic extension agrees with the original array on the base window. -/
theorem periodicExtensionOfNeZero_apply_natCast {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (t : Matrix (Fin n_x) (Fin n_y) α) (i : Fin n_x) (j : Fin n_y) :
    periodicExtensionOfNeZero t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) = t i j := by
  simpa [periodicExtensionOfNeZero] using
    periodicExtension_apply_natCast n_x.pos_of_neZero n_y.pos_of_neZero t i j

/-- Adding one full period does not change the reduced `Fin` index. -/
theorem periodicIndex_add_period {n : ℕ} (h : 0 < n) (k : ℤ) :
    DiscreteSignal.periodicIndex n h (k + n) = DiscreteSignal.periodicIndex n h k := by
  apply Fin.ext
  -- Compare the two reduced indices through their explicit natural-value formula.
  rw [DiscreteSignal.periodicIndex_val, DiscreteSignal.periodicIndex_val]
  simp [Int.add_emod_right]

/-- The periodic extension is periodic in both coordinate directions. -/
theorem periodicExtension_isPeriodic {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (t : Matrix (Fin n_x) (Fin n_y) α) :
    IsPeriodic n_x n_y (periodicExtension h_x h_y t) := by
  -- Reduce two-dimensional periodicity to the independent periodicity of each coordinate.
  refine isPeriodic_iff.mpr ⟨?_, ?_⟩
  · intro j i
    -- Adding one horizontal period leaves the reduced `Fin n_x` index unchanged.
    simp [periodicExtension, periodicIndex_add_period h_x i]
  · intro i j
    -- Adding one vertical period leaves the reduced `Fin n_y` index unchanged.
    simp [periodicExtension, periodicIndex_add_period h_y j]

/-- The `[NeZero]` periodic extension is periodic in both coordinate directions. -/
theorem periodicExtensionOfNeZero_isPeriodic {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (t : Matrix (Fin n_x) (Fin n_y) α) :
    IsPeriodic n_x n_y (periodicExtensionOfNeZero t) := by
  simpa [periodicExtensionOfNeZero] using
    periodicExtension_isPeriodic n_x.pos_of_neZero n_y.pos_of_neZero t

end Matrix
