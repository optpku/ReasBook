/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_11.Toeplitz
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Fin.Basic

public section

universe u

variable {α : Type u} [Zero α]

/-- The explicit circulant-extension vector
`(t 0, t 1, ..., t (n - 1), 0, t (1 - n), ..., t (-1))`. -/
def circulantExtensionVector (n : ℕ) (t : ℤ → α) : Fin (2 * n) → α :=
  fun i ↦
    if (i : ℕ) < n then
      t (i : ℕ)
    else if (i : ℕ) = n then
      0
    else
      t (((i : ℕ) : ℤ) - (2 * n : ℤ))

/-- The length-`2 * n` zero-padding of `v`, with `v` on the first `n` entries
and `0` on the remaining `n` entries. -/
def zeroPadVector (n : ℕ) (v : Fin n → α) : Fin (2 * n) → α :=
  fun i ↦
    if hlt : (i : ℕ) < n then
      v ⟨i, hlt⟩
    else
      0

/-- The defining piecewise formula for `circulantExtensionVector`. -/
theorem circulantExtensionVector_apply (n : ℕ) (t : ℤ → α) (i : Fin (2 * n)) :
    circulantExtensionVector n t i =
      if hlt : (i : ℕ) < n then
        t (i : ℕ)
      else if hmid : (i : ℕ) = n then
        0
      else
        t (((i : ℕ) : ℤ) - (2 * n : ℤ)) := by
  -- Read the vector entry directly from the defining piecewise formula.
  rfl

/-- The defining piecewise formula for `zeroPadVector`. -/
theorem zeroPadVector_apply (n : ℕ) (v : Fin n → α) (i : Fin (2 * n)) :
    zeroPadVector n v i =
      if hlt : (i : ℕ) < n then
        v ⟨i, hlt⟩
      else
        0 := by
  rfl
