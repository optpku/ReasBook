/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_9.PeriodicExtension
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.BTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_27.BCCB
import Mathlib.Tactic

public section

open scoped Matrix

universe u

namespace Matrix

variable {α : Type u} [Zero α]

/-- The centered odd-grid index used to interpret an offset `d : ℤ` inside a
`(2 * n - 1)`-point kernel window. It returns `none` exactly outside the source
offset range `[-(n - 1), n - 1]`. -/
def oddKernelIndex (n : ℕ) (d : ℤ) : Option (Fin (2 * n - 1)) :=
  let k := d + (n - 1 : ℤ)
  if hk : 0 ≤ k ∧ k < 2 * n - 1 then
    some ⟨Int.toNat k, by
      have hk0 : 0 ≤ k := hk.1
      have hk1 : k < 2 * n - 1 := hk.2
      have hcast : (Int.toNat k : ℤ) = k := by
        simp [Int.toNat_of_nonneg hk0]
      omega⟩
  else
    none

/-- The integer-indexed kernel induced by a centered odd-grid array
`t : α^[2 * n_x - 1, 2 * n_y - 1]`. Outside the displayed odd-grid window the
kernel is zero. -/
def oddKernel {n_x n_y : ℕ}
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α) :
    ℤ → ℤ → α :=
  fun d_x d_y ↦
    match oddKernelIndex n_x d_x, oddKernelIndex n_y d_y with
    | some i, some j => t i j
    | _, _ => 0

/-- The defining reduction formula for `Matrix.oddKernel`. -/
theorem oddKernel_apply {n_x n_y : ℕ}
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α)
    (d_x d_y : ℤ) :
    Matrix.oddKernel t d_x d_y =
      match Matrix.oddKernelIndex n_x d_x, Matrix.oddKernelIndex n_y d_y with
      | some i, some j => t i j
      | _, _ => 0 := by
  rfl

/-- The doubled-grid index used in `(5.61)`-`(5.63)`: the first `n` entries
record the nonnegative offsets, the middle index is the inserted zero, and the
remaining entries record the negative offsets. -/
def blockCirculantExtensionIndex (n : ℕ) (i : Fin (2 * n)) :
    Option (Fin (2 * n - 1)) :=
  if hi : (i : ℕ) < n then
    some ⟨i.1 + (n - 1), by
      omega⟩
  else if hmid : (i : ℕ) = n then
    none
  else
    some ⟨i.1 - (n + 1), by
      omega⟩

/-- The doubled `2 * n_x × 2 * n_y` block-circulant-extension array `cExt`
assembled from the centered odd-grid kernel `t` by `(5.61)`-`(5.63)`. -/
def blockCirculantExtension {n_x n_y : ℕ}
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α) :
    Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) α :=
  fun i j ↦
    match blockCirculantExtensionIndex n_x i, blockCirculantExtensionIndex n_y j with
    | some i', some j' => t i' j'
    | _, _ => 0

/-- The defining placement formula for `Matrix.blockCirculantExtension`. -/
theorem blockCirculantExtension_apply {n_x n_y : ℕ}
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α)
    (i : Fin (2 * n_x)) (j : Fin (2 * n_y)) :
    Matrix.blockCirculantExtension t i j =
      match Matrix.blockCirculantExtensionIndex n_x i,
          Matrix.blockCirculantExtensionIndex n_y j with
      | some i', some j' => t i' j'
      | _, _ => 0 := by
  rfl

/-- Helper for `Matrix.bttb_oddKernel_apply`: a source-grid difference lands in
the centered odd-kernel window at the explicit source entry. -/
private theorem oddKernelIndex_eq_some_of_baseDifference {n : ℕ}
    (i k : Fin n) :
    Matrix.oddKernelIndex n ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) =
      some ⟨i.1 + (n - 1 - k.1), by omega⟩ := by
  let d : ℤ := (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ))
  have hd :
      0 ≤ d + (n - 1 : ℤ) ∧ d + (n - 1 : ℤ) < 2 * n - 1 := by
    -- Base-grid differences stay inside the displayed odd-kernel window.
    dsimp [d]
    omega
  -- Unfold the owner and evaluate the in-window branch at the explicit offset.
  rw [Matrix.oddKernelIndex]
  simp [d, hd]
  have htoNat :
      Int.toNat ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) + (n - 1 : ℤ)) =
        i.1 + (n - 1 - k.1) := by
    -- The centered offset is already the natural source-grid index.
    have hEq :
        (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) + (n - 1 : ℤ) =
          (i.1 + (n - 1 - k.1) : ℕ) := by
      omega
    calc
      Int.toNat ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) + (n - 1 : ℤ)) =
          Int.toNat ((i.1 + (n - 1 - k.1) : ℕ) : ℤ) := congrArg Int.toNat hEq
      _ = i.1 + (n - 1 - k.1) := by
            rw [Int.toNat_natCast]
  simpa using htoNat

/-- The centered odd-grid interpretation matches the direct source BTTB entry
formula on the original `n_x × n_y` grid. -/
theorem bttb_oddKernel_apply {n_x n_y : ℕ}
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α)
    (j l : Fin n_y) (i k : Fin n_x) :
    Matrix.bttb n_x n_y (Matrix.oddKernel t) (j, i) (l, k) =
      t ⟨i.1 + (n_x - 1 - k.1), by omega⟩
        ⟨j.1 + (n_y - 1 - l.1), by omega⟩ := by
  -- Expand the BTTB entry and normalize both odd-kernel indices to the
  -- explicit source-grid offsets.
  rw [Matrix.bttb_apply, Matrix.oddKernel_apply]
  rw [oddKernelIndex_eq_some_of_baseDifference i k]
  rw [oddKernelIndex_eq_some_of_baseDifference j l]

/-- Helper for `Matrix.periodicExtension_blockCirculantExtension_apply_baseDifferences`:
reducing a source-grid difference modulo the doubled grid lands in the explicit
block-circulant-extension source entry. -/
private theorem blockCirculantExtensionIndex_eq_some_of_periodicBaseDifference
    {n : ℕ} [NeZero (2 * n)] (i k : Fin n) :
    Matrix.blockCirculantExtensionIndex n
        (DiscreteSignal.periodicIndexOfNeZero
          ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ)) =
      some ⟨i.1 + (n - 1 - k.1), by omega⟩ := by
  let d : ℤ := (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ))
  have hdLower : -((n - 1 : ℕ) : ℤ) ≤ d := by
    -- Every source-grid difference is bounded below by `-(n - 1)`.
    dsimp [d]
    omega
  have hdUpper : d ≤ n - 1 := by
    -- Every source-grid difference is bounded above by `n - 1`.
    dsimp [d]
    omega
  by_cases hnonneg : 0 ≤ d
  · have hval :
        ((DiscreteSignal.periodicIndexOfNeZero d : Fin (2 * n)) : ℕ) = Int.toNat d := by
      -- Nonnegative base differences reduce to themselves modulo the doubled period.
      have hmod : d % (2 * n) = d := by
        rw [Int.emod_eq_of_lt] <;> omega
      simpa [hmod] using (DiscreteSignal.periodicIndexOfNeZero_val (n := 2 * n) d)
    have hlt :
        ((DiscreteSignal.periodicIndexOfNeZero d : Fin (2 * n)) : ℕ) < n := by
      have hdlt : d < n := by omega
      rw [hval]
      exact (Int.toNat_lt_of_ne_zero (show n ≠ 0 by omega)).2 hdlt
    have hval' :
        ((DiscreteSignal.periodicIndexOfNeZero
            ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) : Fin (2 * n)) : ℕ) =
          Int.toNat d := by
      simpa [d] using hval
    -- The nonnegative branch of the owner already gives the explicit source index.
    rw [Matrix.blockCirculantExtensionIndex]
    split_ifs with hlt'
    · apply congrArg some
      apply Fin.ext
      change
        ((DiscreteSignal.periodicIndexOfNeZero
            ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) : Fin (2 * n)) : ℕ) + (n - 1) =
          i.1 + (n - 1 - k.1)
      rw [hval']
      have htoNat : Int.toNat d = i.1 - k.1 := by
        have hEq : d = (i.1 - k.1 : ℕ) := by
          dsimp [d]
          omega
        calc
          Int.toNat d = Int.toNat ((i.1 - k.1 : ℕ) : ℤ) := congrArg Int.toNat hEq
          _ = i.1 - k.1 := by
                rw [Int.toNat_natCast]
      rw [htoNat]
      omega
    · exact False.elim (hlt' hlt)
  · have hdneg : d < 0 := by omega
    have hmod :
        d % (2 * n) = d + 2 * n := by
      -- Negative base differences wrap once around the doubled period.
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega
    have hval :
        ((DiscreteSignal.periodicIndexOfNeZero d : Fin (2 * n)) : ℕ) =
          Int.toNat (d + 2 * n) := by
      simpa [hmod] using (DiscreteSignal.periodicIndexOfNeZero_val (n := 2 * n) d)
    have hnotLt :
        ¬ ((DiscreteSignal.periodicIndexOfNeZero d : Fin (2 * n)) : ℕ) < n := by
      intro hlt
      have hltInt : d + 2 * n < n := by
        rw [hval] at hlt
        exact (Int.toNat_lt_of_ne_zero (show n ≠ 0 by omega)).1 hlt
      omega
    have hnotMid :
        ¬ ((DiscreteSignal.periodicIndexOfNeZero d : Fin (2 * n)) : ℕ) = n := by
      intro hmid
      have hmidInt : d + 2 * n = n := by
        have hmidNat : Int.toNat (d + 2 * n) = n := by
          simpa [hval] using hmid
        have := congrArg (fun m : ℕ ↦ (m : ℤ)) hmidNat
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ d + 2 * n)] at this
        exact this
      omega
    have hval' :
        ((DiscreteSignal.periodicIndexOfNeZero
            ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) : Fin (2 * n)) : ℕ) =
          Int.toNat (d + 2 * n) := by
      simpa [d] using hval
    -- The wrapped negative branch also lands at the same explicit source index.
    rw [Matrix.blockCirculantExtensionIndex]
    split_ifs with hlt'
    · exact (False.elim <| hnotLt hlt')
    · apply congrArg some
      apply Fin.ext
      have htoNat : Int.toNat (d + 2 * n) = i.1 + (2 * n - k.1) := by
        have hEq : d + 2 * n = (i.1 + (2 * n - k.1) : ℕ) := by
          dsimp [d]
          omega
        calc
          Int.toNat (d + 2 * n) = Int.toNat ((i.1 + (2 * n - k.1) : ℕ) : ℤ) :=
              congrArg Int.toNat hEq
          _ = i.1 + (2 * n - k.1) := by
                rw [Int.toNat_natCast]
      change
        ((DiscreteSignal.periodicIndexOfNeZero
            ((((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) : Fin (2 * n)) : ℕ) - (n + 1) =
          i.1 + (n - 1 - k.1)
      rw [hval']
      rw [htoNat]
      omega

/-- Periodizing the doubled block-circulant extension and evaluating it on a
source-grid difference pair recovers the explicit source entry of `t`. -/
theorem periodicExtension_blockCirculantExtension_apply_baseDifferences
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (t : Matrix (Fin (2 * n_x - 1)) (Fin (2 * n_y - 1)) α)
    (i k : Fin n_x) (j l : Fin n_y) :
    Matrix.periodicExtensionOfNeZero (Matrix.blockCirculantExtension t)
      (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ))
      (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) =
      t ⟨i.1 + (n_x - 1 - k.1), by omega⟩
        ⟨j.1 + (n_y - 1 - l.1), by omega⟩ := by
  -- Reduce the periodized doubled-grid kernel to the wrapped doubled indices.
  rw [Matrix.periodicExtensionOfNeZero_apply, Matrix.blockCirculantExtension_apply]
  -- Then normalize each wrapped doubled-grid index to the explicit source entry.
  rw [blockCirculantExtensionIndex_eq_some_of_periodicBaseDifference i k]
  rw [blockCirculantExtensionIndex_eq_some_of_periodicBaseDifference j l]

end Matrix
