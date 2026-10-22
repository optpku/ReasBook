/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.ModEq

public section

universe u

namespace Function

variable {α : Type u}

/-- An integer-periodic sequence takes equal values on congruent indices modulo its period. -/
theorem Periodic.eq_of_modEq {n : ℕ} {t : ℤ → α} (h : Periodic t (n : ℤ))
    {i j : ℤ} (hij : i ≡ j [ZMOD n]) : t i = t j := by
  -- Rewrite the congruence as an integer shift by a multiple of the period.
  rcases Int.modEq_iff_add_fac.mp hij with ⟨m, rfl⟩
  -- Periodicity along integer multiples reduces the shifted value back to `t i`.
  simpa [mul_comm] using (h.int_mul m i).symm

/-- A sequence whose values agree on every congruence class modulo `n` is `n`-periodic. -/
theorem periodic_of_modEq {n : ℕ} {t : ℤ → α}
    (h : ∀ i j, i ≡ j [ZMOD n] → t i = t j) : Periodic t (n : ℤ) := by
  intro i
  -- One period shift preserves the residue class modulo `n`.
  have hshift : i + n ≡ i [ZMOD n] := by
    exact Int.add_modEq_right (a := i) (n := (n : ℤ))
  exact h (i + n) i hshift

end Function

namespace DiscreteSignal

variable {α : Type u}

/-- Reduce an integer index modulo a positive period to obtain a `Fin n` index. -/
def periodicIndex (n : ℕ) (h : 0 < n) (k : ℤ) : Fin n :=
  @Fin.ofNat n ⟨Nat.ne_of_gt h⟩ (Int.toNat (k % n))

/-- The reduced-value formula for `DiscreteSignal.periodicIndex`. -/
theorem periodicIndex_val (n : ℕ) (h : 0 < n) (k : ℤ) :
    ((periodicIndex n h k : Fin n) : ℕ) = Int.toNat (k % n) := by
  have hlt : Int.toNat (k % n) < n := by
    rw [Int.toNat_lt_of_ne_zero (Nat.ne_of_gt h)]
    exact Int.emod_lt_of_pos _ (Int.ofNat_lt.mpr h)
  -- Rewrite the `Fin.ofNat` constructor to its canonical natural representative.
  calc
    ((periodicIndex n h k : Fin n) : ℕ) = Int.toNat (k % n) % n := by
      simp [periodicIndex]
    _ = Int.toNat (k % n) := Nat.mod_eq_of_lt hlt

/-- Reducing an index already in the base `Fin n` window leaves it unchanged. -/
theorem periodicIndex_natCast {n : ℕ} (h : 0 < n) (i : Fin n) :
    periodicIndex n h ((i : ℕ) : ℤ) = i := by
  apply Fin.ext
  -- Compare both `Fin` values through the explicit residue formula.
  rw [periodicIndex_val]
  have hmod : (((i : ℕ) : ℤ) % n) = i := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg i) (Int.ofNat_lt.mpr i.isLt)
  simpa using congrArg Int.toNat hmod

/-- Extend a finite vector to an integer-indexed periodic sequence by reducing indices modulo
its length. -/
def periodicExtension {n : ℕ} (h : 0 < n) (t : Fin n → α) : ℤ → α :=
  fun i ↦ t (periodicIndex n h i)

/-- The defining reduced-index formula for `DiscreteSignal.periodicExtension`. -/
theorem periodicExtension_apply {n : ℕ} (h : 0 < n) (t : Fin n → α) (i : ℤ) :
    periodicExtension h t i = t (periodicIndex n h i) := by
  -- Unfold the extension owner to expose the reduced index.
  simp [periodicExtension]

/-- The periodic extension agrees with the original vector on the base `Fin n` window. -/
theorem periodicExtension_apply_natCast {n : ℕ} (h : 0 < n) (t : Fin n → α) (i : Fin n) :
    periodicExtension h t ((i : ℕ) : ℤ) = t i := by
  simp [periodicExtension, periodicIndex_natCast h i]

/-- Helper for Definition 5.4: adding one full period does not change the reduced `Fin` index.
-/
theorem periodicIndex_add_period {n : ℕ} (h : 0 < n) (k : ℤ) :
    periodicIndex n h (k + n) = periodicIndex n h k := by
  apply Fin.ext
  -- Compare the two reduced indices through their explicit natural-value formula.
  rw [periodicIndex_val, periodicIndex_val]
  simp [Int.add_emod_right]

/-- The periodic extension is periodic with period `n`. -/
theorem periodicExtension_isPeriodic {n : ℕ} (h : 0 < n) (t : Fin n → α) :
    Function.Periodic (periodicExtension h t) (n : ℤ) := by
  intro i
  -- A full-period shift leaves the reduced `Fin` index unchanged.
  simp [periodicExtension, periodicIndex_add_period h i]

/-- The `[NeZero n]` entry point for `DiscreteSignal.periodicExtension`, hiding the
positivity witness. -/
abbrev periodicExtensionOfNeZero {n : ℕ} [NeZero n] (t : Fin n → α) : ℤ → α :=
  periodicExtension n.pos_of_neZero t

/-- Reduce an integer index modulo a nonzero period to obtain a `Fin n` index. -/
abbrev periodicIndexOfNeZero {n : ℕ} [NeZero n] (k : ℤ) : Fin n :=
  periodicIndex n n.pos_of_neZero k

/-- The reduced-value formula for `DiscreteSignal.periodicIndexOfNeZero`. -/
theorem periodicIndexOfNeZero_val {n : ℕ} [NeZero n] (k : ℤ) :
    ((periodicIndexOfNeZero k : Fin n) : ℕ) = Int.toNat (k % n) := by
  simpa [periodicIndexOfNeZero] using periodicIndex_val n n.pos_of_neZero k

/-- Reducing an index already in the base `Fin n` window leaves it unchanged. -/
theorem periodicIndexOfNeZero_natCast {n : ℕ} [NeZero n] (i : Fin n) :
    periodicIndexOfNeZero ((i : ℕ) : ℤ) = i := by
  simpa [periodicIndexOfNeZero] using periodicIndex_natCast n.pos_of_neZero i

/-- The reduced-index formula for `DiscreteSignal.periodicExtensionOfNeZero`. -/
theorem periodicExtensionOfNeZero_apply {n : ℕ} [NeZero n] (t : Fin n → α) (i : ℤ) :
    periodicExtensionOfNeZero t i = t (periodicIndexOfNeZero i) := by
  simpa [periodicExtensionOfNeZero] using periodicExtension_apply n.pos_of_neZero t i

/-- The `[NeZero n]` periodic extension agrees with the original vector on the base window. -/
theorem periodicExtensionOfNeZero_apply_natCast {n : ℕ} [NeZero n]
    (t : Fin n → α) (i : Fin n) : periodicExtensionOfNeZero t ((i : ℕ) : ℤ) = t i := by
  simpa [periodicExtensionOfNeZero, periodicIndexOfNeZero_natCast] using
    periodicExtension_apply_natCast n.pos_of_neZero t i

/-- The `[NeZero n]` periodic extension is periodic with period `n`. -/
theorem periodicExtensionOfNeZero_isPeriodic {n : ℕ} [NeZero n] (t : Fin n → α) :
    Function.Periodic (periodicExtensionOfNeZero t) (n : ℤ) := by
  simpa [periodicExtensionOfNeZero] using periodicExtension_isPeriodic n.pos_of_neZero t

end DiscreteSignal
