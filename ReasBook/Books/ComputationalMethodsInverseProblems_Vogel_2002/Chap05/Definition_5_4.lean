/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Int.ModEq

public section

universe u

namespace Function

variable {α : Type u}

/-- Helper for Definition 5.4: an integer-periodic sequence takes equal values on congruent
indices modulo its period. -/
theorem Periodic.eq_of_modEq {n : ℕ} {t : ℤ → α} (h : Periodic t (n : ℤ))
    {i j : ℤ} (hij : i ≡ j [ZMOD n]) : t i = t j := by
  -- Rewrite the congruence as an integer shift by a multiple of the period.
  rcases Int.modEq_iff_add_fac.mp hij with ⟨m, rfl⟩
  -- Periodicity along integer multiples reduces the shifted value back to `t i`.
  simpa [mul_comm] using (h.int_mul m i).symm

/-- Helper for Definition 5.4: equality on each congruence class modulo `n` implies
`n`-periodicity. -/
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

-- Route correction: rehost the item-local periodic-extension API here so this target file
-- contains the actual proof surface for Definition 5.4.

/-- Helper for Definition 5.4: reduce an integer index modulo a positive period to obtain a
`Fin n` index. -/
def periodicIndex (n : ℕ) (h : 0 < n) (k : ℤ) : Fin n :=
  @Fin.ofNat n ⟨Nat.ne_of_gt h⟩ (Int.toNat (k % n))

/-- Helper for Definition 5.4: the reduced `Fin` index is represented by the natural residue
`Int.toNat (k % n)`. -/
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

/-- Helper for Definition 5.4: reducing an index already in the base `Fin n` window leaves it
unchanged. -/
theorem periodicIndex_natCast {n : ℕ} (h : 0 < n) (i : Fin n) :
    periodicIndex n h ((i : ℕ) : ℤ) = i := by
  apply Fin.ext
  -- Compare both `Fin` values through the explicit residue formula.
  rw [periodicIndex_val]
  have hmod : (((i : ℕ) : ℤ) % n) = i := by
    exact Int.emod_eq_of_lt (Int.natCast_nonneg i) (Int.ofNat_lt.mpr i.isLt)
  simpa using congrArg Int.toNat hmod

/-- Helper for Definition 5.4: extend a finite vector to an integer-indexed periodic sequence
by reducing indices modulo its length. -/
def periodicExtension {n : ℕ} (h : 0 < n) (t : Fin n → α) : ℤ → α :=
  fun i ↦ t (periodicIndex n h i)

/-- Helper for Definition 5.4: the periodic extension evaluates by reducing the input index to
`Fin n`. -/
theorem periodicExtension_apply {n : ℕ} (h : 0 < n) (t : Fin n → α) (i : ℤ) :
    periodicExtension h t i = t (periodicIndex n h i) := by
  -- Unfold the extension owner to expose the reduced index.
  simp [periodicExtension]

/-- Helper for Definition 5.4: the periodic extension agrees with the original vector on the
base `Fin n` window. -/
theorem periodicExtension_apply_natCast {n : ℕ} (h : 0 < n) (t : Fin n → α) (i : Fin n) :
    periodicExtension h t ((i : ℕ) : ℤ) = t i := by
  -- Reduce the base-window cast back to the original `Fin` index.
  simp [periodicExtension, periodicIndex_natCast h i]

/-- Helper for Definition 5.4: adding one full period does not change the reduced `Fin` index. -/
theorem periodicIndex_add_period {n : ℕ} (h : 0 < n) (k : ℤ) :
    periodicIndex n h (k + n) = periodicIndex n h k := by
  apply Fin.ext
  -- Compare the two reduced indices through their explicit natural-value formula.
  rw [periodicIndex_val, periodicIndex_val]
  simp [Int.add_emod_right]

/-- Helper for Definition 5.4: the periodic extension is periodic with period `n`. -/
theorem periodicExtension_isPeriodic {n : ℕ} (h : 0 < n) (t : Fin n → α) :
    Function.Periodic (periodicExtension h t) (n : ℤ) := by
  intro i
  -- A full-period shift leaves the reduced `Fin` index unchanged.
  simp [periodicExtension, periodicIndex_add_period h i]

/-- Helper for Definition 5.4: the `[NeZero n]` entry point for `periodicExtension`, hiding the
positivity witness. -/
abbrev periodicExtensionOfNeZero {n : ℕ} [NeZero n] (t : Fin n → α) : ℤ → α :=
  periodicExtension n.pos_of_neZero t

/-- Helper for Definition 5.4: reduce an integer index modulo a nonzero period to obtain a
`Fin n` index. -/
abbrev periodicIndexOfNeZero {n : ℕ} [NeZero n] (k : ℤ) : Fin n :=
  periodicIndex n n.pos_of_neZero k

/-- Helper for Definition 5.4: the reduced-value formula for `periodicIndexOfNeZero`. -/
theorem periodicIndexOfNeZero_val {n : ℕ} [NeZero n] (k : ℤ) :
    ((periodicIndexOfNeZero k : Fin n) : ℕ) = Int.toNat (k % n) := by
  -- Reuse the positive-period normalization through `n.pos_of_neZero`.
  simpa [periodicIndexOfNeZero] using periodicIndex_val n n.pos_of_neZero k

/-- Helper for Definition 5.4: reducing a base-window index modulo a nonzero period is the
identity. -/
theorem periodicIndexOfNeZero_natCast {n : ℕ} [NeZero n] (i : Fin n) :
    periodicIndexOfNeZero ((i : ℕ) : ℤ) = i := by
  -- Reuse the positive-period base-window compatibility lemma.
  simpa [periodicIndexOfNeZero] using periodicIndex_natCast n.pos_of_neZero i

/-- Helper for Definition 5.4: the `[NeZero n]` periodic extension evaluates by reducing the
input index modulo `n`. -/
theorem periodicExtensionOfNeZero_apply {n : ℕ} [NeZero n] (t : Fin n → α) (i : ℤ) :
    periodicExtensionOfNeZero t i = t (periodicIndexOfNeZero i) := by
  -- Unfold the nonzero-period wrapper back to the positive-period extension.
  simpa [periodicExtensionOfNeZero] using periodicExtension_apply n.pos_of_neZero t i

/-- Helper for Definition 5.4: the `[NeZero n]` periodic extension agrees with the original
vector on the base window. -/
theorem periodicExtensionOfNeZero_apply_natCast {n : ℕ} [NeZero n]
    (t : Fin n → α) (i : Fin n) : periodicExtensionOfNeZero t ((i : ℕ) : ℤ) = t i := by
  -- Reuse the positive-period agreement theorem through the wrapper.
  simpa [periodicExtensionOfNeZero, periodicIndexOfNeZero_natCast] using
    periodicExtension_apply_natCast n.pos_of_neZero t i

/-- Helper for Definition 5.4: the `[NeZero n]` periodic extension is periodic with period `n`.
-/
theorem periodicExtensionOfNeZero_isPeriodic {n : ℕ} [NeZero n] (t : Fin n → α) :
    Function.Periodic (periodicExtensionOfNeZero t) (n : ℤ) := by
  -- Reuse the positive-period periodicity theorem through the wrapper.
  simpa [periodicExtensionOfNeZero] using periodicExtension_isPeriodic n.pos_of_neZero t

/-- The periodicity criterion from equation `(5.21)`: a discrete vector is `n`-periodic exactly
when its values agree at integer indices that are congruent modulo `n`. -/
theorem periodic_iff_modEq {n : ℕ} {t : ℤ → α} :
    Function.Periodic t (n : ℤ) ↔ ∀ i j, i ≡ j [ZMOD n] → t i = t j := by
  constructor
  · intro h i j hij
    -- Periodicity identifies all representatives of the same residue class.
    exact h.eq_of_modEq hij
  · intro h
    -- Equality on congruence classes upgrades to periodicity by one-period shifts.
    exact Function.periodic_of_modEq h

/-- Definition 5.4. The periodic extension of `t : Fin n → α` is `n`-periodic and agrees with
`t` on the base window `0, ..., n - 1`; equation `(5.21)` is recorded separately by
`periodic_iff_modEq`. -/
theorem periodicExtension_spec {n : ℕ} (h : 0 < n) (t : Fin n → α) :
    Function.Periodic (periodicExtension h t) (n : ℤ) ∧
      ∀ i : Fin n, periodicExtension h t ((i : ℕ) : ℤ) = t i := by
  -- Pair the periodicity theorem with the base-window agreement theorem.
  exact ⟨periodicExtension_isPeriodic h t, periodicExtension_apply_natCast h t⟩

/-- The `[NeZero n]` periodic extension of `t : Fin n → α` is `n`-periodic and agrees with `t`
on the base window `0, ..., n - 1`. -/
theorem periodicExtensionOfNeZero_spec {n : ℕ} [NeZero n] (t : Fin n → α) :
    Function.Periodic (periodicExtensionOfNeZero t) (n : ℤ) ∧
      ∀ i : Fin n, periodicExtensionOfNeZero t ((i : ℕ) : ℤ) = t i := by
  -- Repackage the wrapper-level periodicity and base-window agreement.
  exact ⟨periodicExtensionOfNeZero_isPeriodic t, periodicExtensionOfNeZero_apply_natCast t⟩

end DiscreteSignal
