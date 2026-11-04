/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import Mathlib.Data.Nat.Bitwise

/-!
# Binary submasks

Generic bit-level material, extracted from the route spike (#15) once it became clear the
proofs are about an arbitrary power-of-two boundary rather than anything in the machine
encoding. Nothing here mentions a machine, a block layout, or a guard bit.

`Nat.IsBinarySubmask` is stated on `Nat.testBit`, which is the canonical form for this
project: #18 consumes it directly, and #34's contract is phrased in terms of it.

## Main results

* `Nat.isBinarySubmask_two_pow_sub_one_iff`: being a submask of `2 ^ k - 1` is fitting in
  `k` bits.
* `Nat.isBinarySubmask_add_mul_two_pow_iff`: a submask condition splits at a power-of-two
  boundary, provided the low part fits below it.
-/

@[expose] public section

namespace Nat

/-- Every binary digit of `a` is at most the corresponding digit of `b`. -/
def IsBinarySubmask (a b : ℕ) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

@[simp] theorem isBinarySubmask_zero_iff {x : ℕ} : IsBinarySubmask x 0 ↔ x = 0 := by
  constructor
  · intro h
    refine Nat.zero_of_testBit_eq_false fun i => ?_
    by_contra hc
    simpa using h i (by simpa using hc)
  · rintro rfl i hi
    simp at hi

theorem isBinarySubmask_refl (a : ℕ) : IsBinarySubmask a a := fun _ h => h

theorem IsBinarySubmask.trans {a b c : ℕ} (hab : IsBinarySubmask a b)
    (hbc : IsBinarySubmask b c) : IsBinarySubmask a c := fun i h => hbc i (hab i h)

/-- A number is a submask of `2 ^ k - 1` exactly when it fits in `k` bits, since `2 ^ k - 1`
is precisely the low `k` bits. -/
theorem isBinarySubmask_two_pow_sub_one_iff {k x : ℕ} :
    IsBinarySubmask x (2 ^ k - 1) ↔ x < 2 ^ k := by
  simp only [IsBinarySubmask, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  constructor
  · intro h
    refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
    by_contra hc
    exact absurd (h i (by simpa using hc)) (by omega)
  · intro hx i hi
    by_contra hik
    have hle : (2 : ℕ) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)] at hi
    simp at hi

/-- A submask condition splits at a power-of-two boundary: below the boundary and above it
are independent bit ranges. The hypothesis is what makes `a` the low part. -/
theorem isBinarySubmask_add_mul_two_pow_iff {width x a b : ℕ} (ha : a < 2 ^ width) :
    IsBinarySubmask x (a + 2 ^ width * b) ↔
      IsBinarySubmask (x % 2 ^ width) a ∧ IsBinarySubmask (x / 2 ^ width) b := by
  have hmask : ∀ j, (a + 2 ^ width * b).testBit j =
      if j < width then a.testBit j else b.testBit (j - width) := by
    intro j
    have h : a + 2 ^ width * b = 2 ^ width * b + a := by omega
    rw [h, Nat.testBit_two_pow_mul_add b ha j]
  simp only [IsBinarySubmask, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i hi.2
      rw [hmask i, if_pos hi.1] at this
      exact this
    · have := h (i + width) hi
      rw [hmask _, if_neg (by omega)] at this
      simpa using this
  · rintro ⟨hlo, hhi⟩ i hi
    rw [hmask i]
    by_cases hiw : i < width
    · rw [if_pos hiw]
      exact hlo i ⟨hiw, hi⟩
    · rw [if_neg hiw]
      exact hhi (i - width) (by rwa [Nat.sub_add_cancel (by omega)])

end Nat
