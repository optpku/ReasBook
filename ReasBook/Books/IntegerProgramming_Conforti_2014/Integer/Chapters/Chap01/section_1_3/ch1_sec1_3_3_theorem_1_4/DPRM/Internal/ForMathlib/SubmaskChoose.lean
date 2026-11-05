/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.BinarySubmask
public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Binary submasks and binomial parity

Issue #18: the bridge between the bit-level definition and the arithmetic one,

```lean
Nat.IsBinarySubmask k n ↔ Odd (n.choose k)
```

## Route

An adapter around mathlib's Lucas's theorem (`Choose.lucas_theorem_nat`) rather than a
development from Kummer. At `p = 2` Lucas gives

```
n.choose k ≡ ∏ i ∈ range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)   [MOD 2]
```

for any `a` with `n, k < 2 ^ a`. Each local factor is `(n.testBit i).toNat.choose
(k.testBit i).toNat`, and a four-way bit split shows it is `1` exactly when
`k.testBit i → n.testBit i`, and `0` otherwise. The product is odd exactly when every factor
is `1`, and bits at or above the bound vanish on both sides, so no condition on `a` survives
into the statement.

Taking `a := max n k + 1` therefore yields the theorem **unconditionally** — no `k ≤ n`
hypothesis and no separate `IsBinarySubmask k n → k ≤ n` lemma first. Kummer and the
`padicValNat` lemmas stay unused unless #33 turns out to need them.

Kept in a separate file so `BinarySubmask` remains importable by consumers that need only the
bit lemmas, without dragging in the `Choose` hierarchy.
-/

@[expose] public section

namespace Nat

/-- The local Lucas factor at bit `i`: `1` unless `k` has a bit that `n` lacks. -/
theorem choose_bit_eq_one_iff (n k i : ℕ) :
    (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 1 ↔ (k.testBit i = true → n.testBit i = true) := by
  rw [← toNat_testBit, ← toNat_testBit]
  cases hn : n.testBit i <;> cases hk : k.testBit i <;> simp

/-- Bits at or above a bound where both numbers vanish impose no constraint. -/
theorem submask_iff_forall_lt {k n a : ℕ} (hk : k < 2 ^ a) :
    IsBinarySubmask k n ↔ ∀ i < a, k.testBit i = true → n.testBit i = true := by
  constructor
  · intro h i _ hi
    exact h i hi
  · intro h i hi
    by_cases hia : i < a
    · exact h i hia hi
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hk
        (Nat.pow_le_pow_right (by omega) (by omega)))] at hi
      simp at hi

/-- **Binary submask is binomial parity.** Unconditional: no `k ≤ n` hypothesis. -/
theorem isBinarySubmask_iff_odd_choose (k n : ℕ) :
    IsBinarySubmask k n ↔ Odd (n.choose k) := by
  classical
  set a := max n k + 1 with ha
  have hn : n < 2 ^ a := lt_of_le_of_lt (le_max_left n k) (by
    have := Nat.lt_two_pow_self (n := max n k)
    calc max n k < 2 ^ max n k := this
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega))
  have hk : k < 2 ^ a := lt_of_le_of_lt (le_max_right n k) (by
    have := Nat.lt_two_pow_self (n := max n k)
    calc max n k < 2 ^ max n k := this
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega))
  -- Lucas at `p = 2`
  have hluc : n.choose k ≡ ∏ i ∈ Finset.range a,
      (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) [MOD 2] :=
    Choose.lucas_theorem_nat hn hk
  have hodd : Odd (n.choose k) ↔
      (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2 = 1 := by
    rw [Nat.odd_iff]
    exact ⟨fun h => by rwa [← hluc], fun h => by rwa [hluc]⟩
  -- the product is odd exactly when every factor is one
  have hfac : ∀ i, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) ≤ 1 := by
    intro i
    rw [← toNat_testBit, ← toNat_testBit]
    cases n.testBit i <;> cases k.testBit i <;> simp
  have hprod : (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2 = 1 ↔
      ∀ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 1 := by
    constructor
    · intro h i hi
      by_contra hne
      have hzero : (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 0 := by
        have := hfac i; omega
      rw [Finset.prod_eq_zero hi hzero] at h
      simp at h
    · intro h
      have hone : (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) = 1 := by
        rw [Finset.prod_congr rfl h]
        simp
      rw [hone]
  rw [hodd, hprod, submask_iff_forall_lt hk]
  exact ⟨fun h i hi => (choose_bit_eq_one_iff n k i).mpr (h i (Finset.mem_range.mp hi)),
    fun h i hi => (choose_bit_eq_one_iff n k i).mp (h i (Finset.mem_range.mpr hi))⟩

end Nat
