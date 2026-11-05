/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.BinarySubmask
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Guarded block packing

The reusable layer extracted from the route spike (#15): a block layout with one guard bit
per block, and the two APIs its two consumers actually need.

## Two APIs, deliberately

The spike proved both directions of a machine encoding against this layer, and they consume
it differently:

* **soundness** uses the global characterisation `isBinarySubmask_guardMask_iff`, which turns
  a mask hypothesis into every block bound plus `R < blockBase k ^ t`;
* **completeness** uses the recursive split `isBinarySubmask_split` together with
  `guardMask_succ`, peeling one block from each side in step.

Both are exported. Factoring against only one consumer would have picked the wrong API.

The layout is fixed at **one guard bit**: data values below `2 ^ k`, blocks of width `k + 1`.
That is the construction the spike validated, and it is the right reusable unit; block layouts
with more guard bits or non-uniform fields are not generalised over here.

`geom` is not new API — it is `∑ i ∈ Finset.range t, b ^ i`, mathlib's geometric sum, given a
local name for readability. What is worth keeping is `geom_unique`, the subtraction-free
uniqueness statement, which is stated against that sum.
-/

@[expose] public section

namespace Hilbert10

open Finset

/-- `∑ i < t, b ^ i`, the geometric sum that counts one decrement per step. -/
def geom (b t : ℕ) : ℕ := ∑ i ∈ range t, b ^ i

/-- Peeling the first digit: one more step multiplies the geometric sum by the base. -/
theorem geom_succ (b n : ℕ) : geom b (n + 1) = 1 + b * geom b n := by
  simp only [geom, Finset.sum_range_succ']
  rw [Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- The geometric identity, in the subtraction-free form the arithmetisation needs. Holds
for every base, including degenerate ones. -/
theorem geom_spec (b t : ℕ) : geom b t * b + 1 = geom b t + b ^ t := by
  induction t with
  | zero => simp [geom]
  | succ t ih =>
    rw [geom_succ, pow_succ]
    nlinarith [ih]

/-- The geometric identity determines its solution, for any base at least `2`. This is what
lets an encoding carry the geometric sum as a *variable* rather than a computed value. -/
theorem geom_unique {b t G : ℕ} (hb : 2 ≤ b) (h : G * b + 1 = G + b ^ t) :
    G = geom b t := by
  obtain ⟨C, hC⟩ : ∃ C, b = C + 1 := ⟨b - 1, by omega⟩
  have hC0 : 0 < C := by omega
  have h1 : G * C + 1 = b ^ t := by
    have h' : G * C + G + 1 = G + b ^ t := by
      calc G * C + G + 1 = G * (C + 1) + 1 := by ring
        _ = G + b ^ t := by rw [← hC]; exact h
    omega
  have h2 : geom b t * C + 1 = b ^ t := by
    have hg := geom_spec b t
    have h' : geom b t * C + geom b t + 1 = geom b t + b ^ t := by
      calc geom b t * C + geom b t + 1 = geom b t * (C + 1) + 1 := by ring
        _ = geom b t + b ^ t := by rw [← hC]; exact hg
    omega
  exact Nat.eq_of_mul_eq_mul_right hC0 (Nat.add_right_cancel (h1.trans h2.symm))

/-- Permitted register values are `< 2 ^ k`. -/
def dataBound (k : ℕ) : ℕ := 2 ^ k

/-- The packing base: one guard bit above the data field. -/
def blockBase (k : ℕ) : ℕ := 2 ^ (k + 1)

theorem blockBase_eq (k : ℕ) : blockBase k = 2 * dataBound k := by
  simp [blockBase, dataBound, pow_succ, mul_comm]

theorem two_le_blockBase (k : ℕ) : 2 ≤ blockBase k := by
  simpa [blockBase] using Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))

/-- `guardMask k t` is the number whose set bits are the low `k` bits of each of the first
`t` blocks of width `k + 1`. -/
def guardMask (k t : ℕ) : ℕ := (dataBound k - 1) * geom (blockBase k) t

theorem guardMask_zero (k : ℕ) : guardMask k 0 = 0 := by simp [guardMask, geom]

/-- One more block, prepended below the rest. -/
theorem guardMask_succ (k t : ℕ) :
    guardMask k (t + 1) = (dataBound k - 1) + blockBase k * guardMask k t := by
  simp only [guardMask, geom_succ, Nat.mul_add, mul_one]
  ring

/-- The split, specialised to the block layout. The content is generic — see
`Nat.isBinarySubmask_add_mul_two_pow_iff` — since `blockBase k` is a power of two. -/
theorem isBinarySubmask_split {k x a b : ℕ} (ha : a < blockBase k) :
    Nat.IsBinarySubmask x (a + blockBase k * b) ↔
      Nat.IsBinarySubmask (x % blockBase k) a ∧ Nat.IsBinarySubmask (x / blockBase k) b :=
  Nat.isBinarySubmask_add_mul_two_pow_iff ha

/-- The API bridge: `Guarded.mask` is stated with the closed form `(dataBound k - 1) * G`, and
after `geo_unique` that *is* `guardMask k t`. Definitional, but named so the rewrite step is
explicit. -/
theorem guardMask_eq (k t : ℕ) :
    guardMask k t = (dataBound k - 1) * geom (blockBase k) t := rfl

/-- Fitting in the data field, specialised from
`Nat.isBinarySubmask_two_pow_sub_one_iff`. This is where the guard bit does its work:
`dataBound k - 1` permits precisely the low `k` bits. -/
theorem isBinarySubmask_dataBound_sub_one_iff {k x : ℕ} :
    Nat.IsBinarySubmask x (dataBound k - 1) ↔ x < dataBound k :=
  Nat.isBinarySubmask_two_pow_sub_one_iff

/-- **The mask characterisation.** Stated as an equivalence, so that it serves soundness
(every block bound, plus the global bound), completeness (the mask reduced to ordinary bounds
on packed values), and fixes #34's exact semantic contract. -/
theorem isBinarySubmask_guardMask_iff {k t R : ℕ} :
    Nat.IsBinarySubmask R (guardMask k t) ↔
      R < blockBase k ^ t ∧ ∀ i < t, (R / blockBase k ^ i) % blockBase k < dataBound k := by
  induction t generalizing R with
  | zero =>
    simp only [guardMask_zero, pow_zero, Nat.lt_one_iff, Nat.isBinarySubmask_zero_iff]
    constructor
    · intro h
      exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact h
  | succ t ih =>
    have hlow : dataBound k - 1 < blockBase k := by
      simp only [dataBound, blockBase]
      have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
      have h2 : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rw [guardMask_succ, isBinarySubmask_split hlow, isBinarySubmask_dataBound_sub_one_iff, ih]
    have hB : 0 < blockBase k := by simp [blockBase]
    constructor
    · rintro ⟨hmod, hdiv, hblk⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [pow_succ]
        exact (Nat.div_lt_iff_lt_mul hB).mp hdiv
      · cases i with
        | zero => simpa using hmod
        | succ i =>
          have := hblk i (by omega)
          rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this
    · rintro ⟨hlt, hblk⟩
      refine ⟨by simpa using hblk 0 (by omega), ?_, fun i hi => ?_⟩
      · refine (Nat.div_lt_iff_lt_mul hB).mpr ?_
        rwa [← pow_succ]
      · have := hblk (i + 1) (by omega)
        rwa [Nat.div_div_eq_div_mul, ← pow_succ']


end Hilbert10
