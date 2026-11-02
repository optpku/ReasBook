module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.SelectorRegs

/-!
# The selector encoding for many registers: the global layer

#49, phase 4, second layer. `SelectorRegs` reduced the encoded step relation for an
arbitrary `P : Program (k + 1)` to `BlockStepK`. This file packs the blocks.

## The lane family

A configuration of a `k + 1`-register machine has `k + 2` fields, so the lanes are indexed by
`Fin (k + 2)`: lane `0` is the program counter and lane `r.succ` is register `r`. The data width
is `w * (k + 2)` and the outer guarded block is one bit wider. Reassembly is

```
R = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j
```

which is `fieldsCode_configCode_eq_lanes` at register arity `k + 1`. Blockwise it says the block
of `R` is the `fieldsCode` of its lanes' blocks, so the decoder reads each lane off directly —
the one-register file had to do this by hand with a `mod` and a `div`.

The residuals stay indexed by `Fin (k + 1)`: they are per *register*, not per field, since the
program counter has no residual.

## What did not change

The selector family is still one per branch, still one-hot across the program, and still
independent of the register count. Every register equation is bounded by `subSum_le_one`, so no
new carry appears. The masks are the same two constants at the wider block.

## Scope

`globalConditionsK_iff` is the equivalence. Packaging it into `Aggregation (k + 1)` is
`SelectorRegsDioph`, the layer above.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ} {P : Program (k + 1)} {w n R : ℕ}

/-! ### Masks at an arbitrary block width -/

/-- The `w`-bit data mask over `t` blocks of width `W`. -/
def laneMaskAt (W w t : ℕ) : ℕ := (2 ^ w - 1) * geom (2 ^ W) t

/-- The one-bit-per-block mask over `t` blocks of width `W`. -/
def bitMaskAt (W t : ℕ) : ℕ := geom (2 ^ W) t

theorem lane_normAt {W w t X : ℕ} (hv : w ≤ W) (h : Nat.IsBinarySubmask X (laneMaskAt W w t)) :
    X = fieldsCode W (fun i : Fin t => configField W X i) ∧
      ∀ i : Fin t, configField W X i < 2 ^ w :=
  packed_eq_fieldsCode hv h

theorem selector_normAt {W t S : ℕ} (hW : 1 ≤ W)
    (h : Nat.IsBinarySubmask S (bitMaskAt W t)) :
    S = fieldsCode W (fun i : Fin t => configField W S i) ∧
      ∀ i : Fin t, configField W S i < 2 := by
  have hb : Nat.IsBinarySubmask S ((2 ^ 1 - 1) * geom (2 ^ W) t) := by
    simpa [bitMaskAt] using h
  have := packed_eq_fieldsCode (v := 1) (W := W) hW hb
  simpa using this

theorem laneOfAt {W w t : ℕ} (hv : w ≤ W) (f : Fin t → ℕ) (hf : ∀ i, f i < 2 ^ w) :
    Nat.IsBinarySubmask (fieldsCode W f) (laneMaskAt W w t) := by
  have hlt : (2 : ℕ) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hv
  rw [laneMaskAt]
  refine (isBinarySubmask_constMask_iff hv).mpr
    ⟨fieldsCode_lt (fun i => lt_of_lt_of_le (hf i) hlt), fun i hi => ?_⟩
  rw [field_fieldsCode (fun j => lt_of_lt_of_le (hf j) hlt) ⟨i, hi⟩]
  exact hf ⟨i, hi⟩

theorem bitOfAt {W t : ℕ} (hW : 1 ≤ W) (f : Fin t → ℕ) (hf : ∀ i, f i < 2) :
    Nat.IsBinarySubmask (fieldsCode W f) (bitMaskAt W t) := by
  have hlt : (2 : ℕ) ≤ 2 ^ W := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  rw [bitMaskAt, show geom (2 ^ W) t = (2 ^ 1 - 1) * geom (2 ^ W) t from by norm_num]
  refine (isBinarySubmask_constMask_iff (v := 1) hW).mpr
    ⟨fieldsCode_lt (fun i => lt_of_lt_of_le (hf i) hlt), fun i hi => ?_⟩
  rw [field_fieldsCode (fun j => lt_of_lt_of_le (hf j) hlt) ⟨i, hi⟩]
  simpa using hf ⟨i, hi⟩

/-! ### Branches -/

/-- The instruction index a branch belongs to. -/
def branchIdx (P : Program (k + 1)) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (p : ℕ)
  | .inr p => (p : ℕ)

/-- The target a branch jumps to. -/
def branchTgt (P : Program (k + 1)) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (P.get p).jumpPos
  | .inr p => (P.get p).jumpZero

theorem branchIdx_lt (hlen : P.length < 2 ^ w) (c : Fin P.length ⊕ Fin P.length) :
    branchIdx P c < 2 ^ w := by
  cases c with
  | inl p => exact lt_of_lt_of_le p.isLt (by omega)
  | inr p => exact lt_of_lt_of_le p.isLt (by omega)

/-! ### Carry bounds at the wider block -/

theorem two_pow_lt_block (w k : ℕ) : 2 ^ w < 2 ^ (w * (k + 2) + 1) :=
  Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

theorem two_mul_length_lt_block (hlen : P.length < 2 ^ w) :
    2 * P.length < 2 ^ (w * (k + 2) + 1) := by
  have h1 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ (w * (k + 2) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
  omega

/-- The zero branch's carry bound at the wider block. -/
theorem zero_carry_block {x s z : ℕ} (hx : x < 2 ^ w) (hs : s ≤ 1) (hz : z < 2 ^ w) :
    x + s * (2 ^ w - 1) + z < 2 ^ (w * (k + 2) + 1) := by
  have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have hpos2 : 0 < (2 : ℕ) ^ (w * (k + 2) + 1) := Nat.two_pow_pos _
  have hdouble : (2 : ℕ) ^ (w * (k + 2) + 1) = 2 * 2 ^ (w * (k + 2)) := by rw [pow_succ]; ring
  have hsq : (2 : ℕ) ^ w * 2 ^ w ≤ 2 ^ (w * (k + 2)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hsb : s * (2 ^ w - 1) ≤ 2 ^ w - 1 := by
    calc s * (2 ^ w - 1) ≤ 1 * (2 ^ w - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ w - 1 := one_mul _
  rcases Nat.lt_or_ge (2 ^ w) 2 with hsmall | hbig
  · have h1 : (2 : ℕ) ^ w = 1 := by omega
    have hzero : x + s * (2 ^ w - 1) + z = 0 := by rw [h1]; omega
    omega
  · have h4 : 2 * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ hbig
    omega

/-! ### The global conditions -/

/-- **The global selector conditions for an arbitrary program on `k + 1` registers.**

`X j` is lane `j` of the packed run: `X 0` the program counter, `X r.succ` register `r`.
`S (.inl p)` and `S (.inr p)` are instruction `p`'s two branch lanes, and `Res r`, `Zres r` are
register `r`'s two residual lanes. -/
def GlobalConditionsK (P : Program (k + 1)) (w n R : ℕ) (X : Fin (k + 2) → ℕ)
    (S : Fin P.length ⊕ Fin P.length → ℕ) (Res Zres : Fin (k + 1) → ℕ) : Prop :=
  P.length < 2 ^ w ∧
  (∀ j, Nat.IsBinarySubmask (X j) (laneMaskAt (w * (k + 2) + 1) w (n + 1))) ∧
  R = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j ∧
  (∀ c, Nat.IsBinarySubmask (S c) (bitMaskAt (w * (k + 2) + 1) n)) ∧
  (∑ c, S c) = bitMaskAt (w * (k + 2) + 1) n ∧
  X 0 % (2 ^ (w * (k + 2) + 1)) ^ n = ∑ c, branchIdx P c * S c ∧
  X 0 / 2 ^ (w * (k + 2) + 1) = ∑ c, branchTgt P c * S c ∧
  (∀ r, X r.succ / 2 ^ (w * (k + 2) + 1)
      + ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p)
    = X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
      + ∑ p : Fin P.length, (P.get p).gainAt r * S (.inl p)) ∧
  (∀ p, (P.get p).branches = 0 → S (.inr p) = 0) ∧
  (∀ r, X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
      + (∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p)) * (2 ^ w - 1) + Zres r
    = laneMaskAt (w * (k + 2) + 1) w n) ∧
  (∀ r, Nat.IsBinarySubmask (Zres r) (laneMaskAt (w * (k + 2) + 1) w n)) ∧
  (∀ r, X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
    = Res r + ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p)) ∧
  (∀ r, Nat.IsBinarySubmask (Res r) (laneMaskAt (w * (k + 2) + 1) w n)) ∧
  (∀ c, S c = 0 ∨ branchTgt P c < 2 ^ w)

/-! ### Soundness -/

/-- **Soundness of the global system.** -/
theorem globalConditionsK_sound {X : Fin (k + 2) → ℕ}
    {S : Fin P.length ⊕ Fin P.length → ℕ} {Res Zres : Fin (k + 1) → ℕ}
    (h : GlobalConditionsK P w n R X S Res Zres) :
    P.length < 2 ^ w ∧
      Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)) ∧
      ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
        (configField (w * (k + 2) + 1) R (i + 1)) := by
  obtain ⟨hlen, hmX, hR, hmS, hsum, hpcEq, hjump, hupd, hzb, hzeq, hzm, hres, hresm, htgt⟩ := h
  have hwW : w ≤ w * (k + 2) + 1 := by nlinarith
  have h1W : 1 ≤ w * (k + 2) + 1 := by omega
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * (k + 2) + 1) := two_pow_lt_block w k
  have hpowmul : ((2 : ℕ) ^ w) ^ (k + 2) = 2 ^ (w * (k + 2)) := by rw [← pow_mul]
  have hstep : (2 : ℕ) ^ (w * (k + 2)) < 2 ^ (w * (k + 2) + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- normalise every packed witness once
  have eX : ∀ j, X j = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) (X j) i) :=
    fun j => (lane_normAt hwW (hmX j)).1
  have bX : ∀ j, ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) (X j) i < 2 ^ w :=
    fun j => (lane_normAt hwW (hmX j)).2
  have eS : ∀ c, S c = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i) :=
    fun c => (selector_normAt h1W (hmS c)).1
  have bS : ∀ c, ∀ i : Fin n, configField (w * (k + 2) + 1) (S c) i < 2 :=
    fun c => (selector_normAt h1W (hmS c)).2
  have eRes : ∀ r, Res r = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (Res r) i) :=
    fun r => (lane_normAt hwW (hresm r)).1
  have bRes : ∀ r, ∀ i : Fin n, configField (w * (k + 2) + 1) (Res r) i < 2 ^ w :=
    fun r => (lane_normAt hwW (hresm r)).2
  have bZres : ∀ r, ∀ i : Fin n, configField (w * (k + 2) + 1) (Zres r) i < 2 ^ w :=
    fun r => (lane_normAt hwW (hzm r)).2
  have eZres : ∀ r, Zres r = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (Zres r) i) :=
    fun r => (lane_normAt hwW (hzm r)).1
  -- the lanes reassemble `R` blockwise
  have hbd : ∀ i : Fin (n + 1),
      fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i)
        < 2 ^ (w * (k + 2) + 1) := by
    intro i
    have h1 := fieldsCode_lt (w := w) (fun j : Fin (k + 2) => bX j i)
    omega
  have hRe : R = fieldsCode (w * (k + 2) + 1) (fun i : Fin (n + 1) =>
      fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i)) := by
    rw [hR, show (∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j)
        = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * fieldsCode (w * (k + 2) + 1)
          (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) (X j) i) from
      Finset.sum_congr rfl fun j _ => congrArg _ (eX j),
      fieldsCode_sum_smul]
    exact congrArg _ (funext fun i => (fieldsCode_eq_sum w _).symm)
  have hblk : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i
      = fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i) := by
    intro i
    rw [hRe, field_fieldsCode hbd i]
  have hRblk : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i < 2 ^ (w * (k + 2)) := by
    intro i
    rw [hblk i]
    have h1 := fieldsCode_lt (w := w) (fun j : Fin (k + 2) => bX j i)
    omega
  have hRlt : R < (2 ^ (w * (k + 2) + 1)) ^ (n + 1) := by
    rw [hRe]
    exact fieldsCode_lt hbd
  refine ⟨hlen, isBinarySubmask_guardMask_iff.mpr ⟨hRlt, fun i hi => hRblk ⟨i, hi⟩⟩, ?_⟩
  -- decode: each lane is read off directly
  set cs : ℕ → Config (k + 1) :=
    fun i => decodeConfig w (configField (w * (k + 2) + 1) R i) with hcs
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * (k + 2) + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hRblk i)
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hlane : ∀ (i : Fin (n + 1)) (j : Fin (k + 2)),
      configField w (configField (w * (k + 2) + 1) R i) (j : ℕ)
        = configField (w * (k + 2) + 1) (X j) i := by
    intro i j
    rw [hblk i, field_fieldsCode (fun j => bX j i) j]
  have hpcv : ∀ i : Fin (n + 1), (cs i).pc = configField (w * (k + 2) + 1) (X 0) i := by
    intro i
    change configField w (configField (w * (k + 2) + 1) R i) 0 = _
    exact hlane i 0
  have hregv : ∀ (i : Fin (n + 1)) (r : Fin (k + 1)),
      (cs i).regs r = configField (w * (k + 2) + 1) (X r.succ) i := by
    intro i r
    change configField w (configField (w * (k + 2) + 1) R i) ((r : ℕ) + 1) = _
    exact hlane i r.succ
  -- the selectors are one-hot in every block
  have hone : ∀ i : Fin n,
      (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i) = 1 := by
    have hbit : bitMaskAt (w * (k + 2) + 1) n
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
      rw [fieldsCode_const]; simp [bitMaskAt]
    have hkey : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => ∑ c : Fin P.length ⊕ Fin P.length,
          configField (w * (k + 2) + 1) (S c) i)
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
      rw [← fieldsCode_sum (w * (k + 2) + 1) Finset.univ
        (fun c => fun i : Fin n => configField (w * (k + 2) + 1) (S c) i),
        show (∑ c : Fin P.length ⊕ Fin P.length, fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
            = ∑ c : Fin P.length ⊕ Fin P.length, S c from
          Finset.sum_congr rfl fun c _ => (eS c).symm, hsum, hbit]
    have hcard : Fintype.card (Fin P.length ⊕ Fin P.length) = 2 * P.length := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    have h2L : 2 * P.length < 2 ^ (w * (k + 2) + 1) := two_mul_length_lt_block hlen
    have hbdd : ∀ i : Fin n,
        (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i)
          < 2 ^ (w * (k + 2) + 1) := by
      intro i
      have hle : (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i)
          ≤ ∑ _c : Fin P.length ⊕ Fin P.length, 1 :=
        Finset.sum_le_sum fun c _ => by have := bS c i; omega
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hle
      omega
    have hone_lt : (1 : ℕ) < 2 ^ (w * (k + 2) + 1) := by
      calc (1 : ℕ) < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (w * (k + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact fun i => congrFun (fieldsCode_injective hbdd (fun _ => hone_lt) hkey) i
  have honeL : ∀ i : Fin n, (∑ p : Fin P.length,
      (configField (w * (k + 2) + 1) (S (.inl p)) i
        + configField (w * (k + 2) + 1) (S (.inr p)) i)) = 1 := by
    intro i
    calc (∑ p : Fin P.length, (configField (w * (k + 2) + 1) (S (.inl p)) i
          + configField (w * (k + 2) + 1) (S (.inr p)) i))
        = (∑ p : Fin P.length, configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length, configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i :=
          (Fintype.sum_sum_type (fun c => configField (w * (k + 2) + 1) (S c) i)).symm
      _ = 1 := hone i
  -- truncation and shift, for every lane
  have hmod : ∀ j : Fin (k + 2), X j % (2 ^ (w * (k + 2) + 1)) ^ n
      = fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X j) i) := by
    intro j
    conv_lhs => rw [eX j]
    exact fieldsCode_mod_pow (fun i => lt_trans (bX j i) hwlt)
  have hdiv : ∀ j : Fin (k + 2), X j / 2 ^ (w * (k + 2) + 1)
      = fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X j) ((i : ℕ) + 1)) := by
    intro j
    conv_lhs => rw [eX j]
    exact fieldsCode_div _ _ (lt_trans (bX j 0) hwlt)
  -- the sub-sums, blockwise
  have hsubA : ∀ (g : Fin P.length → ℕ), (∀ p, g p ≤ 1) → ∀ i : Fin n,
      (∑ p : Fin P.length, g p * configField (w * (k + 2) + 1) (S (.inl p)) i) ≤ 1 :=
    fun g hg i => (subSum_le_one hg (honeL i)).1
  have hsubZ : ∀ (g : Fin P.length → ℕ), (∀ p, g p ≤ 1) → ∀ i : Fin n,
      (∑ p : Fin P.length, g p * configField (w * (k + 2) + 1) (S (.inr p)) i) ≤ 1 :=
    fun g hg i => (subSum_le_one hg (honeL i)).2
  have hlossle : ∀ r : Fin (k + 1), ∀ p : Fin P.length, (P.get p).lossAt r ≤ 1 :=
    fun r p => Instr.lossAt_le_one r _
  have hgainle : ∀ r : Fin (k + 1), ∀ p : Fin P.length, (P.get p).gainAt r ≤ 1 :=
    fun r p => Instr.gainAt_le_one r _
  -- the aggregate equations, blockwise
  have hA : ∀ i : Fin n, configField (w * (k + 2) + 1) (X 0) i
      = ∑ p : Fin P.length, (p : ℕ) * (configField (w * (k + 2) + 1) (S (.inl p)) i
        + configField (w * (k + 2) + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchIdx P c * fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X 0) i) := by
      rw [← hmod 0, hpcEq]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchIdx P) hone
      (fun c _ => Or.inr (lt_trans (branchIdx_lt hlen c) hwlt))
      (fun i => lt_trans (bX 0 i.castSucc) hwlt)).mp heq
    intro i
    calc configField (w * (k + 2) + 1) (X 0) i
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchIdx P c * configField (w * (k + 2) + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length,
            branchIdx P (.inl p) * configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchIdx P (.inr p) * configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchIdx P c * configField (w * (k + 2) + 1) (S c) i)
      _ = ∑ p : Fin P.length, ((p : ℕ) * configField (w * (k + 2) + 1) (S (.inl p)) i
            + (p : ℕ) * configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_add_distrib.symm
      _ = ∑ p : Fin P.length, (p : ℕ) * (configField (w * (k + 2) + 1) (S (.inl p)) i
            + configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_congr rfl fun p _ => (Nat.mul_add _ _ _).symm
  have hB : ∀ i : Fin n, configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)
      = ∑ p : Fin P.length, ((P.get p).jumpPos * configField (w * (k + 2) + 1) (S (.inl p)) i
        + (P.get p).jumpZero * configField (w * (k + 2) + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchTgt P c * fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)) := by
      rw [← hdiv 0, hjump]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchTgt P) hone
      (fun c _ => by
        rcases htgt c with hzero | hfit
        · exact Or.inl fun i => by rw [hzero]; simp [configField]
        · exact Or.inr (lt_trans hfit hwlt))
      (fun i => by
        have h1 : configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1) < 2 ^ w :=
          bX 0 ⟨(i : ℕ) + 1, by omega⟩
        exact lt_trans h1 hwlt)).mp heq
    intro i
    calc configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchTgt P c * configField (w * (k + 2) + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length,
            branchTgt P (.inl p) * configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchTgt P (.inr p) * configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchTgt P c * configField (w * (k + 2) + 1) (S c) i)
      _ = ∑ p : Fin P.length,
            ((P.get p).jumpPos * configField (w * (k + 2) + 1) (S (.inl p)) i
              + (P.get p).jumpZero * configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_add_distrib.symm
  have hC : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1)
        + ∑ p : Fin P.length,
          (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i
      = configField (w * (k + 2) + 1) (X r.succ) i
        + ∑ p : Fin P.length,
          (P.get p).gainAt r * configField (w * (k + 2) + 1) (S (.inl p)) i := by
    intro r
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1)
          + ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i)
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i
            + ∑ p : Fin P.length,
              (P.get p).gainAt r * configField (w * (k + 2) + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← fieldsCode_sum_smul, ← fieldsCode_sum_smul,
        ← hdiv r.succ, ← hmod r.succ,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm,
        show (∑ p : Fin P.length, (P.get p).gainAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).gainAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hupd r
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_) (fun i => ?_) heq) i
    · have h1 : configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1) < 2 ^ w :=
        bX r.succ ⟨(i : ℕ) + 1, by omega⟩
      have h2 := hsubA (fun p => (P.get p).lossAt r) (hlossle r) i
      omega
    · have h1 : configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w :=
        bX r.succ i.castSucc
      have h2 := hsubA (fun p => (P.get p).gainAt r) (hgainle r) i
      omega
  have hD : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) i
      + (∑ p : Fin P.length,
          (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1)
      + configField (w * (k + 2) + 1) (Zres r) i = 2 ^ w - 1 := by
    intro r
    have hlaneEq : laneMaskAt (w * (k + 2) + 1) w n
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) :=
      (fieldsCode_const _ _).symm
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i
          + (∑ p : Fin P.length,
              (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1)
          + configField (w * (k + 2) + 1) (Zres r) i)
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← hlaneEq, ← hzeq r, ← hmod r.succ, ← eZres r,
        show (fun i : Fin n => (∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1))
          = (fun i : Fin n => (2 ^ w - 1) * ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) from
            funext fun i => Nat.mul_comm _ _,
        ← fieldsCode_smul, ← fieldsCode_sum_smul,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inr p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      rw [Nat.mul_comm (2 ^ w - 1)
        (∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p))]
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_)
      (fun _ => lt_trans (by omega : 2 ^ w - 1 < 2 ^ w) hwlt) heq) i
    have h1 : configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w := bX r.succ i.castSucc
    exact zero_carry_block h1 (hsubZ (fun p => (P.get p).lossAt r) (hlossle r) i) (bZres r i)
  have hE : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) i
        = configField (w * (k + 2) + 1) (Res r) i
          + ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i := by
    intro r
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i)
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (Res r) i
            + ∑ p : Fin P.length,
              (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_sum_smul, ← hmod r.succ, ← eRes r,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hres r
    refine fun i => congrFun (fieldsCode_injective
      (fun i => lt_trans (show configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w from
        bX r.succ i.castSucc) hwlt) (fun i => ?_) heq) i
    have h1 : configField (w * (k + 2) + 1) (Res r) (i : ℕ) < 2 ^ w := bRes r i
    have h2 := hsubA (fun p => (P.get p).lossAt r) (hlossle r) i
    omega
  -- assemble
  intro i hi
  rw [show configField (w * (k + 2) + 1) R i = configCode w (cs i) from (hcode ⟨i, by omega⟩).symm,
    show configField (w * (k + 2) + 1) R (i + 1) = configCode w (cs (i + 1)) from
      (hcode ⟨i + 1, by omega⟩).symm]
  refine (blockStepK_iff P w n cs hfitcs).mpr
    ⟨fun i p => configField (w * (k + 2) + 1) (S (.inl p)) i,
      fun i p => configField (w * (k + 2) + 1) (S (.inr p)) i,
      fun i r => configField (w * (k + 2) + 1) (Res r) i, ?_⟩ i hi
  intro j hj
  dsimp only
  refine ⟨honeL ⟨j, hj⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (cs j).pc = configField (w * (k + 2) + 1) (X 0) j from hpcv ⟨j, by omega⟩]
    exact hA ⟨j, hj⟩
  · rw [show (cs (j + 1)).pc = configField (w * (k + 2) + 1) (X 0) (j + 1) from
      hpcv ⟨j + 1, by omega⟩]
    exact hB ⟨j, hj⟩
  · intro r
    rw [show (cs (j + 1)).regs r = configField (w * (k + 2) + 1) (X r.succ) (j + 1) from
        hregv ⟨j + 1, by omega⟩ r,
      show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    exact hC r ⟨j, hj⟩
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos ((P.get p).branches) with hz | hz
    · rw [hzb p hz]
      simp [configField]
    · have h1 : configField (w * (k + 2) + 1) (S (.inr p)) j < 2 := bS (.inr p) ⟨j, hj⟩
      omega
  · intro r hzsum
    have hd := hD r ⟨j, hj⟩
    dsimp only at hd
    rw [hzsum, one_mul] at hd
    rw [show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    have h1 : configField (w * (k + 2) + 1) (X r.succ) j < 2 ^ w :=
      bX r.succ (⟨j, by omega⟩ : Fin (n + 1))
    have h2 : configField (w * (k + 2) + 1) (Zres r) j < 2 ^ w := bZres r (⟨j, hj⟩ : Fin n)
    have h3 : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    omega
  · intro r
    rw [show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    exact hE r ⟨j, hj⟩
  · exact fun r => bRes r ⟨j, hj⟩
  · intro p hA1
    dsimp only at hA1
    rcases htgt (.inl p) with hzero | hfit
    · rw [hzero] at hA1; simp [configField] at hA1
    · exact hfit
  · intro p hZ1
    dsimp only at hZ1
    rcases htgt (.inr p) with hzero | hfit
    · rw [hzero] at hZ1; simp [configField] at hZ1
    · exact hfit
  · exact (hfitcs (j + 1)).1
  · exact (hfitcs (j + 1)).2

/-! ### Completeness -/

/-- **Completeness of the global system.** -/
theorem globalConditionsK_complete (hlen : P.length < 2 ^ w)
    (hmask : Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)))
    (hstep : ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
      (configField (w * (k + 2) + 1) R (i + 1))) :
    ∃ (X : Fin (k + 2) → ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ)
      (Res Zres : Fin (k + 1) → ℕ), GlobalConditionsK P w n R X S Res Zres := by
  have hwW : w ≤ w * (k + 2) + 1 := by nlinarith
  have h1W : 1 ≤ w * (k + 2) + 1 := by omega
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * (k + 2) + 1) := two_pow_lt_block w k
  obtain ⟨hRlt, hRblk⟩ := isBinarySubmask_guardMask_iff.mp hmask
  have hRlt' : R < (2 ^ (w * (k + 2) + 1)) ^ (n + 1) := hRlt
  set cs : ℕ → Config (k + 1) :=
    fun i => decodeConfig w (configField (w * (k + 2) + 1) R i) with hcs
  have hblkR : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i < 2 ^ (w * (k + 2)) :=
    fun i => hRblk i i.isLt
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * (k + 2) + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hblkR i)
  have hstep' : ∀ i < n,
      EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1))) := by
    intro i hi
    rw [show configCode w (cs i) = configField (w * (k + 2) + 1) R i from hcode ⟨i, by omega⟩,
      show configCode w (cs (i + 1)) = configField (w * (k + 2) + 1) R (i + 1) from
        hcode ⟨i + 1, by omega⟩]
    exact hstep i hi
  obtain ⟨A, Z, res, hbs⟩ := (blockStepK_iff P w n cs hfitcs).mp hstep'
  have hbs' : ∀ i : Fin n, BlockStepK P w (cs (i : ℕ)).pc (cs ((i : ℕ) + 1)).pc
      (cs (i : ℕ)).regs (cs ((i : ℕ) + 1)).regs (res (i : ℕ)) (A (i : ℕ)) (Z (i : ℕ)) :=
    fun i => hbs i i.isLt
  -- the lane family and the selector family
  set lane : Fin (k + 2) → Fin (n + 1) → ℕ :=
    fun j i => (@Fin.cons (k + 1) (fun _ => ℕ) (cs (i : ℕ)).pc (cs (i : ℕ)).regs) j with hlane
  have hlaneb : ∀ (j : Fin (k + 2)) (i : Fin (n + 1)), lane j i < 2 ^ w := by
    intro j i
    refine Fin.cases ?_ ?_ j
    · simpa [hlane] using (hfitcs (i : ℕ)).1
    · intro r; simpa [hlane] using (hfitcs (i : ℕ)).2 r
  have hlane0 : ∀ i : Fin (n + 1), lane 0 i = (cs (i : ℕ)).pc := fun i => by simp [hlane]
  have hlaneS : ∀ (r : Fin (k + 1)) (i : Fin (n + 1)),
      lane r.succ i = (cs (i : ℕ)).regs r := fun r i => by simp [hlane]
  set selv : Fin P.length ⊕ Fin P.length → Fin n → ℕ :=
    Sum.elim (fun p i => A (i : ℕ) p) (fun p i => Z (i : ℕ) p) with hselv
  have hone : ∀ i : Fin n, (∑ c : Fin P.length ⊕ Fin P.length, selv c i) = 1 := by
    intro i
    calc (∑ c : Fin P.length ⊕ Fin P.length, selv c i)
        = (∑ p : Fin P.length, A (i : ℕ) p) + ∑ p : Fin P.length, Z (i : ℕ) p :=
          Fintype.sum_sum_type (fun c => selv c i)
      _ = ∑ p : Fin P.length, (A (i : ℕ) p + Z (i : ℕ) p) := Finset.sum_add_distrib.symm
      _ = 1 := (hbs' i).1
  have hbnd : ∀ (c : Fin P.length ⊕ Fin P.length) (i : Fin n), selv c i < 2 := by
    intro c i
    have hle : selv c i ≤ ∑ c' : Fin P.length ⊕ Fin P.length, selv c' i :=
      Finset.single_le_sum (f := fun c' => selv c' i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)
    rw [hone i] at hle
    omega
  have hbitEq : bitMaskAt (w * (k + 2) + 1) n
      = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
    rw [fieldsCode_const]; simp [bitMaskAt]
  have hlaneEq : laneMaskAt (w * (k + 2) + 1) w n
      = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) :=
    (fieldsCode_const _ _).symm
  have hmod : ∀ j : Fin (k + 2),
      (fieldsCode (w * (k + 2) + 1) (lane j)) % (2 ^ (w * (k + 2) + 1)) ^ n
        = fieldsCode (w * (k + 2) + 1) (fun i : Fin n => lane j i.castSucc) :=
    fun j => fieldsCode_mod_pow (fun i => lt_trans (hlaneb j i) hwlt)
  have hdiv : ∀ j : Fin (k + 2),
      (fieldsCode (w * (k + 2) + 1) (lane j)) / 2 ^ (w * (k + 2) + 1)
        = fieldsCode (w * (k + 2) + 1) (fun i : Fin n => lane j i.succ) :=
    fun j => fieldsCode_div _ _ (lt_trans (hlaneb j 0) hwlt)
  -- the zero residual, blockwise
  have hzsum : ∀ (r : Fin (k + 1)) (i : Fin n),
      (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) ≤ 1 :=
    fun r i => (subSum_le_one (fun p => Instr.lossAt_le_one r _) (hbs' i).1).2
  have hzres : ∀ (r : Fin (k + 1)) (i : Fin n),
      (cs (i : ℕ)).regs r
        + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1)
        + ((2 ^ w - 1) - ((cs (i : ℕ)).regs r
          + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1)))
      = 2 ^ w - 1 := by
    intro r i
    have h1 : (cs (i : ℕ)).regs r < 2 ^ w := (hfitcs (i : ℕ)).2 r
    have h2 := hzsum r i
    rcases (by omega : (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) = 0
        ∨ (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) = 1) with h | h
    · rw [h]; omega
    · rw [h, (hbs' i).2.2.2.2.2.1 r h]; omega
  refine ⟨fun j => fieldsCode (w * (k + 2) + 1) (lane j),
    fun c => fieldsCode (w * (k + 2) + 1) (selv c),
    fun r => fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => res (i : ℕ) r),
    fun r => fieldsCode (w * (k + 2) + 1) (fun i : Fin n =>
      (2 ^ w - 1) - ((cs (i : ℕ)).regs r
        + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1))),
    hlen, fun j => laneOfAt hwW _ (hlaneb j), ?_, fun c => bitOfAt h1W _ (hbnd c), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R` is the scaled sum of its lanes
    have h1 : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) R i) = R :=
      fieldsCode_configField hRlt'
    calc R = fieldsCode (w * (k + 2) + 1) (fun i : Fin (n + 1) => configCode w (cs (i : ℕ))) := by
          rw [← h1]
          exact congrArg _ (funext fun i => (hcode i).symm)
      _ = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * fieldsCode (w * (k + 2) + 1) (lane j) :=
          fieldsCode_configCode_eq_lanes w (fun i : Fin (n + 1) => cs (i : ℕ))
  · -- the branches partition every block
    dsimp only
    rw [fieldsCode_sum (w * (k + 2) + 1) Finset.univ selv, hbitEq]
    exact congrArg _ (funext hone)
  · -- program-counter agreement
    dsimp only
    rw [hmod 0, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc lane 0 i.castSucc = (cs (i : ℕ)).pc := hlane0 i.castSucc
      _ = ∑ p : Fin P.length, (p : ℕ) * (A (i : ℕ) p + Z (i : ℕ) p) := (hbs' i).2.1
      _ = ∑ p : Fin P.length, ((p : ℕ) * A (i : ℕ) p + (p : ℕ) * Z (i : ℕ) p) :=
          Finset.sum_congr rfl fun p _ => Nat.mul_add _ _ _
      _ = (∑ p : Fin P.length, (p : ℕ) * A (i : ℕ) p)
            + ∑ p : Fin P.length, (p : ℕ) * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchIdx P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchIdx P c * selv c i)).symm
  · -- the jump
    dsimp only
    rw [hdiv 0, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc lane 0 i.succ = (cs ((i : ℕ) + 1)).pc := hlane0 i.succ
      _ = ∑ p : Fin P.length, ((P.get p).jumpPos * A (i : ℕ) p
            + (P.get p).jumpZero * Z (i : ℕ) p) := (hbs' i).2.2.1
      _ = (∑ p : Fin P.length, (P.get p).jumpPos * A (i : ℕ) p)
            + ∑ p : Fin P.length, (P.get p).jumpZero * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchTgt P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchTgt P c * selv c i)).symm
  · -- the register updates
    intro r
    dsimp only
    rw [hdiv r.succ, hmod r.succ, fieldsCode_sum_smul, fieldsCode_sum_smul, fieldsCode_add,
      fieldsCode_add]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.succ, hlaneS r i.castSucc]
    exact (hbs' i).2.2.2.1 r
  · -- only a decrement takes a zero branch
    intro p hp
    dsimp only
    have hz : ∀ i : Fin n, Z (i : ℕ) p = 0 := by
      intro i
      have := (hbs' i).2.2.2.2.1 p
      omega
    rw [show selv (.inr p) = (fun _ : Fin n => 0) from funext hz]
    simp
  · -- the zero branch
    intro r
    dsimp only
    rw [hmod r.succ, fieldsCode_sum_smul, Nat.mul_comm (fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => ∑ p : Fin P.length,
          (P.get p).lossAt r * selv (.inr p) i)) (2 ^ w - 1),
      fieldsCode_smul, fieldsCode_add, fieldsCode_add, hlaneEq]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.castSucc, Nat.mul_comm (2 ^ w - 1)]
    exact hzres r i
  · intro r
    exact laneOfAt hwW _ fun i => by have := (hfitcs (i : ℕ)).2 r; omega
  · -- the positive residuals
    intro r
    dsimp only
    rw [hmod r.succ, fieldsCode_sum_smul, fieldsCode_add]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.castSucc]
    exact (hbs' i).2.2.2.2.2.2.1 r
  · intro r
    exact laneOfAt hwW _ fun i => (hbs' i).2.2.2.2.2.2.2.1 r
  · -- each selected target fits
    intro c
    dsimp only
    by_cases hall : ∀ i : Fin n, selv c i = 0
    · left
      rw [show selv c = (fun _ : Fin n => 0) from funext hall]
      simp
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h1 : selv c i = 1 := by have := hbnd c i; omega
      cases c with
      | inl p => exact (hbs' i).2.2.2.2.2.2.2.2.1 p h1
      | inr p => exact (hbs' i).2.2.2.2.2.2.2.2.2.1 p h1

/-- **The global equivalence, for an arbitrary program on `k + 1` registers.** -/
theorem globalConditionsK_iff (P : Program (k + 1)) (w n R : ℕ) :
    (P.length < 2 ^ w ∧ Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)) ∧
        ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
          (configField (w * (k + 2) + 1) R (i + 1))) ↔
      ∃ (X : Fin (k + 2) → ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ)
        (Res Zres : Fin (k + 1) → ℕ), GlobalConditionsK P w n R X S Res Zres := by
  constructor
  · rintro ⟨hlen, hmask, hstep⟩
    exact globalConditionsK_complete hlen hmask hstep
  · rintro ⟨_, _, _, _, h⟩
    exact globalConditionsK_sound h

end RegisterMachine

end Hilbert10
