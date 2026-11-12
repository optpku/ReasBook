/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.BlockPacking
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ConfigCoding
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.BinarySubmask
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Selector packing: global identities read blockwise

The packing algebra the selector encoding is built on, and the answer to the question #49 was
opened to decide. `Aggregation` is a bounded conjunction over block indices, bundled with a guard
mask and a program-length bound; the question was whether it can instead be expressed by finitely
many global identities. It can, and the lemmas here are why.

Originally a time-boxed probe under `Spike/`. It moved out when the general theorem came to
depend on it: `SelectorRegs`, `SelectorRegsGlobal` and `SelectorRegsDioph` are the load-bearing
chain, while the fixed-program and one-register developments stay under `Spike/` as the evidence
that decided the route.

## The distinction that decides it

A condition on a packed number is acceptable if the equivalence

> global identity between numbers  ⟺  the same identity in every block

is a **theorem proved by induction on the block index**, and unacceptable if it is a
*Diophantine condition* that itself needs representing. The circularity trap in
`Spike/Sequences.lean` is the second kind: coding partial products and requiring
`p (i + 1) = p i * h i` reproduces the bounded conjunction one level down.

Every primitive below is of the first kind. That is the content of the probe: `fieldsCode` is
linear, so sums, scalar multiples and pointwise-bounded differences of packed numbers are
blockwise for free; equality of two in-range packings is blockwise by base uniqueness; and a
submask condition is blockwise by peeling one block at a time.

## The intended encoding

Per *register lane*, not per configuration: `Xpc, X₀, …, X_k`, each packing `n + 1` values.

**All lanes use the same outer base as the packed run**, `B = 2 ^ (w * (k + 1) + 1)`. This is
deliberately wasteful — a lane block spends `w * (k + 1) + 1` bits carrying a `w`-bit value —
and it is what keeps the connection to #47's `R` a single global identity,

```
R = Xpc + 2 ^ w * X₀ + 2 ^ (2 * w) * X₁ + ⋯
```

blockwise, since a configuration code is below `2 ^ (w * (k + 1))` and so below `B`. Lanes at
their own tight base `2 ^ (w + 1)` would have forced a second packed-run development alongside
#47 and #48; at base `B` those two are reused unchanged.

The data mask for a lane is `M = (2 ^ w - 1) * geom B (n + 1)`: one `w`-bit field per block,
guard bits clear.

For a fixed program of `m` instructions, selectors `S₀, …, S_{m-1}` pack `n` bits, and each
`dec` selector splits as `S⁺ₚ + S⁰ₚ`. The conditions are then, all global:

* `IsBinarySubmask Sₚ (geom B n)` — each selector is one bit per block;
* `∑ₚ Sₚ = geom B n` — exactly one instruction runs per step, carry-free because
  `P.length < 2 ^ w` is part of `Aggregation`'s bundle;
* `Xpc % Bⁿ = ∑ₚ p · Sₚ` — the selector agrees with the program counter;
* `Xpc / B = ∑ₚ targetₚ · Sₚ^branch` — the jump;
* `X_r / B + ∑_{dec r} S⁺ₚ = X_r % Bⁿ + ∑_{inc r} Sₚ` — the register update, subtraction-free;
* for each instruction, the bound on the target it *selects*:
  `Sₚ = 0 ∨ jₚ < 2 ^ w` for an `inc`, and `S⁺ₚ = 0 ∨ jposₚ < 2 ^ w`,
  `S⁰ₚ = 0 ∨ jzeroₚ < 2 ^ w` for a `dec`;
* for each `dec` instruction `p` reading register `r`:
  `S⁰ₚ + S⁺ₚ = Sₚ`, both submasked by `geom B n`;
  `IsBinarySubmask (S⁰ₚ · (2 ^ w - 1)) (M % Bⁿ - X_r % Bⁿ)` — the zero branch;
  `X_r % Bⁿ = X''ₚ + S⁺ₚ` **together with** `IsBinarySubmask X''ₚ (M % Bⁿ)` — the positive
  branch.

That last mask is load-bearing, not decoration. Without it the equation is unsound blockwise,
because the addition may carry: at `B = 8`, `X = 8`, `S⁺ = 1`, `X'' = 7` satisfies `X = X'' + S⁺`
while block `0` of `X` is zero and block `0` of `S⁺` is one. Bounding each block of `X''` below
`2 ^ w` rules the carry out.

The selected-target bounds are load-bearing for the same reason, one level up.
`P.length < 2 ^ w` bounds instruction *indices*, but a `Program` may carry jump targets far
larger than either `P.length` or `2 ^ w`, and `targetₚ · Sₚ` is blockwise only while
`targetₚ < B`. Without them a large target carries between selector blocks and the jump equation
can be satisfied spuriously. They are stated per branch, and as disjunctions, because
`EncodedStep` bounds only the target it selects: requiring every target in the program to fit
would be strictly stronger, and wrong, since an unreachable branch need not fit. Because a
target is a *constant*, the bounded universal `∀ i < n, sₚ,ᵢ = 1 → jₚ < 2 ^ w` collapses to the
disjunction `Sₚ = 0 ∨ jₚ < 2 ^ w`, which is one `ExpDioph.or`.

Several instructions may read the same register: give each `dec` its own `S⁰ₚ` and `S⁺ₚ`, and the
global selector partition puts their conditions on disjoint blocks.

## Status

The primitives are proved. The **acceptance slice** is **not built**, and until it is, the
encoding above is an argument rather than a theorem. This file discharges nothing of
`Aggregation`.

The slice must exercise four cases: `n = 0`; an increment; both branches of a decrement; and an
*unselected* branch whose target exceeds `2 ^ w`, confirming that the encoding does not
accidentally demand that every target fit. A second decrement reading the same register belongs
in a separate regression rather than the minimal slice.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {W : ℕ}

/-! ### Blockwise arithmetic

`fieldsCode` is a `∑ᵢ fᵢ · Bⁱ`, so it is linear. That is why sums and scalar multiples of
packed numbers need no hypotheses at all: the bounds enter only when *recovering* the blocks. -/

theorem fieldsCode_add (W : ℕ) : ∀ {n : ℕ} (a c : Fin n → ℕ),
    fieldsCode W a + fieldsCode W c = fieldsCode W fun i => a i + c i
  | 0, _, _ => rfl
  | n + 1, a, c => by
    rw [fieldsCode_succ, fieldsCode_succ, fieldsCode_succ,
      show ((fun i => a i + c i) ∘ Fin.succ) = (fun i => (a ∘ Fin.succ) i + (c ∘ Fin.succ) i) from
        rfl,
      ← fieldsCode_add W (a ∘ Fin.succ) (c ∘ Fin.succ)]
    ring

theorem fieldsCode_smul (W m : ℕ) : ∀ {n : ℕ} (a : Fin n → ℕ),
    m * fieldsCode W a = fieldsCode W fun i => m * a i
  | 0, _ => by simp [fieldsCode]
  | n + 1, a => by
    rw [fieldsCode_succ, fieldsCode_succ,
      show ((fun i => m * a i) ∘ Fin.succ) = (fun i => m * (a ∘ Fin.succ) i) from rfl,
      ← fieldsCode_smul W m (a ∘ Fin.succ)]
    ring

/-- Base-`2 ^ W` uniqueness, in packing form. -/
theorem fieldsCode_injective {n : ℕ} {a c : Fin n → ℕ} (ha : ∀ i, a i < 2 ^ W)
    (hc : ∀ i, c i < 2 ^ W) (h : fieldsCode W a = fieldsCode W c) : a = c := by
  funext i
  rw [← field_fieldsCode ha i, ← field_fieldsCode hc i, h]

/-- **The primitive the probe turns on.** A single equation between packed numbers *is* the
family of equations between their blocks, provided nothing overflows a block. Proved by
induction; nothing here is a Diophantine condition. -/
theorem fieldsCode_add_eq_iff {n : ℕ} {a c d : Fin n → ℕ} (h : ∀ i, a i + c i < 2 ^ W)
    (hd : ∀ i, d i < 2 ^ W) :
    fieldsCode W a + fieldsCode W c = fieldsCode W d ↔ ∀ i, a i + c i = d i := by
  rw [fieldsCode_add]
  constructor
  · intro heq i
    exact congrFun (fieldsCode_injective h hd heq) i
  · intro heq
    exact congrArg _ (funext heq)

/-- The same for a sum of scalar multiples, which is the shape of the selector conditions
`Xpc % Bⁿ = ∑ₚ p · Sₚ` and the jump equation. -/
theorem fieldsCode_smul_add_eq_iff {n m₁ m₂ : ℕ} {a c d : Fin n → ℕ}
    (h : ∀ i, m₁ * a i + m₂ * c i < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) :
    m₁ * fieldsCode W a + m₂ * fieldsCode W c = fieldsCode W d ↔
      ∀ i, m₁ * a i + m₂ * c i = d i := by
  rw [fieldsCode_smul, fieldsCode_smul]
  exact fieldsCode_add_eq_iff h hd

/-! ### Finite sums of lanes

Every selector condition is a sum over the program's instructions, so the two-term lemmas are
not enough. `Finset` induction lifts them. -/

theorem fieldsCode_sum {ι : Type} (W : ℕ) {n : ℕ} (s : Finset ι) (g : ι → Fin n → ℕ) :
    ∑ p ∈ s, fieldsCode W (g p) = fieldsCode W fun i => ∑ p ∈ s, g p i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, ih, fieldsCode_add]
    exact congrArg _ (funext fun i => (Finset.sum_insert (f := fun q => g q i) hp).symm)

/-- Three scaled packings added, which is the shape every selector equation takes. -/
theorem fieldsCode_three (W : ℕ) {n : ℕ} (a b c : ℕ) (f g h : Fin n → ℕ) :
    a * fieldsCode W f + b * fieldsCode W g + c * fieldsCode W h
      = fieldsCode W fun i => a * f i + b * g i + c * h i := by
  rw [fieldsCode_smul, fieldsCode_smul, fieldsCode_smul, fieldsCode_add, fieldsCode_add]

theorem fieldsCode_sum_smul {ι : Type} (W : ℕ) {n : ℕ} (s : Finset ι)
    (m : ι → ℕ) (g : ι → Fin n → ℕ) :
    ∑ p ∈ s, m p * fieldsCode W (g p) = fieldsCode W fun i => ∑ p ∈ s, m p * g p i := by
  rw [← fieldsCode_sum]
  exact Finset.sum_congr rfl fun p _ => fieldsCode_smul W (m p) (g p)

/-- The selector-condition shape: one global equation between a scaled sum of lanes and a lane
is the family of its block equations. -/
theorem fieldsCode_sum_smul_eq_iff {ι : Type} {W n : ℕ} {s : Finset ι}
    {m : ι → ℕ} {g : ι → Fin n → ℕ} {d : Fin n → ℕ}
    (h : ∀ i, ∑ p ∈ s, m p * g p i < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) :
    ∑ p ∈ s, m p * fieldsCode W (g p) = fieldsCode W d ↔ ∀ i, ∑ p ∈ s, m p * g p i = d i := by
  rw [fieldsCode_sum_smul]
  constructor
  · intro heq i
    exact congrFun (fieldsCode_injective h hd heq) i
  · intro heq
    exact congrArg _ (funext heq)

/-- **Only selected scalars have to fit.** A scaled sum of selectors is blockwise exactly when
every selector that is used *somewhere* carries a scalar below the block bound; a selector that
is identically zero imposes nothing at all.

This is the mechanism behind the disjunctions `Sₚ = 0 ∨ targetₚ < 2 ^ w` in the condition list.
It is what stops an oversized target on an unreachable branch from being required to fit, and it
is why the bound must be stated per branch rather than over the whole program. -/
theorem fieldsCode_selected_smul_eq_iff {ι : Type} {W n : ℕ} {s : Finset ι} {m : ι → ℕ}
    {sel : ι → Fin n → ℕ} {d : Fin n → ℕ}
    (hone : ∀ i, ∑ p ∈ s, sel p i = 1)
    (hfit : ∀ p ∈ s, (∀ i, sel p i = 0) ∨ m p < 2 ^ W)
    (hd : ∀ i, d i < 2 ^ W) :
    ∑ p ∈ s, m p * fieldsCode W (sel p) = fieldsCode W d ↔
      ∀ i, ∑ p ∈ s, m p * sel p i = d i := by
  classical
  refine fieldsCode_sum_smul_eq_iff (fun i => ?_) hd
  -- exactly one selector is `1` at block `i`, so the block value is that selector's scalar
  obtain ⟨p₀, hp₀s, hp₀⟩ : ∃ p ∈ s, sel p i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have h1 := hone i
    rw [Finset.sum_congr rfl fun p hp => hcon p hp] at h1
    simp at h1
  have hle : sel p₀ i ≤ ∑ p ∈ s, sel p i :=
    Finset.single_le_sum (f := fun p => sel p i) (fun _ _ => Nat.zero_le _) hp₀s
  rw [hone i] at hle
  have hp₀one : sel p₀ i = 1 := by omega
  have hsplit : sel p₀ i + ∑ p ∈ s.erase p₀, sel p i = 1 :=
    (Finset.add_sum_erase s (fun p => sel p i) hp₀s).trans (hone i)
  have hzero : ∑ p ∈ s.erase p₀, sel p i = 0 := by omega
  have herase : ∑ p ∈ s.erase p₀, m p * sel p i = 0 :=
    Finset.sum_eq_zero fun p hp => by rw [Finset.sum_eq_zero_iff.mp hzero p hp, mul_zero]
  have hval : ∑ p ∈ s, m p * sel p i = m p₀ := by
    rw [← Finset.add_sum_erase s (fun p => m p * sel p i) hp₀s, herase, hp₀one, mul_one]
    omega
  rw [hval]
  rcases hfit p₀ hp₀s with h | h
  · exact absurd (h i) hp₀
  · exact h

/-! ### Lane masks

A lane's blocks hold `w`-bit values inside `w * (k + 1) + 1`-bit blocks, so the lane data mask is
*narrower* than `BlockPacking`'s `guardMask` and is not an instance of it. These two lemmas are
the ones the globalisation step demands: the mask is a constant packing, and it characterises
both the range and the per-block bound. -/

theorem fieldsCode_const (W v : ℕ) : ∀ {t : ℕ},
    fieldsCode W (fun _ : Fin t => v) = v * geom (2 ^ W) t
  | 0 => by simp [fieldsCode, geom]
  | t + 1 => by
    rw [fieldsCode_succ,
      show ((fun _ : Fin (t + 1) => v) ∘ Fin.succ) = fun _ : Fin t => v from rfl,
      fieldsCode_const W v, geom_succ]
    ring

/-- **The lane mask says exactly what it should.** Being a submask of `(2 ^ v - 1)` repeated in
every block is being below `(2 ^ W) ^ t` with every block below `2 ^ v`. Mirrors
`isBinarySubmask_guardMask_iff`, which is the same statement at `v = W - 1`. -/
theorem isBinarySubmask_constMask_iff {W v : ℕ} (hv : v ≤ W) : ∀ {t X : ℕ},
    Nat.IsBinarySubmask X ((2 ^ v - 1) * geom (2 ^ W) t) ↔
      X < (2 ^ W) ^ t ∧ ∀ i < t, configField W X i < 2 ^ v := by
  intro t
  induction t with
  | zero =>
    intro X
    simp only [geom, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, Nat.lt_one_iff,
      Nat.isBinarySubmask_zero_iff]
    exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  | succ t ih =>
    intro X
    have hlow : 2 ^ v - 1 < 2 ^ W := by
      have h1 : (2 : ℕ) ^ v ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hv
      have h2 : 0 < (2 : ℕ) ^ v := Nat.two_pow_pos v
      omega
    have hB : 0 < (2 : ℕ) ^ W := Nat.two_pow_pos W
    rw [geom_succ, Nat.mul_add, mul_one,
      show (2 ^ v - 1) * (2 ^ W * geom (2 ^ W) t) = 2 ^ W * ((2 ^ v - 1) * geom (2 ^ W) t) by ring,
      Nat.isBinarySubmask_add_mul_two_pow_iff hlow,
      Nat.isBinarySubmask_two_pow_sub_one_iff, ih]
    constructor
    · rintro ⟨hmod, hlt, hblk⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [pow_succ]
        exact (Nat.div_lt_iff_lt_mul hB).mp hlt
      · cases i with
        | zero => rwa [configField_zero]
        | succ i => rw [configField_succ]; exact hblk i (by omega)
    · rintro ⟨hlt, hblk⟩
      refine ⟨by have := hblk 0 (by omega); rwa [configField_zero] at this, ?_,
        fun i hi => ?_⟩
      · refine (Nat.div_lt_iff_lt_mul hB).mpr ?_
        rwa [← pow_succ]
      · have := hblk (i + 1) (by omega)
        rwa [configField_succ] at this

/-- **Normalising a packed witness.** Every masked number is the packing of its own fields, with
each field bounded. This is the first move in every soundness argument: apply it once per
witness, and afterwards work only with `Fin t` functions. -/
theorem packed_eq_fieldsCode {W v t X : ℕ} (hv : v ≤ W)
    (h : Nat.IsBinarySubmask X ((2 ^ v - 1) * geom (2 ^ W) t)) :
    X = fieldsCode W (fun i : Fin t => configField W X i) ∧
      ∀ i : Fin t, configField W X i < 2 ^ v := by
  obtain ⟨hlt, hblk⟩ := (isBinarySubmask_constMask_iff hv).mp h
  exact ⟨(fieldsCode_configField hlt).symm, fun i => hblk i i.isLt⟩

/-! ### The lane decomposition

Why lanes are packed at the *outer* base `B` rather than at their own tight base: the packed run
of #47 is then a scaled sum of the lanes, one global identity, and #47 and #48 are reused
unchanged. -/

theorem fieldsCode_eq_sum (W : ℕ) : ∀ {n : ℕ} (f : Fin n → ℕ),
    fieldsCode W f = ∑ i : Fin n, (2 ^ W) ^ (i : ℕ) * f i := by
  intro n
  induction n with
  | zero => simp [fieldsCode]
  | succ n ih =>
    intro f
    rw [fieldsCode_succ, ih (f ∘ Fin.succ), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, Function.comp_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **`R` is the scaled sum of its lanes.** The identity that lets the selector encoding talk
about registers separately while #47's packed run stays exactly as it is. -/
theorem fieldsCode_configCode_eq_lanes {k : ℕ} (w : ℕ) {n : ℕ} (cs : Fin n → Config k) :
    fieldsCode (w * (k + 1) + 1) (fun i => configCode w (cs i))
      = ∑ j : Fin (k + 1), (2 ^ w) ^ (j : ℕ) *
          fieldsCode (w * (k + 1) + 1)
            (fun i => (@Fin.cons k (fun _ => ℕ) (cs i).pc (cs i).regs) j) := by
  rw [fieldsCode_sum_smul]
  exact congrArg _ (funext fun i => fieldsCode_eq_sum w _)

/-! ### Truncation

`X % Bⁿ` drops the last block: it is what restricts a lane of `n + 1` values to the `n` steps
that have a successor. -/

theorem fieldsCode_snoc (W : ℕ) : ∀ {n : ℕ} (f : Fin (n + 1) → ℕ),
    fieldsCode W f = fieldsCode W (Fin.init f) + (2 ^ W) ^ n * f (Fin.last n) := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [fieldsCode_succ]
    simp [fieldsCode]
  | succ n ih =>
    intro f
    have h2 : ((Fin.init f) ∘ Fin.succ) = Fin.init (f ∘ Fin.succ) := by
      funext i
      exact congrArg f (Fin.ext (by simp))
    have h3 : (f ∘ Fin.succ) (Fin.last n) = f (Fin.last (n + 1)) :=
      congrArg f (Fin.ext (by simp))
    rw [fieldsCode_succ, fieldsCode_succ W n (Fin.init f), h2, ih (f ∘ Fin.succ), h3,
      show (Fin.init f) 0 = f 0 from congrArg f (Fin.ext (by simp))]
    ring

theorem fieldsCode_mod_pow {W n : ℕ} {f : Fin (n + 1) → ℕ} (hf : ∀ i, f i < 2 ^ W) :
    fieldsCode W f % (2 ^ W) ^ n = fieldsCode W (Fin.init f) := by
  rw [fieldsCode_snoc, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (fieldsCode_lt fun i => hf _)

/-! ### Blockwise masking

The other half: a submask condition between packed numbers is the family of submask conditions
between their blocks. This is the one that decides whether *selector validity* is cheap, since
every selector is constrained by a mask rather than an equation. -/

theorem fieldsCode_mod_base (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f % 2 ^ W = f 0 := by
  rw [fieldsCode_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem fieldsCode_div (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f / 2 ^ W = fieldsCode W (f ∘ Fin.succ) := by
  rw [fieldsCode_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt h0,
    Nat.zero_add]

/-- **A submask condition is blockwise too.** This is the lemma that decides the probe: every
selector is constrained by a mask rather than an equation, so if selector validity were to
recreate a bounded universal, it would have to happen here. It does not — the peeling step is
`Nat.isBinarySubmask_add_mul_two_pow_iff`, and the recursion is on the number of blocks. -/
theorem isBinarySubmask_fieldsCode_iff : ∀ {n : ℕ} {a c : Fin n → ℕ}, (∀ i, a i < 2 ^ W) →
    (∀ i, c i < 2 ^ W) →
      (Nat.IsBinarySubmask (fieldsCode W a) (fieldsCode W c) ↔
        ∀ i, Nat.IsBinarySubmask (a i) (c i)) := by
  intro n
  induction n with
  | zero =>
    intro a c _ _
    exact ⟨fun _ i => i.elim0, fun _ => Nat.isBinarySubmask_refl 0⟩
  | succ n ih =>
    intro a c ha hc
    rw [show fieldsCode W c = c 0 + 2 ^ W * fieldsCode W (c ∘ Fin.succ) from fieldsCode_succ W n c,
      Nat.isBinarySubmask_add_mul_two_pow_iff (hc 0), fieldsCode_mod_base W a (ha 0),
      fieldsCode_div W a (ha 0),
      ih (a := a ∘ Fin.succ) (c := c ∘ Fin.succ) (fun i => ha i.succ) (fun i => hc i.succ)]
    constructor
    · rintro ⟨h0, hs⟩ i
      exact Fin.cases h0 (fun j => hs j) i
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-! ### Sums against a one-hot family -/

/-- A sum against an index indicator collapses to one term. -/
theorem sum_indicator {L m : ℕ} (h : m < L) (f : Fin L → ℕ) :
    ∑ p : Fin L, (if (p : ℕ) = m then f p else 0) = f ⟨m, h⟩ := by
  classical
  calc
    ∑ p : Fin L, (if (p : ℕ) = m then f p else 0) =
        ∑ p : Fin L, (if p = ⟨m, h⟩ then f p else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (p : ℕ) = m
      · have hpe : p = ⟨m, h⟩ := Fin.ext (by simpa using hp)
        simp only [hp, hpe, ↓reduceIte]
      · have hpe : p ≠ ⟨m, h⟩ := fun he => hp (by simpa using congrArg Fin.val he)
        simp only [hp, hpe, ↓reduceIte]
    _ = f ⟨m, h⟩ := by simp

/-- A sum whose family vanishes off one index collapses to that index. -/
theorem sum_eq_of_vanishing {L : ℕ} {g : Fin L → ℕ} {q : Fin L} (h : ∀ p, p ≠ q → g p = 0) :
    ∑ p : Fin L, g p = g q :=
  Finset.sum_eq_single q (fun p _ hp => h p hp) (fun hq => absurd (Finset.mem_univ q) hq)

/-- A family of naturals summing to `1` is `1` at one index and `0` everywhere else. -/
theorem exists_unique_of_sum_eq_one {L : ℕ} {g : Fin L → ℕ} (h : ∑ p : Fin L, g p = 1) :
    ∃ q, g q = 1 ∧ ∀ p, p ≠ q → g p = 0 := by
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ p : Fin L, g p ≠ 0)
  have hsplit : g q + ∑ p ∈ Finset.univ.erase q, g p = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ q)]; exact h
  refine ⟨q, by omega, fun p hp => ?_⟩
  have hz : ∑ p ∈ Finset.univ.erase q, g p = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp hz) p (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩)

end RegisterMachine

end Hilbert10
