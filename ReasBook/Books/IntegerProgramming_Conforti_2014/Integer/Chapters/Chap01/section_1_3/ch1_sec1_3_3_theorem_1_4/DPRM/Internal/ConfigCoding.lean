/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachine
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring

/-!
# Configurations as numbers, and one step as arithmetic

Issue #45, the first child of #21. A configuration of a `k`-register machine becomes a single
natural number written in base `2 ^ w`:

```
digit 0     = pc
digit i + 1 = register i
```

and one step of a *fixed* program becomes a relation between two such numbers.

## What is deliberately absent

There is no encoding of `Instr` or of `Program`, no universal interpreter, and no computable
lookup into an encoded program. #20's endpoint is `exists_machine_graph`, so the program is
obtained by existential elimination and is fixed from then on; its instruction list is finite,
and `EncodedStep` is a finite disjunction over it, built nonuniformly by recursion on the list.
An encoding of the program itself would be a universal machine, which nothing here needs.

## Total, permissive semantics

`configField` and `setField` are total: every natural number has fields, and every field can be
overwritten. Bounds are not part of the definitions but hypotheses on the theorems, saying when
a number *represents* the configuration one has in mind. This is the same discipline as
`Function.extend` in `CleanScratch`: no partiality, no well-formedness predicate threaded
through every statement.

## Composition with `BlockPacking`

`FitsConfig` gives `configCode w c < (2 ^ w) ^ (k + 1) = 2 ^ (w * (k + 1))`, so a run of these
configurations packs into `BlockPacking`'s already-proved one-guard-bit layout at data width
`w * (k + 1)`. That is what #47 and #48 consume; choosing `w` large enough is #46's job.

## Main definitions

* `RegisterMachine.configField`, `setField` — reading and writing one base-`2 ^ w` field
* `RegisterMachine.configCode`, `FitsConfig` — a configuration as a number, and when it fits
* `RegisterMachine.decodeConfig` — and back, totally
* `RegisterMachine.EncodedStep` — one step of a fixed program, as a relation on codes

## Main results

* `RegisterMachine.field_configCode_zero`, `field_configCode_succ` — the fields of a code
* `RegisterMachine.configCode_lt`, `configCode_injective`
* `RegisterMachine.encodedStep_iff` — the headline: for an in-range fitting configuration,
  `EncodedStep` holds of exactly one successor, and it is the code of `step P c`
* `RegisterMachine.configCode_decodeConfig`, `decodeConfig_configCode` — the inverse pair
* `RegisterMachine.decodeConfig_step_of_encodedStep` — the decoded step relation, needing only
  a bound on the *predecessor*; this is why #48 does no carry reasoning
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ### Reading a field

`configField w code i` is digit `i` of `code` in base `2 ^ w`. Total: no bounds are assumed. -/

/-- Digit `i` of `code`, reading `code` in base `2 ^ w`. -/
def configField (w code i : ℕ) : ℕ := code / (2 ^ w) ^ i % 2 ^ w

theorem configField_zero (w x : ℕ) : configField w x 0 = x % 2 ^ w := by
  simp [configField]

theorem configField_succ (w x i : ℕ) : configField w x (i + 1) = configField w (x / 2 ^ w) i := by
  rw [configField, configField, Nat.div_div_eq_div_mul,
    show (2 ^ w) ^ (i + 1) = 2 ^ w * (2 ^ w) ^ i by ring]

theorem configField_lt (w x i : ℕ) : configField w x i < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Fields below `i` depend only on `code % (2 ^ w) ^ i`. -/
theorem configField_of_mod {w x i j : ℕ} (hj : j < i) :
    configField w (x % (2 ^ w) ^ i) j = configField w x j := by
  have key : ∀ y : ℕ, configField w y j = y % (2 ^ w) ^ (j + 1) / (2 ^ w) ^ j := by
    intro y
    rw [configField, show (2 ^ w) ^ (j + 1) = (2 ^ w) ^ j * 2 ^ w by ring,
      Nat.mod_mul_right_div_self]
  rw [key, key, Nat.mod_mod_of_dvd _ (pow_dvd_pow _ hj)]

/-- Fields above `i` depend only on `code / (2 ^ w) ^ (i + 1)`. -/
theorem configField_div {w x i j : ℕ} (h : i < j) :
    configField w (x / (2 ^ w) ^ (i + 1)) (j - (i + 1)) = configField w x j := by
  rw [configField, configField, Nat.div_div_eq_div_mul, ← pow_add,
    show i + 1 + (j - (i + 1)) = j by omega]

/-! ### Writing a field -/

/-- Overwrite digit `i` of `code` with `value`, in base `2 ^ w`. Total: the low part is kept,
the old digit dropped, and the high part shifted back into place. -/
def setField (w code i value : ℕ) : ℕ :=
  code % (2 ^ w) ^ i + value * (2 ^ w) ^ i + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1)

/-- `setField` regrouped so that everything above digit `i` is a single multiple of
`(2 ^ w) ^ i`. Every lemma below is a division or a modulus applied to this form. -/
theorem setField_eq (w code i value : ℕ) :
    setField w code i value
      = code % (2 ^ w) ^ i + (value + code / (2 ^ w) ^ (i + 1) * 2 ^ w) * (2 ^ w) ^ i := by
  rw [setField, show (2 ^ w) ^ (i + 1) = (2 ^ w) ^ i * 2 ^ w by ring]
  ring

theorem setField_mod (w code i value : ℕ) :
    setField w code i value % (2 ^ w) ^ i = code % (2 ^ w) ^ i := by
  rw [setField_eq, Nat.add_mul_mod_self_right, Nat.mod_mod_of_dvd _ dvd_rfl]

/-- The written value is bounded, so the high part is untouched. -/
theorem setField_div {w code i value : ℕ} (hv : value < 2 ^ w) :
    setField w code i value / (2 ^ w) ^ (i + 1) = code / (2 ^ w) ^ (i + 1) := by
  have hlow : code % (2 ^ w) ^ i + value * (2 ^ w) ^ i < (2 ^ w) ^ (i + 1) := by
    calc code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        < (2 ^ w) ^ i + value * (2 ^ w) ^ i :=
          by have := Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i); omega
      _ = (value + 1) * (2 ^ w) ^ i := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ i := Nat.mul_le_mul_right _ hv
      _ = (2 ^ w) ^ (i + 1) := by ring
  rw [show setField w code i value
      = code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) from rfl,
    Nat.add_mul_div_right _ _ (pow_pos (Nat.two_pow_pos w) (i + 1)), Nat.div_eq_of_lt hlow,
    Nat.zero_add]

/-- **Read after write.** -/
theorem configField_setField_self {w code i value : ℕ} (hv : value < 2 ^ w) :
    configField w (setField w code i value) i = value := by
  rw [configField, setField_eq,
    Nat.add_mul_div_right _ _ (pow_pos (Nat.two_pow_pos w) i),
    Nat.div_eq_of_lt (Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i)),
    Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

/-- **Read another field.** -/
theorem configField_setField_of_ne {w code i value j : ℕ} (hv : value < 2 ^ w) (hj : j ≠ i) :
    configField w (setField w code i value) j = configField w code j := by
  rcases Nat.lt_or_ge j i with h | h
  · rw [← configField_of_mod h, setField_mod, configField_of_mod h]
  · have h : i < j := by omega
    rw [← configField_div h, setField_div hv, configField_div h]

/-- Writing a field inside range keeps the number inside range. -/
theorem setField_lt {w n code i value : ℕ} (hc : code < (2 ^ w) ^ n) (hi : i < n)
    (hv : value < 2 ^ w) : setField w code i value < (2 ^ w) ^ n := by
  have hlow : code % (2 ^ w) ^ i + value * (2 ^ w) ^ i < (2 ^ w) ^ (i + 1) := by
    calc code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        < (2 ^ w) ^ i + value * (2 ^ w) ^ i :=
          by have := Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i); omega
      _ = (value + 1) * (2 ^ w) ^ i := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ i := Nat.mul_le_mul_right _ hv
      _ = (2 ^ w) ^ (i + 1) := by ring
  have hhigh : code / (2 ^ w) ^ (i + 1) < (2 ^ w) ^ (n - (i + 1)) := by
    refine Nat.div_lt_of_lt_mul ?_
    calc code < (2 ^ w) ^ n := hc
      _ = (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (n - (i + 1)) := by
          rw [← pow_add]; congr 1; omega
  calc setField w code i value
      = code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) := rfl
    _ < (2 ^ w) ^ (i + 1) + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) := by omega
    _ = (code / (2 ^ w) ^ (i + 1) + 1) * (2 ^ w) ^ (i + 1) := by ring
    _ ≤ (2 ^ w) ^ (n - (i + 1)) * (2 ^ w) ^ (i + 1) := Nat.mul_le_mul_right _ hhigh
    _ = (2 ^ w) ^ n := by rw [← pow_add]; congr 1; omega

/-! ### Codes of field vectors -/

/-- The base-`2 ^ w` code of a field vector: `f i` in place `i`. -/
def fieldsCode (w : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, f => f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ)

theorem fieldsCode_succ (w n : ℕ) (f : Fin (n + 1) → ℕ) :
    fieldsCode w f = f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := rfl

theorem fieldsCode_lt {w : ℕ} : ∀ {n : ℕ} {f : Fin n → ℕ}, (∀ i, f i < 2 ^ w) →
    fieldsCode w f < (2 ^ w) ^ n := by
  intro n
  induction n with
  | zero => intro f _; simp [fieldsCode]
  | succ n ih =>
    intro f hf
    have hrest : fieldsCode w (f ∘ Fin.succ) < (2 ^ w) ^ n := ih fun i => hf i.succ
    calc fieldsCode w f = f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := rfl
      _ < 2 ^ w + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := by have := hf 0; omega
      _ = 2 ^ w * (fieldsCode w (f ∘ Fin.succ) + 1) := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ n := Nat.mul_le_mul_left _ hrest
      _ = (2 ^ w) ^ (n + 1) := by ring

@[simp] theorem fieldsCode_const_zero (w : ℕ) : ∀ {n : ℕ}, fieldsCode w (fun _ : Fin n => 0) = 0
  | 0 => rfl
  | n + 1 => by
    rw [fieldsCode_succ, show ((fun _ : Fin (n + 1) => 0) ∘ Fin.succ) = fun _ : Fin n => 0 from rfl,
      fieldsCode_const_zero w]
    simp

theorem field_fieldsCode {w : ℕ} : ∀ {n : ℕ} {f : Fin n → ℕ}, (∀ i, f i < 2 ^ w) →
    ∀ i : Fin n, configField w (fieldsCode w f) i = f i := by
  intro n
  induction n with
  | zero => intro f _ i; exact i.elim0
  | succ n ih =>
    intro f hf i
    refine Fin.cases ?_ ?_ i
    · rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, fieldsCode_succ, configField_zero,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0)]
    · intro j
      rw [Fin.val_succ, configField_succ, fieldsCode_succ,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (hf 0), Nat.zero_add]
      exact ih (fun i => hf i.succ) j

/-- Every number below `(2 ^ w) ^ n` is the code of its own first `n` fields. -/
theorem fieldsCode_configField {w : ℕ} : ∀ {n z : ℕ}, z < (2 ^ w) ^ n →
    fieldsCode w (fun i : Fin n => configField w z i) = z := by
  intro n
  induction n with
  | zero => intro z hz; simp only [pow_zero] at hz; simpa [fieldsCode] using (by omega : 0 = z)
  | succ n ih =>
    intro z hz
    have hz' : z / 2 ^ w < (2 ^ w) ^ n := by
      refine Nat.div_lt_of_lt_mul ?_
      calc z < (2 ^ w) ^ (n + 1) := hz
        _ = 2 ^ w * (2 ^ w) ^ n := by ring
    rw [fieldsCode_succ,
      show ((fun i : Fin (n + 1) => configField w z i) ∘ Fin.succ)
          = fun i : Fin n => configField w (z / 2 ^ w) i from by
        funext i; simp only [Function.comp_apply, Fin.val_succ]; exact configField_succ w z i,
      ih hz', show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, configField_zero]
    exact Nat.mod_add_div z (2 ^ w)

/-- Two numbers below `(2 ^ w) ^ n` with the same first `n` fields are equal. This is the
extensionality principle every `configCode` computation below goes through. -/
theorem eq_of_configField_eq {w n x y : ℕ} (hx : x < (2 ^ w) ^ n) (hy : y < (2 ^ w) ^ n)
    (h : ∀ i < n, configField w x i = configField w y i) : x = y := by
  rw [← fieldsCode_configField hx, ← fieldsCode_configField hy]
  exact congrArg _ (funext fun i => h i i.isLt)

/-! ### Configurations -/

/-- A configuration as a number: the program counter in digit `0`, register `i` in digit
`i + 1`, base `2 ^ w`. -/
def configCode (w : ℕ) (c : Config k) : ℕ := fieldsCode w (@Fin.cons k (fun _ => ℕ) c.pc c.regs)

/-- `c` fits in width `w` when its program counter and every register are below `2 ^ w`. -/
def FitsConfig (w : ℕ) (c : Config k) : Prop := c.pc < 2 ^ w ∧ ∀ r, c.regs r < 2 ^ w

theorem configFields_lt {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    ∀ i : Fin (k + 1), @Fin.cons k (fun _ => ℕ) c.pc c.regs i < 2 ^ w := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using h.1
  · intro r; simpa using h.2 r

theorem field_configCode_zero {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configField w (configCode w c) 0 = c.pc := by
  have := field_fieldsCode (configFields_lt h) 0
  simpa [configCode] using this

theorem field_configCode_succ {w : ℕ} {c : Config k} (h : FitsConfig w c) (r : Fin k) :
    configField w (configCode w c) ((r : ℕ) + 1) = c.regs r := by
  have := field_fieldsCode (configFields_lt h) r.succ
  simpa [configCode] using this

theorem configCode_lt {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < (2 ^ w) ^ (k + 1) :=
  fieldsCode_lt (configFields_lt h)

/-- The bound in the shape `BlockPacking` wants: a configuration is a datum of width
`w * (k + 1)`. -/
theorem configCode_lt_two_pow {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < 2 ^ (w * (k + 1)) := by
  rw [pow_mul]; exact configCode_lt h

theorem configCode_injective {w : ℕ} {c₁ c₂ : Config k} (h₁ : FitsConfig w c₁)
    (h₂ : FitsConfig w c₂) (h : configCode w c₁ = configCode w c₂) : c₁ = c₂ := by
  have hpc : c₁.pc = c₂.pc := by
    rw [← field_configCode_zero h₁, ← field_configCode_zero h₂, h]
  have hregs : c₁.regs = c₂.regs := by
    funext r
    rw [← field_configCode_succ h₁ r, ← field_configCode_succ h₂ r, h]
  obtain ⟨p₁, r₁⟩ := c₁
  obtain ⟨p₂, r₂⟩ := c₂
  simp only [Config.mk.injEq]
  exact ⟨hpc, hregs⟩

/-- The exhaustive partition of a field index: the program counter, or one register. -/
theorem index_cases {i : ℕ} (hi : i < k + 1) : i = 0 ∨ ∃ r : Fin k, (r : ℕ) + 1 = i := by
  cases i with
  | zero => exact Or.inl rfl
  | succ n => exact Or.inr ⟨⟨n, by omega⟩, rfl⟩

/-- Jumping: writing the program counter field is exactly the code of the jumped-to
configuration. -/
theorem configCode_setPc {w : ℕ} {c : Config k} (h : FitsConfig w c) {j : ℕ} (hj : j < 2 ^ w) :
    configCode w (⟨j, c.regs⟩ : Config k) = setField w (configCode w c) 0 j := by
  have hfit : FitsConfig w (⟨j, c.regs⟩ : Config k) := ⟨hj, h.2⟩
  refine eq_of_configField_eq (configCode_lt hfit)
    (setField_lt (configCode_lt h) (Nat.succ_pos k) hj) ?_
  intro i hi
  rcases index_cases hi with rfl | ⟨r, rfl⟩
  · rw [field_configCode_zero hfit, configField_setField_self hj]
  · rw [field_configCode_succ hfit r, configField_setField_of_ne hj (by omega),
      field_configCode_succ h r]

/-- Jumping and updating one register at once. Both machine instructions have this shape, and
this is the only place `configCode` is computed field by field. -/
theorem configCode_update {w : ℕ} {c : Config k} (h : FitsConfig w c) {j : ℕ} (hj : j < 2 ^ w)
    (r : Fin k) {v : ℕ} (hv : v < 2 ^ w) :
    configCode w (⟨j, Function.update c.regs r v⟩ : Config k)
      = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1) v := by
  have hfit : FitsConfig w (⟨j, Function.update c.regs r v⟩ : Config k) := by
    refine ⟨hj, fun s => ?_⟩
    rcases eq_or_ne s r with rfl | hs
    · simpa using hv
    · simpa [Function.update_of_ne hs] using h.2 s
  have hr : (r : ℕ) + 1 < k + 1 := by have := r.isLt; omega
  refine eq_of_configField_eq (configCode_lt hfit)
    (setField_lt (setField_lt (configCode_lt h) (Nat.succ_pos k) hj) hr hv) ?_
  intro i hi
  rcases index_cases hi with rfl | ⟨s, rfl⟩
  · rw [field_configCode_zero hfit, configField_setField_of_ne hv (by omega),
      configField_setField_self hj]
  · rw [field_configCode_succ hfit s]
    rcases eq_or_ne s r with rfl | hs
    · rw [configField_setField_self hv]
      simp
    · have hsr : (s : ℕ) ≠ (r : ℕ) := fun hh => hs (Fin.ext hh)
      rw [configField_setField_of_ne hv (by omega), configField_setField_of_ne hj (by omega),
        field_configCode_succ h s]
      simp [Function.update_of_ne hs]

/-! ### Decoding

The inverse of `configCode`, total like everything else here. #48 runs it on every block of a
packed run, so it must not carry a fitting hypothesis. -/

/-- The configuration a number codes, read field by field. -/
def decodeConfig (w z : ℕ) : Config k :=
  ⟨configField w z 0, fun r => configField w z ((r : ℕ) + 1)⟩

/-- Unconditional: every extracted field is a remainder modulo `2 ^ w`. -/
theorem fits_decodeConfig {w z : ℕ} : FitsConfig w (decodeConfig (k := k) w z) :=
  ⟨configField_lt w z 0, fun r => configField_lt w z ((r : ℕ) + 1)⟩

theorem configCode_decodeConfig {w z : ℕ} (hz : z < 2 ^ (w * (k + 1))) :
    configCode w (decodeConfig (k := k) w z) = z := by
  rw [pow_mul] at hz
  rw [configCode,
    show @Fin.cons k (fun _ => ℕ) (decodeConfig (k := k) w z).pc (decodeConfig (k := k) w z).regs
        = fun i : Fin (k + 1) => configField w z i from by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro r; rw [Fin.cons_succ, Fin.val_succ]; rfl]
  exact fieldsCode_configField hz

theorem decodeConfig_configCode {w : ℕ} {c : Config k} (hc : FitsConfig w c) :
    decodeConfig w (configCode w c) = c := by
  obtain ⟨p, r⟩ := c
  simp only [decodeConfig, Config.mk.injEq]
  exact ⟨field_configCode_zero hc, funext fun s => field_configCode_succ hc s⟩

/-! ### One step, as a relation on codes

The program is *fixed*. `EncodedStep` is a finite disjunction over its instruction list, built by
recursion on that list: nothing here encodes a program or looks an instruction up. -/

/-- The encoded effect of the single instruction `I` sitting at index `p`. The first conjunct
pins the program counter, which is what makes the disjunction below exclusive. -/
def Instr.EncodedStep (w p : ℕ) : Instr k → ℕ → ℕ → Prop
  | .inc r j => fun b a =>
      configField w b 0 = p ∧ j < 2 ^ w ∧ configField w b ((r : ℕ) + 1) + 1 < 2 ^ w ∧
        a = setField w (setField w b 0 j) ((r : ℕ) + 1) (configField w b ((r : ℕ) + 1) + 1)
  | .dec r jpos jzero => fun b a =>
      configField w b 0 = p ∧
        ((configField w b ((r : ℕ) + 1) = 0 ∧ jzero < 2 ^ w ∧ a = setField w b 0 jzero) ∨
          (0 < configField w b ((r : ℕ) + 1) ∧ jpos < 2 ^ w ∧
            a = setField w (setField w b 0 jpos) ((r : ℕ) + 1)
              (configField w b ((r : ℕ) + 1) - 1)))

/-- The disjunction over a suffix of the program whose first instruction sits at index `p`. -/
def encodedStepFrom (w : ℕ) : ℕ → Program k → ℕ → ℕ → Prop
  | _, [], _, _ => False
  | p, I :: rest, b, a => I.EncodedStep w p b a ∨ encodedStepFrom w (p + 1) rest b a

/-- **One step of a fixed program, as a relation between two codes.** -/
def EncodedStep (P : Program k) (w b a : ℕ) : Prop := encodedStepFrom w 0 P b a

/-- The disjunction, read as a bounded existential over instruction indices. -/
theorem encodedStepFrom_iff (w : ℕ) : ∀ (L : Program k) (p b a : ℕ),
    encodedStepFrom w p L b a ↔ ∃ q, ∃ _ : q < L.length, (L[q]).EncodedStep w (p + q) b a := by
  intro L
  induction L with
  | nil => intro p b a; simp [encodedStepFrom]
  | cons I rest ih =>
    intro p b a
    rw [show encodedStepFrom w p (I :: rest) b a
        = (I.EncodedStep w p b a ∨ encodedStepFrom w (p + 1) rest b a) from rfl, ih]
    constructor
    · rintro (hI | ⟨q, hq, hstep⟩)
      · exact ⟨0, by simp, by simpa using hI⟩
      · exact ⟨q + 1, by simpa using hq, by simpa [Nat.add_assoc, Nat.add_comm 1 q] using hstep⟩
    · rintro ⟨q, hq, hstep⟩
      cases q with
      | zero => exact Or.inl (by simpa using hstep)
      | succ q =>
        refine Or.inr ⟨q, by simpa using hq, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 q] using hstep

theorem encodedStep_iff_exists {P : Program k} {w b a : ℕ} :
    EncodedStep P w b a ↔ ∃ q, ∃ _ : q < P.length, (P[q]).EncodedStep w q b a := by
  rw [EncodedStep]
  simpa using encodedStepFrom_iff w P 0 b a

/-- The instruction at the current program counter, encoded, is satisfied by exactly the code of
the successor configuration — and only when that successor fits. -/
theorem instr_encodedStep_iff {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) :
    (P[c.pc]'hpc).EncodedStep w c.pc (configCode w c) z ↔
      FitsConfig w (step P c) ∧ z = configCode w (step P c) := by
  have hstep : step P c = (P[c.pc]'hpc).exec c.regs :=
    step_of_getElem? (List.getElem?_eq_getElem hpc)
  have hpc0 : configField w (configCode w c) 0 = c.pc := field_configCode_zero hc
  rcases hI : (P[c.pc]'hpc) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
  · -- `inc r j`
    have hexec : step P c = ⟨j, Function.update c.regs r (c.regs r + 1)⟩ := by
      rw [hstep, hI]; rfl
    have hreg : configField w (configCode w c) ((r : ℕ) + 1) = c.regs r :=
      field_configCode_succ hc r
    have hE : Instr.EncodedStep w c.pc (Instr.inc r j) (configCode w c) z ↔
        (j < 2 ^ w ∧ c.regs r + 1 < 2 ^ w ∧
          z = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1) (c.regs r + 1)) := by
      rw [show Instr.EncodedStep w c.pc (Instr.inc r j) (configCode w c) z
          = (configField w (configCode w c) 0 = c.pc ∧ j < 2 ^ w ∧
              configField w (configCode w c) ((r : ℕ) + 1) + 1 < 2 ^ w ∧
              z = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1)
                (configField w (configCode w c) ((r : ℕ) + 1) + 1)) from rfl, hreg]
      exact and_iff_right hpc0
    rw [hE, hexec]
    constructor
    · rintro ⟨hj, hv, hz⟩
      refine ⟨⟨hj, fun s => ?_⟩, by rw [hz, configCode_update hc hj r hv]⟩
      rcases eq_or_ne s r with rfl | hs
      · simpa using hv
      · simpa [Function.update_of_ne hs] using hc.2 s
    · rintro ⟨hfit, hz⟩
      have hj : j < 2 ^ w := hfit.1
      have hv : c.regs r + 1 < 2 ^ w := by simpa using hfit.2 r
      exact ⟨hj, hv, by rw [hz, configCode_update hc hj r hv]⟩
  · -- `dec r jpos jzero`
    have hreg : configField w (configCode w c) ((r : ℕ) + 1) = c.regs r :=
      field_configCode_succ hc r
    have hE : Instr.EncodedStep w c.pc (Instr.dec r jpos jzero) (configCode w c) z ↔
        ((c.regs r = 0 ∧ jzero < 2 ^ w ∧ z = setField w (configCode w c) 0 jzero) ∨
          (0 < c.regs r ∧ jpos < 2 ^ w ∧
            z = setField w (setField w (configCode w c) 0 jpos) ((r : ℕ) + 1)
              (c.regs r - 1))) := by
      rw [show Instr.EncodedStep w c.pc (Instr.dec r jpos jzero) (configCode w c) z
          = (configField w (configCode w c) 0 = c.pc ∧
              ((configField w (configCode w c) ((r : ℕ) + 1) = 0 ∧ jzero < 2 ^ w ∧
                  z = setField w (configCode w c) 0 jzero) ∨
                (0 < configField w (configCode w c) ((r : ℕ) + 1) ∧ jpos < 2 ^ w ∧
                  z = setField w (setField w (configCode w c) 0 jpos) ((r : ℕ) + 1)
                    (configField w (configCode w c) ((r : ℕ) + 1) - 1)))) from rfl,
        hreg]
      exact and_iff_right hpc0
    rw [hE]
    rcases Nat.eq_zero_or_pos (c.regs r) with hz | hz
    · have hexec : step P c = ⟨jzero, c.regs⟩ := by rw [hstep, hI]; simp [Instr.exec, hz]
      rw [hexec]
      constructor
      · rintro (⟨-, hj, h⟩ | ⟨h, -, -⟩)
        · exact ⟨⟨hj, hc.2⟩, by rw [h, configCode_setPc hc hj]⟩
        · omega
      · rintro ⟨hfit, h⟩
        exact Or.inl ⟨hz, hfit.1, by rw [h, configCode_setPc hc hfit.1]⟩
    · have hexec : step P c = ⟨jpos, Function.update c.regs r (c.regs r - 1)⟩ := by
        rw [hstep, hI]; simp [Instr.exec, Nat.ne_of_gt hz]
      have hv : c.regs r - 1 < 2 ^ w := by have := hc.2 r; omega
      rw [hexec]
      constructor
      · rintro (⟨h, -, -⟩ | ⟨-, hj, h⟩)
        · omega
        · refine ⟨⟨hj, fun s => ?_⟩, by rw [h, configCode_update hc hj r hv]⟩
          rcases eq_or_ne s r with rfl | hs
          · simpa using hv
          · simpa [Function.update_of_ne hs] using hc.2 s
      · rintro ⟨hfit, h⟩
        exact Or.inr ⟨hz, hfit.1, by rw [h, configCode_update hc hfit.1 r hv]⟩

/-- **The headline theorem.** For an in-range configuration that fits, the encoded step relation
holds of exactly one number, and only when the real successor fits too.

The successor-fit conjunct is not decoration. `setField` is permissive, so an out-of-range
written value carries into the next field and the resulting code is still bounded: with `w = 2`,
`[inc 0 1, dec 1 2 2]` from `⟨0, ![3, 0]⟩` would encode `⟨1, ![4, 0]⟩` as `17`, whose digits are
`(1, 0, 1)`, and the encoded run would then decrement the carried `1` and terminate at `0` where
the machine terminates at `4`. Every code stays below the bound throughout, so no outer block
constraint catches it. The per-instruction bound conjuncts are what rule it out, and #48 needs
them because the successor-fit hypothesis is not available during soundness.

Only in-range configurations get a case. `Accepts` never steps its terminal configuration, so
there is no out-of-range branch to add — and adding one would cost a disequality guard in every
disjunct downstream. -/
theorem encodedStep_iff {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) :
    EncodedStep P w (configCode w c) z ↔
      FitsConfig w (step P c) ∧ z = configCode w (step P c) := by
  rw [encodedStep_iff_exists]
  constructor
  · rintro ⟨q, hq, hstep⟩
    have hqc : q = c.pc := by
      rcases hI : (P[q]'hq) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩ <;>
        · rw [hI] at hstep
          have := hstep.1
          rw [field_configCode_zero hc] at this
          omega
    subst hqc
    exact (instr_encodedStep_iff hc hpc).mp hstep
  · intro h
    exact ⟨c.pc, hpc, (instr_encodedStep_iff hc hpc).mpr h⟩

/-- Widening the field width preserves fitting. #46 chooses one width large enough for every
configuration of a run; this is what lets a per-configuration bound be promoted to it. -/
theorem FitsConfig.mono {w w' : ℕ} {c : Config k} (h : FitsConfig w c) (hw : w ≤ w') :
    FitsConfig w' c :=
  ⟨lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by norm_num) hw),
    fun r => lt_of_lt_of_le (h.2 r) (Nat.pow_le_pow_right (by norm_num) hw)⟩

/-- Soundness, in the form #48 uses: a related successor code *is* the code of the real
successor, and the real successor fits. No fit hypothesis about the successor is needed. -/
theorem eq_configCode_step_of_encodedStep {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) (h : EncodedStep P w (configCode w c) z) :
    FitsConfig w (step P c) ∧ z = configCode w (step P c) :=
  (encodedStep_iff hc hpc).mp h

/-- Completeness, in the form #47 uses: the intended successor is related. -/
theorem encodedStep_configCode {P : Program k} {w : ℕ} {c : Config k} (hc : FitsConfig w c)
    (hs : FitsConfig w (step P c)) (hpc : c.pc < P.length) :
    EncodedStep P w (configCode w c) (configCode w (step P c)) :=
  (encodedStep_iff hc hpc).mpr ⟨hs, rfl⟩

/-- Determinism. -/
theorem encodedStep_unique {P : Program k} {w : ℕ} {c : Config k} {z₁ z₂ : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length)
    (h₁ : EncodedStep P w (configCode w c) z₁) (h₂ : EncodedStep P w (configCode w c) z₂) :
    z₁ = z₂ :=
  ((encodedStep_iff hc hpc).mp h₁).2.trans ((encodedStep_iff hc hpc).mp h₂).2.symm

/-- Nothing at all is related when the real successor overflows the width. This is the whole
content of the correction: an overflowing step is *unrepresentable* at that width rather than
represented wrongly, and #46's job is to choose a width where it never happens. -/
theorem not_encodedStep_of_not_fits {P : Program k} {w : ℕ} {c : Config k}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) (hs : ¬ FitsConfig w (step P c)) (z : ℕ) :
    ¬ EncodedStep P w (configCode w c) z :=
  fun h => hs ((encodedStep_iff hc hpc).mp h).1

/-- The counterexample above, kept as a regression: at width `2` the machine's first step
overflows register `0`, and the strengthened relation has no successor for it. -/
example (z : ℕ) :
    ¬ EncodedStep ([.inc 0 1, .dec 1 2 2] : Program 2) 2
      (configCode 2 ⟨0, fun i : Fin 2 => if i = 0 then 3 else 0⟩) z := by
  refine not_encodedStep_of_not_fits ⟨by norm_num, fun r => ?_⟩ (by norm_num) (fun h => ?_) z
  · dsimp only; split <;> norm_num
  · have := h.2 0
    rw [show step ([.inc 0 1, .dec 1 2 2] : Program 2) ⟨0, fun i : Fin 2 => if i = 0 then 3 else 0⟩
        = ⟨1, Function.update (fun i : Fin 2 => if i = 0 then 3 else 0) 0 4⟩ from rfl] at this
    norm_num at this

/-! ### The seams #48 consumes

Both directions of the step relation, packaged so that all carry reasoning stays here. -/

/-- The program counter of a related code is in range. #48 needs this before it can apply
`encodedStep_iff`, and the relation already contains it: every disjunct pins the field. -/
theorem configField_zero_lt_of_encodedStep {P : Program k} {w b a : ℕ}
    (h : EncodedStep P w b a) : configField w b 0 < P.length := by
  obtain ⟨q, hq, hstep⟩ := encodedStep_iff_exists.mp h
  rcases hI : (P[q]'hq) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩ <;>
    · rw [hI] at hstep
      rw [hstep.1]
      exact hq

/-- **Soundness of one step, decoded.** Only the bound on `b` is needed: the strengthened
`encodedStep_iff` already proves that the real successor fits and that `a` is its exact code. -/
theorem decodeConfig_step_of_encodedStep {P : Program k} {w b a : ℕ}
    (hb : b < 2 ^ (w * (k + 1))) (h : EncodedStep P w b a) :
    decodeConfig w a = step P (decodeConfig (k := k) w b) := by
  have hc : FitsConfig w (decodeConfig (k := k) w b) := fits_decodeConfig
  have hcode : configCode w (decodeConfig (k := k) w b) = b := configCode_decodeConfig hb
  have hpc : (decodeConfig (k := k) w b).pc < P.length :=
    configField_zero_lt_of_encodedStep h
  rw [← hcode] at h
  obtain ⟨hfit, ha⟩ := (encodedStep_iff hc hpc).mp h
  rw [ha, decodeConfig_configCode hfit]

end RegisterMachine

end Hilbert10
