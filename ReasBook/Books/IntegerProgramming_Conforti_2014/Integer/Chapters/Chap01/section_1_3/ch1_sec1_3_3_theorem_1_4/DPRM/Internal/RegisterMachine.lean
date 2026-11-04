/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Register machines

Issue #19: the smallest machine model that can be arithmetised. A program is a list of
instructions over `Fin k` registers; a configuration is a program counter together with a
register file.

Mathlib has no register, Minsky or FRACTRAN machine at the pinned revision — `TMToPartrec` and
the `Turing.TM*` files are tape-flavoured, which is the wrong shape here. The point of this
model is that a configuration is a *number*, and tapes are not.

## Design

Three decisions, each made to keep #20 and #21 cheap, since every feature here is paid for twice.

**No `halt` instruction.** A configuration is halted exactly when its program counter is out of
range. This makes list concatenation the sequential-composition operator: a machine "exits" by
jumping to `P.length`, and in `P ++ Q` that same jump is `Q`'s entry point. An explicit `halt`
would need a separate rule for what concatenation does to it.

**Every instruction carries its jump targets**, including `inc`, which could have fallen through
to `pc + 1`. Uniform shape means relocating a program is a single map over targets rather than a
case split, which is what #39 consumes.

**No configuration encoding here.** The acceptance criteria originally asked for the encoded
configuration and its step lemma; that obligation now lives in #45, where the base and guard-bit
width are chosen together with the run packing they have to fit.

## Main definitions

* `RegisterMachine.Instr`, `Program`, `Config`
* `RegisterMachine.step`, `run`, `Halted`, `Halts`
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- An instruction over `k` registers.

`inc r j` increments register `r` and jumps to `j`. `dec r jpos jzero` jumps to `jzero` leaving
the registers alone if register `r` is zero, and otherwise decrements it and jumps to `jpos`. -/
inductive Instr (k : ℕ) where
  | inc (r : Fin k) (j : ℕ)
  | dec (r : Fin k) (jpos jzero : ℕ)
  deriving DecidableEq, Repr

/-- A program is a list of instructions; the program counter indexes into it. -/
abbrev Program (k : ℕ) := List (Instr k)

/-- A configuration: a program counter and a register file. -/
structure Config (k : ℕ) where
  /-- The program counter. Out of range means halted. -/
  pc : ℕ
  /-- The contents of the registers. -/
  regs : Fin k → ℕ

/-- The configuration reached by executing `i` on the register file `regs`. -/
def Instr.exec (i : Instr k) (regs : Fin k → ℕ) : Config k :=
  match i with
  | .inc r j => ⟨j, Function.update regs r (regs r + 1)⟩
  | .dec r jpos jzero =>
      if regs r = 0 then ⟨jzero, regs⟩ else ⟨jpos, Function.update regs r (regs r - 1)⟩

/-- One step of `P`. A configuration whose program counter is out of range steps to itself. -/
def step (P : Program k) (c : Config k) : Config k :=
  match P[c.pc]? with
  | none => c
  | some i => i.exec c.regs

/-- `c` is halted for `P` when its program counter is out of range. -/
def Halted (P : Program k) (c : Config k) : Prop := P.length ≤ c.pc

instance (P : Program k) (c : Config k) : Decidable (Halted P c) := Nat.decLe _ _

theorem halted_iff_getElem?_eq_none {P : Program k} {c : Config k} :
    Halted P c ↔ P[c.pc]? = none :=
  List.getElem?_eq_none_iff.symm

@[simp] theorem step_of_halted {P : Program k} {c : Config k} (h : Halted P c) : step P c = c := by
  simp [step, halted_iff_getElem?_eq_none.mp h]

theorem step_of_getElem? {P : Program k} {c : Config k} {i : Instr k} (h : P[c.pc]? = some i) :
    step P c = i.exec c.regs := by
  simp [step, h]

/-- `run P c n` is the configuration after `n` steps of `P` from `c`. -/
def run (P : Program k) (c : Config k) (n : ℕ) : Config k := (step P)^[n] c

@[simp] theorem run_zero (P : Program k) (c : Config k) : run P c 0 = c := rfl

theorem run_succ (P : Program k) (c : Config k) (n : ℕ) :
    run P c (n + 1) = step P (run P c n) :=
  Function.iterate_succ_apply' _ _ _

theorem run_succ' (P : Program k) (c : Config k) (n : ℕ) :
    run P c (n + 1) = run P (step P c) n :=
  Function.iterate_succ_apply _ _ _

theorem run_add (P : Program k) (c : Config k) (m n : ℕ) :
    run P c (m + n) = run P (run P c m) n := by
  simp [run, Nat.add_comm m n, Function.iterate_add_apply]

/-- Halting is stable: once out of range, the program counter stays out of range. -/
theorem run_of_halted {P : Program k} {c : Config k} {n : ℕ} (h : Halted P (run P c n)) (m : ℕ) :
    run P c (n + m) = run P c n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, run_succ, ih, step_of_halted h]

theorem halted_run_of_le {P : Program k} {c : Config k} {n m : ℕ} (h : Halted P (run P c n))
    (hnm : n ≤ m) : Halted P (run P c m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [run_of_halted h]
  exact h

/-- `P` halts from `c` when some run reaches an out-of-range program counter. -/
def Halts (P : Program k) (c : Config k) : Prop := ∃ n, Halted P (run P c n)

theorem Halts.of_halted {P : Program k} {c : Config k} (h : Halted P c) : Halts P c :=
  ⟨0, h⟩

theorem halts_iff_step {P : Program k} {c : Config k} :
    Halts P c ↔ Halted P c ∨ Halts P (step P c) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl hn
    | succ n => exact Or.inr ⟨n, by rwa [← run_succ']⟩
  · rintro (h | ⟨n, hn⟩)
    · exact ⟨0, h⟩
    · exact ⟨n + 1, by rwa [run_succ']⟩

/-!
## A smoke test

The decrement loop of the route spike (#15), as a one-register, one-instruction machine. It
exercises the only nonstandard choice in the model — that halting is a program counter out of
range rather than an instruction — and confirms that a `dec` whose zero-branch jumps to
`P.length` does in fact stop.
-/

/-- Decrement register `0` until it is zero. -/
def decLoop : Program 1 := [.dec 0 0 1]

theorem step_decLoop_succ (n : ℕ) : step decLoop ⟨0, fun _ => n + 1⟩ = ⟨0, fun _ => n⟩ := by
  rw [step_of_getElem? (i := .dec 0 0 1) rfl]
  simp only [Instr.exec, Nat.succ_ne_zero, if_false, Config.mk.injEq, true_and]
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp

theorem run_decLoop (n : ℕ) : run decLoop ⟨0, fun _ => n⟩ n = ⟨0, fun _ => 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ', step_decLoop_succ, ih]

theorem halts_decLoop (n : ℕ) : Halts decLoop ⟨0, fun _ => n⟩ := by
  refine ⟨n + 1, ?_⟩
  rw [run_succ, run_decLoop, step_of_getElem? (i := .dec 0 0 1) rfl]
  simp [Instr.exec, Halted, decLoop]

end RegisterMachine

end Hilbert10
