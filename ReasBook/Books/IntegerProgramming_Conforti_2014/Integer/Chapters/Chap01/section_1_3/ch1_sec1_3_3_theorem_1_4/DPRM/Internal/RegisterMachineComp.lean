module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachine

/-!
# Combining register machines

Issue #39: the two operations every constructor case in #40–#43 uses, together with the lemmas
that say they are semantically harmless.

**Renaming** moves a machine's registers into a larger register file along an injective
`σ : Fin k → Fin k'`. **Relocation** adds a constant to every jump target, so that `P ++ shiftJumps
P.length Q` runs `P` and then `Q`.

## Scope

This file proves that renaming and relocation are harmless; it does not choose names. There is
no fresh-register allocator, no name supply and no constraint generation here — choosing which
registers a compiled program uses is ordinary bookkeeping done case by case in #40–#43. The
distinction matters because the general version of "choose names for me" is #29, the deferred
DSL, arriving through the side door.

For the same reason there is no well-formedness predicate on programs. Sequencing needs to know
that `P` exits at exactly `P.length` rather than jumping past it, but that is a hypothesis on the
particular run, discharged where the program is built, not a global invariant every lemma has to
carry. This follows the project's rule of giving encoded objects total semantics and proving the
completeness side separately.

## Main results

* `Renamed.run`, `halts_renameRegs_iff` — execution equivariance under renaming
* `run_append_of_lt` — a prefix runs unchanged inside a longer program
* `run_append_shiftJumps` — the relocated suffix runs as itself, offset by `P.length`
* `halts_append_of_exits` — sequencing, given that the prefix exits at exactly `P.length`
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k k' k'' : ℕ}

/-! ## Renaming registers -/

/-- Rename the register an instruction touches. Jump targets are untouched. -/
def Instr.renameRegs (σ : Fin k → Fin k') : Instr k → Instr k'
  | .inc r j => .inc (σ r) j
  | .dec r jpos jzero => .dec (σ r) jpos jzero

/-- Rename every register of a program. -/
def renameRegs (σ : Fin k → Fin k') (P : Program k) : Program k' :=
  P.map (Instr.renameRegs σ)

@[simp] theorem Instr.renameRegs_id (i : Instr k) : i.renameRegs id = i := by
  cases i <;> rfl

@[simp] theorem Instr.renameRegs_comp (σ : Fin k → Fin k') (τ : Fin k' → Fin k'') (i : Instr k) :
    (i.renameRegs σ).renameRegs τ = i.renameRegs (τ ∘ σ) := by
  cases i <;> rfl

@[simp] theorem renameRegs_id (P : Program k) : renameRegs id P = P := by
  have : Instr.renameRegs (k := k) id = id := funext fun i => i.renameRegs_id
  simp [renameRegs, this]

@[simp] theorem renameRegs_comp (σ : Fin k → Fin k') (τ : Fin k' → Fin k'') (P : Program k) :
    renameRegs τ (renameRegs σ P) = renameRegs (τ ∘ σ) P := by
  simp [renameRegs, List.map_map, Function.comp_def]

@[simp] theorem length_renameRegs (σ : Fin k → Fin k') (P : Program k) :
    (renameRegs σ P).length = P.length :=
  List.length_map _

theorem getElem?_renameRegs (σ : Fin k → Fin k') (P : Program k) (n : ℕ) :
    (renameRegs σ P)[n]? = P[n]?.map (Instr.renameRegs σ) :=
  List.getElem?_map

/-- `c'` is `c` placed in a larger register file along `σ`: same program counter, and every
renamed register holds what the original did. Registers outside the image of `σ` are
unconstrained — that is the point, since they belong to the other machine. -/
structure Renamed (σ : Fin k → Fin k') (c : Config k) (c' : Config k') : Prop where
  /-- The program counters agree. -/
  pc : c'.pc = c.pc
  /-- Each renamed register holds the original's contents. -/
  regs : ∀ i, c'.regs (σ i) = c.regs i

theorem Renamed.exec {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {c : Config k}
    {c' : Config k'} (h : Renamed σ c c') (i : Instr k) :
    Renamed σ (i.exec c.regs) ((i.renameRegs σ).exec c'.regs) := by
  have key : ∀ (r m : Fin k) (v : ℕ),
      Function.update c'.regs (σ r) v (σ m) = Function.update c.regs r v m := by
    intro r m v
    by_cases hm : m = r
    · subst hm; simp
    · rw [Function.update_of_ne (fun hc => hm (hσ hc)), Function.update_of_ne hm, h.regs]
  cases i with
  | inc r j =>
    refine ⟨rfl, fun m => ?_⟩
    change Function.update c'.regs (σ r) (c'.regs (σ r) + 1) (σ m)
      = Function.update c.regs r (c.regs r + 1) m
    rw [h.regs r]
    exact key r m _
  | dec r jpos jzero =>
    have hr : c'.regs (σ r) = c.regs r := h.regs r
    simp only [Instr.renameRegs, Instr.exec, hr]
    split
    · exact ⟨rfl, h.regs⟩
    · exact ⟨rfl, fun m => key r m _⟩

theorem Renamed.halted_iff {σ : Fin k → Fin k'} {P : Program k} {c : Config k} {c' : Config k'}
    (h : Renamed σ c c') : Halted (renameRegs σ P) c' ↔ Halted P c := by
  simp [Halted, h.pc]

theorem Renamed.step {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') :
    Renamed σ (RegisterMachine.step P c) (RegisterMachine.step (renameRegs σ P) c') := by
  cases hp : P[c.pc]? with
  | none =>
    have hc : Halted P c := halted_iff_getElem?_eq_none.mpr hp
    rw [step_of_halted hc, step_of_halted (h.halted_iff.mpr hc)]
    exact h
  | some i =>
    have hp' : (renameRegs σ P)[c'.pc]? = some (i.renameRegs σ) := by
      rw [getElem?_renameRegs, h.pc, hp]; rfl
    rw [step_of_getElem? hp, step_of_getElem? hp']
    exact h.exec hσ i

theorem Renamed.run {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') (n : ℕ) :
    Renamed σ (RegisterMachine.run P c n) (RegisterMachine.run (renameRegs σ P) c' n) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [run_succ, run_succ]; exact ih.step hσ

/-- Renaming does not touch registers outside the image of `σ`. -/
theorem Instr.regs_exec_renameRegs_of_ne {σ : Fin k → Fin k'} {r : Fin k'} (hr : ∀ i, r ≠ σ i)
    (i : Instr k) (regs : Fin k' → ℕ) : ((i.renameRegs σ).exec regs).regs r = regs r := by
  cases i with
  | inc s j => exact Function.update_of_ne (hr s) _ _
  | dec s jpos jzero =>
    by_cases h : regs (σ s) = 0 <;>
      simp [Instr.renameRegs, Instr.exec, h, Function.update_of_ne (hr s)]

theorem regs_run_renameRegs_of_ne {σ : Fin k → Fin k'} {P : Program k} {c' : Config k'}
    {r : Fin k'} (hr : ∀ i, r ≠ σ i) (n : ℕ) :
    (RegisterMachine.run (renameRegs σ P) c' n).regs r = c'.regs r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases hp : (renameRegs σ P)[(RegisterMachine.run (renameRegs σ P) c' n).pc]? with
    | none => rw [step_of_halted (halted_iff_getElem?_eq_none.mpr hp)]; exact ih
    | some i =>
      rw [step_of_getElem? hp, getElem?_renameRegs] at *
      obtain ⟨i0, _, rfl⟩ := Option.map_eq_some_iff.mp hp
      rw [Instr.regs_exec_renameRegs_of_ne hr]
      exact ih

/-- **Execution equivariance.** Renaming registers along an injection does not change whether a
machine halts. -/
theorem halts_renameRegs_iff {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') :
    Halts (renameRegs σ P) c' ↔ Halts P c :=
  exists_congr fun n => (h.run hσ n).halted_iff

/-! ## Relocating jump targets -/

/-- Add `d` to every jump target of an instruction. -/
def Instr.shiftJumps (d : ℕ) : Instr k → Instr k
  | .inc r j => .inc r (j + d)
  | .dec r jpos jzero => .dec r (jpos + d) (jzero + d)

/-- Add `d` to every jump target of a program. -/
def shiftJumps (d : ℕ) (P : Program k) : Program k := P.map (Instr.shiftJumps d)

@[simp] theorem length_shiftJumps (d : ℕ) (P : Program k) : (shiftJumps d P).length = P.length :=
  List.length_map _

theorem getElem?_shiftJumps (d : ℕ) (P : Program k) (n : ℕ) :
    (shiftJumps d P)[n]? = P[n]?.map (Instr.shiftJumps d) :=
  List.getElem?_map

theorem Instr.exec_shiftJumps (d : ℕ) (i : Instr k) (regs : Fin k → ℕ) :
    (i.shiftJumps d).exec regs = ⟨(i.exec regs).pc + d, (i.exec regs).regs⟩ := by
  cases i with
  | inc r j => rfl
  | dec r jpos jzero => by_cases h : regs r = 0 <;> simp [Instr.shiftJumps, Instr.exec, h]

/-! ## Concatenation -/

/-- Inside a longer program, a step taken strictly within the prefix is a step of the prefix. -/
theorem step_append_of_lt {P R : Program k} {c : Config k} (h : c.pc < P.length) :
    step (P ++ R) c = step P c := by
  rw [step, step, List.getElem?_append_left h]

/-- A run that never leaves the prefix is unchanged by appending to it. -/
theorem run_append_of_lt {P R : Program k} {c : Config k} {n : ℕ}
    (h : ∀ m < n, (run P c m).pc < P.length) : run (P ++ R) c n = run P c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    rw [run_succ, run_succ, hstep, step_append_of_lt (h n (Nat.lt_succ_self n))]

/-- One step of the relocated suffix, seen from inside the concatenation. -/
theorem step_append_shiftJumps (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    step (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ =
      ⟨(step Q ⟨p, regs⟩).pc + P.length, (step Q ⟨p, regs⟩).regs⟩ := by
  rw [step, step, List.getElem?_append_right (Nat.le_add_left _ _)]
  simp only [Nat.add_sub_cancel, getElem?_shiftJumps]
  cases hp : Q[p]? with
  | none => simp
  | some i => simp [Instr.exec_shiftJumps]

/-- **Sequencing.** Once control reaches the relocated suffix, it runs as `Q` does, with every
program counter offset by `P.length`. -/
theorem run_append_shiftJumps (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) (n : ℕ) :
    run (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ n =
      ⟨(run Q ⟨p, regs⟩ n).pc + P.length, (run Q ⟨p, regs⟩ n).regs⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, ih, step_append_shiftJumps]

theorem halted_append_shiftJumps_iff (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    Halted (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ ↔ Halted Q ⟨p, regs⟩ := by
  simp only [Halted, List.length_append, length_shiftJumps]
  omega

/-- The suffix halts inside the concatenation exactly when it halts on its own. -/
theorem halts_append_shiftJumps_iff (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    Halts (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ ↔ Halts Q ⟨p, regs⟩ :=
  exists_congr fun n => by
    rw [run_append_shiftJumps]
    exact halted_append_shiftJumps_iff P Q _ _

/-- **Composition.** If `P` exits at exactly `P.length` after `n` steps without leaving itself
first, then the concatenation halts iff `Q` halts from the register file `P` produced.

The two hypotheses are what each constructor case in #40–#43 must supply about the program it
builds; they are deliberately not packaged as a well-formedness predicate. -/
theorem halts_append_of_exits {P Q : Program k} {c : Config k} {n : ℕ}
    (hin : ∀ m < n, (run P c m).pc < P.length) (hexit : (run P c n).pc = P.length) :
    Halts (P ++ shiftJumps P.length Q) c ↔ Halts Q ⟨0, (run P c n).regs⟩ := by
  have hn : run (P ++ shiftJumps P.length Q) c n = ⟨0 + P.length, (run P c n).regs⟩ := by
    rw [run_append_of_lt hin, Nat.zero_add, ← hexit]
  constructor
  · rintro ⟨m, hm⟩
    refine (halts_append_shiftJumps_iff P Q 0 _).mp ⟨m, ?_⟩
    rw [← hn, ← run_add]
    exact halted_run_of_le hm (Nat.le_add_left m n)
  · intro hq
    obtain ⟨m, hm⟩ := (halts_append_shiftJumps_iff P Q 0 _).mpr hq
    exact ⟨n + m, by rw [run_add, hn]; exact hm⟩

end RegisterMachine

end Hilbert10
