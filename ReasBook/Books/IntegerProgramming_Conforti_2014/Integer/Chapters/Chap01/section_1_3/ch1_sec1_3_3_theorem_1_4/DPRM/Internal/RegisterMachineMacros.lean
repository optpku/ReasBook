module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachineRealises

/-!
# Register plumbing

Issue #51, step 2. The total macros the pairing machines are built from.

Each is stated as a `Realises` fact with an explicit whole-register transformation, so the
statement says at once what was produced *and* that every temporary was left at zero. A macro
that returned the right value while leaving a counter dirty would not typecheck against these
statements, which is the point: the clean-scratch convention of `CleanScratch` is only worth
something if the macros actually give back what they borrow.

Every macro takes the registers it uses as arguments, with distinctness as explicit hypotheses.
There is no allocator and no name supply here, per the standing guard from #39.

## Proving loops

Two small pieces of technique, both learned the hard way.

`step_dec_pos`, `step_dec_zero` and `step_inc` turn one machine step into one equation about
register files, so a loop body becomes a chain of rewrites rather than a nest of `step`
applications.

Each loop's body is proved *once*, for an arbitrary register file, as a `run … c p` fact for the
body's length `p`. The induction over turns of the loop then goes through `run_add`, never
through `run_succ`. This matters: `Config` is a structure, so structure eta lets the pattern
`step P ⟨p, regs⟩` match *any* `step P c`, and `rw` will happily aim a step lemma at the
outermost step of a nest instead of the innermost one.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

theorem run_one (P : Program k) (c : Config k) : run P c 1 = step P c := rfl

theorem step_dec_pos {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r ≠ 0) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r - 1)⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_dec_zero {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r = 0) : step P ⟨p, regs⟩ = ⟨b, regs⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_inc {P : Program k} {r : Fin k} {a p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.inc r a)) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r + 1)⟩ := by
  rw [step_of_getElem? hp]
  rfl

/-- Sequential composition: `++` with the second program relocated. Named because the macros
below chain four of them and the raw form is unreadable at that length. -/
def seq (P Q : Program k) : Program k := P ++ shiftJumps P.length Q

@[simp] theorem length_seq (P Q : Program k) : (seq P Q).length = P.length + Q.length :=
  length_append_shiftJumps P Q

theorem Realises.seq {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ} (hP : Realises P F)
    (hQ : Realises Q G) : Realises (RegisterMachine.seq P Q) fun regs => G (F regs) :=
  hP.append hQ

/-! ## Moving

`move` empties one register into another; `moveTwo` empties it into two at once, which is what
makes a non-destructive copy possible. -/

/-- Add `r` into `s`, leaving `r` at zero. -/
def move (r s : Fin k) : Program k := [.dec r 1 2, .inc s 0]

/-- The register file after `j` turns of `move`'s loop. -/
def moveState (r s : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j else regs i

/-- One turn of `move`'s loop, for an arbitrary register file. -/
theorem run_move_body {r s : Fin k} (hrs : r ≠ s) (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (move r s) ⟨0, R⟩ 2 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1 else R i⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
    step_dec_pos (P := move r s) (b := 2) rfl hR,
    step_inc (P := move r s) (p := 1) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (move r s) ⟨0, regs⟩ (2 * j) = ⟨0, moveState r s regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveState r s regs j r = regs r - j := by simp [moveState]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega),
      run_move_body hrs _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all <;> omega

theorem pc_run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) :
    ∀ m < 2 * regs r + 1, (run (move r s) ⟨0, regs⟩ m).pc < (move r s).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
  have hval : moveState r s regs j r = regs r - j := by simp [moveState]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · rw [Nat.add_zero, run_move hrs regs j (by omega)]
    simp [move]
  · rw [run_add, run_move hrs regs j (by omega), run_one,
      step_dec_pos (P := move r s) (b := 2) rfl (by rw [hval]; omega)]
    simp [move]

theorem realises_move {r s : Fin k} (hrs : r ≠ s) :
    Realises (move r s) fun regs i =>
      if i = r then 0 else if i = s then regs s + regs r else regs i := by
  intro regs
  refine ⟨2 * regs r + 1, pc_run_move hrs regs, ?_⟩
  have hval : moveState r s regs (regs r) r = 0 := by simp [moveState]
  rw [run_add, run_move hrs regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := move r s) (a := 1) rfl hval, show (move r s).length = 2 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveState]
  split_ifs <;> simp_all

/-- Add `r` into both `s` and `t`, leaving `r` at zero. -/
def moveTwo (r s t : Fin k) : Program k := [.dec r 1 3, .inc s 2, .inc t 0]

/-- The register file after `j` turns of `moveTwo`'s loop. -/
def moveTwoState (r s t : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j
    else if i = t then regs t + j else regs i

/-- One turn of `moveTwo`'s loop, for an arbitrary register file. -/
theorem run_moveTwo_body {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (moveTwo r s t) ⟨0, R⟩ 3 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1
        else if i = t then R t + 1 else R i⟩ := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, run_add, run_add, run_one, run_one, run_one,
    step_dec_pos (P := moveTwo r s t) (b := 3) rfl hR,
    step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl,
    step_inc (P := moveTwo r s t) (p := 2) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (moveTwo r s t) ⟨0, regs⟩ (3 * j) = ⟨0, moveTwoState r s t regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, run_add, ih (by omega),
      run_moveTwo_body hrs hrt hst _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all <;> omega

theorem pc_run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ m < 3 * regs r + 1,
    (run (moveTwo r s t) ⟨0, regs⟩ m).pc < (moveTwo r s t).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 3 ∧ m = 3 * j + c :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by omega), by omega⟩
  have hjr : j ≤ regs r := by omega
  have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
  -- `hstep` is only available once we know the loop has not already exited, which is exactly
  -- the case `c ≠ 0`: at `c = 0` the machine is sitting on the zero test.
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · rw [Nat.add_zero, run_moveTwo hrs hrt hst regs j hjr]
    simp [moveTwo]
  · rw [run_add, run_moveTwo hrs hrt hst regs j hjr, run_one,
      step_dec_pos (P := moveTwo r s t) (b := 3) rfl (by rw [hval]; omega)]
    simp [moveTwo]
  · rw [show 3 * j + 2 = 3 * j + 1 + 1 by omega, run_add, run_add,
      run_moveTwo hrs hrt hst regs j hjr, run_one, run_one,
      step_dec_pos (P := moveTwo r s t) (regs := moveTwoState r s t regs j) (b := 3) rfl
        (by rw [hval]; omega),
      step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl]
    simp [moveTwo]

theorem realises_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (moveTwo r s t) fun regs i => if i = r then 0 else if i = s then regs s + regs r
      else if i = t then regs t + regs r else regs i := by
  intro regs
  refine ⟨3 * regs r + 1, pc_run_moveTwo hrs hrt hst regs, ?_⟩
  have hval : moveTwoState r s t regs (regs r) r = 0 := by simp [moveTwoState]
  rw [run_add, run_moveTwo hrs hrt hst regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := moveTwo r s t) (a := 1) rfl hval,
    show (moveTwo r s t).length = 3 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveTwoState]
  split_ifs <;> simp_all

/-! ## Copying

`copy` is the first macro whose statement carries a cleanliness claim: `t` is borrowed as working
storage and handed back at zero, whatever it held before. -/

/-- Copy `r` into `s`, using `t` as working storage and returning it at zero. `r` is unchanged. -/
def copy (r s t : Fin k) : Program k :=
  seq (clear s) (seq (clear t) (seq (moveTwo r s t) (move t r)))

theorem realises_copy {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (copy r s t) fun regs i =>
      if i = s then regs r else if i = t then 0 else regs i := by
  refine (((realises_clear s).seq ((realises_clear t).seq
    ((realises_moveTwo hrs hrt hst).seq (realises_move (Ne.symm hrt))))).congr fun regs => ?_)
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all


/-! ## Comparison

The synchronised-decrement loop returns **both** residuals rather than a Boolean or an encoded
ordering:

```
lo := regs b - regs a      hi := regs a - regs b
```

That is what the implementation naturally produces, and it is exactly what `pairNext` needs: one
call settles all four of its branches. `lo > 0` says `a < b`; under that, `lo = 1` distinguishes
the shell rollover from an ordinary increment; and if `lo = 0` then `hi` distinguishes equality
from `a > b`. A Boolean would have thrown away the information and forced a second comparison.

`lo` and `hi` are *owned outputs*: they overwrite whatever they held. Only `tmp` is borrowed, and
it comes back at zero. -/

/-- Decrement `hi` and `lo` together until one runs out.

Both exits land at exactly `length`. The `inc hi` at position 2 undoes the decrement taken on the
turn that discovered `lo = 0`, which is why the loop tests `hi` first: the register whose test
can fail mid-turn has to be the one that is cheap to restore. -/
def syncDec (hi lo : Fin k) : Program k := [.dec hi 1 3, .dec lo 0 2, .inc hi 3]

/-- The register file after `j` synchronised decrements. -/
def syncDecState (hi lo : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = hi then regs hi - j else if i = lo then regs lo - j else regs i

theorem run_syncDec_body {hi lo : Fin k} (hne : hi ≠ lo) (R : Fin k → ℕ)
    (hH : R hi ≠ 0) (hL : R lo ≠ 0) :
    run (syncDec hi lo) ⟨0, R⟩ 2 =
      ⟨0, fun i => if i = hi then R hi - 1 else if i = lo then R lo - 1 else R i⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
    step_dec_pos (P := syncDec hi lo) (b := 3) rfl hH,
    step_dec_pos (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
      (by rwa [Function.update_of_ne hne.symm])]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem run_syncDec {hi lo : Fin k} (hne : hi ≠ lo) (regs : Fin k → ℕ) :
    ∀ j ≤ min (regs hi) (regs lo),
      run (syncDec hi lo) ⟨0, regs⟩ (2 * j) = ⟨0, syncDecState hi lo regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [syncDecState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hvH : syncDecState hi lo regs j hi = regs hi - j := by simp [syncDecState]
    have hvL : syncDecState hi lo regs j lo = regs lo - j := by simp [syncDecState, hne.symm]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega),
      run_syncDec_body hne _ (by rw [hvH]; omega) (by rw [hvL]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [syncDecState]
    split_ifs <;> simp_all <;> omega

theorem realises_syncDec {hi lo : Fin k} (hne : hi ≠ lo) :
    Realises (syncDec hi lo) fun regs i =>
      if i = hi then regs hi - regs lo else if i = lo then regs lo - regs hi else regs i := by
  intro regs
  have hstate : ∀ j, syncDecState hi lo regs j hi = regs hi - j := by
    intro j; simp [syncDecState]
  have hstateL : ∀ j, syncDecState hi lo regs j lo = regs lo - j := by
    intro j; simp [syncDecState, hne.symm]
  by_cases hle : regs hi ≤ regs lo
  · -- `hi` runs out first: the loop exits on its own zero test.
    refine ⟨2 * regs hi + 1, fun m hm => ?_, ?_⟩
    · obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
        ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
      rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · rw [Nat.add_zero, run_syncDec hne regs j (by omega)]
        simp [syncDec]
      · rw [run_add, run_syncDec hne regs j (by omega), run_one,
          step_dec_pos (P := syncDec hi lo) (b := 3) rfl (by rw [hstate]; omega)]
        simp [syncDec]
    · rw [run_add, run_syncDec hne regs (regs hi) (by omega), run_one,
        step_dec_zero (P := syncDec hi lo) (a := 1) rfl (by rw [hstate]; omega),
        show (syncDec hi lo).length = 3 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [syncDecState]
      split_ifs <;> simp_all
  · -- `lo` runs out first: the turn that discovers it must give `hi` its decrement back.
    refine ⟨2 * regs lo + 3, fun m hm => ?_, ?_⟩
    · obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
        ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
      rcases (show j ≤ regs lo ∨ j = regs lo + 1 by omega) with hjL | rfl
      · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
        · rw [Nat.add_zero, run_syncDec hne regs j (by omega)]
          simp [syncDec]
        · rw [run_add, run_syncDec hne regs j (by omega), run_one,
            step_dec_pos (P := syncDec hi lo) (b := 3) rfl (by rw [hstate]; omega)]
          simp [syncDec]
      · have hc0 : c = 0 := by omega
        subst hc0
        rw [show 2 * (regs lo + 1) + 0 = 2 * regs lo + 1 + 1 by omega, run_add, run_add,
          run_syncDec hne regs (regs lo) (by omega), run_one, run_one,
          step_dec_pos (P := syncDec hi lo) (regs := syncDecState hi lo regs (regs lo))
            (b := 3) rfl
            (by rw [hstate]; omega),
          step_dec_zero (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
            (by rw [Function.update_of_ne hne.symm, hstateL]; omega)]
        simp [syncDec]
    · rw [show 2 * regs lo + 3 = 2 * regs lo + 1 + 1 + 1 by omega, run_add, run_add, run_add,
        run_syncDec hne regs (regs lo) (by omega), run_one, run_one, run_one,
        step_dec_pos (P := syncDec hi lo) (regs := syncDecState hi lo regs (regs lo)) (b := 3)
          rfl (by rw [hstate]; omega),
        step_dec_zero (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
          (by rw [Function.update_of_ne hne.symm, hstateL]; omega),
        step_inc (P := syncDec hi lo) (p := 2) (a := 3) rfl,
        show (syncDec hi lo).length = 3 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [Function.update_apply, syncDecState]
      split_ifs <;> simp_all <;> omega

/-- Compare `a` and `b`, leaving both residuals: `lo = b - a` and `hi = a - b`.

`a` and `b` are untouched, `lo` and `hi` are overwritten, and `tmp` is returned at zero.

Note the absence of a `b ≠ hi` hypothesis, which the other eight distinctness conditions might
lead one to expect. It is genuinely unnecessary: `b` is read into `lo` before `hi` is written, so
if `b` and `hi` coincide the statement's `i = hi` branch describes what happens and the `regs b`
on the right still refers to the original contents. `a ≠ lo` is *not* similarly droppable — there
the overwrite happens before the read. -/
def compare (a b lo hi tmp : Fin k) : Program k :=
  seq (copy b lo tmp) (seq (copy a hi tmp) (syncDec hi lo))

theorem realises_compare {a b lo hi tmp : Fin k} (hlh : lo ≠ hi) (hlt : lo ≠ tmp)
    (hht : hi ≠ tmp) (hal : a ≠ lo) (hah : a ≠ hi) (hat : a ≠ tmp) (hbl : b ≠ lo)
    (hbt : b ≠ tmp) :
    Realises (compare a b lo hi tmp) fun regs i =>
      if i = lo then regs b - regs a else if i = hi then regs a - regs b
        else if i = tmp then 0 else regs i := by
  refine (((realises_copy hbl hbt hlt).seq
    ((realises_copy hah hat hht).seq (realises_syncDec hlh.symm))).congr fun regs => ?_)
  funext i
  split_ifs <;> simp_all


/-! ## Draining in place

A `dec` whose positive branch targets its own position is a loop that empties one register and
falls through. It is the shape every branch of a hand-laid-out program uses to clean up, and
unlike `clear` it is not a standalone program: it sits at a fixed position inside a larger one,
so it is stated against an arbitrary `P` and position. -/

/-- Partway through draining: after `m` turns the register is down by `m` and control has not
moved. -/
theorem run_drain_partial {P : Program k} {r : Fin k} {p e : ℕ}
    (hp : P[p]? = some (.dec r p e)) (regs : Fin k → ℕ) :
    ∀ m ≤ regs r, run P ⟨p, regs⟩ m = ⟨p, Function.update regs r (regs r - m)⟩ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | succ m ih =>
    intro hm
    rw [show m + 1 = m + 1 from rfl, run_add, ih (by omega), run_one,
      step_dec_pos (P := P) hp (by rw [Function.update_self]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- Draining takes one turn per unit plus the turn that finds zero, then falls through to `e`. -/
theorem run_drain {P : Program k} {r : Fin k} {p e : ℕ} (hp : P[p]? = some (.dec r p e))
    (regs : Fin k → ℕ) :
    run P ⟨p, regs⟩ (regs r + 1) = ⟨e, Function.update regs r 0⟩ := by
  rw [run_add, run_drain_partial hp regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := P) hp (by rw [Function.update_self]; omega)]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end RegisterMachine

end Hilbert10
