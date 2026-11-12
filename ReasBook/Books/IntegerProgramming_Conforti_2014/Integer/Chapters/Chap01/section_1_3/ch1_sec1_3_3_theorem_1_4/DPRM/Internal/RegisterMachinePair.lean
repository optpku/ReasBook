/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachineUnpair

/-!
# `Nat.pair` by walking the enumeration

Issue #51, step 5. Enumerate from `(0, 0)`, counting steps, until the candidate is the target.
`Nat.iterate_pairNext_pair` says that happens after exactly `Nat.pair a b` steps, so the loop
terminates and the count is the answer. No unbounded search and no `rfind'`.

## Layout

`Fin 9`:

| register | role |
|---|---|
| `0`, `1` | the target pair, preserved |
| `2` | the step count, and the result |
| `3`, `4` | the candidate pair |
| `5` | accumulated distance from candidate to target |
| `6`, `7`, `8` | `compare`'s residuals and temporary |

**On the extra register.** Testing a *pair* for equality needs two comparisons, and `compare`
needs three scratch registers of its own, which is eight before an accumulator. With one more the
loop body is a straight line ending in a single branch, and its proof is one splice. Testing the
coordinates separately fits in eight registers but branches forward out of the middle of the
body from two places, giving four entry paths into the advance block and four splices. The
register is cheaper than the proof.

## The loop

```
0 … T-1    measure the distance into register 5
T          decrement 5; positive → drain and advance, zero → exit
T+1        drain the rest of 5
T+2 … T+M+1  the relocated pairNextMachine
T+M+2      increment the count, jump back to 0
```

The advance block cleans registers `6`, `7`, `8` whatever they held, so the drain at `T+1` is the
only cleanup the loop performs — the measurement's leftovers are somebody else's problem, and
that somebody already handles them.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

/-! ## Measuring the distance -/

/-- Add the coordinatewise distance from `(3, 4)` to `(0, 1)` into register `5`. -/
def measure : Program 9 :=
  seq (compare 3 0 6 7 8)
    (seq (move 6 5) (seq (move 7 5)
      (seq (compare 4 1 6 7 8) (seq (move 6 5) (move 7 5)))))

theorem realises_measure : Realises measure fun regs i =>
    if i = 5 then regs 5 + ((regs 0 - regs 3) + (regs 3 - regs 0))
        + ((regs 1 - regs 4) + (regs 4 - regs 1))
      else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine (((realises_compare (a := 3) (b := 0) (lo := 6) (hi := 7) (tmp := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).seq
      ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
        ((realises_move (show (7 : Fin 9) ≠ 5 by decide)).seq
          ((realises_compare (a := 4) (b := 1) (lo := 6) (hi := 7) (tmp := 8)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).seq
              ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
                (realises_move (show (7 : Fin 9) ≠ 5 by decide))))))).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp
  all_goals omega

/-! ## Advancing the candidate -/

/-- Where `pairNextMachine`'s five registers go: the candidate pair and the top three scratch
registers. The accumulator, register `5`, is deliberately outside the block. -/
def pairAdvanceIdx (i : Fin 5) : Fin 9 :=
  if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 6 else if i = 3 then 7 else 8

def pairAdvance : Program 9 := renameRegs pairAdvanceIdx pairNextMachine

theorem realises_pairAdvance : Realises pairAdvance fun regs i =>
    if i = 3 then (Nat.pairNext (regs 3, regs 4)).1
    else if i = 4 then (Nat.pairNext (regs 3, regs 4)).2
    else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine realises_pairNextMachine.renameRegs
    (show Function.Injective pairAdvanceIdx by decide) ?_ ?_
  · intro regs i
    fin_cases i <;> simp [pairAdvanceIdx]
  · intro regs r hr
    have h3 : r ≠ 3 := by simpa [pairAdvanceIdx] using hr 0
    have h4 : r ≠ 4 := by simpa [pairAdvanceIdx] using hr 1
    have h6 : r ≠ 6 := by simpa [pairAdvanceIdx] using hr 2
    have h7 : r ≠ 7 := by simpa [pairAdvanceIdx] using hr 3
    have h8 : r ≠ 8 := by simpa [pairAdvanceIdx] using hr 4
    simp [h3, h4, h6, h7, h8]

/-- The distance is zero exactly when the candidate is the target. -/
theorem measure_eq_zero_iff (regs : Fin 9 → ℕ) :
    ((regs 0 - regs 3) + (regs 3 - regs 0)) + ((regs 1 - regs 4) + (regs 4 - regs 1)) = 0 ↔
      (regs 3, regs 4) = (regs 0, regs 1) := by
  rw [Prod.mk.injEq]
  omega


/-! ## The loop -/

/-- The header state after `q` turns: the targets, the count, the `q`th pair of the enumeration,
and clean scratch. -/
def pairState (a b q : ℕ) : Fin 9 → ℕ :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then q
    else if i = 3 then (Nat.pairNext^[q] (0, 0)).1
    else if i = 4 then (Nat.pairNext^[q] (0, 0)).2 else 0

/-- The measurement, then the branch on its result. -/
def pairPre : Program 9 :=
  measure ++ [Instr.dec 5 (measure.length + 1) (measure.length + pairAdvance.length + 3),
              Instr.dec 5 (measure.length + 1) (measure.length + 2)]

/-- Walk the enumeration, counting, until the candidate is the target. -/
def pairLoop : Program 9 := pairPre ++ shiftJumps pairPre.length pairAdvance ++ [Instr.inc 2 0]

theorem length_pairPre : pairPre.length = measure.length + 2 := by simp [pairPre]

theorem length_pairLoop : pairLoop.length = measure.length + pairAdvance.length + 3 := by
  simp [pairLoop, pairPre]
  omega

theorem getElem?_test : pairLoop[measure.length]? =
    some (Instr.dec 5 (measure.length + 1) (measure.length + pairAdvance.length + 3)) := by
  rw [pairLoop, List.getElem?_append_left (by simp [length_pairPre]; omega),
    List.getElem?_append_left (by rw [length_pairPre]; omega), pairPre,
    List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem getElem?_drain : pairLoop[measure.length + 1]? =
    some (Instr.dec 5 (measure.length + 1) (measure.length + 2)) := by
  rw [pairLoop, List.getElem?_append_left (by simp [length_pairPre]; omega),
    List.getElem?_append_left (by rw [length_pairPre]; omega), pairPre,
    List.getElem?_append_right (by simp)]
  simp

theorem getElem?_inc :
    pairLoop[measure.length + pairAdvance.length + 2]? = some (Instr.inc 2 0) := by
  rw [pairLoop, List.getElem?_append_right (by simp [length_pairPre]; omega)]
  simp only [List.length_append, length_pairPre, length_shiftJumps]
  rw [show measure.length + pairAdvance.length + 2 -
    (measure.length + 2 + pairAdvance.length) = 0 by omega]
  rfl

theorem pairLoop_eq :
    pairLoop = measure ++ ([Instr.dec 5 (measure.length + 1)
        (measure.length + pairAdvance.length + 3),
      Instr.dec 5 (measure.length + 1) (measure.length + 2)]
      ++ shiftJumps pairPre.length pairAdvance ++ [Instr.inc 2 0]) := by
  simp [pairLoop, pairPre]

theorem run_measure_seg {R : Fin 9 → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run measure ⟨0, R⟩ m).pc < measure.length) (m : ℕ) (hm : m ≤ n) :
    run pairLoop ⟨0, R⟩ m = run measure ⟨0, R⟩ m := by
  rw [pairLoop_eq, run_append_of_lt (fun j hj => hin j (by omega))]

/-- The measurement, inside the loop, from a header state. `q` is kept abstract throughout: the
terminal turn instantiates it to `Nat.pair a b` only at the very end, since substituting it early
makes every subterm large enough to defeat `split_ifs`. -/
theorem run_measure_header (a b q : ℕ) :
    ∃ nm, (∀ m < nm, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ nm = ⟨measure.length, fun i =>
        if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
          + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
        else pairState a b q i⟩ := by
  obtain ⟨nm, hmin, hmex⟩ := realises_measure (pairState a b q)
  refine ⟨nm, fun m hm => ?_, ?_⟩
  · rw [run_measure_seg hmin m (Nat.le_of_lt hm), length_pairLoop]
    have := hmin m hm
    omega
  · rw [run_measure_seg hmin nm (Nat.le_refl _), hmex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]

/-- The terminal turn: the candidate is the target, so the branch exits. -/
theorem run_turn_eq (a b q : ℕ) (hcand : Nat.pairNext^[q] (0, 0) = (a, b)) :
    ∃ n, (∀ m < n, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ n = ⟨pairLoop.length, pairState a b q⟩ := by
  obtain ⟨nm, h1in, h1ex⟩ := run_measure_header a b q
  have hfix : (fun i : Fin 9 =>
      if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
        + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
      else pairState a b q i) = pairState a b q := by
    funext i
    rw [hcand]
    by_cases h : i = 5
    · subst h; simp [pairState]
    · rw [if_neg h]
  rw [hfix] at h1ex
  have hzero : pairState a b q 5 = 0 := by simp [pairState]
  have h2ex : run pairLoop ⟨measure.length, pairState a b q⟩ 1 =
      ⟨pairLoop.length, pairState a b q⟩ := by
    rw [run_one, step_dec_zero getElem?_test hzero, length_pairLoop]
  exact ⟨nm + 1, run_segment_trans h1in h1ex (fun m hm => by
    rw [show m = 0 by omega, run_zero, length_pairLoop]
    exact show measure.length < measure.length + pairAdvance.length + 3 by omega) h2ex⟩


theorem run_advance_seg {R : Fin 9 → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run pairAdvance ⟨0, R⟩ m).pc < pairAdvance.length) (m : ℕ) (hm : m ≤ n) :
    run pairLoop ⟨0 + pairPre.length, R⟩ m =
      ⟨(run pairAdvance ⟨0, R⟩ m).pc + pairPre.length, (run pairAdvance ⟨0, R⟩ m).regs⟩ :=
  run_middle (A := pairPre) (C := [Instr.inc 2 0]) hin m hm

/-- An ordinary turn: the candidate is not the target, so the loop drains the distance, advances
the enumeration, counts, and jumps back. -/
theorem run_turn_ne (a b q : ℕ) (hne : Nat.pairNext^[q] (0, 0) ≠ (a, b)) :
    ∃ n, (∀ m < n, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ n = ⟨0, pairState a b (q + 1)⟩ := by
  obtain ⟨nm, h1in, h1ex⟩ := run_measure_header a b q
  have hLp : pairLoop.length = measure.length + pairAdvance.length + 3 := length_pairLoop
  have hpre : (0 : ℕ) + pairPre.length = measure.length + 2 := by
    rw [Nat.zero_add, length_pairPre]
  -- the measured distance is positive, because the candidate misses the target
  set Rm : Fin 9 → ℕ := fun i =>
    if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
      + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
    else pairState a b q i with hRm
  have hd : Rm 5 ≠ 0 := by
    simp only [hRm, if_pos rfl]
    intro h0
    exact hne (Prod.ext_iff.mpr ⟨by omega, by omega⟩)
  -- step 2: the branch takes the mismatch side
  have h2ex : run pairLoop ⟨measure.length, Rm⟩ 1 =
      ⟨measure.length + 1, Function.update Rm 5 (Rm 5 - 1)⟩ := by
    rw [run_one, step_dec_pos getElem?_test hd]
  -- step 3: drain what is left of the distance
  have h3ex : run pairLoop ⟨measure.length + 1, Function.update Rm 5 (Rm 5 - 1)⟩ (Rm 5) =
      ⟨measure.length + 2, Function.update Rm 5 0⟩ := by
    have h := run_drain getElem?_drain (Function.update Rm 5 (Rm 5 - 1))
    rw [Function.update_self, Function.update_idem] at h
    rw [show Rm 5 = Rm 5 - 1 + 1 by omega]
    exact h
  -- step 4: advance the enumeration
  obtain ⟨na, hain, haex⟩ := realises_pairAdvance (Function.update Rm 5 0)
  set Ra : Fin 9 → ℕ := fun i =>
    if i = 3 then (Nat.pairNext (Function.update Rm 5 0 3, Function.update Rm 5 0 4)).1
    else if i = 4 then (Nat.pairNext (Function.update Rm 5 0 3, Function.update Rm 5 0 4)).2
    else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0
    else Function.update Rm 5 0 i with hRa
  have h4ex : run pairLoop ⟨measure.length + 2, Function.update Rm 5 0⟩ na =
      ⟨pairAdvance.length + pairPre.length, Ra⟩ := by
    rw [← hpre, run_advance_seg hain na (Nat.le_refl _), haex]
  -- step 5: count and jump back
  have h5ex : run pairLoop ⟨pairAdvance.length + pairPre.length, Ra⟩ 1 =
      ⟨0, pairState a b (q + 1)⟩ := by
    rw [show pairAdvance.length + pairPre.length = measure.length + pairAdvance.length + 2 by
      rw [length_pairPre]; omega, run_one, step_inc getElem?_inc]
    have hiter : Nat.pairNext^[q + 1] (0, 0) = Nat.pairNext (Nat.pairNext^[q] (0, 0)) :=
      Function.iterate_succ_apply' _ _ _
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;>
      simp [hRa, hRm, pairState, hiter, Function.update_apply, Prod.mk.eta]
  -- the four in-range obligations
  have i2 : ∀ m < 1, (run pairLoop ⟨measure.length, Rm⟩ m).pc < pairLoop.length := by
    intro m hm
    rw [show m = 0 by omega, run_zero, hLp]
    exact show measure.length < measure.length + pairAdvance.length + 3 by omega
  have i3 : ∀ m < Rm 5, (run pairLoop ⟨measure.length + 1,
      Function.update Rm 5 (Rm 5 - 1)⟩ m).pc < pairLoop.length := by
    intro m hm
    rw [run_drain_partial getElem?_drain (Function.update Rm 5 (Rm 5 - 1)) m
      (by rw [Function.update_self]; omega), hLp]
    exact show measure.length + 1 < measure.length + pairAdvance.length + 3 by omega
  have i4 : ∀ m < na, (run pairLoop ⟨measure.length + 2, Function.update Rm 5 0⟩ m).pc <
      pairLoop.length := by
    intro m hm
    rw [← hpre, run_advance_seg hain m (Nat.le_of_lt hm), hLp, length_pairPre]
    have := hain m hm
    exact show (run pairAdvance ⟨0, Function.update Rm 5 0⟩ m).pc + (measure.length + 2) <
      measure.length + pairAdvance.length + 3 by omega
  have i5 : ∀ m < 1, (run pairLoop ⟨pairAdvance.length + pairPre.length, Ra⟩ m).pc <
      pairLoop.length := by
    intro m hm
    rw [show m = 0 by omega, run_zero, hLp, length_pairPre]
    exact show pairAdvance.length + (measure.length + 2) <
      measure.length + pairAdvance.length + 3 by omega
  obtain ⟨j2in, j2ex⟩ := run_segment_trans i4 h4ex i5 h5ex
  obtain ⟨j3in, j3ex⟩ := run_segment_trans i3 h3ex j2in j2ex
  obtain ⟨j4in, j4ex⟩ := run_segment_trans i2 h2ex j3in j3ex
  exact ⟨nm + (1 + (Rm 5 + (na + 1))), run_segment_trans h1in h1ex j4in j4ex⟩


/-! ## From the origin to the target -/

theorem run_loop_to (a b : ℕ) : ∀ q ≤ Nat.pair a b, ∃ n,
    (∀ m < n, (run pairLoop ⟨0, pairState a b 0⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b 0⟩ n = ⟨0, pairState a b q⟩ := by
  intro q
  induction q with
  | zero => intro _; exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), rfl⟩
  | succ q ih =>
    intro hq
    obtain ⟨n, hin, hex⟩ := ih (by omega)
    obtain ⟨nt, htin, htex⟩ := run_turn_ne a b q (Nat.iterate_pairNext_ne_of_lt (by omega))
    exact ⟨n + nt, run_segment_trans hin hex htin htex⟩

/-- **The loop terminates, after exactly `Nat.pair a b` turns.** `Nat.iterate_pairNext_ne_of_lt`
rules out an earlier match and `Nat.iterate_pairNext_pair` supplies the terminal one. -/
theorem run_pairLoop (a b : ℕ) : ∃ n,
    (∀ m < n, (run pairLoop ⟨0, pairState a b 0⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b 0⟩ n =
        ⟨pairLoop.length, pairState a b (Nat.pair a b)⟩ := by
  obtain ⟨n, hin, hex⟩ := run_loop_to a b (Nat.pair a b) (Nat.le_refl _)
  obtain ⟨nt, htin, htex⟩ := run_turn_eq a b (Nat.pair a b) (Nat.iterate_pairNext_pair a b)
  exact ⟨n + nt, run_segment_trans hin hex htin htex⟩

/-! ## The machine

The loop exits with the candidate still in registers `3` and `4`. Those have to be cleared for
the result to satisfy the clean-scratch contract of `CleanScratch`, which is what step 6 will
call through, so the epilogue is not optional. -/

/-- Clear everything but the two targets. -/
def pairPrologue : Program 9 :=
  seq (clear 2) (seq (clear 3) (seq (clear 4) (seq (clear 5) (seq (clear 6)
    (seq (clear 7) (clear 8))))))

/-- Clear the candidate the loop matched on. -/
def pairEpilogue : Program 9 := seq (clear 3) (clear 4)

/-- `Nat.pair` on registers `0` and `1`, with the answer in register `2`. -/
def pairMachine : Program 9 := seq pairPrologue (seq pairLoop pairEpilogue)

theorem realises_pairPrologue : Realises pairPrologue fun regs i =>
    if i = 0 then regs 0 else if i = 1 then regs 1 else 0 := by
  refine (((realises_clear 2).seq ((realises_clear 3).seq ((realises_clear 4).seq
    ((realises_clear 5).seq ((realises_clear 6).seq
      ((realises_clear 7).seq (realises_clear 8))))))).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp

theorem realises_pairEpilogue : Realises pairEpilogue fun regs i =>
    if i = 3 then 0 else if i = 4 then 0 else regs i := by
  refine (((realises_clear 3).seq (realises_clear 4)).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp

/-- **`pairMachine` computes `Nat.pair`.** The targets survive, the answer lands in register `2`,
and every other register comes back at zero whatever it held. -/
theorem realises_pairMachine : Realises pairMachine fun regs i =>
    if i = 0 then regs 0 else if i = 1 then regs 1
    else if i = 2 then Nat.pair (regs 0) (regs 1) else 0 := by
  intro regs
  obtain ⟨n0, h0in, h0ex⟩ := realises_pairPrologue regs
  have h0ex' : run pairPrologue ⟨0, regs⟩ n0 =
      ⟨pairPrologue.length, pairState (regs 0) (regs 1) 0⟩ := by
    rw [h0ex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]
  obtain ⟨n1, h1in, h1ex⟩ := run_pairLoop (regs 0) (regs 1)
  obtain ⟨n2, h2in, h2ex⟩ :=
    realises_pairEpilogue (pairState (regs 0) (regs 1) (Nat.pair (regs 0) (regs 1)))
  have h2ex' : run pairEpilogue
      ⟨0, pairState (regs 0) (regs 1) (Nat.pair (regs 0) (regs 1))⟩ n2 =
      ⟨pairEpilogue.length, fun i => if i = 0 then regs 0 else if i = 1 then regs 1
        else if i = 2 then Nat.pair (regs 0) (regs 1) else 0⟩ := by
    rw [h2ex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]
  obtain ⟨jin, jex⟩ := join_exit h1in h1ex h2in h2ex'
  exact ⟨n0 + (n1 + n2), join_exit h0in h0ex' jin jex⟩

end RegisterMachine

end Hilbert10
