module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachinePairing
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CleanScratch

/-!
# `Nat.unpair` as a counted loop

Issue #51, step 4. Iterating `pairNextMachine` exactly `n` times from `(0, 0)` computes
`Nat.unpair n`, by `Nat.iterate_pairNext`. There is no search here and so nothing to prove sound
about one: the loop runs a known number of times.

## Layout

`Fin 6`, with `0` the remaining count and `1`–`5` the `pairNextMachine` block renamed along
`Fin.succ`:

| register | role |
|---|---|
| `0` | remaining iterations |
| `1`, `2` | the candidate pair |
| `3`, `4`, `5` | `pairNextMachine`'s `lo`, `hi`, `tmp` |

```
0          decrement the count; positive → body, zero → exit
1 … L      the relocated pairNextMachine
L + 1      decrement register 5; both targets 0
```

The last instruction is a jump back to the top. It is safe *because* of what
`realises_pairNextMachine` says: register `5` is zero on exit, so the decrement has no effect and
both branches lead to `0`. A general jump combinator would have been the alternative, and this
loop is the only place one would be needed.

## Two things the proof does deliberately

The invariant counts **logical iterations**, not machine steps. Each turn of `pairNextMachine`
runs for an input-dependent time, so the step counts are accumulated as existentials through
`run_add` rather than computed.

`Nat.pairNext^[q] (0, 0)` stays **opaque** for the whole induction, and `Nat.iterate_pairNext` is
applied once at `q = n`. Unfolding `pairNext` while simultaneously comparing `Fin 6` register
files would recreate the branch-product blow-up that #51 step 3 had to work around.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ## The loop -/

/-- `pairNextMachine` moved off register `0`, which the loop keeps for its counter. -/
def unpairBody : Program 6 := renameRegs Fin.succ pairNextMachine

theorem realises_unpairBody : Realises unpairBody fun regs i =>
    if i = 0 then regs 0
    else if i = 1 then (Nat.pairNext (regs 1, regs 2)).1
    else if i = 2 then (Nat.pairNext (regs 1, regs 2)).2
    else 0 := by
  refine realises_pairNextMachine.renameRegs (Fin.succ_injective 5) ?_ ?_
  · intro regs i
    fin_cases i <;> simp
  · intro regs r hr
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨i, rfl⟩
    · simp
    · exact absurd rfl (hr i)

/-- Count down, advancing the candidate pair each turn. -/
def unpairLoop : Program 6 :=
  [Instr.dec 0 1 (unpairBody.length + 2)] ++ shiftJumps 1 unpairBody ++ [Instr.dec 5 0 0]

theorem length_unpairLoop : unpairLoop.length = unpairBody.length + 2 := by
  simp [unpairLoop]

/-- One turn: decrement the counter, advance the pair, jump back. -/
theorem run_turn (R : Fin 6 → ℕ) (hR : R 0 ≠ 0) :
    ∃ n, (∀ m < n, (run unpairLoop ⟨0, R⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, R⟩ n = ⟨0, fun i => if i = 0 then R 0 - 1
        else if i = 1 then (Nat.pairNext (R 1, R 2)).1
        else if i = 2 then (Nat.pairNext (R 1, R 2)).2 else 0⟩ := by
  set R1 := Function.update R 0 (R 0 - 1) with hR1
  have hstep : step unpairLoop ⟨0, R⟩ = ⟨1, R1⟩ :=
    step_dec_pos (P := unpairLoop) (p := 0) (a := 1) (b := unpairBody.length + 2) rfl hR
  obtain ⟨nb, hbin, hbex⟩ := realises_unpairBody R1
  have hmid : ∀ m ≤ nb, run unpairLoop ⟨1, R1⟩ m =
      ⟨(run unpairBody ⟨0, R1⟩ m).pc + 1, (run unpairBody ⟨0, R1⟩ m).regs⟩ := fun m hm =>
    run_middle (A := [Instr.dec 0 1 (unpairBody.length + 2)]) (C := [Instr.dec 5 0 0])
      hbin m hm
  have hbody : run unpairLoop ⟨1, R1⟩ nb =
      ⟨unpairBody.length + 1, fun i => if i = 0 then R1 0
        else if i = 1 then (Nat.pairNext (R1 1, R1 2)).1
        else if i = 2 then (Nat.pairNext (R1 1, R1 2)).2 else 0⟩ := by
    rw [hmid nb (Nat.le_refl _), hbex]
  refine ⟨nb + 2, fun m hm => ?_, ?_⟩
  · rcases (show m = 0 ∨ (1 ≤ m ∧ m ≤ nb) ∨ m = nb + 1 by omega) with rfl | ⟨hm1, hm2⟩ | rfl
    · rw [length_unpairLoop]; simp
    · rw [show m = 1 + (m - 1) by omega, run_add, run_one, hstep, hmid (m - 1) (by omega),
        length_unpairLoop]
      have := hbin (m - 1) (by omega)
      exact show (run unpairBody ⟨0, R1⟩ (m - 1)).pc + 1 < unpairBody.length + 2 by omega
    · rw [show nb + 1 = 1 + nb by omega, run_add, run_one, hstep, hbody, length_unpairLoop]
      exact show unpairBody.length + 1 < unpairBody.length + 2 by omega
  · have hidx : unpairLoop[unpairBody.length + 1]? = some (Instr.dec 5 0 0) := by
      rw [unpairLoop, List.getElem?_append_right (by simp)]
      simp
    have hzero : (fun i : Fin 6 => if i = 0 then R1 0
        else if i = 1 then (Nat.pairNext (R1 1, R1 2)).1
        else if i = 2 then (Nat.pairNext (R1 1, R1 2)).2 else 0) 5 = 0 := by
      simp only [Fin.reduceEq, if_false]
    rw [show nb + 2 = 1 + nb + 1 by omega, run_add, run_add, run_one, run_one, hstep, hbody,
      step_dec_zero (P := unpairLoop) (p := unpairBody.length + 1) (a := 0) (b := 0) hidx hzero]
    refine congrArg _ (funext fun i => ?_)
    simp only [hR1, Function.update_apply]
    split_ifs <;> simp_all


/-! ## The counted loop -/

/-- The register file after `q` turns, from the clean input configuration. `Nat.pairNext^[q]`
stays opaque here on purpose. -/
def loopState (n q : ℕ) : Fin 6 → ℕ :=
  fun i => if i = 0 then n - q
    else if i = 1 then (Nat.pairNext^[q] (0, 0)).1
    else if i = 2 then (Nat.pairNext^[q] (0, 0)).2 else 0

theorem run_loop (n : ℕ) : ∀ q ≤ n, ∃ steps,
    (∀ m < steps, (run unpairLoop ⟨0, unaryConfig 5 n⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, unaryConfig 5 n⟩ steps = ⟨0, loopState n q⟩ := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    refine congrArg _ (funext fun i => ?_)
    simp only [loopState, unaryConfig, Function.update_apply, Function.iterate_zero_apply]
    split_ifs <;> simp_all
  | succ q ih =>
    intro hq
    obtain ⟨steps, hin, hex⟩ := ih (by omega)
    have hne : loopState n q 0 ≠ 0 := by simp [loopState]; omega
    obtain ⟨nt, htin, htex⟩ := run_turn (loopState n q) hne
    refine ⟨steps + nt, (run_segment_trans hin hex htin htex).1, ?_⟩
    · rw [(run_segment_trans hin hex htin htex).2]
      have hiter : Nat.pairNext^[q + 1] (0, 0) = Nat.pairNext (Nat.pairNext^[q] (0, 0)) :=
        Function.iterate_succ_apply' _ _ _
      refine congrArg _ (funext fun i => ?_)
      simp only [loopState, hiter, Fin.reduceEq, if_true, if_false, Prod.mk.eta]
      split_ifs <;> simp_all
      all_goals omega

/-- **The counted loop computes `Nat.unpair`.** From the clean input configuration it exits with
the two components in registers `1` and `2` and everything else at zero.

`Nat.iterate_pairNext` is used exactly here, at `q = n`, and nowhere inside the induction. -/
theorem run_unpairLoop (n : ℕ) : ∃ steps,
    (∀ m < steps, (run unpairLoop ⟨0, unaryConfig 5 n⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, unaryConfig 5 n⟩ steps =
        ⟨unpairLoop.length, fun i => if i = 1 then (Nat.unpair n).1
          else if i = 2 then (Nat.unpair n).2 else 0⟩ := by
  obtain ⟨steps, hin, hex⟩ := run_loop n n (Nat.le_refl _)
  have hz : loopState n n 0 = 0 := by simp [loopState]
  refine ⟨steps + 1, fun m hm => ?_, ?_⟩
  · rcases (show m < steps ∨ m = steps by omega) with h | rfl
    · exact hin m h
    · rw [hex, length_unpairLoop]
      exact show 0 < unpairBody.length + 2 by omega
  · rw [run_add, hex, run_one,
      step_dec_zero (P := unpairLoop) (p := 0) (a := 1) (b := unpairBody.length + 2) rfl hz,
      length_unpairLoop]
    refine congrArg _ (funext fun i => ?_)
    simp only [loopState, Nat.iterate_pairNext]
    split_ifs <;> simp_all

/-! ## The two constructors

The loop theorem is proved once; `left` and `right` differ only in which component they move into
register `0`. -/

/-- `Nat.Partrec.Code.left`. -/
def leftMachine : Program 6 := seq unpairLoop (seq (move 1 0) (clear 2))

/-- `Nat.Partrec.Code.right`. -/
def rightMachine : Program 6 := seq unpairLoop (seq (move 2 0) (clear 1))

theorem cleanPartComputesUnary_leftMachine :
    CleanPartComputesUnary leftMachine fun n => Part.some (Nat.unpair n).1 := by
  intro n
  refine ⟨fun y hy => ?_, fun _ => trivial⟩
  obtain rfl : y = (Nat.unpair n).1 := by simpa using hy
  obtain ⟨s1, h1in, h1ex⟩ := run_unpairLoop n
  obtain ⟨s2, h2in, h2ex⟩ := ((realises_move (show (1 : Fin 6) ≠ 0 by decide)).seq
    (realises_clear 2)) (fun i => if i = 1 then (Nat.unpair n).1
      else if i = 2 then (Nat.unpair n).2 else 0)
  refine ⟨s1 + s2, join_exit h1in h1ex h2in ?_⟩
  rw [h2ex]
  refine congrArg _ (funext fun i => ?_)
  simp only [unaryConfig, Function.update_apply, Fin.reduceEq, if_true, if_false]
  split_ifs <;> simp_all

theorem cleanPartComputesUnary_rightMachine :
    CleanPartComputesUnary rightMachine fun n => Part.some (Nat.unpair n).2 := by
  intro n
  refine ⟨fun y hy => ?_, fun _ => trivial⟩
  obtain rfl : y = (Nat.unpair n).2 := by simpa using hy
  obtain ⟨s1, h1in, h1ex⟩ := run_unpairLoop n
  obtain ⟨s2, h2in, h2ex⟩ := ((realises_move (show (2 : Fin 6) ≠ 0 by decide)).seq
    (realises_clear 1)) (fun i => if i = 1 then (Nat.unpair n).1
      else if i = 2 then (Nat.unpair n).2 else 0)
  refine ⟨s1 + s2, join_exit h1in h1ex h2in ?_⟩
  rw [h2ex]
  refine congrArg _ (funext fun i => ?_)
  simp only [unaryConfig, Function.update_apply, Fin.reduceEq, if_true, if_false]
  split_ifs <;> simp_all

end RegisterMachine

end Hilbert10
