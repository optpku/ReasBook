module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachineMacros
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.PairingEnumeration
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The pairing enumeration as a register machine

Issue #51, step 3. `pairNextMachine` advances a pair of registers one place along `Nat.pair`'s
enumeration, and is proved against the semantic `Nat.pairNext`.

## Roles, not parameters

This machine fixes a `Fin 5` layout — `0 = a`, `1 = b`, `2 = lo`, `3 = hi`, `4 = tmp` — rather
than taking five register arguments with ten distinctness hypotheses. Callers place it in a
larger register file with `renameRegs` (#39) or `CleanPartComputesUnary.call`, supplying the
injection themselves. That is still no allocator, and it keeps the statement readable.

## The finishing program

After `compare` the registers hold `lo = b - a` and `hi = a - b`, and one branch on those two
settles all four cases of `pairNext`:

| condition | result |
|---|---|
| `lo ≥ 2` | `(a + 1, b)` |
| `lo = 1` | `(a + 1, 0)`, which is `(b, 0)` since `b = a + 1` |
| `lo = 0`, `hi = 0` | `(0, a + 1)` |
| `lo = 0`, `hi > 0` | `(a, b + 1)` |

The `lo = 1` case is the shell rollover, and it needs no copy: `a + 1` *is* `b` there.

The program does its own cleanup by consuming the residuals rather than calling `clear`, so it is
one flat ten-instruction list with no control-flow combinator, no jump gadget and no scratch
beyond what `compare` already used. Each branch ends by draining a register in place, which is
what `run_drain` is for.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

/-- Turn `compare`'s residuals into `pairNext`'s answer.

Positions 2, 5, 6 and 9 are drains: a `dec` whose positive branch is its own position. -/
def pairNextFinish : Program 5 :=
  [.dec 2 1 4,   -- 0: lo > 0 → 1;  lo = 0 → 4
   .dec 2 2 3,   -- 1: lo ≥ 2 → 2;  lo = 1 → 3
   .dec 2 2 8,   -- 2: drain lo → 8
   .inc 0 9,     -- 3: a++ → 9
   .dec 3 5 6,   -- 4: hi > 0 → 5;  hi = 0 → 6
   .dec 3 5 7,   -- 5: drain hi → 7
   .dec 0 6 7,   -- 6: drain a → 7
   .inc 1 10,    -- 7: b++, exit
   .inc 0 10,    -- 8: a++, exit
   .dec 1 9 10]  -- 9: drain b, exit

/-- The register file `pairNextFinish` produces, as a function of the one it is given. -/
def finishState (regs : Fin 5 → ℕ) : Fin 5 → ℕ :=
  if 2 ≤ regs 2 then fun i => if i = 0 then regs 0 + 1 else if i = 2 then 0 else regs i
  else if regs 2 = 1 then
    fun i => if i = 0 then regs 0 + 1 else if i = 1 then 0 else if i = 2 then 0 else regs i
  else if regs 3 = 0 then fun i => if i = 0 then 0 else if i = 1 then regs 1 + 1 else regs i
  else fun i => if i = 1 then regs 1 + 1 else if i = 3 then 0 else regs i

theorem realises_pairNextFinish : Realises pairNextFinish finishState := by
  intro regs
  by_cases h2 : 2 ≤ regs 2
  · -- `lo ≥ 2`: consume two, drain the rest, then `a++`
    have hL : regs 2 ≠ 0 := by omega
    have hpre : run pairNextFinish ⟨0, regs⟩ 2 =
        ⟨2, Function.update regs 2 (regs 2 - 2)⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
        step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl hL,
        step_dec_pos (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
          (by rw [Function.update_self]; omega)]
      refine congrArg _ (funext fun i => ?_)
      simp only [Function.update_apply]
      split_ifs <;> omega
    have hdrain : run pairNextFinish ⟨2, Function.update regs 2 (regs 2 - 2)⟩
        (regs 2 - 2 + 1) = ⟨8, Function.update regs 2 0⟩ := by
      have h := run_drain (P := pairNextFinish) (r := 2) (p := 2) (e := 8) rfl
        (Function.update regs 2 (regs 2 - 2))
      rwa [Function.update_self, Function.update_idem] at h
    refine ⟨regs 2 + 2, fun m hm => ?_, ?_⟩
    · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 2) ∨ m = regs 2 + 1 by omega)
        with rfl | rfl | ⟨hm2, hm3⟩ | rfl
      · simp [pairNextFinish]
      · rw [run_one, step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl hL]
        simp [pairNextFinish]
      · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
          run_drain_partial (P := pairNextFinish) (r := 2) (p := 2) (e := 8) rfl _ (m - 2)
            (by rw [Function.update_self]; omega)]
        simp [pairNextFinish]
      · rw [show regs 2 + 1 = 2 + (regs 2 - 2 + 1) by omega, run_add, hpre, hdrain]
        simp [pairNextFinish]
    · rw [show regs 2 + 2 = 2 + (regs 2 - 2 + 1) + 1 by omega, run_add, run_add, hpre, hdrain,
        run_one, step_inc (P := pairNextFinish) (p := 8) (a := 10) rfl,
        show pairNextFinish.length = 10 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [finishState, if_pos h2, Function.update_apply]
      split_ifs <;> simp_all
  · by_cases h1 : regs 2 = 1
    · -- `lo = 1`: the shell rollover, `a++` and `b := 0`
      have hpre : run pairNextFinish ⟨0, regs⟩ 3 =
          ⟨9, Function.update (Function.update regs 2 0) 0 (regs 0 + 1)⟩ := by
        rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, run_add, run_add, run_one, run_one, run_one,
          step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
          step_dec_zero (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
            (by rw [Function.update_self]; omega),
          step_inc (P := pairNextFinish) (p := 3) (a := 9) rfl]
        refine congrArg _ (funext fun i => ?_)
        simp only [Function.update_apply]
        split_ifs <;> simp_all
      have hdrain : run pairNextFinish
          ⟨9, Function.update (Function.update regs 2 0) 0 (regs 0 + 1)⟩ (regs 1 + 1) =
          ⟨10, Function.update
            (Function.update (Function.update regs 2 0) 0 (regs 0 + 1)) 1 0⟩ := by
        have h := run_drain (P := pairNextFinish) (r := 1) (p := 9) (e := 10) rfl
          (Function.update (Function.update regs 2 0) 0 (regs 0 + 1))
        rwa [show Function.update (Function.update regs 2 0) 0 (regs 0 + 1) 1 = regs 1 by
          simp] at h
      refine ⟨regs 1 + 4, fun m hm => ?_, ?_⟩
      · rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ (3 ≤ m ∧ m ≤ regs 1 + 3) by omega)
          with rfl | rfl | rfl | ⟨hm3, hm4⟩
        · simp [pairNextFinish]
        · rw [run_one, step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
            (by omega)]
          simp [pairNextFinish]
        · rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_zero (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
              (by rw [Function.update_self]; omega)]
          simp [pairNextFinish]
        · rw [show m = 3 + (m - 3) by omega, run_add, hpre,
            run_drain_partial (P := pairNextFinish) (r := 1) (p := 9) (e := 10) rfl _ (m - 3)
              (by rw [show Function.update (Function.update regs 2 0) 0 (regs 0 + 1) 1 = regs 1 by
                simp]; omega)]
          simp [pairNextFinish]
      · rw [show regs 1 + 4 = 3 + (regs 1 + 1) by omega, run_add, hpre, hdrain,
          show pairNextFinish.length = 10 from rfl]
        refine congrArg _ (funext fun i => ?_)
        simp only [finishState, if_neg h2, if_pos h1, Function.update_apply]
        split_ifs <;> simp_all
    · by_cases h3 : regs 3 = 0
      · -- `lo = 0`, `hi = 0`: the diagonal, `a := 0` and `b++`
        have hpre : run pairNextFinish ⟨0, regs⟩ 2 = ⟨6, regs⟩ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_zero (P := pairNextFinish) (p := 4) (a := 5) (b := 6) rfl h3]
        have hdrain : run pairNextFinish ⟨6, regs⟩ (regs 0 + 1) =
            ⟨7, Function.update regs 0 0⟩ :=
          run_drain (P := pairNextFinish) (r := 0) (p := 6) (e := 7) rfl regs
        refine ⟨regs 0 + 4, fun m hm => ?_, ?_⟩
        · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 0 + 2) ∨ m = regs 0 + 3 by omega)
            with rfl | rfl | ⟨hm2, hm3⟩ | rfl
          · simp [pairNextFinish]
          · rw [run_one, step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
              (by omega)]
            simp [pairNextFinish]
          · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
              run_drain_partial (P := pairNextFinish) (r := 0) (p := 6) (e := 7) rfl _ (m - 2)
                (by omega)]
            simp [pairNextFinish]
          · rw [show regs 0 + 3 = 2 + (regs 0 + 1) by omega, run_add, hpre, hdrain]
            simp [pairNextFinish]
        · rw [show regs 0 + 4 = 2 + (regs 0 + 1) + 1 by omega, run_add, run_add, hpre, hdrain,
            run_one, step_inc (P := pairNextFinish) (p := 7) (a := 10) rfl,
            show pairNextFinish.length = 10 from rfl]
          refine congrArg _ (funext fun i => ?_)
          simp only [finishState, if_neg h2, if_neg h1, if_pos h3, Function.update_apply]
          split_ifs <;> simp_all
      · -- `lo = 0`, `hi > 0`: below the diagonal, `b++`
        have hpre : run pairNextFinish ⟨0, regs⟩ 2 =
            ⟨5, Function.update regs 3 (regs 3 - 1)⟩ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_pos (P := pairNextFinish) (p := 4) (a := 5) (b := 6) rfl h3]
        have hdrain : run pairNextFinish ⟨5, Function.update regs 3 (regs 3 - 1)⟩
            (regs 3 - 1 + 1) = ⟨7, Function.update regs 3 0⟩ := by
          have h := run_drain (P := pairNextFinish) (r := 3) (p := 5) (e := 7) rfl
            (Function.update regs 3 (regs 3 - 1))
          rwa [Function.update_self, Function.update_idem] at h
        refine ⟨regs 3 + 3, fun m hm => ?_, ?_⟩
        · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 3 + 1) ∨ m = regs 3 + 2 by omega)
            with rfl | rfl | ⟨hm2, hm3⟩ | rfl
          · simp [pairNextFinish]
          · rw [run_one, step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
              (by omega)]
            simp [pairNextFinish]
          · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
              run_drain_partial (P := pairNextFinish) (r := 3) (p := 5) (e := 7) rfl _ (m - 2)
                (by rw [Function.update_self]; omega)]
            simp [pairNextFinish]
          · rw [show regs 3 + 2 = 2 + (regs 3 - 1 + 1) by omega, run_add, hpre, hdrain]
            simp [pairNextFinish]
        · rw [show regs 3 + 3 = 2 + (regs 3 - 1 + 1) + 1 by omega, run_add, run_add, hpre,
            hdrain, run_one, step_inc (P := pairNextFinish) (p := 7) (a := 10) rfl,
            show pairNextFinish.length = 10 from rfl]
          refine congrArg _ (funext fun i => ?_)
          simp only [finishState, if_neg h2, if_neg h1, if_neg h3, Function.update_apply]
          split_ifs <;> simp_all

/-! ## The machine -/

/-- One step along the pairing enumeration, on registers `0` and `1`. -/
def pairNextMachine : Program 5 := seq (compare 0 1 2 3 4) pairNextFinish

/-- **`pairNextMachine` realises `Nat.pairNext`.** Registers `0` and `1` become the components of
the successor pair; `2`, `3` and `4` come back at zero whatever they held.

The four `by_cases` fix which branch of `pairNext` applies *before* the register-by-register
comparison, rather than letting `split_ifs` enumerate the product of the two. That ordering is
not cosmetic: the other way round exhausts a million heartbeats. -/
theorem realises_pairNextMachine :
    Realises pairNextMachine fun regs i =>
      if i = 0 then (Nat.pairNext (regs 0, regs 1)).1
      else if i = 1 then (Nat.pairNext (regs 0, regs 1)).2
      else 0 := by
  refine ((realises_compare (a := 0) (b := 1) (lo := 2) (hi := 3) (tmp := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).seq realises_pairNextFinish).congr fun regs => ?_
  rw [finishState]
  simp only [Fin.reduceEq, if_true, if_false]
  by_cases h2 : 2 ≤ regs 1 - regs 0
  · rw [if_pos h2, show Nat.pairNext (regs 0, regs 1) = (regs 0 + 1, regs 1) by
      simp only [Nat.pairNext]
      rw [if_pos (show regs 0 < regs 1 by omega), if_pos (show regs 0 + 1 < regs 1 by omega)]]
    funext i
    fin_cases i <;> simp
    all_goals omega
  · rw [if_neg h2]
    by_cases h1 : regs 1 - regs 0 = 1
    · rw [if_pos h1, show Nat.pairNext (regs 0, regs 1) = (regs 0 + 1, 0) by
        simp only [Nat.pairNext]
        rw [if_pos (show regs 0 < regs 1 by omega), if_neg (show ¬ regs 0 + 1 < regs 1 by omega)]
        exact congrArg (fun x => (x, 0)) (by omega)]
      funext i
      fin_cases i <;> simp
      all_goals omega
    · rw [if_neg h1]
      by_cases h3 : regs 0 - regs 1 = 0
      · rw [if_pos h3, show Nat.pairNext (regs 0, regs 1) = (0, regs 0 + 1) by
          simp only [Nat.pairNext]
          rw [if_neg (show ¬ regs 0 < regs 1 by omega), if_pos (show regs 0 = regs 1 by omega)]]
        funext i
        fin_cases i <;> simp
        all_goals omega
      · rw [if_neg h3, show Nat.pairNext (regs 0, regs 1) = (regs 0, regs 1 + 1) by
          simp only [Nat.pairNext]
          rw [if_neg (show ¬ regs 0 < regs 1 by omega), if_neg (show ¬ regs 0 = regs 1 by omega)]]
        funext i
        fin_cases i <;> simp
        all_goals omega

end RegisterMachine

end Hilbert10
