/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ConfigCoding
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A width that is big enough

Issue #46. #45 leaves every statement conditional on `FitsConfig w`, so something has to produce
a `w`. This file produces one, for a bounded prefix of a run.

## Deliberately not minimal

The width is a *sum*, not a maximum and not a logarithm:

```
configWeight c = c.pc + ∑ r, c.regs r
programWeight P = P.length + ∑ I ∈ P, I.jumpWeight
runWidth P c n = programWeight P + ∑ i ≤ n, configWeight (run P c i)
```

Every quantity that has to fit is one summand of `runWidth`, so every bound is
`Finset.single_le_sum` followed by `Nat.lt_two_pow_self : m < 2 ^ m`. There is no `Nat.log`, no
`Finset.max'`, no case split on emptiness, and no arithmetic to verify: the width is grotesquely
larger than necessary, which costs nothing because it is representation data inside an
existential that #47 and #48 immediately eliminate.

Using the weight as an exponent is the whole trick. `runWidth` bounds the *values*, and
`2 ^ runWidth` then dominates them with room to spare, so the two roles a width plays — being
large enough to hold a value, and being a field width — never have to be reconciled.

## Main results

* `RegisterMachine.fits_runWidth` — every configuration of the prefix fits
* `RegisterMachine.exists_width` — the packaged form: one width for the configurations, the
  program length, and every jump target in the program
* `RegisterMachine.encodedStep_run` — the handoff: at this width, consecutive configurations of
  a run are related by #45's step relation
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- Everything a single configuration needs to fit, added up. -/
def configWeight (c : Config k) : ℕ := c.pc + ∑ r, c.regs r

/-- The jump targets of one instruction, added up. -/
def Instr.jumpWeight : Instr k → ℕ
  | .inc _ j => j
  | .dec _ jpos jzero => jpos + jzero

/-- Everything the program's own constants need to fit, added up. -/
def programWeight (P : Program k) : ℕ := P.length + (P.map Instr.jumpWeight).sum

/-- A width large enough for the first `n + 1` configurations of the run from `c`, and for the
program's constants. -/
def runWidth (P : Program k) (c : Config k) (n : ℕ) : ℕ :=
  programWeight P + ∑ i ∈ Finset.range (n + 1), configWeight (run P c i)

theorem pc_le_configWeight (c : Config k) : c.pc ≤ configWeight c := Nat.le_add_right _ _

theorem regs_le_configWeight (c : Config k) (r : Fin k) : c.regs r ≤ configWeight c :=
  le_trans (Finset.single_le_sum (f := c.regs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
    (Nat.le_add_left _ _)

theorem length_le_programWeight (P : Program k) : P.length ≤ programWeight P :=
  Nat.le_add_right _ _

theorem jumpWeight_le_programWeight {P : Program k} {I : Instr k} (hI : I ∈ P) :
    I.jumpWeight ≤ programWeight P :=
  le_trans (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hI))
    (Nat.le_add_left _ _)

theorem programWeight_le_runWidth (P : Program k) (c : Config k) (n : ℕ) :
    programWeight P ≤ runWidth P c n := Nat.le_add_right _ _

theorem configWeight_le_runWidth {P : Program k} {c : Config k} {i n : ℕ} (hi : i ≤ n) :
    configWeight (run P c i) ≤ runWidth P c n :=
  le_trans (Finset.single_le_sum (f := fun j => configWeight (run P c j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))) (Nat.le_add_left _ _)

/-- The one arithmetic fact this file uses: a weight is dwarfed by two to that weight. -/
theorem lt_two_pow_runWidth {P : Program k} {c : Config k} {n m : ℕ} (h : m ≤ runWidth P c n) :
    m < 2 ^ runWidth P c n :=
  lt_of_le_of_lt h Nat.lt_two_pow_self

theorem runWidth_mono {P : Program k} {c : Config k} {m n : ℕ} (h : m ≤ n) :
    runWidth P c m ≤ runWidth P c n := by
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset ?_) _
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- **Every configuration of the prefix fits.** -/
theorem fits_runWidth {P : Program k} {c : Config k} {i n : ℕ} (hi : i ≤ n) :
    FitsConfig (runWidth P c n) (run P c i) :=
  ⟨lt_two_pow_runWidth (le_trans (pc_le_configWeight _) (configWeight_le_runWidth hi)),
    fun r => lt_two_pow_runWidth
      (le_trans (regs_le_configWeight _ r) (configWeight_le_runWidth hi))⟩

theorem length_lt_two_pow_runWidth (P : Program k) (c : Config k) (n : ℕ) :
    P.length < 2 ^ runWidth P c n :=
  lt_two_pow_runWidth (le_trans (length_le_programWeight P) (programWeight_le_runWidth P c n))

theorem jumpWeight_lt_two_pow_runWidth {P : Program k} {I : Instr k} (hI : I ∈ P) (c : Config k)
    (n : ℕ) : I.jumpWeight < 2 ^ runWidth P c n :=
  lt_two_pow_runWidth (le_trans (jumpWeight_le_programWeight hI) (programWeight_le_runWidth P c n))

/-- **The packaged form.** One width under which the whole prefix of the run is representable and
every constant of the program fits.

The jump targets are listed separately because that is the shape #45's `EncodedStep` asks for:
each disjunct bounds the target it selects. -/
theorem exists_width (P : Program k) (c : Config k) (n : ℕ) :
    ∃ w, P.length < 2 ^ w
      ∧ (∀ (r : Fin k) (j : ℕ), Instr.inc r j ∈ P → j < 2 ^ w)
      ∧ (∀ (r : Fin k) (jpos jzero : ℕ), Instr.dec r jpos jzero ∈ P →
          jpos < 2 ^ w ∧ jzero < 2 ^ w)
      ∧ ∀ i ≤ n, FitsConfig w (run P c i) := by
  refine ⟨runWidth P c n, length_lt_two_pow_runWidth P c n, ?_, ?_, fun i hi => fits_runWidth hi⟩
  · intro r j hI
    have := jumpWeight_lt_two_pow_runWidth hI c n
    simpa [Instr.jumpWeight] using this
  · intro r jpos jzero hI
    have := jumpWeight_lt_two_pow_runWidth hI c n
    simp only [Instr.jumpWeight] at this
    omega

/-- The handoff to #47: at `runWidth`, consecutive configurations of the run are related by the
encoded step. This is where #45's local statement and #46's width meet, and it is the only place
the two files need to be read together. -/
theorem encodedStep_run {P : Program k} {c : Config k} {i n : ℕ} (hi : i < n)
    (hpc : (run P c i).pc < P.length) :
    EncodedStep P (runWidth P c n) (configCode (runWidth P c n) (run P c i))
      (configCode (runWidth P c n) (run P c (i + 1))) := by
  have hstep : step P (run P c i) = run P c (i + 1) := (run_succ P c i).symm
  rw [← hstep]
  exact encodedStep_configCode (fits_runWidth (by omega))
    (hstep ▸ fits_runWidth (P := P) (c := c) (i := i + 1) (n := n) (by omega)) hpc

end RegisterMachine

end Hilbert10
