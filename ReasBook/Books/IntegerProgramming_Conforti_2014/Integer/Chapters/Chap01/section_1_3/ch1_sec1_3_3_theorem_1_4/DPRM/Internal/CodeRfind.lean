/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodePrec

/-!
# The source semantics of `Nat.Partrec.Code.rfind'`

Issue #43, before any register is chosen — the same order as #41, #51 and #42.

`rfind'` minimises *from an offset*: on input `Nat.pair a m` it returns the least `y ≥ m` with
`f (Nat.pair a y) = 0`. Mathlib writes that with `Nat.rfind` over a shifted predicate and a
`Part.map`, and `Nat.mem_rfind` is the decisive fact.

## Keeping the offset

`mem_rfindSem` is stated in terms of the number of *unsuccessful turns* `q`, not as an interval
`m ≤ z < y`:

```lean
y ∈ rfindSem f a m ↔ ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
  ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0
```

That is what the machine does: after `q` unsuccessful turns its candidate is `q + m`. An interval
form is a corollary if a consumer ever wants one; stating it that way first would put an
arithmetic translation between the machine and its specification, which is exactly the sort of
gap the earlier constructors avoided by naming the recurrence first.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- Minimisation from an offset, named. -/
def rfindSem (f : ℕ →. ℕ) (a m : ℕ) : Part ℕ :=
  (Nat.rfind fun n => (fun z => z = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The predicate the search minimises, spelled out: `true` means the callee returned zero. -/
theorem mem_map_decide_true {f : ℕ →. ℕ} {u : ℕ} :
    true ∈ ((fun z => decide (z = 0)) <$> f u) ↔ 0 ∈ f u := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    have hz' : z = 0 := by simpa using hz0
    exact hz' ▸ hz
  · intro h
    exact ⟨0, h, by simp⟩

theorem mem_map_decide_false {f : ℕ →. ℕ} {u : ℕ} :
    false ∈ ((fun z => decide (z = 0)) <$> f u) ↔ ∃ z ∈ f u, z ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩

/-- **The search characterisation**, counting unsuccessful turns. -/
theorem mem_rfindSem {f : ℕ →. ℕ} {a m y : ℕ} :
    y ∈ rfindSem f a m ↔
      ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
        ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  rw [rfindSem, Part.mem_map_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Nat.mem_rfind] at hq
    exact ⟨q, rfl, mem_map_decide_true.mp hq.1,
      fun j hj => mem_map_decide_false.mp (hq.2 hj)⟩
  · rintro ⟨q, rfl, hq, hmin⟩
    exact ⟨q, Nat.mem_rfind.mpr ⟨mem_map_decide_true.mpr hq,
      fun {j} hj => mem_map_decide_false.mpr (hmin j hj)⟩, rfl⟩

/-- **The bridge.** `Code.rfind'`'s evaluation on a paired input is the named search. -/
theorem eval_rfind_eq (cf : Code) (a m : ℕ) :
    (Code.rfind' cf).eval (Nat.pair a m) = rfindSem cf.eval a m := by
  rw [Code.eval, Nat.unpaired, Nat.unpair_pair]
  rfl

/-- The same for an arbitrary input, which is what the machine receives. -/
theorem eval_rfind_unpair (cf : Code) (x : ℕ) :
    (Code.rfind' cf).eval x = rfindSem cf.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_rfind_eq cf _ _

/-! ## The controller's register layout

`Fin (k + 20)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current candidate |
| `3` | the temporary `copy` borrows |
| `4`–`12` | the `pairMachine` block |
| `13`–`18` | the `unpairLoop` block |
| `19 …` | the predicate callee's block |

Simpler than `prec`'s: one callee, one pairing block, no accumulator. -/

variable (k)

/-- The parameter. -/ def sA : Fin (k + 20) := ⟨1, by omega⟩
/-- The current candidate. -/ def sC : Fin (k + 20) := ⟨2, by omega⟩
/-- The temporary. -/ def sT : Fin (k + 20) := ⟨3, by omega⟩

/-- The pairing block. -/
def sPair (i : Fin 9) : Fin (k + 20) := ⟨4 + i.val, by omega⟩

/-- The unpairing block. -/
def sUnpair (i : Fin 6) : Fin (k + 20) := ⟨13 + i.val, by omega⟩

/-- The predicate callee's block. -/
def sCall (i : Fin (k + 1)) : Fin (k + 20) := ⟨19 + i.val, by omega⟩

variable {k}

@[simp] theorem sA_val : (sA k).val = 1 := rfl
@[simp] theorem sC_val : (sC k).val = 2 := rfl
@[simp] theorem sT_val : (sT k).val = 3 := rfl
@[simp] theorem sPair_val (i : Fin 9) : (sPair k i).val = 4 + i.val := rfl
@[simp] theorem sUnpair_val (i : Fin 6) : (sUnpair k i).val = 13 + i.val := rfl
@[simp] theorem sCall_val (i : Fin (k + 1)) : (sCall k i).val = 19 + i.val := rfl

theorem sPair_injective : Function.Injective (sPair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sUnpair_injective : Function.Injective (sUnpair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sCall_injective : Function.Injective (sCall k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive**: `4 + 9 + 6 + (k+1) = k + 20`. -/
theorem sLayout_cases (r : Fin (k + 20)) :
    r = 0 ∨ r = sA k ∨ r = sC k ∨ r = sT k ∨ (∃ i, r = sPair k i) ∨
      (∃ i, r = sUnpair k i) ∨ ∃ i, r = sCall k i := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ (4 ≤ r.val ∧ r.val ≤ 12) ∨
      (13 ≤ r.val ∧ r.val ≤ 18) ∨ 19 ≤ r.val by omega) with h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 4, by omega⟩, Fin.ext (by simp; omega)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 13, by omega⟩, Fin.ext (by simp; omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 19, by omega⟩, Fin.ext (by simp; omega)⟩)))))

/-! ### Separation -/

theorem sFixed_ne :
    (0 : Fin (k + 20)) ≠ sA k ∧ (0 : Fin (k + 20)) ≠ sC k ∧ (0 : Fin (k + 20)) ≠ sT k ∧
    sA k ≠ sC k ∧ sA k ≠ sT k ∧ sC k ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; have := congrArg Fin.val h; simp at this)

theorem sFixed_ne' :
    sA k ≠ (0 : Fin (k + 20)) ∧ sC k ≠ (0 : Fin (k + 20)) ∧ sT k ≠ (0 : Fin (k + 20)) ∧
    sC k ≠ sA k ∧ sT k ≠ sA k ∧ sT k ≠ sC k :=
  ⟨sFixed_ne.1.symm, sFixed_ne.2.1.symm, sFixed_ne.2.2.1.symm, sFixed_ne.2.2.2.1.symm,
    sFixed_ne.2.2.2.2.1.symm, sFixed_ne.2.2.2.2.2.symm⟩

theorem sPair_ne_fixed (i : Fin 9) :
    sPair k i ≠ 0 ∧ sPair k i ≠ sA k ∧ sPair k i ≠ sC k ∧ sPair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sUnpair_ne_fixed (i : Fin 6) :
    sUnpair k i ≠ 0 ∧ sUnpair k i ≠ sA k ∧ sUnpair k i ≠ sC k ∧ sUnpair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sCall_ne_fixed (i : Fin (k + 1)) :
    sCall k i ≠ 0 ∧ sCall k i ≠ sA k ∧ sCall k i ≠ sC k ∧ sCall k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sPair_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + 20)) ≠ sPair k i ∧ sA k ≠ sPair k i ∧ sC k ≠ sPair k i ∧ sT k ≠ sPair k i :=
  ⟨(sPair_ne_fixed i).1.symm, (sPair_ne_fixed i).2.1.symm, (sPair_ne_fixed i).2.2.1.symm,
    (sPair_ne_fixed i).2.2.2.symm⟩

theorem sUnpair_ne_fixed' (i : Fin 6) :
    (0 : Fin (k + 20)) ≠ sUnpair k i ∧ sA k ≠ sUnpair k i ∧ sC k ≠ sUnpair k i ∧
      sT k ≠ sUnpair k i :=
  ⟨(sUnpair_ne_fixed i).1.symm, (sUnpair_ne_fixed i).2.1.symm, (sUnpair_ne_fixed i).2.2.1.symm,
    (sUnpair_ne_fixed i).2.2.2.symm⟩

theorem sCall_ne_fixed' (i : Fin (k + 1)) :
    (0 : Fin (k + 20)) ≠ sCall k i ∧ sA k ≠ sCall k i ∧ sC k ≠ sCall k i ∧ sT k ≠ sCall k i :=
  ⟨(sCall_ne_fixed i).1.symm, (sCall_ne_fixed i).2.1.symm, (sCall_ne_fixed i).2.2.1.symm,
    (sCall_ne_fixed i).2.2.2.symm⟩

theorem sPair_ne_sUnpair (i : Fin 9) (j : Fin 6) : sPair k i ≠ sUnpair k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sPair_ne_sCall (i : Fin 9) (j : Fin (k + 1)) : sPair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sCall (i : Fin 6) (j : Fin (k + 1)) : sUnpair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sPair (j : Fin 6) (i : Fin 9) : sUnpair k j ≠ sPair k i :=
  (sPair_ne_sUnpair i j).symm

theorem sCall_ne_sPair (j : Fin (k + 1)) (i : Fin 9) : sCall k j ≠ sPair k i :=
  (sPair_ne_sCall i j).symm

theorem sCall_ne_sUnpair (j : Fin (k + 1)) (i : Fin 6) : sCall k j ≠ sUnpair k i :=
  (sUnpair_ne_sCall i j).symm

attribute [local simp] sFixed_ne sFixed_ne' sPair_ne_fixed sPair_ne_fixed'
  sUnpair_ne_fixed sUnpair_ne_fixed' sCall_ne_fixed sCall_ne_fixed'
  sPair_ne_sUnpair sPair_ne_sCall sUnpair_ne_sCall
  sUnpair_ne_sPair sCall_ne_sPair sCall_ne_sUnpair

/-! ## The machine

One callee, one pairing, and a branch on its answer. The loop body is a *prefix* of the loop
rather than a middle segment, so `run_append_of_lt` and `halts_append_of_exits` suffice and
`run_middle` is not needed at all. -/

variable (Cf : Program (k + 1))

/-- Compute `Nat.pair a c` in the pairing block. -/
def rfindPairUp : Program (k + 20) :=
  seq (copy (sA k) (sPair k 0) (sT k))
    (seq (copy (sC k) (sPair k 1) (sT k)) (renameRegs (sPair k) pairMachine))

/-- Hand it to the callee and give the pairing block back clean. -/
def rfindSeedCall : Program (k + 20) :=
  seq (copy (sPair k 2) (sCall k 0) (sT k))
    (seq (clear (sPair k 0)) (seq (clear (sPair k 1)) (clear (sPair k 2))))

/-- One evaluation of the predicate at the current candidate. -/
def rfindBody : Program (k + 20) :=
  seq (rfindPairUp (k := k)) (seq (rfindSeedCall (k := k)) (renameRegs (sCall k) Cf))

/-- The search: evaluate, and on a nonzero answer discard it, step the candidate and repeat.

The `dec` at `rfindBody.length` is the branch — a zero answer leaves the loop, anything else
falls into the drain and then the increment, which also jumps back. -/
def rfindLoop : Program (k + 20) :=
  rfindBody (k := k) Cf ++
    [Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 3),
      Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 2),
      Instr.inc (sC k) 0]

theorem length_rfindLoop :
    (rfindLoop (k := k) Cf).length = (rfindBody (k := k) Cf).length + 3 := by
  simp [rfindLoop]

/-- Split the input. -/
def rfindSplit : Program (k + 20) :=
  seq (copy 0 (sUnpair k 0) (sT k)) (renameRegs (sUnpair k) unpairLoop)

/-- Move the parameter and the initial candidate into place. -/
def rfindSeed : Program (k + 20) :=
  seq (move (sUnpair k 1) (sA k)) (seq (move (sUnpair k 2) (sC k)) (clear 0))

/-- Return the candidate the search stopped at. -/
def rfindFinish : Program (k + 20) := seq (clear (sA k)) (move (sC k) 0)

/-- The whole controller. -/
def rfindController : Program (k + 20) :=
  seq (rfindSplit (k := k))
    (seq (rfindSeed (k := k)) (seq (rfindLoop (k := k) Cf) (rfindFinish (k := k))))

variable {Cf}

/-! ### The loop head

The only state the search carries: the parameter and the current candidate. There is no counter,
which is what makes soundness an induction on halting time rather than on a register. -/

/-- The register file at a loop head. -/
def searchState (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c else 0

/-- After the pairing: the candidate's argument built. -/
def searchPaired (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sPair k 0 then a else if r = sPair k 1 then c
    else if r = sPair k 2 then Nat.pair a c else 0

/-- After the callee is seeded and the pairing block cleaned. -/
def searchSeeded (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then Nat.pair a c else 0

/-- After the call. -/
def searchAnswered (a c z : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then z else 0

/-! ### The body's transitions -/

/-- After the parameter reaches the pairing block. -/
def searchPairA (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sPair k 0 then a
    else if r = sA k then a else if r = sC k then c else 0

/-- After the candidate reaches it. -/
def searchPairB (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sPair k 1 then c else if r = sPair k 0 then a
    else if r = sA k then a else if r = sC k then c else 0

theorem searchPairB_comp_sPair (a c : ℕ) :
    searchPairB (k := k) a c ∘ sPair k = fun i => if i = 0 then a else if i = 1 then c else 0 := by
  funext i
  fin_cases i <;> simp [searchPairB, sPair_injective.eq_iff]

theorem run_rfindPairUp_copyA (a c : ℕ) :
    ∃ N, (∀ m < N, (run (copy (sA k) (sPair k 0) (sT k)) ⟨0, searchState a c⟩ m).pc <
        (copy (sA k) (sPair k 0) (sT k)).length) ∧
      run (copy (sA k) (sPair k 0) (sT k)) ⟨0, searchState a c⟩ N =
        ⟨(copy (sA k) (sPair k 0) (sT k)).length, searchPairA a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := sA k) (s := sPair k 0) (t := sT k) (by simp) (by simp) (by simp)
      (searchState (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchState, searchPairA, sPair_injective.eq_iff]

theorem run_rfindPairUp_copyC (a c : ℕ) :
    ∃ N, (∀ m < N, (run (copy (sC k) (sPair k 1) (sT k)) ⟨0, searchPairA a c⟩ m).pc <
        (copy (sC k) (sPair k 1) (sT k)).length) ∧
      run (copy (sC k) (sPair k 1) (sT k)) ⟨0, searchPairA a c⟩ N =
        ⟨(copy (sC k) (sPair k 1) (sT k)).length, searchPairB a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := sC k) (s := sPair k 1) (t := sT k) (by simp) (by simp) (by simp)
      (searchPairA (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchPairA, searchPairB, sPair_injective.eq_iff]

theorem run_rfindPairUp_pair (a c : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (sPair k) pairMachine) ⟨0, searchPairB a c⟩ m).pc <
        (renameRegs (sPair k) pairMachine).length) ∧
      run (renameRegs (sPair k) pairMachine) ⟨0, searchPairB a c⟩ N =
        ⟨(renameRegs (sPair k) pairMachine).length, searchPaired a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState sPair_injective) (searchPairB (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_apply sPair_injective, searchPairB_comp_sPair]
    simp only [searchPaired]
    fin_cases i <;> simp [sPair_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [searchPairB, searchPaired]

theorem run_rfindPairUp (a c : ℕ) :
    ∃ N, (∀ m < N, (run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ m).pc <
        (rfindPairUp (k := k)).length) ∧
      run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ N =
        ⟨(rfindPairUp (k := k)).length, searchPaired a c⟩ := by
  rw [rfindPairUp]
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp_copyA (k := k) a c
  obtain ⟨N2, i2, e2⟩ := run_rfindPairUp_copyC (k := k) a c
  obtain ⟨N3, i3, e3⟩ := run_rfindPairUp_pair (k := k) a c
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

theorem run_rfindSeedCall (a c : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ m).pc <
        (rfindSeedCall (k := k)).length) ∧
      run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ N =
        ⟨(rfindSeedCall (k := k)).length, searchSeeded a c⟩ := by
  rw [rfindSeedCall]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_copy (r := sPair k 2) (s := sCall k 0) (t := sT k)
        (by simp) (by simp) (by simp)).seq
      ((realises_clear (sPair k 0)).seq
        ((realises_clear (sPair k 1)).seq (realises_clear (sPair k 2)))))
      (searchPaired (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · fin_cases i <;> simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · by_cases hi : i = 0
    · subst hi; simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
    · simp [searchPaired, searchSeeded, sCall_injective.eq_iff, hi]

theorem callState_searchSeeded (a c z : ℕ) :
    callState (sCall k) (searchSeeded (k := k) a c) z = searchAnswered a c z := by
  classical
  funext r
  by_cases hrng : ∃ i, r = sCall k i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply sCall_injective]
    by_cases hi : i = 0
    · subst hi; simp [searchAnswered]
    · rw [unaryConfig_of_ne hi]
      simp [searchAnswered, sCall_injective.eq_iff, hi]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp [searchSeeded, searchAnswered, hrng 0]

/-- **One evaluation of the predicate.** -/
theorem run_rfindBody {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c z : ℕ)
    (hz : z ∈ f (Nat.pair a c)) :
    ∃ N, (∀ m < N, (run (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindBody (k := k) Cf).length) ∧
      run (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ N =
        ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ := by
  rw [rfindBody]
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp (k := k) a c
  obtain ⟨N2, i2, e2⟩ := run_rfindSeedCall (k := k) a c
  obtain ⟨N3, i3, e3⟩ :=
    hf.call_exit sCall_injective (regs := searchSeeded (k := k) a c)
      (x := Nat.pair a c) (by simp [searchSeeded])
      (fun i hi => by simp [searchSeeded, sCall_injective.eq_iff, hi]) hz
  rw [callState_searchSeeded] at e3
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### The two turns

`rfindBody` is a *prefix* of `rfindLoop`, so peeling it needs only `run_append_of_lt` and
`halts_prefix_of_halts_append`; the absolute jump back in the suffix does not interfere with
either. -/

theorem getElem?_sBranch :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length]? =
      some (Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 3)) := by
  rw [rfindLoop, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem getElem?_sDrain :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length + 1]? =
      some (Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 2)) := by
  rw [rfindLoop, List.getElem?_append_right (by omega)]
  simp

theorem getElem?_sInc :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length + 2]? =
      some (Instr.inc (sC k) 0) := by
  rw [rfindLoop, List.getElem?_append_right (by omega)]
  simp

theorem run_body_in_loop {S : Fin (k + 20) → ℕ} {N : ℕ}
    (hin : ∀ m < N, (run (rfindBody (k := k) Cf) ⟨0, S⟩ m).pc <
      (rfindBody (k := k) Cf).length) (m : ℕ) (hm : m ≤ N) :
    run (rfindLoop (k := k) Cf) ⟨0, S⟩ m = run (rfindBody (k := k) Cf) ⟨0, S⟩ m := by
  rw [rfindLoop, run_append_of_lt (fun j hj => hin j (by omega))]

/-- **Zero turn.** The predicate answered zero, so the branch leaves the loop at the current
candidate. -/
theorem run_rfindTurn_zero {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c : ℕ)
    (hz : 0 ∈ f (Nat.pair a c)) :
    ∃ N, (∀ m < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
        ⟨(rfindLoop (k := k) Cf).length, searchState a c⟩ := by
  obtain ⟨N, hin, hex⟩ := run_rfindBody (k := k) hf a c 0 hz
  have hb : run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c 0⟩ := by
    rw [run_body_in_loop hin N (Nat.le_refl _), hex]
  refine ⟨N + 1, fun j hj => ?_, ?_⟩
  · rcases (show j ≤ N by omega).lt_or_eq with hlt | rfl
    · rw [run_body_in_loop hin j (by omega), length_rfindLoop]
      have := hin j hlt
      omega
    · rw [hb, length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length < (rfindBody (k := k) Cf).length + 3 by omega
  · rw [show N + 1 = N + 1 from rfl, run_add, hb, run_one,
      step_dec_zero (getElem?_sBranch (Cf := Cf)) (by simp [searchAnswered]), length_rfindLoop]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [searchAnswered, searchState]

/-- **Nonzero turn.** The predicate answered something else, so the loop discards it, steps the
candidate and returns to the head. The step count is positive, which is what the halting-time
induction needs. -/
theorem run_rfindTurn_ne {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c z : ℕ)
    (hzm : z ∈ f (Nat.pair a c)) (hz : z ≠ 0) :
    ∃ N, 0 < N ∧ (∀ m < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N = ⟨0, searchState a (c + 1)⟩ := by
  obtain ⟨N, hin, hex⟩ := run_rfindBody (k := k) hf a c z hzm
  have hval : searchAnswered (k := k) a c z (sCall k 0) = z := by simp [searchAnswered]
  have hb : run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ := by
    rw [run_body_in_loop hin N (Nat.le_refl _), hex]
  have hstep : step (rfindLoop (k := k) Cf)
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ =
      ⟨(rfindBody (k := k) Cf).length + 1,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1)⟩ := by
    rw [step_dec_pos (getElem?_sBranch (Cf := Cf)) (by rw [hval]; exact hz), hval]
  have hdrain : run (rfindLoop (k := k) Cf)
      ⟨(rfindBody (k := k) Cf).length + 1,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1)⟩ z =
      ⟨(rfindBody (k := k) Cf).length + 2,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) 0⟩ := by
    have h := run_drain (getElem?_sDrain (Cf := Cf))
      (Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1))
    rw [Function.update_self, Function.update_idem,
      show z - 1 + 1 = z from by omega] at h
    exact h
  refine ⟨N + (1 + (z + 1)), by omega, fun j hj => ?_, ?_⟩
  · rcases (show j ≤ N ∨ (N + 1 ≤ j ∧ j ≤ N + z) ∨ j = N + 1 + z by omega)
      with hle | ⟨h1, h2⟩ | rfl
    · rcases hle.lt_or_eq with hlt | rfl
      · rw [run_body_in_loop hin j (by omega), length_rfindLoop]
        have := hin j hlt
        omega
      · rw [hb, length_rfindLoop]
        exact show (rfindBody (k := k) Cf).length < (rfindBody (k := k) Cf).length + 3 by omega
    · rw [show j = N + 1 + (j - N - 1) by omega, run_add, run_add, run_one, hb, hstep,
        run_drain_partial (getElem?_sDrain (Cf := Cf)) _ (j - N - 1)
          (by rw [Function.update_self]; omega), length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length + 1 <
        (rfindBody (k := k) Cf).length + 3 by omega
    · rw [show N + 1 + z = N + 1 + z from rfl, run_add, run_add, run_one, hb, hstep, hdrain,
        length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length + 2 <
        (rfindBody (k := k) Cf).length + 3 by omega
  · rw [show N + (1 + (z + 1)) = N + 1 + z + 1 by omega, run_add, run_add, run_add,
      run_one, run_one, hb, hstep, hdrain, step_inc (getElem?_sInc (Cf := Cf))]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · by_cases hi : i = 0
      · subst hi; simp [searchAnswered, searchState]
      · simp [searchAnswered, searchState, sCall_injective.eq_iff, hi]

/-! ### Soundness

There is no counter to induct on, so the induction is on the halting time. The nonzero turn's
`0 < steps` and its in-range clause together give `N - steps < N`. -/

/-- A halting loop forces the predicate to converge at the current candidate. -/
theorem rfindLoop_call_dom {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c : ℕ)
    (hh : Halts (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩) : (f (Nat.pair a c)).Dom := by
  have hbody : Halts (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ := by
    rw [rfindLoop] at hh
    exact halts_prefix_of_halts_append hh
  rw [rfindBody] at hbody
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp (k := k) a c
  have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hbody
  rw [show (run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ N1).regs =
    searchPaired a c from by rw [e1]] at h1
  obtain ⟨N2, i2, e2⟩ := run_rfindSeedCall (k := k) a c
  have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
  rw [show (run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ N2).regs =
    searchSeeded a c from by rw [e2]] at h2
  exact (hf.call_halts_iff sCall_injective (regs := searchSeeded (k := k) a c)
    (x := Nat.pair a c) (by simp [searchSeeded])
    (fun i hi => by simp [searchSeeded, sCall_injective.eq_iff, hi])).mp h2

/-- **Soundness, with an explicit halting time.** A loop that halts at time `N` from candidate
`q + m` exhibits a stopping point `d ≥ q`, together with the failures in between. -/
theorem rfindLoop_sound_at {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    ∀ N q, Halted (rfindLoop (k := k) Cf)
        (run (rfindLoop (k := k) Cf) ⟨0, searchState a (q + m)⟩ N) →
      ∃ d, 0 ∈ f (Nat.pair a (d + m)) ∧ q ≤ d ∧
        ∀ j, q ≤ j → j < d → ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro q hN
    have hdom := rfindLoop_call_dom (k := k) hf a (q + m) ⟨N, hN⟩
    by_cases hz : (f (Nat.pair a (q + m))).get hdom = 0
    · exact ⟨q, hz ▸ Part.get_mem hdom, Nat.le_refl q,
        fun j h1 h2 => absurd h2 (Nat.not_lt.mpr h1)⟩
    · obtain ⟨steps, hpos, hin, hex⟩ :=
        run_rfindTurn_ne (k := k) hf a (q + m) _ (Part.get_mem hdom) hz
      have hle : steps ≤ N := by
        by_contra hlt
        exact absurd hN (Nat.not_le.mpr (hin N (Nat.not_le.mp hlt)))
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_add, hex] at hN
      have hnext : Halted (rfindLoop (k := k) Cf)
          (run (rfindLoop (k := k) Cf) ⟨0, searchState a (q + 1 + m)⟩ t) := by
        rw [show q + 1 + m = q + m + 1 from by omega]
        exact hN
      obtain ⟨d, hd0, hdq, hdj⟩ := ih t (by omega) (q + 1) hnext
      refine ⟨d, hd0, by omega, fun j h1 h2 => ?_⟩
      rcases (show j = q ∨ q + 1 ≤ j by omega) with rfl | h3
      · exact ⟨_, Part.get_mem hdom, hz⟩
      · exact hdj j h3 h2

/-! ### Completeness, and the semantic endpoint -/

/-- **Segment completeness.** Given `q` failures, the loop walks from candidate `m` to `q + m`. -/
theorem run_rfindFailures {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    ∀ q, (∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0) →
      ∃ steps, (∀ s < steps, (run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ s).pc <
          (rfindLoop (k := k) Cf).length) ∧
        run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ steps =
          ⟨0, searchState a (q + m)⟩ := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨0, fun s hs => absurd hs (Nat.not_lt_zero s), ?_⟩
    rw [run_zero, show (0 : ℕ) + m = m from Nat.zero_add m]
  | succ q ih =>
    intro hfail
    obtain ⟨s1, i1, e1⟩ := ih (fun j hj => hfail j (by omega))
    obtain ⟨z, hz, hz0⟩ := hfail q (by omega)
    obtain ⟨s2, _, i2, e2⟩ := run_rfindTurn_ne (k := k) hf a (q + m) z hz hz0
    rw [show q + m + 1 = q + 1 + m from by omega] at e2
    exact ⟨s1 + s2, run_segment_trans i1 e1 i2 e2⟩

/-- **The loop's exact exit.** -/
theorem run_rfindLoop {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m y : ℕ)
    (hy : y ∈ rfindSem f a m) :
    ∃ N, (∀ s < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ s).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ N =
        ⟨(rfindLoop (k := k) Cf).length, searchState a y⟩ := by
  obtain ⟨q, rfl, hq, hmin⟩ := mem_rfindSem.mp hy
  obtain ⟨s1, i1, e1⟩ := run_rfindFailures (k := k) hf a m q hmin
  obtain ⟨s2, i2, e2⟩ := run_rfindTurn_zero (k := k) hf a (q + m) hq
  exact ⟨s1 + s2, run_segment_trans i1 e1 i2 e2⟩

/-- **The semantic endpoint of the loop.** -/
theorem rfindLoop_halts_iff {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    Halts (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ ↔ (rfindSem f a m).Dom := by
  constructor
  · rintro ⟨N, hN⟩
    have hN' : Halted (rfindLoop (k := k) Cf)
        (run (rfindLoop (k := k) Cf) ⟨0, searchState a (0 + m)⟩ N) := by
      rw [show (0 : ℕ) + m = m from Nat.zero_add m]
      exact hN
    obtain ⟨d, hd0, _, hdj⟩ := rfindLoop_sound_at (k := k) hf a m N 0 hN'
    exact Part.dom_iff_mem.mpr ⟨d + m,
      mem_rfindSem.mpr ⟨d, rfl, hd0, fun j hj => hdj j (Nat.zero_le j) hj⟩⟩
  · intro hd
    obtain ⟨N, _, hex⟩ :=
      run_rfindLoop (k := k) hf a m ((rfindSem f a m).get hd) (Part.get_mem hd)
    exact ⟨N, by rw [hex]; exact Nat.le_refl _⟩

/-! ## The controller

One partial boundary: the packaged search loop. -/

/-- After the input has been copied to the unpairing block. -/
def rfindCtlA (x : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sUnpair k 0 then x else if r = 0 then x else 0

/-- After unpairing. -/
def rfindCtlB (x : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sUnpair k 1 then x.unpair.1 else if r = sUnpair k 2 then x.unpair.2
    else if r = 0 then x else 0

theorem run_rfindSplit (x : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ m).pc <
        (rfindSplit (k := k)).length) ∧
      run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ N =
        ⟨(rfindSplit (k := k)).length, rfindCtlB x⟩ := by
  rw [rfindSplit]
  obtain ⟨N1, i1, e1⟩ :=
    realises_copy (r := (0 : Fin (k + 20))) (s := sUnpair k 0) (t := sT k)
      (by simp) (by simp) (by simp) (unaryConfig (k + 19) x)
  have e1' : run (copy 0 (sUnpair k 0) (sT k)) ⟨0, unaryConfig (k + 19) x⟩ N1 =
      ⟨(copy 0 (sUnpair k 0) (sT k)).length, rfindCtlA x⟩ := by
    rw [e1]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [unaryConfig, rfindCtlA, sUnpair_injective.eq_iff]
  obtain ⟨N2, hu2, hu3⟩ := run_unpairLoop x
  obtain ⟨i2, e2⟩ :=
    run_renameRegs_of_exit sUnpair_injective hu2 hu3 (regs := rfindCtlA (k := k) x)
      (fun i => by
        rcases (show i = 0 ∨ i ≠ 0 by tauto) with rfl | hi
        · simp [rfindCtlA, unaryConfig]
        · simp [rfindCtlA, unaryConfig, sUnpair_injective.eq_iff, hi])
  have e2' : run (renameRegs (sUnpair k) unpairLoop) ⟨0, rfindCtlA x⟩ N2 =
      ⟨(renameRegs (sUnpair k) unpairLoop).length, rfindCtlB x⟩ := by
    rw [e2]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.2.1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.2.2 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact (sUnpair_ne_sPair j i) hj)]
      simp [rfindCtlA, rfindCtlB]
    · rw [sUnpair_injective.extend_apply]
      simp only [rfindCtlB]
      fin_cases i <;> simp [sUnpair_injective.eq_iff]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact (sUnpair_ne_sCall j i) hj)]
      simp [rfindCtlA, rfindCtlB]
  exact ⟨N1 + N2, join_exit i1 e1' i2 e2'⟩

theorem run_rfindSeed (x : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ m).pc <
        (rfindSeed (k := k)).length) ∧
      run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ N =
        ⟨(rfindSeed (k := k)).length, searchState x.unpair.1 x.unpair.2⟩ := by
  rw [rfindSeed]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (r := sUnpair k 1) (s := sA k) (by simp)).seq
      ((realises_move (r := sUnpair k 2) (s := sC k) (by simp)).seq
        (realises_clear (0 : Fin (k + 20))))) (rfindCtlB (k := k) x)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · fin_cases i <;> simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]

theorem run_rfindFinish (a y : ℕ) :
    ∃ N, (∀ m < N, (run (rfindFinish (k := k)) ⟨0, searchState a y⟩ m).pc <
        (rfindFinish (k := k)).length) ∧
      run (rfindFinish (k := k)) ⟨0, searchState a y⟩ N =
        ⟨(rfindFinish (k := k)).length, unaryConfig (k + 19) y⟩ := by
  rw [rfindFinish]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (sA k)).seq
      (realises_move (r := sC k) (s := (0 : Fin (k + 20))) (by simp)))
      (searchState (k := k) a y)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchState, unaryConfig]

/-- **`Code.rfind'`'s closure theorem.** -/
theorem CleanPartComputesUnary.rfind' {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) :
    CleanPartComputesUnary (rfindController (k := k) Cf)
      fun x => rfindSem f x.unpair.1 x.unpair.2 := by
  intro x
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · obtain ⟨N1, i1, e1⟩ := run_rfindSplit (k := k) x
    obtain ⟨N2, i2, e2⟩ := run_rfindSeed (k := k) x
    obtain ⟨N3, i3, e3⟩ := run_rfindLoop (k := k) hf x.unpair.1 x.unpair.2 y hy
    obtain ⟨N4, i4, e4⟩ := run_rfindFinish (k := k) x.unpair.1 y
    obtain ⟨j34, f34⟩ := join_exit i3 e3 i4 e4
    obtain ⟨j234, f234⟩ := join_exit i2 e2 j34 f34
    exact ⟨N1 + (N2 + (N3 + N4)), join_exit i1 e1 j234 f234⟩
  · obtain ⟨N1, i1, e1⟩ := run_rfindSplit (k := k) x
    have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hh
    rw [show (run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ N1).regs =
      rfindCtlB x from by rw [e1]] at h1
    obtain ⟨N2, i2, e2⟩ := run_rfindSeed (k := k) x
    have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
    rw [show (run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ N2).regs =
      searchState x.unpair.1 x.unpair.2 from by rw [e2]] at h2
    exact (rfindLoop_halts_iff (k := k) hf x.unpair.1 x.unpair.2).mp
      (halts_prefix_of_halts_append h2)

/-- **`Code.rfind'`.** `congr` through the source-semantics bridge, and nothing else. -/
theorem CleanPartComputesUnary.codeRfind {cf : Code} (hf : CleanPartComputesUnary Cf cf.eval) :
    CleanPartComputesUnary (rfindController (k := k) Cf) (Code.rfind' cf).eval :=
  (CleanPartComputesUnary.rfind' (k := k) hf).congr fun x => (eval_rfind_unpair cf x).symm

end RegisterMachine

end Hilbert10
