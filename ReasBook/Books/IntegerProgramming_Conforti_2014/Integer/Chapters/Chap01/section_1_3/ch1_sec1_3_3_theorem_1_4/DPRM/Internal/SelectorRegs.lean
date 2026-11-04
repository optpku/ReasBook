/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.SelectorMask

/-!
# The selector encoding for many registers: the blockwise layer

#49, phase 4. `Spike/SelectorProgram` and its two successors proved `Aggregation 1`. The
remaining scaling question is the register count, and this file is its blockwise layer: the same
selector vocabulary for an arbitrary `P : Program (k + 1)`.

## What becomes register-indexed

The selectors do not. There is still one ordinary and one zero selector per instruction, and
they are still one-hot across the whole program. What becomes indexed by `Fin (k + 1)` is the
*coefficients* and the *residuals*:

* `gainAt r` and `lossAt r` pick out the instructions that increment or decrement register `r`,
  so each register gets its own subtraction-free update equation;
* the positive residual becomes one per register;
* the zero branch is tested at the decremented register, so its selector sub-sum is
  `∑ p, lossAt r (P.get p) * Z p` — the decrements *on `r`* that took their zero branch.

## Why the sub-sums do not carry

Every one of those sums is bounded by `1`, even when many instructions mention the same
register, because each is a sub-sum of the global one-hot family: `lossAt r I ≤ 1` and
`A p ≤ A p + Z p`. `subSum_le_one` is that fact, proved once and used by every register
equation. It is what keeps the register equations carry-free at the layer above, and it is the
only place the register count could have introduced a new bound.

## Scope

`blockStepK_iff` only. Globalising the lanes is `SelectorRegsGlobal`, and packaging them into
`Aggregation (k + 1)` is `SelectorRegsDioph`. The one-register development is left untouched, as
regression evidence for the route.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ### Per-instruction coefficients, register-indexed where they must be -/

namespace Instr

/-- The target of the ordinary branch. -/
def jumpPos : Instr k → ℕ
  | .inc _ j => j
  | .dec _ jpos _ => jpos

/-- The target of the zero branch; an increment has none. -/
def jumpZero : Instr k → ℕ
  | .inc _ _ => 0
  | .dec _ _ jzero => jzero

/-- Whether a zero branch exists at all. -/
def branches : Instr k → ℕ
  | .inc _ _ => 0
  | .dec _ _ _ => 1

/-- The register the instruction acts on, and whose value its branch tests. -/
def testReg : Instr k → Fin k
  | .inc r _ => r
  | .dec r _ _ => r

/-- What the ordinary branch adds to register `r`. -/
def gainAt [DecidableEq (Fin k)] (r : Fin k) : Instr k → ℕ
  | .inc r' _ => if r' = r then 1 else 0
  | .dec _ _ _ => 0

/-- What the ordinary branch removes from register `r`; also which decrements test `r`. -/
def lossAt [DecidableEq (Fin k)] (r : Fin k) : Instr k → ℕ
  | .inc _ _ => 0
  | .dec r' _ _ => if r' = r then 1 else 0

theorem gainAt_le_one (r : Fin k) (I : Instr k) : gainAt r I ≤ 1 := by
  unfold gainAt; split <;> [split; skip] <;> omega

theorem lossAt_le_one (r : Fin k) (I : Instr k) : lossAt r I ≤ 1 := by
  unfold lossAt; split <;> [skip; split] <;> omega

end Instr

/-- Two configurations agreeing on the program counter and every register are equal. -/
theorem config_ext {c₁ c₂ : Config k} (hpc : c₁.pc = c₂.pc) (hr : ∀ r, c₁.regs r = c₂.regs r) :
    c₁ = c₂ := by
  obtain ⟨p₁, r₁⟩ := c₁
  obtain ⟨p₂, r₂⟩ := c₂
  simp only [Config.mk.injEq]
  exact ⟨hpc, funext hr⟩

/-- **The sub-sums stay one-hot.** A coefficient family bounded by `1`, summed against either
selector of a one-hot pair, is itself at most `1`. Every register equation below is an instance,
which is why no register equation can carry. -/
theorem subSum_le_one {L : ℕ} {A Z g : Fin L → ℕ} (hg : ∀ p, g p ≤ 1)
    (hone : (∑ p : Fin L, (A p + Z p)) = 1) :
    (∑ p : Fin L, g p * A p) ≤ 1 ∧ (∑ p : Fin L, g p * Z p) ≤ 1 := by
  constructor
  · calc (∑ p : Fin L, g p * A p) ≤ ∑ p : Fin L, (A p + Z p) :=
          Finset.sum_le_sum fun p _ => by
            calc g p * A p ≤ 1 * A p := Nat.mul_le_mul_right _ (hg p)
              _ = A p := one_mul _
              _ ≤ A p + Z p := Nat.le_add_right _ _
      _ = 1 := hone
  · calc (∑ p : Fin L, g p * Z p) ≤ ∑ p : Fin L, (A p + Z p) :=
          Finset.sum_le_sum fun p _ => by
            calc g p * Z p ≤ 1 * Z p := Nat.mul_le_mul_right _ (hg p)
              _ = Z p := one_mul _
              _ ≤ A p + Z p := Nat.le_add_left _ _
      _ = 1 := hone

/-! ### The blockwise conditions -/

/-- **The selector conditions at one step, for an arbitrary program on `k + 1` registers.**

Read in order: the selectors are one-hot; the program counter names the selected instruction and
jumps to its target; every register has its own subtraction-free update equation; only a
decrement may take a zero branch, and a zero branch on `r` forces `r` to vanish; every register
has a positive residual; and each selected target fits. -/
def BlockStepK (P : Program (k + 1)) (w pcHere pcNext : ℕ)
    (regsHere regsNext res : Fin (k + 1) → ℕ) (A Z : Fin P.length → ℕ) : Prop :=
  (∑ p : Fin P.length, (A p + Z p)) = 1 ∧
  pcHere = ∑ p : Fin P.length, (p : ℕ) * (A p + Z p) ∧
  pcNext = ∑ p : Fin P.length, ((P.get p).jumpPos * A p + (P.get p).jumpZero * Z p) ∧
  (∀ r, regsNext r + ∑ p : Fin P.length, (P.get p).lossAt r * A p
    = regsHere r + ∑ p : Fin P.length, (P.get p).gainAt r * A p) ∧
  (∀ p, Z p ≤ (P.get p).branches) ∧
  (∀ r, (∑ p : Fin P.length, (P.get p).lossAt r * Z p) = 1 → regsHere r = 0) ∧
  (∀ r, regsHere r = res r + ∑ p : Fin P.length, (P.get p).lossAt r * A p) ∧
  (∀ r, res r < 2 ^ w) ∧
  (∀ p, A p = 1 → (P.get p).jumpPos < 2 ^ w) ∧
  (∀ p, Z p = 1 → (P.get p).jumpZero < 2 ^ w) ∧
  pcNext < 2 ^ w ∧ (∀ r, regsNext r < 2 ^ w)

/-- The ordinary selector of a configuration: the instruction at the program counter is selected
unless it is a decrement whose tested register has run out. -/
def ordFlagK (P : Program (k + 1)) (c : Config (k + 1)) (p : Fin P.length) : ℕ :=
  if (P.get p).branches = 1 ∧ c.regs ((P.get p).testReg) = 0 then 0 else 1

theorem ordFlagK_le_one (P : Program (k + 1)) (c : Config (k + 1)) (p : Fin P.length) :
    ordFlagK P c p ≤ 1 := by
  unfold ordFlagK; split <;> omega

/-- **The blockwise equivalence, for an arbitrary program on `k + 1` registers.** -/
theorem blockStepK_iff (P : Program (k + 1)) (w n : ℕ) (cs : ℕ → Config (k + 1))
    (hfit : ∀ i, FitsConfig w (cs i)) :
    (∀ i < n, EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1)))) ↔
      ∃ A Z : ℕ → Fin P.length → ℕ, ∃ res : ℕ → Fin (k + 1) → ℕ, ∀ i < n,
        BlockStepK P w (cs i).pc (cs (i + 1)).pc (cs i).regs (cs (i + 1)).regs (res i)
          (A i) (Z i) := by
  constructor
  · intro h
    refine ⟨fun i p => if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0,
      fun i p => if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0,
      fun i r => (cs i).regs r - ∑ p : Fin P.length, (P.get p).lossAt r *
        (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0), ?_⟩
    intro i hi
    dsimp only
    have hstep := h i hi
    have hpc : (cs i).pc < P.length := by
      have := configField_zero_lt_of_encodedStep hstep
      rwa [field_configCode_zero (hfit i)] at this
    obtain ⟨hfits, hz⟩ := (encodedStep_iff (hfit i) hpc).mp hstep
    have hnext : cs (i + 1) = step P (cs i) :=
      configCode_injective (hfit (i + 1)) hfits hz
    set q : Fin P.length := ⟨(cs i).pc, hpc⟩ with hq
    have hget : step P (cs i) = (P.get q).exec (cs i).regs :=
      step_of_getElem? (by simp [hq])
    -- every sum collapses to the selected instruction
    have hsumA : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = f q * ordFlagK P (cs i) q := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * ordFlagK P (cs i) p else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show (∑ p : Fin P.length,
          f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * ordFlagK P (cs i) p else 0) from by rw [e],
        sum_indicator hpc]
    have hsumZ : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = f q * (1 - ordFlagK P (cs i) q) := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * (1 - ordFlagK P (cs i) p) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show (∑ p : Fin P.length,
          f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * (1 - ordFlagK P (cs i) p) else 0) from by rw [e],
        sum_indicator hpc]
    have hsum1 : (∑ p : Fin P.length,
        ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))) = 1 := by
      have e : (fun p : Fin P.length =>
          (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then 1 else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle := ordFlagK_le_one P (cs i) p
          rw [if_pos hp, if_pos hp, if_pos hp]
          omega
        · rw [if_neg hp, if_neg hp, if_neg hp]
      rw [show (∑ p : Fin P.length,
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then 1 else 0) from by rw [e]]
      simpa using sum_indicator hpc (fun _ => 1)
    have hsumPc : (∑ p : Fin P.length, (p : ℕ) *
        ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))) = (cs i).pc := by
      have e : (fun p : Fin P.length => (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then (p : ℕ) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle := ordFlagK_le_one P (cs i) p
          rw [if_pos hp, if_pos hp, if_pos hp,
            show ordFlagK P (cs i) p + (1 - ordFlagK P (cs i) p) = 1 from by omega, Nat.mul_one]
        · rw [if_neg hp, if_neg hp, if_neg hp]
          simp
      rw [show (∑ p : Fin P.length, (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then (p : ℕ) else 0) from by rw [e],
        sum_indicator hpc (fun p => (p : ℕ))]
    have hbr : ∀ r, (cs i).regs r < 2 ^ w := (hfit i).2
    have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
    have hb1 : ∀ r, (cs (i + 1)).regs r < 2 ^ w := (hfit (i + 1)).2
    rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
    · -- an increment
      have hord : ordFlagK P (cs i) q = 1 := by
        unfold ordFlagK
        rw [hinstr]
        simp [Instr.branches]
      have hexec : cs (i + 1) = ⟨j, Function.update (cs i).regs r ((cs i).regs r + 1)⟩ := by
        rw [hnext, hget, hinstr]
        rfl
      have hpcn : (cs (i + 1)).pc = j := by rw [hexec]
      have hrn : ∀ s, (cs (i + 1)).regs s
          = (cs i).regs s + (if r = s then 1 else 0) := by
        intro s
        rw [hexec]
        by_cases hs : s = r
        · subst hs; simp
        · simp [Function.update_of_ne hs, Ne.symm hs]
      refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
        (try dsimp only)
      · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
          hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
        simp [Instr.jumpPos, hpcn]
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
          hinstr, hrn s]
        simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one]
        split <;> omega
      · intro p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [if_pos hp, hpq, hord]
          simp
        · simp [hp]
      · intro s hzs
        exfalso
        rw [hsumZ (fun p => (P.get p).lossAt s), hord] at hzs
        simp at hzs
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
        simp [Instr.lossAt]
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
        simp only [Instr.lossAt, Nat.mul_one, Nat.sub_zero]
        exact hbr s
      · intro p hA
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [hpq, hinstr]
          simpa [Instr.jumpPos, hpcn] using hb0
        · rw [if_neg hp] at hA; omega
      · intro p hZ
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
        · rw [if_neg hp] at hZ; omega
      · exact hb1
    · -- a decrement
      rcases eq_or_ne ((cs i).regs r) 0 with hz0 | hz0
      · -- the zero branch
        have hord : ordFlagK P (cs i) q = 0 := by
          unfold ordFlagK
          rw [hinstr]
          simp [Instr.branches, Instr.testReg, hz0]
        have hexec : cs (i + 1) = ⟨jzero, (cs i).regs⟩ := by
          rw [hnext, hget, hinstr]
          simp only [Instr.exec]
          rw [if_pos hz0]
        have hpcn : (cs (i + 1)).pc = jzero := by rw [hexec]
        have hrn : ∀ s, (cs (i + 1)).regs s = (cs i).regs s := by intro s; rw [hexec]
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
          (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
          simp [Instr.jumpZero, hpcn]
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
            hrn s]
          simp
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.branches]
          · simp [hp]
        · intro s hzs
          rw [hsumZ (fun p => (P.get p).lossAt s), hord, hinstr] at hzs
          simp only [Instr.lossAt, Nat.sub_zero, Nat.mul_one] at hzs
          by_cases hs : r = s
          · subst hs; exact hz0
          · rw [if_neg hs] at hzs; omega
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord]
          simp
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord]
          simpa using hbr s
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hA; omega
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.jumpZero, hpcn] using hb0
          · rw [if_neg hp] at hZ; omega
        · exact hb1
      · -- the positive branch
        have hord : ordFlagK P (cs i) q = 1 := by
          unfold ordFlagK
          rw [hinstr]
          simp [Instr.branches, Instr.testReg, hz0]
        have hexec : cs (i + 1)
            = ⟨jpos, Function.update (cs i).regs r ((cs i).regs r - 1)⟩ := by
          rw [hnext, hget, hinstr]
          simp only [Instr.exec]
          rw [if_neg hz0]
        have hpcn : (cs (i + 1)).pc = jpos := by rw [hexec]
        have hpos : 0 < (cs i).regs r := Nat.pos_of_ne_zero hz0
        have hrn : ∀ s, (cs (i + 1)).regs s + (if r = s then 1 else 0) = (cs i).regs s := by
          intro s
          rw [hexec]
          by_cases hs : s = r
          · subst hs; simp; omega
          · simp [Function.update_of_ne hs, Ne.symm hs]
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
          (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
          simp [Instr.jumpPos, hpcn]
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
            hinstr]
          simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero]
          exact hrn s
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.branches]
          · simp [hp]
        · intro s hzs
          exfalso
          rw [hsumZ (fun p => (P.get p).lossAt s), hord] at hzs
          simp at hzs
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
          simp only [Instr.lossAt, Nat.mul_one]
          have := hrn s
          by_cases hs : r = s
          · subst hs; rw [if_pos rfl] at this ⊢; omega
          · rw [if_neg hs] at this ⊢; omega
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
          simp only [Instr.lossAt, Nat.mul_one]
          have := hbr s
          omega
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.jumpPos, hpcn] using hb0
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
          · rw [if_neg hp] at hZ; omega
        · exact hb1
  · rintro ⟨A, Z, res, h⟩ i hi
    obtain ⟨hone, hpcH, hpcN, hupd, hzb, hzero, hres, hresb, htA, htZ, hpb, hrb⟩ := h i hi
    obtain ⟨q, hq1, hq0⟩ := exists_unique_of_sum_eq_one hone
    have hcollapse : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (A i p + Z i p)) = f q * (A i q + Z i q) :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p + Z i p = 0 from by omega, Nat.mul_zero]
    have hpcq : (cs i).pc = (q : ℕ) := by
      rw [hpcH, show (∑ p : Fin P.length, (p : ℕ) * (A i p + Z i p))
        = (q : ℕ) * (A i q + Z i q) from hcollapse _, hq1, mul_one]
    have hpcLt : (cs i).pc < P.length := by rw [hpcq]; exact q.isLt
    have hAZ : (A i q = 1 ∧ Z i q = 0) ∨ (A i q = 0 ∧ Z i q = 1) := by omega
    have hsumA : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * A i p) = f q * A i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p = 0 from by omega, Nat.mul_zero]
    have hsumZ : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * Z i p) = f q * Z i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show Z i p = 0 from by omega, Nat.mul_zero]
    have hget : step P (cs i) = (P.get ⟨(cs i).pc, hpcLt⟩).exec (cs i).regs :=
      step_of_getElem? (by simp)
    have hqe : (⟨(cs i).pc, hpcLt⟩ : Fin P.length) = q := Fin.ext hpcq
    rw [hqe] at hget
    have hnext : cs (i + 1) = step P (cs i) := by
      rw [hget]
      rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
      · -- an increment: the zero selector is forced off
        have hZq : Z i q = 0 := by
          have := hzb q
          rw [hinstr] at this
          simpa [Instr.branches] using this
        have hAq : A i q = 1 := by omega
        have hpcn : (cs (i + 1)).pc = j := by
          rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
          simp [Instr.jumpPos]
        have hrn : ∀ s, (cs (i + 1)).regs s
            = (cs i).regs s + (if r = s then 1 else 0) := by
          intro s
          have hu := hupd s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hAq,
            hinstr] at hu
          simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero] at hu
          exact hu
        simp only [Instr.exec]
        refine config_ext (by simpa using hpcn) fun s => ?_
        change (cs (i + 1)).regs s = Function.update (cs i).regs r ((cs i).regs r + 1) s
        rcases eq_or_ne s r with rfl | hs
        · rw [Function.update_self]
          have h1 := hrn s
          rw [if_pos rfl] at h1
          omega
        · rw [Function.update_of_ne hs]
          have h1 := hrn s
          rw [if_neg (Ne.symm hs)] at h1
          omega
      · rcases hAZ with ⟨hAq, hZq⟩ | ⟨hAq, hZq⟩
        · -- the positive branch
          have hloss : (∑ p : Fin P.length, (P.get p).lossAt r * A i p) = 1 := by
            rw [hsumA (fun p => (P.get p).lossAt r), hAq, hinstr]
            simp [Instr.lossAt]
          have hpos : 0 < (cs i).regs r := by have := hres r; omega
          have hpcn : (cs (i + 1)).pc = jpos := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
              hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
            simp [Instr.jumpPos]
          have hrn : ∀ s, (cs (i + 1)).regs s + (if r = s then 1 else 0) = (cs i).regs s := by
            intro s
            have hu := hupd s
            rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hAq,
              hinstr] at hu
            simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero] at hu
            exact hu
          simp only [Instr.exec]
          rw [if_neg (by omega : ¬ (cs i).regs r = 0)]
          refine config_ext (by simpa using hpcn) fun s => ?_
          change (cs (i + 1)).regs s = Function.update (cs i).regs r ((cs i).regs r - 1) s
          rcases eq_or_ne s r with rfl | hs
          · rw [Function.update_self]
            have h1 := hrn s
            rw [if_pos rfl] at h1
            omega
          · rw [Function.update_of_ne hs]
            have h1 := hrn s
            rw [if_neg (Ne.symm hs)] at h1
            omega
        · -- the zero branch
          have hzsum : (∑ p : Fin P.length, (P.get p).lossAt r * Z i p) = 1 := by
            rw [hsumZ (fun p => (P.get p).lossAt r), hZq, hinstr]
            simp [Instr.lossAt]
          have hr0 : (cs i).regs r = 0 := hzero r hzsum
          have hpcn : (cs (i + 1)).pc = jzero := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
              hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
            simp [Instr.jumpZero]
          have hrn : ∀ s, (cs (i + 1)).regs s = (cs i).regs s := by
            intro s
            have hu := hupd s
            rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s),
              hAq] at hu
            simp only [Nat.mul_zero, Nat.add_zero] at hu
            exact hu
          simp only [Instr.exec]
          rw [if_pos hr0]
          exact config_ext (by simpa using hpcn) fun s => by simpa using hrn s
    have hfits : FitsConfig w (step P (cs i)) := by rw [← hnext]; exact hfit (i + 1)
    have := encodedStep_configCode (hfit i) hfits hpcLt
    rwa [← hnext] at this

end RegisterMachine

end Hilbert10
