/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RegisterMachinePair
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CleanScratch
public import Mathlib.Computability.PartrecCode

/-!
# Compiling `Nat.Partrec.Code.pair`

Issue #51, step 6. The closure theorem for `pair`: given clean machines for two subcodes, build
one for `fun n => Nat.pair <$> cf n <*> cg n`. Assembling this over `Code.rec` is #44.

This is a controller and calling-convention proof rather than an arithmetic one. The arithmetic
was step 5.

## The source semantics, once

Mathlib evaluates `pair cf cg` applicatively. `mem_eval_pair` below turns that into an explicit
existential, so no `Seq.seq` or `Part.bind` reasoning reaches the machine proof, and the
`cf`-before-`cg` order is fixed in one place.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

/-- The applicative source semantics of `Code.pair`, as an existential. `cf`'s value is `a`,
`cg`'s is `b`, and the result is `Nat.pair a b` in that order. -/
theorem mem_eval_pair {f g : ℕ →. ℕ} {n y : ℕ} :
    y ∈ (Nat.pair <$> f n <*> g n) ↔ ∃ a ∈ f n, ∃ b ∈ g n, y = Nat.pair a b := by
  simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

/-- The evaluation of `Code.pair` really is that applicative expression. -/
theorem mem_eval_code_pair {cf cg : Nat.Partrec.Code} {n y : ℕ} :
    y ∈ (Nat.Partrec.Code.pair cf cg).eval n ↔
      ∃ a ∈ cf.eval n, ∃ b ∈ cg.eval n, y = Nat.pair a b :=
  mem_eval_pair


/-! ## The controller's register layout

One explicit layout, over `Fin (k + k' + 13)`:

| register | role |
|---|---|
| `0` | the original input, preserved across both calls, then the output |
| `1`, `2` | the two subresults, and `pairMachine`'s targets |
| `3` | `pairMachine`'s answer |
| `4`–`9` | `pairMachine`'s candidate, accumulator and scratch |
| `10` | the temporary `copy` borrows |
| `11 …` | `cf`'s block, then `cg`'s block |

The facts below are arithmetic about *this* layout, nothing more: three embeddings are
injective, their images are pairwise disjoint, and the fixed registers `0` and `10` lie outside
all of them. They are proved once so that `Fin` index juggling stays out of the semantic proof.

This is not an allocator. The embeddings are three explicit offsets, written down here and
supplied to `CleanPartComputesUnary.call` by hand. -/

variable (k k' : ℕ)

/-- `cf`'s block, starting at register `11`. -/
def embedF (i : Fin (k + 1)) : Fin (k + k' + 13) := ⟨11 + i.val, by omega⟩

/-- `cg`'s block, immediately after `cf`'s. -/
def embedG (j : Fin (k' + 1)) : Fin (k + k' + 13) := ⟨12 + k + j.val, by omega⟩

/-- `pairMachine`'s nine registers, onto `1`–`9`. -/
def embedP (i : Fin 9) : Fin (k + k' + 13) := ⟨1 + i.val, by omega⟩

variable {k k'}

@[simp] theorem embedF_val (i : Fin (k + 1)) : (embedF k k' i).val = 11 + i.val := rfl
@[simp] theorem embedG_val (j : Fin (k' + 1)) : (embedG k k' j).val = 12 + k + j.val := rfl
@[simp] theorem embedP_val (i : Fin 9) : (embedP k k' i).val = 1 + i.val := rfl

/-- The temporary that `copy` borrows: the one fixed controller register outside `0`–`9`. -/
def ten : Fin (k + k' + 13) := ⟨10, by omega⟩

theorem embedF_injective : Function.Injective (embedF k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedG_injective : Function.Injective (embedG k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedP_injective : Function.Injective (embedP k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-! ### Register `0` and the borrowed temporary lie outside every block -/

theorem zero_ne_embedF (i : Fin (k + 1)) : (0 : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem zero_ne_embedG (j : Fin (k' + 1)) : (0 : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem ten_ne_embedF (i : Fin (k + 1)) : (ten : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp [ten] at this; omega

theorem ten_ne_embedG (j : Fin (k' + 1)) :
    (ten : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp [ten] at this; omega

/-! ### The three blocks are pairwise disjoint -/

theorem embedF_ne_embedG (i : Fin (k + 1)) (j : Fin (k' + 1)) :
    embedF k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedF (i : Fin 9) (j : Fin (k + 1)) : embedP k k' i ≠ embedF k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedG (i : Fin 9) (j : Fin (k' + 1)) : embedP k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- `pairMachine`'s block is exactly registers `1`–`9`, so the controller's fixed registers `0`
and `10` are outside it too. -/
theorem embedP_ne_zero (i : Fin 9) : embedP k k' i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

theorem embedP_ne_ten (i : Fin 9) : embedP k k' i ≠ (ten : Fin (k + k' + 13)) := by
  intro h
  have := congrArg Fin.val h
  simp [ten] at this
  omega

/-! ### The layout is exhaustive

The lemmas above say the blocks are separated. This one says they cover: registers `0`, `1`–`9`,
`10`, `cf`'s block and `cg`'s block account for every register, with nothing left over.

It is the eliminator for the final `funext` — showing the controller returns a clean unary
configuration means saying something about *every* register, and without this the proof would
rediscover the offset arithmetic one register at a time. -/
theorem layout_cases (r : Fin (k + k' + 13)) :
    r = 0 ∨ (∃ i, r = embedP k k' i) ∨ r = ten ∨
      (∃ i, r = embedF k k' i) ∨ ∃ j, r = embedG k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ (1 ≤ r.val ∧ r.val ≤ 9) ∨ r.val = 10 ∨
      (11 ≤ r.val ∧ r.val ≤ 11 + k) ∨ 12 + k ≤ r.val by omega) with h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl ⟨⟨r.val - 1, by omega⟩, Fin.ext (by simp [embedP]; omega)⟩)
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [ten] using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 11, by omega⟩, Fin.ext (by simp [embedF]; omega)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 12 - k, by omega⟩, Fin.ext (by simp [embedG]; omega)⟩)))

/-! ## The controller

Eight named blocks, grouped into five units so that adjacent total blocks splice once instead of
four times. The two partial units are the calls; everything else is a `Realises` macro. -/

variable (P : Program (k + 1)) (Q : Program (k' + 1))

/-- Unit 1: put the input where `cf` will read it. -/
def seedF : Program (k + k' + 13) := copy 0 (embedF k k' 0) ten

/-- Unit 3: save `cf`'s answer into register `1`, then seed `cg` from the untouched input.

Registers `1`, `2`, `3` are written as `embedP 0`, `embedP 1`, `embedP 2` throughout. They *are*
`pairMachine`'s two targets and its answer, so naming them that way records the connection and
keeps `Fin` numerals — whose `OfNat` goes through `%` — out of every proof. -/
def saveFSeedG : Program (k + k' + 13) :=
  seq (move (embedF k k' 0) (embedP k k' 0)) (copy 0 (embedG k k' 0) ten)

/-- Unit 5: save `cg`'s answer into register `2`, pair the two, and return the answer in `0`. -/
def saveGPair : Program (k + k' + 13) :=
  seq (move (embedG k k' 0) (embedP k k' 1)) (renameRegs (embedP k k') pairMachine)

/-- Unit 5b: discard the two operands and return the answer in register `0`. -/
def finishPair : Program (k + k' + 13) :=
  seq (clear (embedP k k' 0))
    (seq (clear (embedP k k' 1)) (seq (clear 0) (move (embedP k k' 2) 0)))

/-- Unit 5. -/
def saveGFinish : Program (k + k' + 13) :=
  seq (saveGPair (k := k) (k' := k')) (finishPair (k := k) (k' := k'))

/-- The whole controller. -/
def pairController : Program (k + k' + 13) :=
  seq (seedF (k := k) (k' := k'))
    (seq (renameRegs (embedF k k') P)
      (seq (saveFSeedG (k := k) (k' := k'))
        (seq (renameRegs (embedG k k') Q) (saveGFinish (k := k) (k' := k')))))

/-! ### The fixed registers are distinct from the blocks -/

theorem zero_ne_ten : (0 : Fin (k + k' + 13)) ≠ ten := by
  intro h; have := congrArg Fin.val h; simp [ten] at this

/-! ### Interface states

The register file expected between units, written down before the transition lemmas so that each
splice has a small stated interface and no proof accumulates an unfolded register function. -/

/-- After unit 1: the input, and a copy of it where `cf` will read it. -/
def state1 (n : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedF k k' 0 then n else 0

/-- After calling `cf`: its answer sits in its own input register, the input is untouched. -/
def state2 (n a : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedF k k' 0 then a else 0

/-- After unit 3: `cf`'s answer saved, `cg` seeded from the still-untouched input. -/
def state3 (n a : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedG k k' 0 then n else 0

/-- After calling `cg`. -/
def state4 (n a b : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedG k k' 0 then b else 0

/-! ### The three total units -/

theorem run_seedF (n : ℕ) :
    ∃ N, (∀ m < N, (run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ m).pc <
        (seedF (k := k) (k' := k')).length) ∧
      run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ N =
        ⟨(seedF (k := k) (k' := k')).length, state1 n⟩ := by
  rw [seedF]
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := (0 : Fin (k + k' + 13))) (s := embedF k k' 0) (t := ten)
      (zero_ne_embedF 0) zero_ne_ten (Ne.symm (ten_ne_embedF 0)) (unaryConfig (k + k' + 12) n)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  simp only [state1, unaryConfig, Function.update_apply]
  by_cases h1 : r = embedF k k' 0
  · subst h1; simp [(zero_ne_embedF 0).symm]
  · by_cases h2 : r = ten
    · subst h2; simp [h1, zero_ne_ten.symm]
    · simp [h1, h2]

/-- The disequalities among the controller's fixed registers and the two block entry points.
Collected once; every state transition below simplifies with the whole set. -/
theorem entry_ne (k k' : ℕ) :
    embedF k k' 0 ≠ 0 ∧ embedG k k' 0 ≠ 0 ∧ embedP k k' 0 ≠ 0 ∧ embedP k k' 1 ≠ 0 ∧
      embedP k k' 2 ≠ 0 ∧ (ten : Fin (k + k' + 13)) ≠ 0 ∧
      embedF k k' 0 ≠ embedG k k' 0 ∧ embedF k k' 0 ≠ embedP k k' 0 ∧
      embedF k k' 0 ≠ embedP k k' 1 ∧ embedF k k' 0 ≠ ten ∧
      embedG k k' 0 ≠ embedP k k' 0 ∧ embedG k k' 0 ≠ embedP k k' 1 ∧
      embedG k k' 0 ≠ ten ∧ embedP k k' 0 ≠ ten ∧ embedP k k' 1 ≠ ten ∧
      embedP k k' 0 ≠ embedP k k' 1 :=
  ⟨(zero_ne_embedF 0).symm, (zero_ne_embedG 0).symm, embedP_ne_zero 0, embedP_ne_zero 1,
    embedP_ne_zero 2, zero_ne_ten.symm, embedF_ne_embedG 0 0, (embedP_ne_embedF 0 0).symm,
    (embedP_ne_embedF 1 0).symm, (ten_ne_embedF 0).symm, (embedP_ne_embedG 0 0).symm,
    (embedP_ne_embedG 1 0).symm, (ten_ne_embedG 0).symm, embedP_ne_ten 0, embedP_ne_ten 1,
    fun h => absurd (embedP_injective h) (by decide)⟩

theorem run_saveFSeedG (n a : ℕ) :
    ∃ N, (∀ m < N, (run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n a⟩ m).pc <
        (saveFSeedG (k := k) (k' := k')).length) ∧
      run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n a⟩ N =
        ⟨(saveFSeedG (k := k) (k' := k')).length, state3 n a⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have fg' := fg.symm; have fp0' := fp0.symm
  have fp1' := fp1.symm; have ft' := ft.symm; have gp0' := gp0.symm; have gp1' := gp1.symm
  have gt' := gt.symm; have p0t' := p0t.symm; have p1t' := p1t.symm; have p01' := p01.symm
  rw [saveFSeedG]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (Ne.symm (embedP_ne_embedF 0 0))).seq
      (realises_copy (r := (0 : Fin (k + k' + 13))) (s := embedG k k' 0) (t := ten)
        (zero_ne_embedG 0) zero_ne_ten (Ne.symm (ten_ne_embedG 0)))) (state2 n a)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  simp only [state2, state3]
  by_cases h1 : r = embedG k k' 0
  · subst h1
    simp_all
  · by_cases h2 : r = ten
    · subst h2
      simp_all
    · by_cases h3 : r = embedF k k' 0
      · subst h3
        simp_all
      · by_cases h4 : r = embedP k k' 0
        · subst h4
          simp_all
        · simp_all


/-! ### The two calls, as state transitions

`callState` is never expanded; only its two accessors are used, and only at the handful of
registers the controller cares about. -/

theorem callState_state1 (n a : ℕ) :
    callState (embedF k k') (state1 (k := k) (k' := k') n) a = state2 n a := by
  classical
  funext r
  by_cases hrng : ∃ i, r = embedF k k' i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply embedF_injective]
    simp only [state2, if_neg (Ne.symm (zero_ne_embedF i))]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg fun h => hi (embedF_injective h), unaryConfig_of_ne hi]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp only [state1, state2, if_neg (hrng 0)]

theorem callState_state3 (n a b : ℕ) :
    callState (embedG k k') (state3 (k := k) (k' := k') n a) b = state4 n a b := by
  classical
  funext r
  by_cases hrng : ∃ j, r = embedG k k' j
  · obtain ⟨j, rfl⟩ := hrng
    rw [callState_apply embedG_injective]
    simp only [state4, if_neg (Ne.symm (zero_ne_embedG j)),
      if_neg (embedP_ne_embedG 0 j).symm]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg fun h => hj (embedG_injective h), unaryConfig_of_ne hj]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp only [state3, state4, if_neg (hrng 0)]


/-! ### Unit 5, in two halves

Six blocks in one splice made the goals unmanageable — the composite unfolds at every register
class at once. Splitting at `state5`, with `pairMachine` on one side and the cleanup on the
other, is the same interface discipline the earlier units use.

`pairMachine` goes through `blockState`, the *total* renaming API, which is what keeps it from
becoming a fourth partiality case: it is a call in the layout sense but not in the semantic one. -/

/-- After `pairMachine`: both operands still present, the answer beside them. -/
def state5 (n a b : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedP k k' 1 then b
    else if r = embedP k k' 2 then Nat.pair a b else 0

theorem run_saveGPair (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (saveGPair (k := k) (k' := k')) ⟨0, state4 n a b⟩ m).pc <
        (saveGPair (k := k) (k' := k')).length) ∧
      run (saveGPair (k := k) (k' := k')) ⟨0, state4 n a b⟩ N =
        ⟨(saveGPair (k := k) (k' := k')).length, state5 n a b⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have fg' := fg.symm; have fp0' := fp0.symm
  have fp1' := fp1.symm; have ft' := ft.symm; have gp0' := gp0.symm; have gp1' := gp1.symm
  have gt' := gt.symm; have p0t' := p0t.symm; have p1t' := p1t.symm; have p01' := p01.symm
  have pz : ∀ i : Fin 9, embedP k k' i ≠ 0 := embedP_ne_zero
  have pz' : ∀ i : Fin 9, (0 : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_zero i).symm
  have pt : ∀ i : Fin 9, embedP k k' i ≠ ten := embedP_ne_ten
  have pt' : ∀ i : Fin 9, (ten : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_ten i).symm
  have pf : ∀ (i : Fin 9) (j : Fin (k + 1)), embedP k k' i ≠ embedF k k' j := embedP_ne_embedF
  have pf' : ∀ (j : Fin (k + 1)) (i : Fin 9), embedF k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedF i j).symm
  have pg : ∀ (i : Fin 9) (j : Fin (k' + 1)), embedP k k' i ≠ embedG k k' j := embedP_ne_embedG
  have pg' : ∀ (j : Fin (k' + 1)) (i : Fin 9), embedG k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedG i j).symm
  have fz : ∀ i : Fin (k + 1), embedF k k' i ≠ 0 := fun i => (zero_ne_embedF i).symm
  have gz : ∀ j : Fin (k' + 1), embedG k k' j ≠ 0 := fun j => (zero_ne_embedG j).symm
  have hblock : (fun i => if i = embedG k k' 0 then 0
      else if i = embedP k k' 1 then
        state4 (k := k) (k' := k') n a b (embedP k k' 1) +
          state4 (k := k) (k' := k') n a b (embedG k k' 0)
      else state4 (k := k) (k' := k') n a b i) ∘ embedP k k' =
      fun j => if j = 0 then a else if j = 1 then b else 0 := by
    funext j
    fin_cases j <;>
      simp_all [state4, embedP_injective.eq_iff, embedP_ne_zero, embedP_ne_embedG]
  rw [saveGPair]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move gp1).seq
      (realises_pairMachine.renameRegs_blockState embedP_injective)) (state4 n a b)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  dsimp only
  rcases layout_cases r with rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_zero i).symm)]
    simp_all [state4, state5]
  · rw [blockState_apply embedP_injective, hblock]
    simp only [state5]
    fin_cases i <;> simp_all [state4, embedP_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_ten i).symm)]
    simp_all [state4, state5]
  · rw [blockState_of_not_mem _ _ (fun j => (embedP_ne_embedF j i).symm)]
    simp_all [state4, state5]
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_embedG i j).symm)]
    simp_all [state4, state5, embedG_injective.eq_iff]

theorem run_finishPair (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (finishPair (k := k) (k' := k')) ⟨0, state5 n a b⟩ m).pc <
        (finishPair (k := k) (k' := k')).length) ∧
      run (finishPair (k := k) (k' := k')) ⟨0, state5 n a b⟩ N =
        ⟨(finishPair (k := k) (k' := k')).length,
          unaryConfig (k + k' + 12) (Nat.pair a b)⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have p01' := p01.symm
  have pz : ∀ i : Fin 9, embedP k k' i ≠ 0 := embedP_ne_zero
  have pz' : ∀ i : Fin 9, (0 : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_zero i).symm
  have pt : ∀ i : Fin 9, embedP k k' i ≠ ten := embedP_ne_ten
  have pt' : ∀ i : Fin 9, (ten : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_ten i).symm
  have pf : ∀ (i : Fin 9) (j : Fin (k + 1)), embedP k k' i ≠ embedF k k' j := embedP_ne_embedF
  have pf' : ∀ (j : Fin (k + 1)) (i : Fin 9), embedF k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedF i j).symm
  have pg : ∀ (i : Fin 9) (j : Fin (k' + 1)), embedP k k' i ≠ embedG k k' j := embedP_ne_embedG
  have pg' : ∀ (j : Fin (k' + 1)) (i : Fin 9), embedG k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedG i j).symm
  have fz : ∀ i : Fin (k + 1), embedF k k' i ≠ 0 := fun i => (zero_ne_embedF i).symm
  have gz : ∀ j : Fin (k' + 1), embedG k k' j ≠ 0 := fun j => (zero_ne_embedG j).symm
  rw [finishPair]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (embedP k k' 0)).seq
      ((realises_clear (embedP k k' 1)).seq
        ((realises_clear (0 : Fin (k + k' + 13))).seq (realises_move p2)))) (state5 n a b)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  dsimp only
  rcases layout_cases r with rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp_all [state5, unaryConfig, embedP_injective.eq_iff]
  · simp only [Function.update_apply]
    fin_cases i <;>
      simp_all [state5, unaryConfig, embedP_injective.eq_iff]
  · simp_all [state5, unaryConfig]
  · simp_all [state5, unaryConfig]
  · simp_all [state5, unaryConfig]

/-- Unit 5, the two halves spliced. -/
theorem run_saveGFinish (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (saveGFinish (k := k) (k' := k')) ⟨0, state4 n a b⟩ m).pc <
        (saveGFinish (k := k) (k' := k')).length) ∧
      run (saveGFinish (k := k) (k' := k')) ⟨0, state4 n a b⟩ N =
        ⟨(saveGFinish (k := k) (k' := k')).length,
          unaryConfig (k + k' + 12) (Nat.pair a b)⟩ := by
  obtain ⟨N1, h1in, h1ex⟩ := run_saveGPair (k := k) (k' := k') n a b
  obtain ⟨N2, h2in, h2ex⟩ := run_finishPair (k := k) (k' := k') n a b
  exact ⟨N1 + N2, join_exit h1in h1ex h2in h2ex⟩

/-! ## The closure theorem

Neither clause needs a case split. The exit clause gets `a` and `b` from `mem_eval_pair` and
splices the five exits; the halting clause peels the controller forwards, and the three
operational cases — the first call cannot halt, the first does and the second cannot, both do —
are where that argument can *stop*, not branches Lean has to enumerate. -/

theorem CleanPartComputesUnary.pair {P : Program (k + 1)} {Q : Program (k' + 1)}
    {f g : ℕ →. ℕ} (hf : CleanPartComputesUnary P f) (hg : CleanPartComputesUnary Q g) :
    CleanPartComputesUnary (pairController P Q) fun n => Nat.pair <$> f n <*> g n := by
  intro n
  have hxF : state1 (k := k) (k' := k') n (embedF k k' 0) = n := by
    simp [state1, (zero_ne_embedF 0).symm]
  have hcF : ∀ i, i ≠ 0 → state1 (k := k) (k' := k') n (embedF k k' i) = 0 := by
    intro i hi
    have hne : embedF k k' i ≠ embedF k k' 0 := fun h => hi (embedF_injective h)
    simp [state1, (zero_ne_embedF i).symm, hne]
  have hxG : ∀ a, state3 (k := k) (k' := k') n a (embedG k k' 0) = n := by
    intro a
    simp [state3, (zero_ne_embedG 0).symm, (embedP_ne_embedG 0 0).symm]
  have hcG : ∀ a j, j ≠ 0 → state3 (k := k) (k' := k') n a (embedG k k' j) = 0 := by
    intro a j hj
    have hne : embedG k k' j ≠ embedG k k' 0 := fun h => hj (embedG_injective h)
    simp [state3, (zero_ne_embedG j).symm, (embedP_ne_embedG 0 j).symm, hne]
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_eval_pair.mp hy
    obtain ⟨N1, i1, e1⟩ := run_seedF (k := k) (k' := k') n
    obtain ⟨N2, i2, e2⟩ := hf.call_exit embedF_injective hxF hcF ha
    rw [callState_state1] at e2
    obtain ⟨N3, i3, e3⟩ := run_saveFSeedG (k := k) (k' := k') n a
    obtain ⟨N4, i4, e4⟩ := hg.call_exit embedG_injective (hxG a) (hcG a) hb
    rw [callState_state3] at e4
    obtain ⟨N5, i5, e5⟩ := run_saveGFinish (k := k) (k' := k') n a b
    obtain ⟨j45, f45⟩ := join_exit i4 e4 i5 e5
    obtain ⟨j345, f345⟩ := join_exit i3 e3 j45 f45
    obtain ⟨j2345, f2345⟩ := join_exit i2 e2 j345 f345
    exact ⟨N1 + (N2 + (N3 + (N4 + N5))), join_exit i1 e1 j2345 f2345⟩
  · -- peel the seeding block, reaching the first call
    obtain ⟨N1, i1, e1⟩ := run_seedF (k := k) (k' := k') n
    have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hh
    rw [show (run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ N1).regs =
      state1 n from by rw [e1]] at h1
    -- the first call halts, so `f n` converges
    have hdf := (hf.call_halts_iff embedF_injective hxF hcF).mp (halts_prefix_of_halts_append h1)
    obtain ⟨N2, i2, e2⟩ := hf.call_exit embedF_injective hxF hcF (Part.get_mem hdf)
    rw [callState_state1] at e2
    have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
    rw [show (run (renameRegs (embedF k k') P) ⟨0, state1 n⟩ N2).regs =
      state2 n ((f n).get hdf) from by rw [e2]] at h2
    -- peel the saving-and-seeding block, reaching the second call
    obtain ⟨N3, i3, e3⟩ := run_saveFSeedG (k := k) (k' := k') n ((f n).get hdf)
    have h3 := (halts_append_of_exits i3 (by rw [e3])).mp h2
    rw [show (run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n ((f n).get hdf)⟩ N3).regs =
      state3 n ((f n).get hdf) from by rw [e3]] at h3
    have hdg := (hg.call_halts_iff embedG_injective (hxG _) (hcG _)).mp
      (halts_prefix_of_halts_append h3)
    exact Part.dom_iff_mem.mpr ⟨Nat.pair ((f n).get hdf) ((g n).get hdg),
      mem_eval_pair.mpr ⟨_, Part.get_mem hdf, _, Part.get_mem hdg, rfl⟩⟩

/-- **`Code.pair`.** A corollary of the closure theorem and nothing else: the two `mem_` lemmas
identify the applicative source semantics with the existential the machine proof used. -/
theorem CleanPartComputesUnary.codePair {P : Program (k + 1)} {Q : Program (k' + 1)}
    {cf cg : Nat.Partrec.Code} (hf : CleanPartComputesUnary P cf.eval)
    (hg : CleanPartComputesUnary Q cg.eval) :
    CleanPartComputesUnary (pairController P Q) (Nat.Partrec.Code.pair cf cg).eval :=
  (hf.pair hg).congr fun n => Part.ext fun y => by rw [mem_eval_code_pair, mem_eval_pair]

end RegisterMachine

end Hilbert10
