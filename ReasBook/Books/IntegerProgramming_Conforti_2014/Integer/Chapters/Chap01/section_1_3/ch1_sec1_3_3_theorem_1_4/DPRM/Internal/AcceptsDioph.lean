module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ConfigCodingDioph
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ExpDiophChoose
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.PackedRun

/-!
# The machine route, reduced to one obligation

Issue #49, first phase. #48 closed the semantic chain: `Accepts` is *equivalent* to the
existence of a packed run. This file represents every part of that statement except one, and
gives the remainder a name.

## What is discharged here

The endpoint of `accepts_iff_exists_encodedRun` has eight conjuncts under four existentials.
Seven of them are ordinary exponential Diophantine atoms:

* the two input and output bounds, `of_lt`;
* two endpoint equalities, `of_eq`, using the closed form `configCode w ⟨p, unaryConfig k x⟩
  = p + 2 ^ w * x`.

The rest — the program-length bound, the guard mask, and the bounded conjunction over indices —
is bundled into `Aggregation` and taken as a hypothesis, so that the accounting cannot drift:
`expDioph_accepts` is *conditional*, and the condition is a single `def` one can read.

## Why the bundle, and not the conjunct alone

The mask is not hard to represent. It is `ExpDioph.of_isBinarySubmask` (#34) applied to
`guardMask` with `geom` carried as a *variable* pinned by `geom_unique` — which is exactly what
that subtraction-free identity was proved for — and the program-length bound is one `of_lt`.
They are bundled anyway, because any construction that discharges the bounded conjunction needs
them as *hypotheses*: without the mask it must reason about arbitrary, possibly overflowing
block values, and without `P.length < 2 ^ w` it cannot bound instruction indices inside a block.
Stating the obligation as the weakest thing the endpoint actually needs is the same "prove only
the endpoint" rule the rest of the development follows. The geometric-sum witness therefore
stays internal to whatever proof discharges `Aggregation`.

## How it is discharged, and what did not count as progress

`Aggregation` is the same bounded-universal theorem the direct-route spike isolated in
`Spike/Sequences.lean`. `SelectorRegsDioph.aggregation_succ` discharges it at every register
count, by the selector encoding rather than by any bounded-universal representation: finitely
many identities over one-hot selector lanes replace the quantifier outright. Two things would
not have counted as progress, and did not happen:

* adding a bounded-product or bounded-forall constructor to `ExpTerm` — that relocates the
  missing proof into new syntax;
* `boundedForall_eq_iff_prod`. Product-equals-one is *equivalent* to the bounded universal for
  those gap factors, so the reduction is free and the representation of the variable product is
  the whole of the difficulty.

A discharge has to come from an independently proved representation theorem, and attribution
belongs at the deepest non-circular one — here, the selector construction.

## Main definitions

* `RegisterMachine.blockTerm` — outer block lookup at a **variable** index
* `RegisterMachine.Aggregation` — the obligation, discharged in `SelectorRegsDioph`

## Main results

* `RegisterMachine.expDioph_accepts` — conditional on `Aggregation`; the unconditional form
  is `RegisterMachine.dioph_accepts_regs`
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-! ### Terms for the outer layer

`ConfigCodingDioph`'s `fieldTerm` reads a field at a numeral index, which is right for the
inner layer: the program is fixed, so its register indices are numerals. The outer index runs
over blocks and is a variable, so it needs its own term. -/

/-- The data width of one block: `w * (k + 1)` for a `k`-register machine. -/
def dataBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.mul W (.const (k + 1)))

@[simp] theorem eval_dataBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (dataBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1)) := rfl

/-- The outer packing base: one block is the data plus one guard bit. -/
def outerBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.add (.mul W (.const (k + 1))) (.const 1))

@[simp] theorem eval_outerBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (outerBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1) + 1) := rfl

/-- **Outer block lookup at a variable index.** -/
def blockTerm (k : ℕ) (W R I : ExpTerm α) : ExpTerm α :=
  .mod (.div R (.pow (outerBaseTerm k W) I)) (outerBaseTerm k W)

@[simp] theorem eval_blockTerm (k : ℕ) (W R I : ExpTerm α) (v : α → ℕ) :
    (blockTerm k W R I).eval v
      = configField (W.eval v * (k + 1) + 1) (R.eval v) (I.eval v) := rfl

/-! ### The obligation -/

/-- **The obligation for one program**: a bounded conjunction of step relations over a variable
number of block indices, bundled with the two facts any proof of it would have to assume anyway.

Stated with `N`, `W`, `R` as terms and the index quantified semantically, so that it cannot be
satisfied by making the index a numeral or by assuming a representable lookup function.

Separated from `Aggregation` because it is provable for particular programs — see
`Spike/SelectorSliceDioph` — long before it is provable for all of them, and the endpoint below
only ever needs it at the one program it is applied to. -/
def StepBundle (P : Program k) (N W R : ExpTerm α) : Set (α → ℕ) :=
  {v : α → ℕ |
    P.length < 2 ^ W.eval v ∧
    Nat.IsBinarySubmask (R.eval v) (guardMask (W.eval v * (k + 1)) (N.eval v + 1)) ∧
    ∀ i < N.eval v,
      EncodedStep P (W.eval v)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) i)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) (i + 1))}

/-- **The sole remaining representability obligation of #21**: `StepBundle`, uniformly in the
program. -/
def Aggregation (k : ℕ) : Prop :=
  ∀ {α : Type} (P : Program k) (N W R : ExpTerm α), ExpDioph (StepBundle P N W R)

/-! ### Everything else -/

/-- The witness block of `expDioph_accepts`: `0` is the run length, `1` the width, `2` the
packed run. There is no fourth witness — the geometric sum moved inside `Aggregation`. -/
def runBody (P : Program (k + 1)) (X Y : ExpTerm α) : Set ((α ⊕ Fin 3) → ℕ) :=
  {u | (X.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    (Y.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) 0
      = 2 ^ u (Sum.inr 1) * (X.map Sum.inl).eval u ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (u (Sum.inr 0))
      = P.length + 2 ^ u (Sum.inr 1) * (Y.map Sum.inl).eval u ∧
    (P.length < 2 ^ u (Sum.inr 1) ∧
      Nat.IsBinarySubmask (u (Sum.inr 2))
        (guardMask (u (Sum.inr 1) * (k + 1 + 1)) (u (Sum.inr 0) + 1)) ∧
      ∀ i < u (Sum.inr 0),
        EncodedStep P (u (Sum.inr 1))
          (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) i)
          (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (i + 1)))}

theorem expDioph_runBody_of_bundle {P : Program (k + 1)}
    (hP : ∀ {β : Type} (N W R : ExpTerm β), ExpDioph (StepBundle P N W R)) (X Y : ExpTerm α) :
    ExpDioph (runBody P X Y) := by
  refine ExpDioph.congr (ExpDioph.and
    (ExpDioph.of_lt (s := X.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_lt (s := Y.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.const 0))
      (t := .mul (widthTerm (.var (Sum.inr 1))) (X.map Sum.inl))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.var (Sum.inr 0)))
      (t := .add (.const P.length) (.mul (widthTerm (.var (Sum.inr 1))) (Y.map Sum.inl))))
    (hP (.var (Sum.inr 0)) (.var (Sum.inr 1)) (.var (Sum.inr 2))))))) ?_
  intro u
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, runBody, StepBundle, widthTerm, ExpTerm.eval,
    eval_blockTerm]

theorem expDioph_runBody (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph (runBody P X Y) :=
  expDioph_runBody_of_bundle (fun {β} N W R => hagg (α := β) P N W R) X Y

/-- **The endpoint, for a single program.**

Every conjunct of `accepts_iff_exists_encodedRun` other than the bundle is discharged here:
the input and output bounds, and the two endpoint equalities. Only `StepBundle` for the one
program in hand is assumed, so a program whose aggregation is provable is representable
outright, without waiting for `Aggregation`. -/
theorem expDioph_accepts_of_bundle {P : Program (k + 1)}
    (hP : ∀ {β : Type} (N W R : ExpTerm β), ExpDioph (StepBundle P N W R)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_runBody_of_bundle hP X Y)) fun v => ?_
  simp only [runBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl, Sum.elim_inr]
  rw [accepts_iff_exists_encodedRun]
  simp only [EncodedRun, configCode_unaryConfig, Nat.zero_add]
  constructor
  · rintro ⟨u, hx, hy, h0, hn, hlen, hmask, hstep⟩
    exact ⟨u 0, u 1, u 2, hx, hy, hlen, hmask, h0, hn, hstep⟩
  · rintro ⟨n, w, R, hx, hy, hlen, hmask, h0, hn, hstep⟩
    exact ⟨![n, w, R], hx, hy, h0, hn, hlen, hmask, hstep⟩

/-- **The endpoint, conditional on aggregation.** -/
theorem expDioph_accepts (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  expDioph_accepts_of_bundle (fun {β} N W R => hagg (α := β) P N W R) X Y

end RegisterMachine

end Hilbert10
