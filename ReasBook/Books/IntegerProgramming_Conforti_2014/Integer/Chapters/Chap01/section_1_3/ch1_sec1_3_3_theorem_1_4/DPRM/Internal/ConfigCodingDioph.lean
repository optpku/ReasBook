/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ConfigCoding
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ExpDioph

/-!
# The encoded step relation is exponential Diophantine

The second half of #45. `ConfigCoding` proves that `EncodedStep` says exactly the right thing;
this file proves it is expressible.

The width is a *term*, not a numeral. Register values and run lengths grow with the input, so
`w` cannot be fixed in advance — choosing it is #46's job, and by then it has to be a variable of
the formula being built. Likewise `before` and `after` are arbitrary terms, because #49 instantiates
them with two block lookups into a single packed run.

Field indices, by contrast, *are* numerals: the program is fixed by the time this is used, so
each register index appearing in it is a concrete number.

## Main results

* `RegisterMachine.expDioph_encodedStep`
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-! ### Terms for the field operations -/

/-- The base, `2 ^ w`, given a term for `w`. -/
def widthTerm (W : ExpTerm α) : ExpTerm α := .pow (.const 2) W

/-- Reading field `i`. -/
def fieldTerm (W t : ExpTerm α) (i : ℕ) : ExpTerm α :=
  .mod (.div t (.pow (widthTerm W) (.const i))) (widthTerm W)

@[simp] theorem eval_fieldTerm (W t : ExpTerm α) (i : ℕ) (v : α → ℕ) :
    (fieldTerm W t i).eval v = configField (W.eval v) (t.eval v) i := rfl

/-- Writing `u` into field `i`. -/
def setFieldTerm (W t : ExpTerm α) (i : ℕ) (u : ExpTerm α) : ExpTerm α :=
  .add (.add (.mod t (.pow (widthTerm W) (.const i))) (.mul u (.pow (widthTerm W) (.const i))))
    (.mul (.div t (.pow (widthTerm W) (.const (i + 1)))) (.pow (widthTerm W) (.const (i + 1))))

@[simp] theorem eval_setFieldTerm (W t : ExpTerm α) (i : ℕ) (u : ExpTerm α) (v : α → ℕ) :
    (setFieldTerm W t i u).eval v = setField (W.eval v) (t.eval v) i (u.eval v) := rfl

/-! ### Representability -/

/-- A single instruction's encoded effect is exponential Diophantine. -/
theorem expDioph_instrEncodedStep (W b a : ExpTerm α) (p : ℕ) (I : Instr k) :
    ExpDioph {v : α → ℕ | I.EncodedStep (W.eval v) p (b.eval v) (a.eval v)} := by
  cases I with
  | inc r j =>
    refine ExpDioph.congr
      (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b 0) (t := .const p))
        (ExpDioph.and (ExpDioph.of_lt (s := .const j) (t := widthTerm W))
          (ExpDioph.and
            (ExpDioph.of_lt (s := .add (fieldTerm W b ((r : ℕ) + 1)) (.const 1))
              (t := widthTerm W))
            (ExpDioph.of_eq (s := a)
              (t := setFieldTerm W (setFieldTerm W b 0 (.const j)) ((r : ℕ) + 1)
                (.add (fieldTerm W b ((r : ℕ) + 1)) (.const 1))))))) ?_
    intro v
    simp [Instr.EncodedStep, ExpTerm.eval, widthTerm]
  | dec r jpos jzero =>
    refine ExpDioph.congr
      (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b 0) (t := .const p))
        (ExpDioph.or
          (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b ((r : ℕ) + 1)) (t := .const 0))
            (ExpDioph.and (ExpDioph.of_lt (s := .const jzero) (t := widthTerm W))
              (ExpDioph.of_eq (s := a) (t := setFieldTerm W b 0 (.const jzero)))))
          (ExpDioph.and (ExpDioph.of_lt (s := .const 0) (t := fieldTerm W b ((r : ℕ) + 1)))
            (ExpDioph.and (ExpDioph.of_lt (s := .const jpos) (t := widthTerm W))
              (ExpDioph.of_eq (s := a)
                (t := setFieldTerm W (setFieldTerm W b 0 (.const jpos)) ((r : ℕ) + 1)
                  (.sub (fieldTerm W b ((r : ℕ) + 1)) (.const 1)))))))) ?_
    intro v
    simp [Instr.EncodedStep, ExpTerm.eval, widthTerm]

/-- The disjunction over a suffix of the program. Recursion on the instruction list; each `::`
is one use of `ExpDioph.or`. -/
theorem expDioph_encodedStepFrom (W b a : ExpTerm α) : ∀ (L : Program k) (p : ℕ),
    ExpDioph {v : α → ℕ | encodedStepFrom (W.eval v) p L (b.eval v) (a.eval v)} := by
  intro L
  induction L with
  | nil =>
    intro p
    exact ExpDioph.congr ExpDioph.of_false fun v => by simp [encodedStepFrom]
  | cons I rest ih =>
    intro p
    refine ExpDioph.congr (ExpDioph.or (expDioph_instrEncodedStep W b a p I) (ih (p + 1))) ?_
    intro v
    simp [encodedStepFrom]

/-- **The step relation is exponential Diophantine**, hence Diophantine by `ExpDioph.dioph`.

The program is a fixed finite list, so this is a finite disjunction assembled nonuniformly —
no instruction is ever encoded, and no lookup is ever computed. -/
theorem expDioph_encodedStep (P : Program k) (W b a : ExpTerm α) :
    ExpDioph {v : α → ℕ | EncodedStep P (W.eval v) (b.eval v) (a.eval v)} :=
  expDioph_encodedStepFrom W b a P 0

theorem dioph_encodedStep (P : Program k) (W b a : ExpTerm α) :
    Dioph {v : α → ℕ | EncodedStep P (W.eval v) (b.eval v) (a.eval v)} :=
  (expDioph_encodedStep P W b a).dioph

end RegisterMachine

end Hilbert10
