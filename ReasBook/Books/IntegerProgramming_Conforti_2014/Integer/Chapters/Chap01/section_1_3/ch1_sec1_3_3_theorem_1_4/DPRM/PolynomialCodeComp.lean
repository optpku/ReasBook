/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCodePrimcodable
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.PrimrecInt
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.PrimrecNat
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Computability of evaluation

Issue #9, second half. The `Primcodable` contract and the primitive recursiveness of the
projections live in `PolynomialCodePrimcodable`; what remains here is `eval`, which is the
only part that needs anything about `ℤ`.

## Note on integers

`eval` is `ℤ`-valued, and at the pinned mathlib revision the computability library exposes
no lemmas about `ℤ` at all. That layer lives in
`Hilbert10/Internal/ForMathlib/PrimrecInt.lean` (issue #36), deliberately separate: it
is a mathlib gap rather than anything about this wire format, and it must not be allowed to
reshape `PolynomialCode` or `evalMonomial`.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-! ### Evaluation

`eval` is `ℤ`-valued, but its integer content is thin: each coefficient splits as
`c = c.toNat - negPart c` with both parts natural, so `eval` is a difference of two
natural-valued sums. Computability then needs exactly one integer lemma,
`Primrec.int_subNat`, with the rest of the work over `ℕ`.

`natEvalMonomial`, `evalPos`, `evalNeg` and the decomposition are private: they are proof
scaffolding for `primrec₂_eval`, not API.
-/

/-- `evalMonomial`, valued in `ℕ`. Every monomial value is a product of natural powers, so
nothing is lost. -/
def natEvalMonomial : MonomialCode → List ℕ → ℕ
  | [], _ => 1
  | e :: es, [] => 0 ^ e * natEvalMonomial es []
  | e :: es, v :: vs => v ^ e * natEvalMonomial es vs

theorem evalMonomial_eq_cast (e : MonomialCode) (x : List ℕ) :
    evalMonomial e x = (natEvalMonomial e x : ℤ) := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp only [evalMonomial, natEvalMonomial, ih]; push_cast; ring
    | cons v vs => simp only [evalMonomial, natEvalMonomial, ih]; push_cast; ring

/-- The negative part of a coefficient, as a natural number. Written with `natAbs` and
`toNat` rather than `(-c).toNat` so that only lemmas already in `Internal/ForMathlib/PrimrecInt`
are needed. -/
def negPart (c : ℤ) : ℕ := c.natAbs - c.toNat

theorem int_eq_toNat_sub_negPart (c : ℤ) : c = (c.toNat : ℤ) - (negPart c : ℤ) := by
  unfold negPart
  omega

def evalPos (p : PolynomialCode) (x : List ℕ) : ℕ :=
  (p.terms.map fun t => t.1.toNat * natEvalMonomial t.2 x).sum

def evalNeg (p : PolynomialCode) (x : List ℕ) : ℕ :=
  (p.terms.map fun t => negPart t.1 * natEvalMonomial t.2 x).sum

theorem term_eq (c : ℤ) (m : ℕ) :
    c * (m : ℤ) = ((c.toNat * m : ℕ) : ℤ) - ((negPart c * m : ℕ) : ℤ) := by
  push_cast
  conv_lhs => rw [int_eq_toNat_sub_negPart c]
  ring

theorem sum_eq_sub (x : List ℕ) (ts : List (ℤ × MonomialCode)) :
    (ts.map fun t => t.1 * evalMonomial t.2 x).sum =
      ((ts.map fun t => t.1.toNat * natEvalMonomial t.2 x).sum : ℤ) -
        ((ts.map fun t => negPart t.1 * natEvalMonomial t.2 x).sum : ℤ) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, evalMonomial_eq_cast, term_eq]
    push_cast
    ring

theorem eval_eq_sub (p : PolynomialCode) (x : List ℕ) :
    p.eval x = (evalPos p x : ℤ) - (evalNeg p x : ℤ) :=
  sum_eq_sub x p.terms

/-! #### Computability of the natural-valued pieces -/

theorem primrec₂_natEvalMonomial : Primrec₂ natEvalMonomial := by
  -- Parallel recursion on the exponent vector and the assignment, as a left fold that
  -- carries the unconsumed assignment in the accumulator.
  have key : ∀ (e : MonomialCode) (x : List ℕ) (a : ℕ),
      (e.foldl (fun q ei => (q.1 * q.2.headI ^ ei, q.2.tail)) (a, x)).1 =
        a * natEvalMonomial e x := by
    intro e
    induction e with
    | nil => intro x a; simp [natEvalMonomial]
    | cons ei es ih =>
      intro x a
      cases x with
      | nil =>
        have hdef : (default : ℕ) = 0 := rfl
        simp only [List.foldl_cons, ih, natEvalMonomial, List.headI_nil, List.tail_nil, hdef]
        ring
      | cons v vs =>
        simp only [List.foldl_cons, ih, natEvalMonomial, List.headI_cons, List.tail_cons]
        ring
  have hstep : Primrec₂ fun (_ : MonomialCode × List ℕ) (q : (ℕ × List ℕ) × ℕ) =>
      (q.1.1 * q.1.2.headI ^ q.2, q.1.2.tail) :=
    Primrec.pair
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_pow.comp
          (Primrec.list_headI.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have h := Primrec.list_foldl (f := fun a : MonomialCode × List ℕ => a.1)
    (g := fun a : MonomialCode × List ℕ => ((1 : ℕ), a.2))
    (h := fun _ q => (q.1.1 * q.1.2.headI ^ q.2, q.1.2.tail))
    Primrec.fst (Primrec.pair (Primrec.const 1) Primrec.snd) hstep
  exact (Primrec.fst.comp h).of_eq fun a => by rw [key a.1 a.2 1, one_mul]

theorem primrec₂_evalPos : Primrec₂ evalPos := by
  have hstep : Primrec₂ fun (a : PolynomialCode × List ℕ) (q : (ℤ × MonomialCode) × ℕ) =>
      q.1.1.toNat * natEvalMonomial q.1.2 a.2 + q.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.int_toNat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (primrec₂_natEvalMonomial.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun a : PolynomialCode × List ℕ => a.1.terms)
    (g := fun _ : PolynomialCode × List ℕ => (0 : ℕ))
    (h := fun a q => q.1.1.toNat * natEvalMonomial q.1.2 a.2 + q.2)
    (primrec_terms.comp Primrec.fst) (Primrec.const 0) hstep
  refine h.of_eq fun a => ?_
  simp only [evalPos]
  induction a.1.terms with
  | nil => rfl
  | cons t ts ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

theorem primrec₂_evalNeg : Primrec₂ evalNeg := by
  have hnegPart : Primrec negPart :=
    Primrec.nat_sub.comp Primrec.int_natAbs Primrec.int_toNat
  have hstep : Primrec₂ fun (a : PolynomialCode × List ℕ) (q : (ℤ × MonomialCode) × ℕ) =>
      negPart q.1.1 * natEvalMonomial q.1.2 a.2 + q.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (hnegPart.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (primrec₂_natEvalMonomial.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun a : PolynomialCode × List ℕ => a.1.terms)
    (g := fun _ : PolynomialCode × List ℕ => (0 : ℕ))
    (h := fun a q => negPart q.1.1 * natEvalMonomial q.1.2 a.2 + q.2)
    (primrec_terms.comp Primrec.fst) (Primrec.const 0) hstep
  refine h.of_eq fun a => ?_
  simp only [evalNeg]
  induction a.1.terms with
  | nil => rfl
  | cons t ts ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- Evaluation of an encoded polynomial is primitive recursive in the code and the
assignment jointly. -/
theorem primrec₂_eval : Primrec₂ eval := by
  have h := Primrec.int_subNat.comp primrec₂_evalPos primrec₂_evalNeg
  exact h.of_eq fun a => (eval_eq_sub a.1 a.2).symm

/-- Evaluation of an encoded polynomial is computable in the code and the assignment
jointly. -/
theorem computable₂_eval : Computable₂ eval := primrec₂_eval.to_comp

end PolynomialCode

end Hilbert10
