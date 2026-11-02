module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeAlgebra
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCodePrimcodable
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.PrimrecInt
public import Mathlib.Computability.Partrec

/-!
# The code algebra is primitive recursive

Issue #28. Both reductions build their transformed code out of the same six operations, and both
need the map on codes to be computable, so the operation-level `Primrec` lemmas live here rather
than in either reduction.

## The integer dependency, certified by the proofs rather than predicted

Only two integer operations are reached:

* `Primrec.int_neg`, for `neg`;
* `Primrec.int_mul`, for the coefficients of a convolution product.

Nothing combines coefficients by integer *addition* — `add` is list append, and `const` merely
transports its coefficient. That is the minimal scope #36 should propose upstream.

## Main results

* `Hilbert10.PolynomialCode.primrec₂_add`, `primrec₂_mul`, `primrec₂_npow` and friends
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open Primrec

/-! ### Exponent addition -/

theorem primrec₂_addExponents : Primrec₂ addExponents := by
  have h : Primrec fun q : MonomialCode × MonomialCode =>
      (List.range (max q.1.length q.2.length)).map fun i => q.1.getD i 0 + q.2.getD i 0 := by
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec₂.comp Primrec.nat_max
        (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))) ?_
    exact Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun q => (addExponents_eq_range q.1 q.2).symm

/-! ### The operations -/

theorem primrec_const : Primrec const := by
  have h : Primrec fun c : ℤ => mk [(c, ([] : MonomialCode))] :=
    primrec_mk.comp (Primrec.list_cons.comp
      (Primrec.id.pair (Primrec.const ([] : MonomialCode)))
      (Primrec.const []))
  exact h.of_eq fun c => rfl

theorem primrec_X : Primrec X := by
  have h : Primrec fun i : ℕ => mk [((1 : ℤ), List.replicate i 0 ++ [1])] := by
    have hexp : Primrec fun i : ℕ => List.replicate i (0 : ℕ) ++ [1] :=
      Primrec₂.comp Primrec.list_append Primrec.list_replicate_zero (Primrec.const [1])
    exact primrec_mk.comp (Primrec.list_cons.comp
      ((Primrec.const (1 : ℤ)).pair hexp) (Primrec.const []))
  exact h.of_eq fun i => rfl

theorem primrec₂_add : Primrec₂ add := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode => mk (q.1.terms ++ q.2.terms) :=
    primrec_mk.comp (Primrec₂.comp Primrec.list_append
      (primrec_terms.comp Primrec.fst) (primrec_terms.comp Primrec.snd))
  exact h.of_eq fun q => rfl

theorem primrec_neg : Primrec neg := by
  have h : Primrec fun p : PolynomialCode => mk (p.terms.map fun t => (-t.1, t.2)) := by
    refine primrec_mk.comp (Primrec.list_map primrec_terms ?_)
    exact (Primrec.int_neg.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun p => rfl

theorem primrec₂_mul : Primrec₂ mul := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode =>
      mk (q.1.terms.flatMap fun t => q.2.terms.map fun s =>
        (t.1 * s.1, addExponents t.2 s.2)) := by
    refine primrec_mk.comp (Primrec.list_flatMap (primrec_terms.comp Primrec.fst) ?_)
    refine Primrec.list_map (primrec_terms.comp (Primrec.snd.comp Primrec.fst)) ?_
    exact (Primrec₂.comp Primrec.int_mul
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec₂.comp primrec₂_addExponents
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun q => rfl

theorem primrec₂_npow : Primrec₂ npow := by
  have h := Primrec.nat_rec' (f := fun q : PolynomialCode × ℕ => q.2)
    (g := fun _ : PolynomialCode × ℕ => one)
    (h := fun (q : PolynomialCode × ℕ) (r : ℕ × PolynomialCode) => mul q.1 r.2)
    Primrec.snd (Primrec.const one)
    (Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun q => ?_
  obtain ⟨p, n⟩ := q
  induction n with
  | zero => rfl
  | succ m ih => simp only [npow, ← ih]

end PolynomialCode

end Hilbert10
