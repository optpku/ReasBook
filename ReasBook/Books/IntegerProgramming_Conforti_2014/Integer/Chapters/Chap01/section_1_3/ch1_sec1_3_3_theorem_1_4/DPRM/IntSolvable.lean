module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.NatSolvable
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.SubUV
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.SubUVComp
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.FourSquares
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.FourSquaresComp
public import Mathlib.Computability.Reduce
public import Mathlib.NumberTheory.SumFourSquares

/-!
# Integer solvability, and its equivalence with the natural version

Issue #28. `IntSolvable` is Hilbert's own question for the encoded wire format: does the coded
polynomial have an **integer** root? This file defines it and proves that it holds exactly when
the difference-substituted code has a natural root.

## Why the equivalence is stated on codes

`intSolvable_iff_natSolvable_subUV` is the mathematical content of the reduction
`IntSolvable ≤₀ NatSolvable`; what the reduction adds is that `subUV` is computable. Keeping the
two apart means the arithmetic can be checked without reading a computability proof, and the
computability proof does not have to re-establish any arithmetic.

## Both directions normalise first

The predicates quantify over arbitrary-length assignments, while the two-block reading needs a
fixed boundary at `p.arity`. Each direction therefore normalises its witness to an exact length
before splitting: integer witnesses through `exists_length_eq_arity_evalInt_eq`, natural ones
through the arity bound `arity_subUV_le` and zero-extension. Skipping that step would let a short
witness make `take` and `drop` describe the wrong blocks.

## Main results

* `Hilbert10.IntSolvable`
* `Hilbert10.intSolvable_iff_natSolvable_subUV`
* `Hilbert10.intSolvable_manyOneReducible_natSolvable`
* `Hilbert10.natSolvable_iff_intSolvable_fourSquares`
* `Hilbert10.natSolvable_manyOneReducible_intSolvable`
* `Hilbert10.natSolvable_manyOneEquiv_intSolvable`
-/

@[expose] public section

namespace Hilbert10

open PolynomialCode

/-- **Hilbert's tenth problem over the integers**, for the encoded wire format. -/
def IntSolvable (p : PolynomialCode) : Prop := ∃ x : List ℤ, p.evalInt x = 0

theorem intSolvable_iff (p : PolynomialCode) :
    IntSolvable p ↔ ∃ x : List ℤ, p.evalInt x = 0 := Iff.rfl

/-- **The reduction, as an equivalence of codes.** An integer root of `p` is exactly a natural
root of the difference-substituted code. -/
theorem intSolvable_iff_natSolvable_subUV (p : PolynomialCode) :
    IntSolvable p ↔ NatSolvable (subUV p) := by
  constructor
  · rintro ⟨x, hx⟩
    -- normalise the integer witness, then split it componentwise
    obtain ⟨y, hylen, hy⟩ := exists_length_eq_arity_evalInt_eq p x
    refine ⟨y.map Int.toNat ++ y.map fun z => (-z).toNat, ?_⟩
    rw [eval_subUV p (by simpa using hylen) (by simpa using hylen), diffList_toNat, hy, hx]
  · rintro ⟨w, hw⟩
    -- normalise the natural witness to exactly `2 * p.arity`, then split it in half
    set n := p.arity with hn
    set w' := (w ++ List.replicate (2 * n) 0).take (2 * n) with hw'
    have hw'len : w'.length = 2 * n := by
      simp only [hw', List.length_take, List.length_append, List.length_replicate]
      omega
    have hw'eval : eval (subUV p) w' = 0 := by
      have hsplit : (w ++ List.replicate (2 * n) 0)
          = w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n) := by
        simp [hw']
      have hlen : (subUV p).arity ≤ w'.length := by
        rw [hw'len]; exact arity_subUV_le p
      calc eval (subUV p) w'
          = eval (subUV p) (w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n)) :=
            (eval_append_of_arity_le hlen _).symm
        _ = eval (subUV p) (w ++ List.replicate (2 * n) 0) := by rw [← hsplit]
        _ = eval (subUV p) w := eval_append_replicate_zero _ _ _
        _ = 0 := hw
    refine ⟨diffList (w'.take n) (w'.drop n), ?_⟩
    have hu : (w'.take n).length = n := by
      simp only [List.length_take, hw'len]
      omega
    have hv : (w'.drop n).length = n := by
      simp only [List.length_drop, hw'len]
      omega
    rw [← eval_subUV p hu hv, List.take_append_drop, hw'eval]

/-- **Integer solvability reduces to natural solvability.** The computable map is the difference
substitution; the equivalence above is its correctness. -/
theorem intSolvable_manyOneReducible_natSolvable : IntSolvable ≤₀ NatSolvable :=
  ⟨subUV, computable_subUV, intSolvable_iff_natSolvable_subUV⟩

/-! ### The other direction: four squares

Natural roots become integer roots of the constraint code. Nothing is substituted into `p`; the
original variables are kept and each is forced to be a sum of four integer squares. -/

/-- **The four-square equivalence.** -/
theorem natSolvable_iff_intSolvable_fourSquares (p : PolynomialCode) :
    NatSolvable p ↔ IntSolvable (fourSquares p) := by
  set n := p.arity with hn
  constructor
  · rintro hp
    obtain ⟨x, hxlen, hx⟩ := (natSolvable_iff_arity p).mp hp
    -- Lagrange supplies four witnesses for every coordinate
    choose a b c d hw using fun i : ℕ => Nat.sum_four_squares (x.getD i 0)
    set w : ℕ → ℕ := fun k =>
      if k % 4 = 0 then a (k / 4) else if k % 4 = 1 then b (k / 4)
      else if k % 4 = 2 then c (k / 4) else d (k / 4) with hwdef
    refine ⟨x.map (Nat.cast : ℕ → ℤ)
        ++ (List.range (4 * n)).map fun k => ((w k : ℕ) : ℤ), ?_⟩
    set y : List ℤ := x.map (Nat.cast : ℕ → ℤ)
      ++ (List.range (4 * n)).map fun k => ((w k : ℕ) : ℤ) with hy
    have hfirst : (x.map (Nat.cast : ℕ → ℤ)).length = n := by
      simp only [List.length_map, hxlen, hn]
    -- the original block
    have hx0 : ∀ i < n, y.getD i 0 = ((x.getD i 0 : ℕ) : ℤ) := by
      intro i hi
      rw [hy, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < _),
        ← List.getD_eq_getElem?_getD, getD_map_natCast]
    -- the interleaved witness block, stated only at `n + (4 * i + r)`
    have hacc : ∀ i r : ℕ, i < n → r < 4 →
        y.getD (n + (4 * i + r)) 0 = ((w (4 * i + r) : ℕ) : ℤ) := by
      intro i r hi hr
      have hlt : 4 * i + r < 4 * n := by omega
      rw [hy, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega : (x.map (Nat.cast : ℕ → ℤ)).length ≤ n + (4 * i + r))]
      rw [hfirst, show n + (4 * i + r) - n = 4 * i + r from by omega,
        List.getElem?_map, List.getElem?_range hlt]
      simp
    refine (evalInt_fourSquares_eq_zero_iff p y).mpr ⟨?_, fun i hi => ?_⟩
    · -- `p` only reads the first block
      have : evalInt p y = evalInt p (x.map (Nat.cast : ℕ → ℤ)) := by
        rw [hy]
        exact evalInt_append_of_arity_le (by rw [hfirst]) _
      rw [this, evalInt_map_natCast, hx]
    · -- each constraint holds by Lagrange
      have e0 := hacc i 0 hi (by omega)
      have e1 := hacc i 1 hi (by omega)
      have e2 := hacc i 2 hi (by omega)
      have e3 := hacc i 3 hi (by omega)
      have hw0 : w (4 * i + 0) = a i := by simp [hwdef]
      have hw1 : w (4 * i + 1) = b i := by
        have hm : (4 * i + 1) % 4 = 1 := by omega
        have hd : (4 * i + 1) / 4 = i := by omega
        simp [hwdef, hm, hd]
      have hw2 : w (4 * i + 2) = c i := by
        have hm : (4 * i + 2) % 4 = 2 := by omega
        have hd : (4 * i + 2) / 4 = i := by omega
        simp [hwdef, hm, hd]
      have hw3 : w (4 * i + 3) = d i := by
        have hm : (4 * i + 3) % 4 = 3 := by omega
        have hd : (4 * i + 3) / 4 = i := by omega
        simp [hwdef, hm, hd]
      rw [hx0 i hi, evalInt_fourSq,
        show n + 4 * i + 3 = n + (4 * i + 3) from by omega,
        show n + 4 * i + 2 = n + (4 * i + 2) from by omega,
        show n + 4 * i + 1 = n + (4 * i + 1) from by omega,
        show n + 4 * i = n + (4 * i + 0) from by omega,
        e0, e1, e2, e3, hw0, hw1, hw2, hw3, ← hw i]
      push_cast
      ring
  · rintro ⟨y₀, hy₀⟩
    -- normalise to the full frozen length, then split off the first block
    obtain ⟨y, hylen, hyval⟩ :=
      exists_length_eq_evalInt_eq (fourSquares p) y₀ (arity_fourSquares_le p)
    have hzero : evalInt (fourSquares p) y = 0 := by rw [hyval, hy₀]
    obtain ⟨hp, hc⟩ := (evalInt_fourSquares_eq_zero_iff p y).mp hzero
    have hnonneg : ∀ i < n, 0 ≤ y.getD i 0 := by
      intro i hi
      rw [hc i hi]
      exact evalInt_fourSq_nonneg _ _ _
    refine (natSolvable_iff_arity p).mpr ⟨(y.take n).map Int.toNat, ?_, ?_⟩
    · simp only [List.length_map, List.length_take, hylen]
      omega
    have hcast : ((y.take n).map Int.toNat).map (Nat.cast : ℕ → ℤ) = y.take n := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      have hi : i < n := by
        simp only [List.length_take, hylen] at h2
        omega
      have := hnonneg i hi
      simp only [List.getElem_map, List.getElem_take]
      have hy0 : y.getD i 0 = y[i]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp
      rw [hy0] at this
      omega
    rw [eval_eq_evalInt, hcast]
    have hsplit : evalInt p (y.take n) = evalInt p y := by
      have harity : p.arity ≤ (y.take n).length := by
        simp only [List.length_take, hylen]
        omega
      have := evalInt_append_of_arity_le (p := p) (x := y.take n) harity (y.drop n)
      rw [List.take_append_drop] at this
      exact this.symm
    rw [hsplit, hp]

/-- **Natural solvability reduces to integer solvability.** The computable map is the four-square
transformation; the equivalence above is its correctness. With
`intSolvable_manyOneReducible_natSolvable`, the two formulations of Hilbert's tenth problem for
the wire format are many-one equivalent. -/
theorem natSolvable_manyOneReducible_intSolvable : NatSolvable ≤₀ IntSolvable :=
  ⟨fourSquares, computable_fourSquares, natSolvable_iff_intSolvable_fourSquares⟩

/-- **The two formulations have the same many-one degree.** Packaged with mathlib's
`ManyOneEquiv`, so that downstream results can transport reducibility facts along it. -/
theorem natSolvable_manyOneEquiv_intSolvable : ManyOneEquiv NatSolvable IntSolvable :=
  ⟨natSolvable_manyOneReducible_intSolvable, intSolvable_manyOneReducible_natSolvable⟩

/-! ### Zero-arity regression

At `p.arity = 0` the frozen layout has no variables at all and the constraint list is empty, so the
transformation degenerates to `p²`. Both truth values are checked, since an off-by-one in the empty
`List.range` would make the equivalence vacuously true rather than visibly wrong. -/

example : IntSolvable (fourSquares (const 0)) :=
  (natSolvable_iff_intSolvable_fourSquares _).mp ⟨[], by simp⟩

example : ¬ IntSolvable (fourSquares (const 1)) := by
  rw [← natSolvable_iff_intSolvable_fourSquares]
  rintro ⟨x, hx⟩
  simp at hx

end Hilbert10
