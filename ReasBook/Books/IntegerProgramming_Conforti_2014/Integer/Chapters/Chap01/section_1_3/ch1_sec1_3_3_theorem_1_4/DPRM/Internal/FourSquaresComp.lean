module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.FourSquares
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeAlgebraComp

/-!
# The four-square transformation is primitive recursive

Issue #28, fourth piece, computability half. `NatSolvable ≤₀ IntSolvable` needs a *computable* map
on codes, so this file proves `Primrec fourSquares`. Everything semantic lives in `FourSquares`.

Unlike the difference substitution, nothing here is substituted into `p`: the transformed code is
built from `p` itself, the arity, and one constraint per variable. The only shape that needs work
is the fold over `List.range p.arity`, and the same `list_range`/`list_map`/`list_foldr` vocabulary
covers it. No integer operation beyond the two already certified in `CodeAlgebraComp` is reached.

## Main results

* `Hilbert10.PolynomialCode.primrec_fourSquares`
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open Primrec

theorem primrec_npow_X {α : Type*} [Primcodable α] {k : α → ℕ} (hk : Primrec k) :
    Primrec fun a => npow (X (k a)) 2 :=
  Primrec₂.comp primrec₂_npow (primrec_X.comp hk) (Primrec.const 2)

theorem primrec_fourSq : Primrec fun q : ℕ × ℕ => fourSq q.1 q.2 := by
  have hbase : Primrec fun q : ℕ × ℕ => q.1 + 4 * q.2 :=
    Primrec₂.comp Primrec.nat_add Primrec.fst
      (Primrec₂.comp Primrec.nat_mul (Primrec.const 4) Primrec.snd)
  have hoff : ∀ c : ℕ, Primrec fun q : ℕ × ℕ => q.1 + 4 * q.2 + c := fun c =>
    Primrec₂.comp Primrec.nat_add hbase (Primrec.const c)
  have h : Primrec fun q : ℕ × ℕ =>
      add (add (npow (X (q.1 + 4 * q.2)) 2) (npow (X (q.1 + 4 * q.2 + 1)) 2))
        (add (npow (X (q.1 + 4 * q.2 + 2)) 2) (npow (X (q.1 + 4 * q.2 + 3)) 2)) :=
    Primrec₂.comp primrec₂_add
      (Primrec₂.comp primrec₂_add (primrec_npow_X hbase) (primrec_npow_X (hoff 1)))
      (Primrec₂.comp primrec₂_add (primrec_npow_X (hoff 2)) (primrec_npow_X (hoff 3)))
  exact h.of_eq fun q => rfl

theorem primrec_fourSqConstraint :
    Primrec fun q : ℕ × ℕ => fourSqConstraint q.1 q.2 := by
  have h : Primrec fun q : ℕ × ℕ => npow (add (X q.2) (neg (fourSq q.1 q.2))) 2 :=
    Primrec₂.comp primrec₂_npow
      (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.snd)
        (primrec_neg.comp primrec_fourSq))
      (Primrec.const 2)
  exact h.of_eq fun q => rfl

/-- **The four-square transformation is primitive recursive**, hence computable — which is what
the many-one reduction consumes. -/
theorem primrec_fourSquares : Primrec fourSquares := by
  have hconstraints : Primrec fun p : PolynomialCode =>
      (List.range p.arity).map fun i => fourSqConstraint p.arity i := by
    refine Primrec.list_map (Primrec.list_range.comp primrec_arity) ?_
    exact primrec_fourSqConstraint.comp ((primrec_arity.comp Primrec.fst).pair Primrec.snd)
  have hfold : Primrec fun p : PolynomialCode =>
      (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero) := by
    refine Primrec.list_foldr (h := fun _ (r : PolynomialCode × PolynomialCode) => add r.1 r.2)
      hconstraints (Primrec.const zero) ?_
    exact Primrec₂.comp primrec₂_add (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have h : Primrec fun p : PolynomialCode =>
      add (npow p 2)
        (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero) :=
    Primrec₂.comp primrec₂_add
      (Primrec₂.comp primrec₂_npow Primrec.id (Primrec.const 2)) hfold
  exact h.of_eq fun p => rfl

theorem computable_fourSquares : Computable fourSquares := primrec_fourSquares.to_comp

end PolynomialCode

end Hilbert10
