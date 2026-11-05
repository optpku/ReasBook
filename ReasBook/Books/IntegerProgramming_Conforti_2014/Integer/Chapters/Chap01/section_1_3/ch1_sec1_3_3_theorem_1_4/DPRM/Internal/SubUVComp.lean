/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.SubUV
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeAlgebraComp

/-!
# The difference substitution is primitive recursive

Issue #28, third piece, computability half. `IntSolvable ≤₀ NatSolvable` needs a *computable* map
on codes, so this file proves `Primrec subUV`. Everything else about the substitution — semantics
and arity — lives on the structural definitions in `SubUV`; this file works through the index
presentations proved equal to them there.

## One vocabulary

The whole chain uses five list operations, all of which mathlib supplies `Primrec` lemmas for:
`list_range`, `list_map`, `list_getD`, `list_foldr`, `list_flatMap`. Nothing needs truncated
subtraction, and nothing needs a `zipWith` lemma — which mathlib does not have.

The operations of the code algebra are primitive recursive in `CodeAlgebraComp`, which is where
the integer dependency on #36 is certified; this file only assembles them.

## Main results

* `Hilbert10.PolynomialCode.primrec_subUV`
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open Primrec

/-! ### Index presentation, for computability

`subUVMonomialFrom` increments its index in the recursive call, so `Primrec.list_foldr` does not
apply to it directly. The equivalent presentation below folds over `List.range`, where the index
is supplied rather than threaded, and it is proved equal to the structural definition once. Every
semantic and arity result stays on the structural one. -/

theorem subUVMonomialFrom_eq_foldr (n : ℕ) : ∀ (i : ℕ) (es : MonomialCode),
    subUVMonomialFrom n i es
      = (((List.range es.length).map fun j => npow (diffVar n (i + j)) (es.getD j 0)).foldr
          mul one)
  | _, [] => by simp [subUVMonomialFrom]
  | i, e :: es => by
    have ih := subUVMonomialFrom_eq_foldr n (i + 1) es
    rw [show subUVMonomialFrom n i (e :: es)
        = mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es) from rfl, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.foldr_cons, Function.comp_def]
    congr 2
    exact List.map_congr_left fun a _ => by
      rw [show i + 1 + a = i + (a + 1) from by omega]
      simp

/-! ### The substitution -/

theorem primrec_diffVar : Primrec fun q : ℕ × ℕ => diffVar q.1 q.2 := by
  have h : Primrec fun q : ℕ × ℕ => add (X q.2) (neg (X (q.1 + q.2))) :=
    Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.snd)
      (primrec_neg.comp (primrec_X.comp
        (Primrec₂.comp Primrec.nat_add Primrec.fst Primrec.snd)))
  exact h.of_eq fun q => rfl

theorem primrec_subUVMonomialFrom :
    Primrec fun q : (ℕ × ℕ) × MonomialCode => subUVMonomialFrom q.1.1 q.1.2 q.2 := by
  have hfactors : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      (List.range q.2.length).map fun j => npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
    refine Primrec₂.comp primrec₂_npow ?_ ?_
    · exact primrec_diffVar.comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec₂.comp Primrec.nat_add
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
    · exact Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0)
        (Primrec.list_getD 0) (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      ((List.range q.2.length).map fun j =>
        npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0)).foldr mul one := by
    refine Primrec.list_foldr (h := fun _ (r : PolynomialCode × PolynomialCode) => mul r.1 r.2)
      hfactors (Primrec.const one) ?_
    exact Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun q => (subUVMonomialFrom_eq_foldr q.1.1 q.1.2 q.2).symm

/-- **The difference substitution is primitive recursive**, hence computable — which is what the
many-one reduction consumes. -/
theorem primrec_subUV : Primrec subUV := by
  have h : Primrec fun p : PolynomialCode =>
      mk (p.terms.flatMap fun t => (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms) := by
    refine primrec_mk.comp (Primrec.list_flatMap primrec_terms ?_)
    refine primrec_terms.comp (Primrec₂.comp primrec₂_mul
      (primrec_const.comp (Primrec.fst.comp Primrec.snd)) ?_)
    exact primrec_subUVMonomialFrom.comp
      (((primrec_arity.comp Primrec.fst).pair (Primrec.const 0)).pair
        (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun p => rfl

theorem computable_subUV : Computable subUV := primrec_subUV.to_comp

end PolynomialCode

end Hilbert10
