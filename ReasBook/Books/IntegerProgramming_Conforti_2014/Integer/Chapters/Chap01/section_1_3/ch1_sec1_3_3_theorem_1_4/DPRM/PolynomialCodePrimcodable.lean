/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCode
public import Mathlib.Computability.Primrec.List

/-!
# The encoding contract of the wire format

Issue #9, first half. `PolynomialCode` is a one-field structure over `List (ℤ × List ℕ)`, so
its `Primcodable` instance is transported along an explicit equivalence rather than built by
hand. Computability of the constructor, of the `terms` projection and of `arity` follows
immediately, so no later proof ever has to unfold the encoding.

Split out from `PolynomialCodeComp` for a boundary reason. Computability of `eval` needs
`Primrec` lemmas about `ℤ` that the pinned mathlib does not have (#36); the *encoding* needs
none of them, because `Primcodable ℤ` itself is already in mathlib and only the lemmas are
missing. Keeping the two apart means the input type of Hilbert's tenth problem carries its
`Primcodable` contract without depending on a local mathlib shim.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- A `PolynomialCode` is exactly its list of terms. -/
def equivTerms : PolynomialCode ≃ List (ℤ × MonomialCode) where
  toFun := terms
  invFun := mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance : Primcodable PolynomialCode := Primcodable.ofEquiv _ equivTerms

/-- The `terms` projection is primitive recursive. Downstream proofs use this rather than
unfolding the encoding. -/
theorem primrec_terms : Primrec terms :=
  Primrec.of_equiv (e := equivTerms)

/-- The constructor is primitive recursive. -/
theorem primrec_mk : Primrec mk :=
  Primrec.of_equiv_symm (e := equivTerms)

/-! ### Arity -/

theorem arity_eq_foldr (p : PolynomialCode) :
    p.arity = p.terms.foldr (fun t acc => max t.2.length acc) 0 := by
  simp only [arity]
  induction p.terms with
  | nil => rfl
  | cons s ss ih => simp [ih]

theorem primrec_arity : Primrec arity := by
  have hstep : Primrec₂ fun (_ : PolynomialCode) (q : (ℤ × MonomialCode) × ℕ) =>
      max q.1.2.length q.2 :=
    Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun p : PolynomialCode => p.terms)
    (g := fun _ : PolynomialCode => (0 : ℕ))
    (h := fun _ q => max q.1.2.length q.2) primrec_terms (Primrec.const 0) hstep
  exact h.of_eq fun p => (arity_eq_foldr p).symm

end PolynomialCode

end Hilbert10
