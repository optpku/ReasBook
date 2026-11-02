module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.NumberTheory.Dioph

/-!
# The `Poly` / `MvPolynomial` bridge

Issues #3, #4 and #5. `Mathlib.NumberTheory.Dioph` carries the TODO "Connect `Poly` to
`MvPolynomial`"; this is that connection, in the form the Diophantine normal form (#6)
needs.

## Main declarations

* `MvPolynomial.toDiophPoly`: the ring homomorphism `MvPolynomial α ℤ →+* Poly α`.
* `exists_mvPolynomial`: conversely, every `Poly` agrees with some `MvPolynomial` at
  natural-number valuations. This is an *existence* statement, not a function: `Poly` is an
  extensional subtype whose induction principle eliminates into `Prop` only, so no
  computable extraction is available or attempted.
* `MvPolynomial.RepresentsNat`: the specification relation saying that a polynomial in
  input variables `α` and witness variables `β` represents a relation on `α`-tuples.

## Implementation notes

`Poly α` is a `CommRing` (`Mathlib/NumberTheory/Dioph.lean`), so the forward direction is
`eval₂Hom` rather than a bare function. Everything downstream then commutes with `+`, `*`
and `C` by `map_add` / `map_mul` / `map_intCast` instead of bespoke induction.
-/

@[expose] public section

namespace Hilbert10

open MvPolynomial

variable {α β : Type*}

/-! ### From `MvPolynomial` to `Poly` -/

/-- The ring homomorphism sending a multivariate integer polynomial to the corresponding
`Poly`, i.e. to its evaluation function on natural-number valuations. -/
def toDiophPoly : MvPolynomial α ℤ →+* Poly α :=
  eval₂Hom (Int.castRingHom (Poly α)) Poly.proj

@[simp]
theorem toDiophPoly_X (i : α) : toDiophPoly (X i : MvPolynomial α ℤ) = Poly.proj i := by
  simp [toDiophPoly]

/-- The integer cast into `Poly α` is the constant function. -/
@[simp]
theorem Poly.intCast_apply (n : ℤ) (x : α → ℕ) : ((n : Poly α)) x = n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => push_cast at ih ⊢; simp [ih]
  | pred k ih => push_cast at ih ⊢; simp [ih]

@[simp]
theorem toDiophPoly_C (n : ℤ) : toDiophPoly (C n : MvPolynomial α ℤ) = Poly.const n := by
  ext x
  simp [toDiophPoly]

/-- Evaluating the `Poly` produced by `toDiophPoly` at a natural-number valuation agrees
with evaluating the original polynomial at the corresponding integer valuation. -/
@[simp]
theorem toDiophPoly_apply (p : MvPolynomial α ℤ) (x : α → ℕ) :
    toDiophPoly p x = eval (fun i => (x i : ℤ)) p := by
  induction p using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-! ### From `Poly` to `MvPolynomial` -/

/-- Every `Poly` agrees, at natural-number valuations, with some multivariate integer
polynomial.

This is an existence statement rather than a function: `Poly.induction` eliminates into
`Prop` only, so nothing here extracts syntax from a `Poly`. Note also where finiteness
enters — the `MvPolynomial` produced has finite support by construction, whereas the
variable type of the `Poly` may be arbitrary. -/
theorem exists_mvPolynomial (p : Poly α) :
    ∃ q : MvPolynomial α ℤ, ∀ x : α → ℕ, eval (fun i => (x i : ℤ)) q = p x := by
  induction p using Poly.induction with
  | H1 i => exact ⟨X i, fun x => by simp⟩
  | H2 n => exact ⟨C n, fun x => by simp⟩
  | H3 f g hf hg =>
    obtain ⟨qf, hqf⟩ := hf
    obtain ⟨qg, hqg⟩ := hg
    exact ⟨qf - qg, fun x => by simp [hqf, hqg]⟩
  | H4 f g hf hg =>
    obtain ⟨qf, hqf⟩ := hf
    obtain ⟨qg, hqg⟩ := hg
    exact ⟨qf * qg, fun x => by simp [hqf, hqg]⟩

/-! ### The specification relation -/

/-- `p.RepresentsNat R` says that the polynomial `p`, in input variables `α` and witness
variables `β`, represents the relation `R` on `α`-tuples of naturals: `R x` holds exactly
when `p` has a natural-number root extending `x`.

The variable types are deliberately left general; the finite `Fin n ⊕ Fin m` shape belongs
to the normal-form theorem (#6), not to this definition.

Note this lives in the `Hilbert10` namespace rather than `MvPolynomial`: dot
notation on `MvPolynomial` is unreliable anyway, since the type unfolds to
`AddMonoidAlgebra`. It moves to the `MvPolynomial` namespace when upstreamed. -/
def RepresentsNat (p : MvPolynomial (α ⊕ β) ℤ) (R : (α → ℕ) → Prop) : Prop :=
  ∀ x : α → ℕ, R x ↔ ∃ y : β → ℕ,
    eval (Sum.elim (fun i => (x i : ℤ)) (fun j => (y j : ℤ))) p = 0

theorem RepresentsNat.congr {p : MvPolynomial (α ⊕ β) ℤ} {R S : (α → ℕ) → Prop}
    (h : RepresentsNat p R) (hRS : ∀ x, R x ↔ S x) : RepresentsNat p S :=
  fun x => (hRS x).symm.trans (h x)

end Hilbert10
