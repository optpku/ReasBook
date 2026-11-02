module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A wire format for Hilbert's tenth problem

Issue #8. To state H10 as a decision problem the input must be a finitely encoded object;
this is that encoding, and deliberately nothing more.

## Design

* **Permissive, not canonical.** Duplicate monomials, zero coefficients, trailing zero
  exponents and arbitrary term order are all legal. H10's undecidability must not depend
  on canonicalisation, so there is no quotient, no normal form and no `DecidableEq`
  obligation.
* **Missing variables evaluate to zero.** Evaluation recurses structurally over the
  exponent and assignment lists in parallel; an exhausted assignment is treated as zeros.
  This is what makes zero-extension hold *unconditionally* and keeps the computability
  proof of #9 free of index arithmetic.
* **`arity` is a presentation upper bound**, the maximum exponent-vector length — not the
  minimal semantic arity, which would be false for a permissive format. Every use of it in
  this project is an upper bound. Do not state or rely on any minimality lemma.

Deliberately absent: any `MvPolynomial` connection (that is #10), any `+`/`*` API,
substitution beyond #12, systems of equations, or fresh-variable allocation.
-/

@[expose] public section

namespace Hilbert10

/-- The exponent vector of a monomial: the `i`-th entry is the exponent of variable `i`. -/
abbrev MonomialCode := List ℕ

/-- A permissive sparse encoding of a multivariate integer polynomial as a list of
`(coefficient, exponent vector)` pairs. -/
structure PolynomialCode where
  /-- The terms of the polynomial, as `(coefficient, exponent vector)` pairs. -/
  terms : List (ℤ × MonomialCode)

namespace PolynomialCode

/-- The value of a monomial at an assignment, by structural recursion on the exponent
vector and the assignment in parallel. Variables past the end of the assignment are taken
to be `0`; note `(0 : ℤ) ^ 0 = 1`, so a zero exponent is harmless there. -/
def evalMonomial : MonomialCode → List ℕ → ℤ
  | [], _ => 1
  | e :: es, [] => (0 : ℤ) ^ e * evalMonomial es []
  | e :: es, v :: vs => (v : ℤ) ^ e * evalMonomial es vs

/-- The value of an encoded polynomial at an assignment. -/
def eval (p : PolynomialCode) (x : List ℕ) : ℤ :=
  (p.terms.map fun t => t.1 * evalMonomial t.2 x).sum

/-- A presentation upper bound on the number of variables: the maximum exponent-vector
length. Trailing zero exponents inflate it, which is harmless — see the module docstring. -/
def arity (p : PolynomialCode) : ℕ :=
  (p.terms.map fun t => t.2.length).foldr max 0

@[simp] theorem evalMonomial_nil (x : List ℕ) : evalMonomial [] x = 1 := rfl

@[simp] theorem eval_mk_nil (x : List ℕ) : eval ⟨[]⟩ x = 0 := rfl

/-! ### Zero-extension

Padding an assignment with zeros never changes a value, with no hypothesis at all: the
variables being supplied were already being read as zero.
-/

theorem evalMonomial_append_zeros (e : MonomialCode) (x z : List ℕ) (hz : ∀ v ∈ z, v = 0) :
    evalMonomial e (x ++ z) = evalMonomial e x := by
  induction e generalizing x z with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil =>
      cases z with
      | nil => rfl
      | cons c cs =>
        obtain rfl : c = 0 := hz c (by simp)
        have hrec : evalMonomial es cs = evalMonomial es [] := by
          simpa using ih [] cs fun v hv => hz v (by simp [hv])
        simp [evalMonomial, hrec]
    | cons v vs =>
      simp only [List.cons_append, evalMonomial]
      rw [ih vs z hz]

theorem eval_append_zeros (p : PolynomialCode) (x z : List ℕ) (hz : ∀ v ∈ z, v = 0) :
    p.eval (x ++ z) = p.eval x := by
  simp only [eval]
  congr 1
  exact List.map_congr_left fun t _ => by rw [evalMonomial_append_zeros t.2 x z hz]

/-- Zero-extension: padding an assignment with zeros is invisible. -/
theorem eval_append_replicate_zero (p : PolynomialCode) (x : List ℕ) (k : ℕ) :
    p.eval (x ++ List.replicate k 0) = p.eval x :=
  p.eval_append_zeros x _ fun _ hv => List.eq_of_mem_replicate hv

/-! ### Append-invariance under the arity bound

Once an assignment is at least as long as the arity, appending anything is invisible: the
extra values are never read.
-/

theorem evalMonomial_append_of_length_le {e : MonomialCode} {x : List ℕ} (h : e.length ≤ x.length)
    (y : List ℕ) : evalMonomial e (x ++ y) = evalMonomial e x := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp at h
    | cons v vs =>
      simp only [List.cons_append, evalMonomial]
      rw [ih (by simpa using h)]

theorem length_le_foldr_max {l : List (ℤ × MonomialCode)} {t : ℤ × MonomialCode} (ht : t ∈ l) :
    t.2.length ≤ (l.map fun s => s.2.length).foldr max 0 := by
  induction l with
  | nil => cases ht
  | cons s ss ih =>
    rcases List.mem_cons.mp ht with rfl | hts
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hts) (Nat.le_max_right _ _)

theorem length_le_arity {p : PolynomialCode} {t : ℤ × MonomialCode} (ht : t ∈ p.terms) :
    t.2.length ≤ p.arity :=
  length_le_foldr_max ht

theorem eval_append_of_arity_le {p : PolynomialCode} {x : List ℕ} (h : p.arity ≤ x.length)
    (y : List ℕ) : p.eval (x ++ y) = p.eval x := by
  simp only [eval]
  congr 1
  exact List.map_congr_left fun t ht => by
    rw [evalMonomial_append_of_length_le (Nat.le_trans (length_le_arity ht) h)]

/-! ### Sanity checks

Concrete instances of the three conventions, kept as regression tests: the encoding of
`x₀ ^ 2 + x₁ ^ 2 - 25`, a variable read past the end of an assignment, and a trailing zero
exponent inflating `arity` without changing any value.
-/

example : (⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).eval [3, 4] = 0 := by decide

example : (⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).arity = 2 := by decide

example : (⟨[(1, [0, 1])]⟩ : PolynomialCode).eval [5] = 0 := by decide

example : (⟨[(1, [1, 0, 0])]⟩ : PolynomialCode).arity = 3 := by decide

example : (⟨[(1, [1, 0, 0])]⟩ : PolynomialCode).eval [4] = 4 := by decide

end PolynomialCode

end Hilbert10
