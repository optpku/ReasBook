/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

set_option autoImplicit false

/-!
Primary domain: Diophantine subsets of integer lattices and their polynomial presentations.

Layer triage:
- `source-facing`: subsets `S ⊆ ℤⁿ` and the textbook definition that membership in `S` is
  equivalent to solvability of one integer polynomial equation.
- `core/canonical`: `MvPolynomial` and `MvPolynomial.eval` are mathlib's owner abstractions for
  multivariate integer polynomials and their evaluation on integer tuples.
- `bridge/view`: no extra public bridge is needed; the source-facing definition can speak directly
  in the language of the canonical polynomial owner.

Domain sampling:
1. `MvPolynomial` is the canonical owner for multivariate polynomials with coefficients in `ℤ`.
2. `MvPolynomial.eval` is the canonical evaluation map at a tuple of integer values.
3. `Dioph` from `Mathlib.NumberTheory.Dioph` is mathlib's owner notion for the natural-valued
   Diophantine predicate; since the textbook item is explicitly about subsets of `ℤⁿ`, the main
   declaration here stays source-facing rather than collapsing to that natural-coded owner.
4. `Dioph.reindex_dioph` shows the upstream API is organized around variable reindexing, so the
   polynomial witness should remain primitive data and the existential Diophantine property should
   be derived from it.

Primitive vs. derived:
- primitive source data: the subset `S ⊆ ℤⁿ` and a polynomial witness `P`;
- derived API: the existential predicate `S.IsDiophantine`;
- the solvability condition for `P` is stated directly via `MvPolynomial.eval`, rather than
  packaged as a second public owner.
-/

namespace Set

/-- Definition 4-7-5: a subset `S ⊆ ℤⁿ` is Diophantine when some integer polynomial enumerates
`S`. -/
def IsDiophantine {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∃ m : ℕ, ∃ p : MvPolynomial (Fin n ⊕ Fin m) ℤ,
    ∀ s : Fin n → ℤ, s ∈ S ↔ ∃ y : Fin m → ℤ, p.eval (Sum.elim s y) = 0

/-- A subset of `ℤⁿ` is Diophantine exactly when it is enumerated by some integer polynomial in
the displayed and auxiliary variables. -/
theorem isDiophantine_iff {n : ℕ} (S : Set (Fin n → ℤ)) :
    S.IsDiophantine ↔
      ∃ m : ℕ, ∃ p : MvPolynomial (Fin n ⊕ Fin m) ℤ,
        ∀ s : Fin n → ℤ, s ∈ S ↔ ∃ y : Fin m → ℤ, p.eval (Sum.elim s y) = 0 :=
  Iff.rfl

end Set
