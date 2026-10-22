/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

set_option autoImplicit false

open Nat.Partrec (Code)

/-!
Primary domain: computability-theoretic subsets of the positive integers in the Higman embedding
section.

Layer triage:
- `source-facing`: a subset `S ⊆ ℕ+` that is recursively enumerable but not recursive.
- `core/canonical`: `REPred` and `ComputablePred` are mathlib's owner predicates for recursively
  enumerable and computable membership predicates, while
  `ComputablePred.halting_problem_re` / `ComputablePred.halting_problem` are the canonical
  existence and noncomputability theorems used here.
- `bridge/view`: `Denumerable.equiv₂ Code ℕ+` transports the halting predicate from
  `Nat.Partrec.Code` to a source-facing subset of positive integers.

Domain sampling:
1. `REPred` is mathlib's owner predicate for recursively enumerable subsets of a `Primcodable`
   type.
2. `ComputablePred` is the owner predicate for recursive/computable membership.
3. `ComputablePred.halting_problem_re` and `ComputablePred.halting_problem` provide the canonical
   r.e.-but-noncomputable predicate.
4. `Denumerable.equiv₂` together with `Computable.equiv₂` is the canonical bridge for moving that
   predicate from `Nat.Partrec.Code` to `ℕ+`.

Primitive vs. derived:
- primitive public data: only the witness subset `S : Set ℕ+`;
- derived owner-side properties: recursive enumerability and failure of computability of the
  membership predicate of `S`.
-/

/-- Theorem 4-7-7: there exists a recursively enumerable non-recursive set of positive integers.
In the canonical owner language, this is an r.e. but noncomputable subset of `ℕ+`. -/
theorem exists_recursivelyEnumerable_not_recursive_set_positiveIntegers :
    ∃ S : Set ℕ+, REPred (· ∈ S) ∧ ¬ ComputablePred (· ∈ S) := by
  let e : ℕ+ ≃ Code := Denumerable.equiv₂ _ _
  let P : Code → Prop := fun c ↦ (c.eval 0).Dom
  let S : Set ℕ+ := {n | P (e n)}
  have he : e.Computable := Computable.equiv₂ _ _
  have htransport : OneOneEquiv (P ∘ e) P := OneOneEquiv.of_equiv he
  refine ⟨S, ?_, ?_⟩
  · change REPred (P ∘ e)
    refine REPred.of_eq (((ComputablePred.halting_problem_re 0).comp he.1).dom_re) ?_
    intro n
    simp [P, Part.assert]
  · change ¬ ComputablePred (P ∘ e)
    intro hS
    exact ComputablePred.halting_problem 0 <|
      ComputablePred.computable_of_oneOneReducible htransport.2 hS
