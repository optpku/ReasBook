module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Compacting only the witness variables

Issue #2, staged here for upstreaming to mathlib.

`MvPolynomial.exists_fin_rename` reindexes the *entire* variable type along an injection
`Fin n → σ`. Applied at `σ = Fin n ⊕ β` it renumbers the input variables together with the
witnesses, which destroys the input/witness partition that the whole Hilbert-tenth
development is built on (issue #6 fixes inputs as the left summand and existential
witnesses as the right one).

What is needed instead is a *right-only* compaction: the `Fin n` block is fixed pointwise
and only `β` is compacted to its finite support.
-/

@[expose] public section

namespace Hilbert10

open MvPolynomial

variable {β R : Type*} [CommSemiring R]

/-- Every polynomial in `σ ⊕ τ` is a polynomial in all of the variables from `σ` and finitely
many of the variables from `τ`. Mirrors `MvPolynomial.exists_finset_rename`. -/
theorem exists_finset_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R) :
    ∃ (t : Finset β) (q : MvPolynomial (σ ⊕ { x // x ∈ t }) R),
      p = rename (Sum.map id (↑)) q := by
  classical
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let f : { x // x ∈ s } → σ ⊕ { x // x ∈ s.toRight } := fun x =>
    match h : x.1 with
    | .inl a => .inl a
    | .inr b => .inr ⟨b, Finset.mem_toRight.mpr (h ▸ x.2)⟩
  refine ⟨s.toRight, rename f q, ?_⟩
  rw [rename_rename]
  congr 2
  funext x
  rcases x with ⟨a | b, h⟩
  · rfl
  · simp [f]

/-- Compact only the right summand of the variable type: the variables from `σ` are preserved
pointwise, and the witnesses are reindexed by a finite injection.

Unlike `MvPolynomial.exists_fin_rename`, which reindexes the whole variable type along an
injection `Fin n → σ ⊕ β`, the left summand is left untouched. This is what the Diophantine
normal form needs: renumbering the *input* variables would change the relation represented.

Upstreamed as leanprover-community/mathlib4#42203; delete this file once that merges. -/
theorem exists_fin_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R) :
    ∃ (m : ℕ) (f : Fin m → β) (_ : Function.Injective f) (q : MvPolynomial (σ ⊕ Fin m) R),
      p = rename (Sum.map id f) q := by
  obtain ⟨t, q, rfl⟩ := exists_finset_right_rename p
  let m := Fintype.card { x // x ∈ t }
  let e := Fintype.equivFin { x // x ∈ t }
  refine ⟨m, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective,
    rename (Sum.map id e) q, ?_⟩
  rw [rename_rename]
  congr 1
  ext x
  obtain a | b := x <;> simp

/-- The evaluation corollary that downstream actually consumes. Stated with assignments in
the coefficient ring; for a different target ring use `eval₂` with a `RingHom R →+* S`
rather than an `S`-valued `eval`, which would not typecheck against `R` coefficients. -/
theorem eval_of_exists_fin_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R)
    {m : ℕ} {f : Fin m → β} {q : MvPolynomial (σ ⊕ Fin m) R}
    (hq : p = rename (Sum.map id f) q) (x : σ → R) (y : β → R) :
    eval (Sum.elim x y) p = eval (Sum.elim x (y ∘ f)) q := by
  subst hq
  have hassign : Sum.elim x y ∘ Sum.map id f = Sum.elim x (y ∘ f) := by
    funext i
    cases i <;> rfl
  rw [eval_rename, hassign]

end Hilbert10
