module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCodeDenote
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Every finite-arity polynomial has a code

Issue #11, core half. This module imports only #10, so its independence from the
`Poly`/`MvPolynomial` bridge is a fact about the Lean module graph and not merely a claim
in prose. The `RepresentsNat` corollary, which does need #5, lives in
`Hilbert10/ExistsCodeRepresents.lean`.

## The variable contract

Inputs are variables `0, …, n-1` and witnesses are variables `n, …, n+m-1`, contiguously
and in that order. That is exactly

```lean
Sum.elim (fun i : Fin n => i.val) (fun j : Fin m => n + j.val)
```

which is `varIndex` below. Every later milestone assumes this ordering, so it is stated
once, as a definition, and never re-derived.

## Implementation notes

The contract is an equality of *denotations*, not agreement of evaluations; the evaluation
corollary is derived from it via `eval_denote` and `MvPolynomial.eval_rename`.

Codes are built by induction on the polynomial with every exponent vector of length exactly
`n + m`. The fixed length is what makes multiplication by a variable well defined as
`List.set` at the variable's index: with ragged vectors `List.set` past the end is silently
a no-op, which would be a soundness bug rather than an inconvenience.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

variable {n m : ℕ}

/-- The variable-index contract: inputs first, then witnesses, contiguously. -/
def varIndex (n m : ℕ) : Fin n ⊕ Fin m → ℕ :=
  Sum.elim (fun i : Fin n => i.val) (fun j : Fin m => n + j.val)

/-- The contract, expressed through `finSumFinEquiv`. Injectivity and the bound are read
off from the equivalence, but every downstream statement is phrased in terms of `varIndex`
itself. -/
theorem varIndex_eq (n m : ℕ) : varIndex n m = fun v => ((finSumFinEquiv v : Fin (n + m)) : ℕ) := by
  funext v
  cases v <;> simp [varIndex]

theorem varIndex_lt (v : Fin n ⊕ Fin m) : varIndex n m v < n + m := by
  rw [varIndex_eq]
  exact (finSumFinEquiv v).isLt

theorem varIndex_injective : Function.Injective (varIndex n m) := by
  rw [varIndex_eq]
  exact Fin.val_injective.comp finSumFinEquiv.injective

/-! ### Multiplying a code by a variable -/

/-- Multiply a code by the variable `k`, by incrementing the exponent at index `k` in every
term. Sound only when every exponent vector is long enough to reach `k`; see
`denote_mulX`. -/
def mulX (k : ℕ) (q : PolynomialCode) : PolynomialCode :=
  ⟨q.terms.map fun t => (t.1, t.2.set k (t.2.getD k 0 + 1))⟩

theorem denote_mulX_aux (k : ℕ) :
    ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, k < t.2.length) →
      (ts.map fun t : ℤ × MonomialCode =>
          C t.1 * denoteMonomial (t.2.set k (t.2.getD k 0 + 1))).sum =
        (ts.map fun t : ℤ × MonomialCode => C t.1 * denoteMonomial t.2).sum * X k := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
    intro hts
    simp only [List.map_cons, List.sum_cons]
    rw [ih fun s hs => hts s (List.mem_cons_of_mem _ hs),
      denoteMonomial_set t.2 k (hts t (List.mem_cons_self ..))]
    ring

theorem denote_mulX {k : ℕ} {q : PolynomialCode}
    (hq : ∀ t ∈ q.terms, k < t.2.length) : (mulX k q).denote = q.denote * X k := by
  simp only [mulX, denote, List.map_map]
  exact denote_mulX_aux k q.terms hq

theorem length_mem_mulX {k : ℕ} {q : PolynomialCode} {N : ℕ}
    (hq : ∀ t ∈ q.terms, t.2.length = N) :
    ∀ t ∈ (mulX k q).terms, t.2.length = N := by
  simp only [mulX]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  simpa using hq s hs

/-! ### The coding theorem -/

/-- Every polynomial in `n` input and `m` witness variables has a code, whose denotation is
literally the renaming of that polynomial along the variable contract.

The auxiliary conclusion — that every exponent vector has length exactly `n + m` — is what
makes the induction go through; `arity ≤ n + m` follows. -/
theorem exists_code_aux (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    ∃ q : PolynomialCode, (∀ t ∈ q.terms, t.2.length = n + m) ∧
      q.denote = rename (varIndex n m) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨⟨[(r, List.replicate (n + m) 0)]⟩, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      simp [ht]
    · rw [denote_singleton, denoteMonomial_replicate_zero, mul_one, rename_C]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hlen₁, hden₁⟩ := h₁
    obtain ⟨q₂, hlen₂, hden₂⟩ := h₂
    refine ⟨⟨q₁.terms ++ q₂.terms⟩, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hlen₁ t h
      · exact hlen₂ t h
    · rw [denote_append, map_add, hden₁, hden₂]
  | mul_X p v h =>
    obtain ⟨q, hlen, hden⟩ := h
    refine ⟨mulX (varIndex n m v) q, length_mem_mulX hlen, ?_⟩
    rw [denote_mulX fun t ht => by rw [hlen t ht]; exact varIndex_lt v, hden, map_mul, rename_X]

/-- **Every finite-arity polynomial has a code.** The contract is denotation equality, not
evaluation agreement. -/
theorem exists_code (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    ∃ q : PolynomialCode, q.arity ≤ n + m ∧ q.denote = rename (varIndex n m) p := by
  obtain ⟨q, hlen, hden⟩ := exists_code_aux p
  refine ⟨q, ?_, hden⟩
  simp only [arity]
  have aux : ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, t.2.length = n + m) →
      (ts.map fun t : ℤ × MonomialCode => t.2.length).foldr max 0 ≤ n + m := by
    intro ts
    induction ts with
    | nil => intro _; simp
    | cons t ts ih =>
      intro hts
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (le_of_eq (hts t (List.mem_cons_self ..)))
        (ih fun s hs => hts s (List.mem_cons_of_mem _ hs))
  exact aux q.terms hlen

/-! ### Evaluation

Derived from the denotation contract, rather than proved separately by pointwise reasoning.
-/

theorem getD_ofFn_append (x : Fin n → ℕ) (y : Fin m → ℕ) (v : Fin n ⊕ Fin m) :
    (List.ofFn x ++ List.ofFn y).getD (varIndex n m v) 0 = Sum.elim x y v := by
  cases v with
  | inl i =>
    have hi : varIndex n m (Sum.inl i) = (i : ℕ) := rfl
    rw [hi, List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | inr j =>
    have hj : varIndex n m (Sum.inr j) = n + (j : ℕ) := rfl
    rw [hj, List.getD_append_right _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

/-- Evaluating a code at inputs followed by witnesses agrees with evaluating the polynomial
it codes. Derived from the denotation contract via `eval_denote` and `eval_rename`, not by
pointwise reasoning about the code. -/
theorem eval_exists_code {p : MvPolynomial (Fin n ⊕ Fin m) ℤ} {q : PolynomialCode}
    (hq : q.denote = rename (varIndex n m) p) (x : Fin n → ℕ) (y : Fin m → ℕ) :
    q.eval (List.ofFn x ++ List.ofFn y) =
      MvPolynomial.eval (Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ)) p := by
  have hassign :
      (fun i => (((List.ofFn x ++ List.ofFn y).getD i 0 : ℕ) : ℤ)) ∘ varIndex n m =
        Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ) := by
    funext v
    simp only [Function.comp_apply, getD_ofFn_append x y v]
    cases v <;> rfl
  rw [← eval_denote q (List.ofFn x ++ List.ofFn y), hq, eval_rename, hassign]

end PolynomialCode

end Hilbert10
