module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCode
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Ring

/-!
# The wire format denotes a multivariate polynomial

Issue #10. This is the semantic anchor for `PolynomialCode`: it is what makes the encoding
a *representation of a polynomial* rather than an arbitrary evaluator, and it is what #11
states its contract against.

## Main results

* `denote`: the `MvPolynomial ℕ ℤ` denoted by a code.
* `eval_denote`: evaluating the denotation agrees with `eval`, for **every** assignment
  list, under the same zero-default convention `eval` uses.
* `denote_singleton`, `denote_append`: #11 needs algebraic equality of denotations, not
  merely agreement of evaluations, so the compositional structure is exposed.
* `vars_denote_subset`: `p.denote.vars ⊆ Finset.range p.arity`, an **upper bound only** —
  `arity` is a presentation bound and no minimality holds for a permissive format.

## Implementation notes

Monomial denotation mirrors `evalMonomial` structurally, threading the variable index
through the recursion. That keeps the evaluation proof a straightforward induction and
makes the treatment of trailing zero exponents visible: a trailing `0` contributes
`X i ^ 0 = 1`, so it changes the denotation not at all while still counting towards
`arity`.

Nothing here normalizes. Duplicate monomials denote as a genuine repeated sum, which is
equal — not merely equivalent — to the combined term, because addition in `MvPolynomial`
does the combining.

No computability results: that is #9, and it deliberately does not depend on this file.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

-- `MvPolynomial` is noncomputable, and `PolynomialCode.eval` shadows `MvPolynomial.eval`
-- inside this namespace, so the latter is always written out in full below.
noncomputable section

/-- Denotation of an exponent vector whose first entry refers to variable `i`. -/
def denoteMonomialFrom : ℕ → MonomialCode → MvPolynomial ℕ ℤ
  | _, [] => 1
  | i, e :: es => X i ^ e * denoteMonomialFrom (i + 1) es

/-- The monomial denoted by an exponent vector: the `i`-th entry is the exponent of
variable `i`. -/
def denoteMonomial (e : MonomialCode) : MvPolynomial ℕ ℤ := denoteMonomialFrom 0 e

/-- The multivariate integer polynomial denoted by a code. -/
def denote (p : PolynomialCode) : MvPolynomial ℕ ℤ :=
  (p.terms.map fun t => C t.1 * denoteMonomial t.2).sum

/-! ### Compositional structure

Exposed because #11 needs to prove an equality of denotations, which is done by induction
over the term list rather than by comparing evaluations.
-/

@[simp] theorem denote_nil : (⟨[]⟩ : PolynomialCode).denote = 0 := rfl

theorem denote_singleton (c : ℤ) (e : MonomialCode) :
    (⟨[(c, e)]⟩ : PolynomialCode).denote = C c * denoteMonomial e := by
  simp [denote]

theorem denote_cons (t : ℤ × MonomialCode) (ts : List (ℤ × MonomialCode)) :
    (⟨t :: ts⟩ : PolynomialCode).denote =
      C t.1 * denoteMonomial t.2 + (⟨ts⟩ : PolynomialCode).denote := by
  simp [denote]

theorem denote_append (s t : List (ℤ × MonomialCode)) :
    (⟨s ++ t⟩ : PolynomialCode).denote =
      (⟨s⟩ : PolynomialCode).denote + (⟨t⟩ : PolynomialCode).denote := by
  simp [denote, List.map_append, List.sum_append]

/-! ### No normalization

Two consequences of denoting structurally, stated rather than left implicit: trailing zero
exponents contribute nothing, and duplicate terms denote as a genuine repeated sum whose
value is *equal* to the combined term — addition in `MvPolynomial` does the combining, so
no normalization step is needed anywhere.
-/

theorem denoteMonomialFrom_replicate_zero (i k : ℕ) :
    denoteMonomialFrom i (List.replicate k 0) = 1 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, denoteMonomialFrom, ih]

theorem denoteMonomialFrom_append_replicate_zero (e : MonomialCode) (i k : ℕ) :
    denoteMonomialFrom i (e ++ List.replicate k 0) = denoteMonomialFrom i e := by
  induction e generalizing i with
  | nil =>
    rw [List.nil_append]
    exact (denoteMonomialFrom_replicate_zero i k).trans rfl
  | cons a es ih => simp [denoteMonomialFrom, ih]

/-- An all-zero exponent vector denotes `1`. -/
@[simp] theorem denoteMonomial_replicate_zero (k : ℕ) :
    denoteMonomial (List.replicate k 0) = 1 :=
  denoteMonomialFrom_replicate_zero 0 k

/-- Trailing zero exponents do not change a denotation, though they do inflate `arity`. -/
theorem denoteMonomial_append_replicate_zero (e : MonomialCode) (k : ℕ) :
    denoteMonomial (e ++ List.replicate k 0) = denoteMonomial e :=
  denoteMonomialFrom_append_replicate_zero e 0 k

/-- Duplicate terms need no normalization: two copies of a term denote the same polynomial
as the single term with the coefficients added. -/
theorem denote_duplicate (c d : ℤ) (e : MonomialCode) :
    (⟨[(c, e), (d, e)]⟩ : PolynomialCode).denote = (⟨[(c + d, e)]⟩ : PolynomialCode).denote := by
  simp only [denote, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, map_add]
  ring

-- Regression tests for the two claims above. Note the trailing-zero lemma applies in the
-- `e ++ List.replicate k 0` form, which is how padding arises; a *literal* exponent list
-- like `[1, 0, 0]` is normalized by the elaborator before any rewrite can match it, so
-- state it as an append.
example : denoteMonomial ([1] ++ List.replicate 2 0) = denoteMonomial [1] :=
  denoteMonomial_append_replicate_zero [1] 2

example (e : MonomialCode) :
    (⟨[(1, e), (1, e)]⟩ : PolynomialCode).denote = (⟨[(2, e)]⟩ : PolynomialCode).denote := by
  simpa using denote_duplicate 1 1 e

/-- Incrementing the exponent at index `k` multiplies the monomial by `X k`. Sound only
when the exponent vector is long enough to reach `k`: `List.set` past the end is silently a
no-op. Used by #11, where every exponent vector is padded to a fixed length. -/
theorem denoteMonomial_set :
    ∀ (e : MonomialCode) (k : ℕ), k < e.length →
      denoteMonomial (e.set k (e.getD k 0 + 1)) = denoteMonomial e * X k := by
  have aux : ∀ (e : MonomialCode) (i k : ℕ), k < e.length →
      denoteMonomialFrom i (e.set k (e.getD k 0 + 1)) =
        denoteMonomialFrom i e * X (i + k) := by
    intro e
    induction e with
    | nil => intro i k hk; simp at hk
    | cons a es ih =>
      intro i k hk
      cases k with
      | zero =>
        simp only [List.set_cons_zero, List.getD_cons_zero, denoteMonomialFrom, Nat.add_zero,
          pow_succ]
        ring
      | succ k =>
        have hk' : k < es.length := by simpa using hk
        simp only [List.set_cons_succ, List.getD_cons_succ, denoteMonomialFrom, ih (i + 1) k hk']
        have hi : i + 1 + k = i + (k + 1) := by
          exact (Nat.add_assoc i 1 k).trans (congrArg (fun n ↦ i + n) (Nat.add_comm 1 k))
        rw [hi]
        ring
  intro e k hk
  simpa [denoteMonomial] using aux e 0 k hk

/-! ### Evaluation -/

theorem eval_denoteMonomialFrom (x : List ℕ) :
    ∀ (e : MonomialCode) (i : ℕ),
      MvPolynomial.eval (fun j => ((x.getD j 0 : ℕ) : ℤ)) (denoteMonomialFrom i e) =
        evalMonomial e (x.drop i) := by
  intro e
  induction e with
  | nil => intro i; simp [denoteMonomialFrom]
  | cons a es ih =>
    intro i
    simp only [denoteMonomialFrom, map_mul, map_pow, eval_X, ih]
    by_cases hi : i < x.length
    · rw [List.drop_eq_getElem_cons hi]
      simp only [evalMonomial, List.getD_eq_getElem _ _ hi]
    · have hnil : x.drop i = [] := List.drop_eq_nil_of_le (le_of_not_gt hi)
      have hnil' : x.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil, hnil', List.getD_eq_default _ _ (le_of_not_gt hi)]
      simp only [evalMonomial, Nat.cast_zero]

/-- Evaluating the denotation agrees with `eval`, for every assignment list. Variables past
the end of the list are read as `0` on both sides. -/
theorem eval_denote (p : PolynomialCode) (x : List ℕ) :
    MvPolynomial.eval (fun i => ((x.getD i 0 : ℕ) : ℤ)) p.denote = p.eval x := by
  simp only [denote, PolynomialCode.eval]
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, map_add, map_mul, eval_C, ih]
    rw [denoteMonomial, eval_denoteMonomialFrom x t.2 0, List.drop_zero]

/-! ### Variables

An upper bound only. `arity` is the maximum exponent-vector length, so trailing zero
exponents inflate it; no minimal-arity statement is true for a permissive encoding.
-/

theorem vars_denoteMonomialFrom (e : MonomialCode) (i : ℕ) :
    (denoteMonomialFrom i e).vars ⊆ Finset.range (i + e.length) := by
  induction e generalizing i with
  | nil => simp [denoteMonomialFrom]
  | cons a es ih =>
    classical
    refine (vars_mul _ _).trans ?_
    refine Finset.union_subset ?_ ?_
    · refine (vars_pow _ _).trans ?_
      rw [vars_X]
      intro j hj
      simp only [Finset.mem_singleton] at hj
      simp [hj]
    · refine (ih (i + 1)).trans ?_
      simp only [List.length_cons]
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega

theorem vars_denoteMonomial (e : MonomialCode) :
    (denoteMonomial e).vars ⊆ Finset.range e.length := by
  have h := vars_denoteMonomialFrom e 0
  simpa [denoteMonomial] using h

theorem vars_sum_subset_of_le (n : ℕ) :
    ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, t.2.length ≤ n) →
      (ts.map fun t : ℤ × MonomialCode => C t.1 * denoteMonomial t.2).sum.vars ⊆
        Finset.range n := by
  classical
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
    intro hts
    simp only [List.map_cons, List.sum_cons]
    refine (vars_add_subset _ _).trans (Finset.union_subset ?_ ?_)
    · refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_)
      · simp only [vars_C]
        exact Finset.empty_subset _
      · exact (vars_denoteMonomial t.2).trans
          (Finset.range_mono (hts t (List.mem_cons_self ..)))
    · exact ih fun s hs => hts s (List.mem_cons_of_mem _ hs)

/-- The variables of a denotation are bounded by the arity. This is an **upper bound only**:
`arity` counts trailing zero exponents, which contribute no variables. -/
theorem vars_denote_subset (p : PolynomialCode) :
    p.denote.vars ⊆ Finset.range p.arity :=
  vars_sum_subset_of_le p.arity p.terms fun _ ht => length_le_arity ht

end

end PolynomialCode

end Hilbert10
