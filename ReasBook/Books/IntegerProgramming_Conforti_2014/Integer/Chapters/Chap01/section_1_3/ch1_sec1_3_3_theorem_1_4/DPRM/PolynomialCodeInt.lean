/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCode

/-!
# Evaluating an encoded polynomial at an integer assignment

Issue #28, first piece. The wire format's `eval` takes a *natural* assignment, because that is
what the natural-root problem needs. Hilbert asked about integer solutions, so the same code has
to be readable at an integer assignment too.

## The same recursion, one type up

`evalMonomialInt` and `evalInt` mirror `evalMonomial` and `eval` exactly: same shape, same
out-of-range convention (variables past the end of the assignment are `0`), same permissiveness.
Only the assignment's type changes. That is deliberate — the two evaluations agree on natural
assignments, `evalInt_map_natCast`, which is what lets the two solvability predicates be compared
rather than merely coexist.

## Computability is not proved here

`primrec₂_eval` exists because `NatSolvable`'s recursive enumerability needs it. The integer
analogue has no consumer yet: `rePred_intSolvable` is expected to follow from
`IntSolvable ≤₀ NatSolvable` and recursive enumerability of the natural version, since recursive
enumerability transfers along many-one reductions. If some later step does need
`Primrec₂ evalInt`, it should be added then — the sign handling it requires is real work, and
speculative work here is exactly what #28 says to avoid.

## Main results

* `Hilbert10.PolynomialCode.evalInt`
* `Hilbert10.PolynomialCode.evalInt_map_natCast` — the two evaluations agree under the cast
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- The value of a monomial at an integer assignment, by structural recursion on the exponent
vector and the assignment in parallel. Variables past the end of the assignment are taken to be
`0`, exactly as in `evalMonomial`. -/
def evalMonomialInt : MonomialCode → List ℤ → ℤ
  | [], _ => 1
  | e :: es, [] => (0 : ℤ) ^ e * evalMonomialInt es []
  | e :: es, v :: vs => v ^ e * evalMonomialInt es vs

/-- The value of an encoded polynomial at an integer assignment. -/
def evalInt (p : PolynomialCode) (x : List ℤ) : ℤ :=
  (p.terms.map fun t => t.1 * evalMonomialInt t.2 x).sum

@[simp] theorem evalMonomialInt_nil (x : List ℤ) : evalMonomialInt [] x = 1 := rfl

@[simp] theorem evalInt_mk_nil (x : List ℤ) : evalInt ⟨[]⟩ x = 0 := rfl

@[simp] theorem evalInt_mk_cons (t : ℤ × MonomialCode) (ts : List (ℤ × MonomialCode))
    (x : List ℤ) :
    evalInt ⟨t :: ts⟩ x = t.1 * evalMonomialInt t.2 x + evalInt ⟨ts⟩ x := by
  simp [evalInt]

/-! ### Agreement with the natural evaluation -/

theorem evalMonomialInt_map_natCast :
    ∀ (m : MonomialCode) (x : List ℕ),
      evalMonomialInt m (x.map (Nat.cast : ℕ → ℤ)) = evalMonomial m x
  | [], _ => rfl
  | _ :: es, [] => by
    have ih : evalMonomialInt es [] = evalMonomial es [] := by
      simpa using evalMonomialInt_map_natCast es []
    simp only [List.map_nil, evalMonomialInt, evalMonomial, ih]
  | _ :: es, v :: vs => by
    simp only [List.map_cons, evalMonomialInt, evalMonomial,
      evalMonomialInt_map_natCast es vs]

/-- **The two evaluations agree on natural assignments.** This is what makes the natural and
integer formulations comparable: a natural root is an integer root of the same code. -/
theorem evalInt_map_natCast (p : PolynomialCode) (x : List ℕ) :
    evalInt p (x.map (Nat.cast : ℕ → ℤ)) = eval p x := by
  simp only [evalInt, eval, evalMonomialInt_map_natCast]


/-! ### Normalising an integer assignment

The two solvability predicates quantify over arbitrary-length lists, while a block layout needs a
fixed length. These are the integer analogues of the natural-root padding lemmas, added because
the difference substitution consumes them — nothing more general. -/

theorem evalMonomialInt_append_zeros (e : MonomialCode) (x z : List ℤ) (hz : ∀ v ∈ z, v = 0) :
    evalMonomialInt e (x ++ z) = evalMonomialInt e x := by
  induction e generalizing x z with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil =>
      cases z with
      | nil => rfl
      | cons c cs =>
        obtain rfl : c = 0 := hz c (by simp)
        have hrec : evalMonomialInt es cs = evalMonomialInt es [] := by
          simpa using ih [] cs fun v hv => hz v (by simp [hv])
        simp [evalMonomialInt, hrec]
    | cons v vs =>
      simp only [List.cons_append, evalMonomialInt]
      rw [ih vs z hz]

theorem evalInt_append_zeros (p : PolynomialCode) (x z : List ℤ) (hz : ∀ v ∈ z, v = 0) :
    p.evalInt (x ++ z) = p.evalInt x := by
  simp only [evalInt]
  congr 1
  exact List.map_congr_left fun t _ => by rw [evalMonomialInt_append_zeros t.2 x z hz]

theorem evalInt_append_replicate_zero (p : PolynomialCode) (x : List ℤ) (k : ℕ) :
    p.evalInt (x ++ List.replicate k 0) = p.evalInt x :=
  p.evalInt_append_zeros x _ fun _ hv => List.eq_of_mem_replicate hv

theorem evalMonomialInt_append_of_length_le {e : MonomialCode} {x : List ℤ}
    (h : e.length ≤ x.length) (y : List ℤ) :
    evalMonomialInt e (x ++ y) = evalMonomialInt e x := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp at h
    | cons v vs =>
      simp only [List.cons_append, evalMonomialInt]
      rw [ih (by simpa using h)]

theorem evalInt_append_of_arity_le {p : PolynomialCode} {x : List ℤ} (h : p.arity ≤ x.length)
    (y : List ℤ) : p.evalInt (x ++ y) = p.evalInt x := by
  simp only [evalInt]
  congr 1
  exact List.map_congr_left fun t ht => by
    rw [evalMonomialInt_append_of_length_le (Nat.le_trans (length_le_arity ht) h)]

/-- **Every integer assignment normalises to any length at least the arity.** Pad with zeros,
then truncate; both steps are invisible to the value. -/
theorem exists_length_eq_evalInt_eq (p : PolynomialCode) (x : List ℤ) {m : ℕ}
    (hm : p.arity ≤ m) : ∃ y : List ℤ, y.length = m ∧ p.evalInt y = p.evalInt x := by
  refine ⟨(x ++ List.replicate m 0).take m, ?_, ?_⟩
  · simp only [List.length_take, List.length_append, List.length_replicate]
    omega
  · have hsplit : (x ++ List.replicate m 0)
        = (x ++ List.replicate m 0).take m ++ (x ++ List.replicate m 0).drop m := by
      simp
    have hlen : p.arity ≤ ((x ++ List.replicate m 0).take m).length := by
      simp only [List.length_take, List.length_append, List.length_replicate]
      omega
    calc p.evalInt ((x ++ List.replicate m 0).take m)
        = p.evalInt ((x ++ List.replicate m 0).take m ++ (x ++ List.replicate m 0).drop m) :=
          (evalInt_append_of_arity_le hlen _).symm
      _ = p.evalInt (x ++ List.replicate m 0) := by rw [← hsplit]
      _ = p.evalInt x := evalInt_append_replicate_zero p x _

/-- The special case used by the difference substitution. -/
theorem exists_length_eq_arity_evalInt_eq (p : PolynomialCode) (x : List ℤ) :
    ∃ y : List ℤ, y.length = p.arity ∧ p.evalInt y = p.evalInt x :=
  exists_length_eq_evalInt_eq p x (Nat.le_refl _)

end PolynomialCode

end Hilbert10
