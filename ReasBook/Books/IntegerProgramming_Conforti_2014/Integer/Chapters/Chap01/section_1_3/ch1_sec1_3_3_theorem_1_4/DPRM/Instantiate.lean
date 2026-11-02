module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolynomialCodeComp

/-!
# Specializing the initial variables of a code

Issue #12. This is the only substitution-like operation the project ships, and it is
simultaneously the computable step in the nonuniform-specialisation reduction (#35) and the
partial-evaluation primitive a future compiler would want.

## Design

A term is specialized by *evaluating its own initial segment*:

```lean
specializeTerm params t =
  (eval ⟨[(t.1, t.2.take params.length)]⟩ params, t.2.drop params.length)
```

The new coefficient is the old one with the parameter powers folded in, computed by reusing
`eval` itself, so no integer multiplication lemma is needed beyond what #9 already proved.
The variable shift is exactly `List.drop params.length`, term count and order are preserved,
and the encoding stays permissive.

`eval_instantiate` holds unconditionally — in particular for parameter lists longer than a
term's exponent vector, where the vector is entirely consumed and `drop` leaves nothing.
That is a consequence of the zero-extension convention from #8, not an extra hypothesis.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- Specialize one term: fold the parameter powers into the coefficient, and drop the
exponents that have been consumed. -/
def specializeTerm (params : List ℕ) (t : ℤ × MonomialCode) : ℤ × MonomialCode :=
  (eval ⟨[(t.1, t.2.take params.length)]⟩ params, t.2.drop params.length)

/-- Substitute `params` for the initial variables, shifting the remaining ones down. -/
def instantiate (p : PolynomialCode) (params : List ℕ) : PolynomialCode :=
  ⟨p.terms.map (specializeTerm params)⟩

@[simp] theorem eval_singleton (c : ℤ) (e : MonomialCode) (x : List ℕ) :
    eval ⟨[(c, e)]⟩ x = c * evalMonomial e x := by
  simp [eval]

/-! ### Evaluation -/

/-- Splitting an assignment splits a monomial's value: the exponents consumed by `params`
contribute a factor computed from `params` alone. Holds for every `e` and `params`, with no
length hypothesis — if `e` is shorter than `params` the second factor is `1`. -/
theorem evalMonomial_append_split (e : MonomialCode) (params w : List ℕ) :
    evalMonomial e (params ++ w) =
      evalMonomial (e.take params.length) params * evalMonomial (e.drop params.length) w := by
  induction params generalizing e with
  | nil => simp
  | cons a rest ih =>
    cases e with
    | nil => simp [evalMonomial]
    | cons ei es =>
      simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        evalMonomial, ih es]
      ring

/-- Instantiating and then evaluating is evaluating at the concatenated assignment. No
length hypotheses: the zero-extension convention of #8 makes this hold for every list. -/
theorem eval_instantiate (p : PolynomialCode) (params witnesses : List ℕ) :
    (p.instantiate params).eval witnesses = p.eval (params ++ witnesses) := by
  simp only [instantiate, eval, List.map_map]
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, specializeTerm,
      eval_singleton, evalMonomial_append_split t.2 params witnesses]
    ring

/-! ### Arity -/

theorem foldr_max_drop_le (k : ℕ) :
    ∀ (ts : List (ℤ × MonomialCode)) (N : ℕ), (∀ t ∈ ts, t.2.length ≤ N) →
      (ts.map fun t => ((t.2.drop k).length)).foldr max 0 ≤ N - k := by
  intro ts
  induction ts with
  | nil => intro _ _; simp
  | cons t ts ih =>
    intro N hts
    simp only [List.map_cons, List.foldr_cons]
    refine max_le ?_ (ih N fun s hs => hts s (List.mem_cons_of_mem _ hs))
    have := hts t (List.mem_cons_self ..)
    simp only [List.length_drop]
    omega

/-- Instantiating decreases the arity by the number of parameters supplied. An upper bound,
like every `arity` statement. -/
theorem arity_instantiate (p : PolynomialCode) (params : List ℕ) :
    (p.instantiate params).arity ≤ p.arity - params.length := by
  have h := foldr_max_drop_le params.length p.terms p.arity fun t ht => length_le_arity ht
  calc (p.instantiate params).arity
      = (p.terms.map fun t => (t.2.drop params.length).length).foldr max 0 := by
        simp [instantiate, arity, Function.comp_def, specializeTerm]
    _ ≤ p.arity - params.length := h

/-! ### Computability -/

theorem primrec₂_specializeTerm :
    Primrec₂ fun (params : List ℕ) (t : ℤ × MonomialCode) => specializeTerm params t := by
  have hparams : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.1 := Primrec.fst
  have hlen : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.1.length :=
    Primrec.list_length.comp hparams
  have hcoeff : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hexp : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have htake : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.2.take a.1.length :=
    Primrec.list_take.comp hlen hexp
  have hcode : Primrec fun a : List ℕ × (ℤ × MonomialCode) =>
      (⟨[(a.2.1, a.2.2.take a.1.length)]⟩ : PolynomialCode) :=
    primrec_mk.comp (Primrec.list_cons.comp (Primrec.pair hcoeff htake) (Primrec.const []))
  exact Primrec.pair (primrec₂_eval.comp hcode hparams)
    (Primrec.list_drop.comp hlen hexp)

theorem primrec₂_instantiate : Primrec₂ instantiate := by
  have hg : Primrec₂ fun (a : PolynomialCode × List ℕ) (t : ℤ × MonomialCode) =>
      specializeTerm a.2 t :=
    primrec₂_specializeTerm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h := Primrec.list_map (primrec_terms.comp Primrec.fst) hg
  exact (primrec_mk.comp h).of_eq fun _ => rfl

theorem computable₂_instantiate : Computable₂ instantiate := primrec₂_instantiate.to_comp

/-! ### Sanity checks

`x₀ ^ 2 + x₁ ^ 2 - 25` specialized at `x₀ := 3` becomes `9 + x₀ ^ 2 - 25`: the term count
and order are preserved, the first term collapses to a constant, and the surviving variable
has shifted down by one. The second example supplies more parameters than the polynomial has
variables, which is legal and leaves nothing.
-/

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate [3]).terms =
      [(9, []), (1, [2]), (-25, [])] := by decide

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate [3]).eval [4] = 0 := by
  decide

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate
      [3, 4, 7, 9]).arity = 0 := by
  decide

end PolynomialCode

end Hilbert10
