/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.NormalForm
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Specialization
public import Mathlib.Computability.RE

/-!
# Diophantine implies recursively enumerable

Issue #14, the cheap half of the eventual `Dioph ↔ REPred` characterisation, and the
integration test for M1 and M2 together: it is the first result that needs the finite
normal form (#6), the wire format (#8), its computability (#9) and the coding theorem (#11)
to fit together.

## Architecture

Both endpoints are specializations of one closure lemma,

```lean
ComputablePred.rePred_exists : ComputablePred P → REPred fun a => ∃ b, P (a, b)
```

which is independently useful and has nothing to do with polynomials: projecting a
decidable predicate along an existential over any `Primcodable` type gives an RE predicate.
It is proved by searching the *encodings* of witnesses with `Nat.rfindOpt`, so the search
enumerates encoded witness tuples directly rather than boxes of naturals, and invalid codes
map to `none` rather than to some default.

## Why `decode` and not `decode₂`

The search needs a computable surjection onto candidate witnesses, and rechecks `P` on every
one, so canonicality of codes is irrelevant. `decode₂` additionally rejects non-canonical
codes — what an *injective* enumeration needs — which would add machinery without
strengthening soundness or completeness. Completeness here is exactly
`Encodable.encodek : decode (encode b) = some b`.
-/

@[expose] public section

namespace Hilbert10

open MvPolynomial PolynomialCode

/-- Projecting a decidable predicate along an existential over a `Primcodable` type yields a
recursively enumerable predicate.

The search runs over encodings of witnesses: at stage `n` it decodes `n`, and succeeds if it
decodes to a witness satisfying `P`. Completeness comes from `Encodable.encodek`, since the
witness `b` is found at stage `encode b`. -/
theorem ComputablePred.rePred_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {P : α × β → Prop} (hP : ComputablePred P) : REPred fun a => ∃ b, P (a, b) := by
  obtain ⟨_inst, hPc⟩ := hP
  classical
  have hg : Computable₂ fun (a : α) (n : ℕ) =>
      (Encodable.decode (α := β) n).bind fun b => if P (a, b) then some b else none := by
    refine Computable.option_bind (Computable.decode.comp Computable.snd) ?_
    have hdec : Computable fun z : (α × ℕ) × β => decide (P (z.1.1, z.2)) :=
      hPc.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
    exact (Computable.cond hdec (Computable.option_some.comp Computable.snd)
      (Computable.const none)).of_eq fun z => by by_cases h : P (z.1.1, z.2) <;> simp [h]
  refine ((Partrec.rfindOpt hg).dom_re).of_eq fun a => ?_
  simp only [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, b, hb⟩
    cases hd : Encodable.decode (α := β) n with
    | none =>
      rw [hd] at hb
      simp at hb
    | some c =>
      rw [hd] at hb
      by_cases hP : P (a, c)
      · exact ⟨c, hP⟩
      · simp only [Option.bind, if_neg hP] at hb
        simp at hb
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, b, by simp [Encodable.encodek, hb]⟩

/-- Evaluating a fixed code at a pair of `Fin`-indexed tuples is a computable predicate. -/
theorem computablePred_eval_ofFn (q : PolynomialCode) (n m : ℕ) :
    ComputablePred fun z : (Fin n → ℕ) × (Fin m → ℕ) =>
      q.eval (List.ofFn z.1 ++ List.ofFn z.2) = 0 := by
  have hlist : Primrec fun z : (Fin n → ℕ) × (Fin m → ℕ) => List.ofFn z.1 ++ List.ofFn z.2 :=
    Primrec.list_append.comp (primrec_ofFn.comp Primrec.fst) (primrec_ofFn.comp Primrec.snd)
  exact PrimrecPred.computablePred
    (PrimrecRel.comp Primrec.eq (primrec₂_eval.comp (Primrec.const q) hlist) (Primrec.const 0))

/-- **Diophantine implies recursively enumerable.** -/
theorem Dioph.rePred {n : ℕ} {R : (Fin n → ℕ) → Prop} (h : Dioph {x : Fin n → ℕ | R x}) :
    REPred R := by
  obtain ⟨m, p, hp⟩ := (dioph_iff_exists_fin_mvPolynomial R).mp h
  obtain ⟨q, _, hq⟩ := exists_code_representsNat hp
  refine (ComputablePred.rePred_exists (computablePred_eval_ofFn q n m)).of_eq fun x => ?_
  exact (hq x).symm

/-- Evaluating a code at an assignment is a computable predicate, jointly in both. -/
theorem computablePred_eval : ComputablePred fun z : PolynomialCode × List ℕ =>
    z.1.eval z.2 = 0 :=
  PrimrecPred.computablePred
    (PrimrecRel.comp Primrec.eq (primrec₂_eval.comp Primrec.fst Primrec.snd) (Primrec.const 0))

/-- **Hilbert's tenth problem over the naturals is recursively enumerable.** -/
theorem rePred_natSolvable : REPred NatSolvable :=
  (ComputablePred.rePred_exists computablePred_eval).of_eq fun _ => Iff.rfl

end Hilbert10
