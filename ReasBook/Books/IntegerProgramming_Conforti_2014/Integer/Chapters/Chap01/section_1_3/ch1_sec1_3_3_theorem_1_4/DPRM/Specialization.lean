module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.ExistsCodeRepresents
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Instantiate
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.NatSolvable
public import Mathlib.Computability.Reduce

/-!
# From a representation to a reduction

Issue #35, the computational centrepiece — and the whole scope argument of the project in
one theorem. A relation with *any* polynomial representation many-one reduces to
`NatSolvable`, with **no DPRM content whatsoever**.

## Why the nonuniformity is fine

The target `R ≤₀ NatSolvable` is a proposition, so existential elimination may fix the
representing polynomial locally. **No uniform data-valued extractor is produced**: there is
deliberately no function from representations to codes here, and in particular nothing of
the shape `Nat.Partrec.Code → PolynomialCode` (see #29).

The reduction is `fun x => q.instantiate (List.ofFn x)`. It is computable in `x` because `q`
is a *constant* — chosen once, outside the reduction — and only `instantiate` has to be
computable. Note that fixing `q` needs no choice principle at all: eliminating an
existential into a `Prop` is constructive.

## Test rather than argument

The final example compiles a hand-written representation of "is a sum of two squares" all
the way to a many-one reduction, exercising #5, #10, #11, #12 and #13 end to end before any
of M4's cost is incurred.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- A list of known length is `List.ofFn` of the corresponding function. -/
theorem ofFn_getD_of_length_eq {l : List ℕ} {m : ℕ} (hl : l.length = m) :
    List.ofFn (fun i : Fin m => l.getD i 0) = l := by
  subst hl
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

/-- Roots may be taken in `List.ofFn` form at any length at least the arity. This is the one
place the conversion between root lists and `Fin`-indexed witnesses happens. -/
theorem hasNatRoot_iff_fin_of_arity_le {p : PolynomialCode} {m : ℕ} (h : p.arity ≤ m) :
    p.HasNatRoot ↔ ∃ y : Fin m → ℕ, p.eval (List.ofFn y) = 0 := by
  constructor
  · intro hp
    obtain ⟨x, hlen, hx⟩ := (hasNatRoot_iff p).mp hp
    have hll : (x ++ List.replicate (m - p.arity) 0).length = m := by
      simp only [List.length_append, List.length_replicate, hlen]
      omega
    refine ⟨fun i => (x ++ List.replicate (m - p.arity) 0).getD i 0, ?_⟩
    rw [ofFn_getD_of_length_eq hll, eval_append_replicate_zero]
    exact hx
  · rintro ⟨y, hy⟩
    exact ⟨List.ofFn y, hy⟩

/-- Assembling a `List.ofFn` from a `Fin`-indexed tuple is primitive recursive. -/
theorem primrec_ofFn {n : ℕ} : Primrec fun x : Fin n → ℕ => List.ofFn x :=
  Primrec.list_ofFn fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i)

end PolynomialCode

open PolynomialCode MvPolynomial

/-- **Representation to reduction, general arity.** A relation on `Fin n`-tuples that is
represented by *some* polynomial many-one reduces to `NatSolvable`.

The representation is an existential and stays one; nothing is extracted from it. -/
theorem representsNat_manyOneReducible_natSolvable' {n : ℕ} {R : (Fin n → ℕ) → Prop}
    (h : ∃ (m : ℕ) (p : MvPolynomial (Fin n ⊕ Fin m) ℤ), RepresentsNat p R) :
    R ≤₀ NatSolvable := by
  obtain ⟨m, p, hp⟩ := h
  obtain ⟨q, harity, hq⟩ := exists_code_representsNat hp
  refine ⟨fun x => q.instantiate (List.ofFn x),
    computable₂_instantiate.comp (Computable.const q) primrec_ofFn.to_comp, fun x => ?_⟩
  have harity' : (q.instantiate (List.ofFn x)).arity ≤ m := by
    refine le_trans (arity_instantiate q (List.ofFn x)) ?_
    simp only [List.length_ofFn]
    omega
  rw [hq x]
  rw [show NatSolvable (q.instantiate (List.ofFn x)) =
      (q.instantiate (List.ofFn x)).HasNatRoot from rfl,
    hasNatRoot_iff_fin_of_arity_le harity']
  exact exists_congr fun y => by rw [eval_instantiate]

/-- **Representation to reduction, unary.** Derived from the general form by supplying the
constant tuple; no auxiliary predicate on lists is introduced. -/
theorem representsNat_manyOneReducible_natSolvable {R : ℕ → Prop}
    (h : ∃ (m : ℕ) (p : MvPolynomial (Fin 1 ⊕ Fin m) ℤ),
      RepresentsNat p fun v : Fin 1 → ℕ => R (v 0)) :
    R ≤₀ NatSolvable := by
  obtain ⟨f, hf, hfR⟩ := representsNat_manyOneReducible_natSolvable' h
  have hconst : Primrec fun a : ℕ => (fun _ : Fin 1 => a) :=
    Primrec.fin_curry.mpr (show Primrec₂ fun (a : ℕ) (_ : Fin 1) => a from Primrec.fst)
  exact ⟨fun a => f fun _ => a, hf.comp hconst.to_comp, fun a => hfR fun _ => a⟩

/-! ### End-to-end test

A hand-written representation, compiled to a reduction. This exercises the whole M1–M2
pipeline — `RepresentsNat`, `exists_code`, `denote`, `instantiate`, `NatSolvable` — with no
DPRM content, which is the point of doing it now rather than after M4.
-/

/-- Being a sum of two squares is represented by `x₀ - y₀² - y₁²`. -/
theorem representsNat_sumTwoSquares :
    RepresentsNat (X (Sum.inl 0) - X (Sum.inr 0) ^ 2 - X (Sum.inr 1) ^ 2 :
        MvPolynomial (Fin 1 ⊕ Fin 2) ℤ)
      (fun v : Fin 1 → ℕ => ∃ a b : ℕ, v 0 = a ^ 2 + b ^ 2) := by
  intro v
  simp only [map_sub, map_pow, eval_X]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨![a, b], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl,
      Sum.elim_inr, hab]
    push_cast
    ring
  · rintro ⟨y, hy⟩
    refine ⟨y 0, y 1, ?_⟩
    simp only [Sum.elim_inl, Sum.elim_inr] at hy
    have : ((v 0 : ℕ) : ℤ) = ((y 0 ^ 2 + y 1 ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-- The compiled reduction: "is a sum of two squares" many-one reduces to Hilbert's tenth
problem over the naturals. -/
theorem sumTwoSquares_manyOneReducible_natSolvable :
    (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2) ≤₀ NatSolvable :=
  representsNat_manyOneReducible_natSolvable ⟨2, _, representsNat_sumTwoSquares⟩

end Hilbert10
