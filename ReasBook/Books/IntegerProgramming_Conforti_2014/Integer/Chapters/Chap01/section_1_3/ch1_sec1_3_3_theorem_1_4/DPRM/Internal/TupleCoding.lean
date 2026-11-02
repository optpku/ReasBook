module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ExpDioph
public import Mathlib.Computability.Partrec

/-!
# Coding a finite tuple as one natural number

Issue #23, second part, and nothing more: a machine consumes one natural number, while an
`n`-ary predicate receives a `Fin n → ℕ`. Bridging that needs an encoding which is at once
computable to invert and Diophantine to impose.

## Why it is written out rather than imported

`Primcodable (Fin n → ℕ)` already provides an encoding, but an opaque one: its graph is not
known to be Diophantine, and assuming it were would beg the question. The temptation to reach
for "`Dioph` is closed under computable preimages" is worse — that statement *is* DPRM, so using
it here would be circular. So the encoding is an explicit right-associated `Nat.pair`, whose
graph is Diophantine because `Nat.pair` is piecewise polynomial.

Only two properties are needed, and they point in opposite directions:

* `tupleDecode_tupleCode` with `computable_tupleDecode` — the decoder is computable, which is
  what transports a recursively enumerable predicate on tuples to one on `ℕ`;
* `expDioph_tupleCode_graph` — the encoder's graph is exponential Diophantine, which is what
  transports the resulting Diophantine condition back to tuples.

This is deliberately not a coded-sequence library: there is no lookup, no length, no
concatenation, and `n` is fixed in every statement.

## Main results

* `Hilbert10.tupleDecode_tupleCode`, `Hilbert10.computable_tupleDecode`
* `Hilbert10.expDioph_tupleCode_graph`
-/

@[expose] public section

namespace Hilbert10

variable {α : Type}

/-! ### The encoding -/

/-- A tuple as one number, pairing to the right. -/
def tupleCode : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, v => Nat.pair (v 0) (tupleCode fun i => v i.succ)

/-- Drop the first `i` components of a code. -/
def tupleDrop : ℕ → ℕ → ℕ
  | 0, z => z
  | i + 1, z => tupleDrop i z.unpair.2

/-- The decoder: component `i` is the first half of what is left after dropping `i`. -/
def tupleDecode (n : ℕ) (z : ℕ) : Fin n → ℕ := fun i => (tupleDrop i z).unpair.1

@[simp] theorem tupleCode_zero (v : Fin 0 → ℕ) : tupleCode v = 0 := rfl

theorem tupleCode_succ {n : ℕ} (v : Fin (n + 1) → ℕ) :
    tupleCode v = Nat.pair (v 0) (tupleCode fun i => v i.succ) := rfl

/-- **The round trip.** -/
theorem tupleDecode_tupleCode : ∀ {n : ℕ} (v : Fin n → ℕ), tupleDecode n (tupleCode v) = v
  | 0, v => funext fun i => i.elim0
  | n + 1, v => by
    funext i
    refine Fin.cases ?_ ?_ i
    · change (tupleDrop 0 (tupleCode v)).unpair.1 = v 0
      rw [tupleCode_succ]
      simp [tupleDrop]
    · intro j
      change (tupleDrop ((j : ℕ) + 1) (tupleCode v)).unpair.1 = v j.succ
      rw [tupleCode_succ]
      have : tupleDrop ((j : ℕ) + 1) (Nat.pair (v 0) (tupleCode fun i => v i.succ))
          = tupleDrop (j : ℕ) (tupleCode fun i => v i.succ) := by
        simp [tupleDrop]
      rw [this]
      exact congrFun (tupleDecode_tupleCode (fun i => v i.succ)) j

/-! ### The decoder is computable -/

theorem computable_tupleDrop (i : ℕ) : Computable (tupleDrop i) := by
  induction i with
  | zero => exact Computable.id
  | succ i ih =>
    have h : Computable fun z : ℕ => z.unpair.2 :=
      Computable.snd.comp (Primrec.unpair.to_comp)
    exact (ih.comp h).of_eq fun z => rfl

/-- The decoder at a fixed arity is computable. Transferred through the `List.Vector`
equivalence that `Primcodable (Fin n → ℕ)` is built from. -/
theorem computable_tupleDecode (n : ℕ) : Computable (tupleDecode n) := by
  have h1 : Computable fun z : ℕ =>
      List.Vector.ofFn (fun i : Fin n => (tupleDrop i z).unpair.1) :=
    Computable.vector_ofFn fun i => Computable.fst.comp
      (Primrec.unpair.to_comp.comp (computable_tupleDrop i))
  have h2 := (Primrec.of_equiv_symm (e := (Equiv.vectorEquivFin ℕ n).symm)).to_comp.comp h1
  refine h2.of_eq fun z => ?_
  funext i
  simp [Equiv.vectorEquivFin, tupleDecode]

/-! ### The encoder's graph is exponential Diophantine -/

/-- `Nat.pair` is piecewise polynomial, so its graph is a union of two polynomial conditions. -/
theorem expDioph_pair (a b c : ExpTerm α) :
    ExpDioph {v : α → ℕ | Nat.pair (a.eval v) (b.eval v) = c.eval v} := by
  refine (ExpDioph.or
    (ExpDioph.and (ExpDioph.of_lt (s := a) (t := b))
      (ExpDioph.of_eq (s := c) (t := .add (.mul b b) a)))
    (ExpDioph.and (ExpDioph.of_le (s := b) (t := a))
      (ExpDioph.of_eq (s := c) (t := .add (.add (.mul a a) a) b)))).congr fun v => ?_
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, ExpTerm.eval, Nat.pair]
  by_cases h : a.eval v < b.eval v
  · rw [if_pos h]
    constructor
    · rintro (⟨-, hc⟩ | ⟨hle, -⟩)
      · exact hc.symm
      · omega
    · intro hc
      exact Or.inl ⟨h, hc.symm⟩
  · rw [if_neg h]
    constructor
    · rintro (⟨hlt, -⟩ | ⟨-, hc⟩)
      · omega
      · exact hc.symm
    · intro hc
      exact Or.inr ⟨by omega, hc.symm⟩

/-- **The encoder's graph.** The tuple sits on `Fin n` variables and its code on the extra one;
the induction adds one existential per component, which is `finite existential composition` and
not a quantifier over anything the problem supplies. -/
theorem expDioph_tupleCode_graph :
    ∀ n : ℕ, ExpDioph {u : (Fin n ⊕ Unit) → ℕ |
      tupleCode (fun i => u (.inl i)) = u (.inr ())}
  | 0 => by
    refine (ExpDioph.of_eq (s := .const 0) (t := .var (.inr ()))).congr fun u => ?_
    simp [Set.mem_setOf_eq, ExpTerm.eval]
  | n + 1 => by
    -- `f` places the induction hypothesis' variables inside the larger block
    let f : Fin n ⊕ Unit → (Fin (n + 1) ⊕ Unit) ⊕ Unit :=
      Sum.elim (fun i => .inl (.inl i.succ)) (fun _ => .inr ())
    refine (ExpDioph.congr (ExpDioph.ex (ExpDioph.and
      (ExpDioph.reindex (expDioph_tupleCode_graph n) f)
      (expDioph_pair (.var (.inl (.inl 0))) (.var (.inr ())) (.var (.inl (.inr ()))))))
      fun u => ?_)
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Function.comp, ExpTerm.eval, f,
      Sum.elim_inl, Sum.elim_inr, tupleCode_succ]
    constructor
    · rintro ⟨w, h1, h2⟩
      rw [← h2, h1]
    · intro h
      exact ⟨fun _ => tupleCode (fun i : Fin n => u (.inl i.succ)), rfl, by rw [← h]⟩

end Hilbert10
