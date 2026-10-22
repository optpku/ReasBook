/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_11_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

/- Layer triage:
- `source-facing`: the Section `11` finite reduction chain
  `u₀ a₀ u₁ a₁ ... uₙ aₙ`, the chosen decompositions
  `uᵢ = pᵢ⁻¹ * hᵢ * qᵢ`, the source comparison `A pᵢ < A qᵢ`, and the bridge steps between adjacent
  syllables.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form data
  `NormalWord.Transversal φ`, the owner length `syllableLength d`, and the canonical subgroup
  embeddings `(base φ).range` and `(of ν).range`.
- `bridge/view`: finite indexing by `Fin (n + 1)` and `Fin n`, together with the source-facing
  predicates `IsSection11BridgeStep` and `IsSection11ReductionChain`, which record the Section
  `11` chain directly over the canonical owner without exposing auxiliary chosen bridge words or an
  arbitrary order-key model.

Domain sampling:
1. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner declaration for
   the Section `11` length.
2. `(base φ).range` is the canonical realization of the amalgamated subgroup `A`.
3. `(of ν).range` is the canonical realization of the factor subgroup `H_ν`.
4. Neighboring Section `11` files such as Lemmas `1-11-7` and `1-11-19` already state the
   textbook assertions directly over `PushoutI φ`, so this file should reuse that owner instead of
   introducing a parallel sequence package. The right abstraction layer here is the reduction-chain
   predicate itself, not the chosen list of bridge syllables or a comparison encoded through
   `orderKey`.

Primitive vs. derived:
the primitive public data are the actual reduction entries `uᵢ`, the bridge entries `aᵢ`, the
chosen decomposition terms `pᵢ`, `hᵢ`, `qᵢ`, and the source comparison relation expressing
`A pᵢ < A qᵢ`. The existence of bridge-word realizations between adjacent syllables is auxiliary
chain structure and therefore belongs inside a reduction-chain predicate rather than as public
chosen data. The terminal factorizations, the common terminal factor outside `(base φ).range`, and
the bound by the total product are derived theorem-level conclusions. -/

variable {n : ℕ}

/-- The total product of the finite Section `11` chain `u₀ a₀ u₁ a₁ ... uₙ aₙ`. -/
abbrev interleavedProd
    (u a : Fin (n + 1) → PushoutI φ) : PushoutI φ :=
  (List.ofFn fun i : Fin (n + 1) ↦ u i * a i).prod

/-- One bridge step in a Section `11` reduction chain: the connecting factor `a` is represented by
a finite word whose syllables all have length `1` or lie in the amalgamated subgroup, and every
terminal segment preserves the length of the next syllable `u`. -/
def IsSection11BridgeStep
    (d : Transversal φ) (u a : PushoutI φ) : Prop :=
  ∃ bridge : List (PushoutI φ),
    a = bridge.prod ∧
      ∀ j : Fin bridge.length,
        (syllableLength d (bridge.get j) = 1 ∨ bridge.get j ∈ (base φ).range) ∧
          syllableLength d (bridge.get j) ≤ syllableLength d u ∧
          syllableLength d ((bridge.drop j.1).prod * u) = syllableLength d u

/-- The source-facing Section `11` reduction-chain hypotheses on the interleaved word
`u₀ a₀ u₁ a₁ ... uₙ aₙ`.

The parameter `A_lt` records the textbook comparison `A p < A q` between the terminal fragments of
one syllable decomposition. -/
def IsSection11ReductionChain
    (d : Transversal φ) (A_lt : PushoutI φ → PushoutI φ → Prop)
    (u a p h q : Fin (n + 1) → PushoutI φ) : Prop :=
  (∀ i : Fin (n + 1),
    u i = (p i)⁻¹ * h i * q i ∧
      syllableLength d (p i) = syllableLength d (q i) ∧
      syllableLength d (h i) ≤ 1) ∧
  (∀ i : Fin n, IsSection11BridgeStep d (u i.succ) (a i.castSucc)) ∧
  a (Fin.last n) ∈ (base φ).range ∧
  (∀ i : Fin n,
    syllableLength d (u i.castSucc) ≤
        syllableLength d (u i.castSucc * a i.castSucc * u i.succ) ∧
      syllableLength d (u i.succ) ≤
        syllableLength d (u i.castSucc * a i.castSucc * u i.succ)) ∧
  (∀ i : Fin n,
    A_lt (p i.castSucc) (q i.castSucc) →
      syllableLength d (u i.succ) <
        syllableLength d (u i.castSucc * a i.castSucc * u i.succ)) ∧
  ∀ i : Fin n,
    A_lt (q i.succ) (p i.succ) →
      syllableLength d (u i.castSucc) <
        syllableLength d (u i.castSucc * a i.castSucc * u i.succ)

variable (d : Transversal φ) (A_lt : PushoutI φ → PushoutI φ → Prop)
variable (u a p h q : Fin (n + 1) → PushoutI φ)

/-- Lemma 1-11-3 (1): if `A p_t < A q_t` and `|h_t| = 0`, then the full word factors as
`z * q_t * a_t` for some prefix `z`. -/
-- Proof sketch: argue by induction on the truncated reduction chain. In the terminal case
-- `A p_t < A q_t` with `|h_t| = 0`, the last decomposition collapses the middle syllable, and the
-- preceding inductive control leaves only a residual prefix multiplying `q_t a_t`.
theorem exists_prefix_mul_last_q_mul_last_a_of_terminal_drop_case
    (hchain : IsSection11ReductionChain d A_lt u a p h q)
    (hdrop : A_lt (p (Fin.last n)) (q (Fin.last n)))
    (hhlast : syllableLength d (h (Fin.last n)) = 0) :
    ∃ z : PushoutI φ,
      interleavedProd u a = z * q (Fin.last n) * a (Fin.last n) :=
  sorry

/-- Lemma 1-11-3 (2): outside the exceptional terminal drop case, the last syllable and the full
word both admit terminal representatives in a common `H_ν \ A`. -/
-- Proof sketch: induct on the truncated reduction chain and exclude the terminal drop case. The
-- remaining normal-form analysis keeps one non-base terminal syllable visible in the last factor,
-- both for `u_t` and for the total word.
theorem exists_terminal_syllables_outside_amalgamated_unless_terminal_drop_case
    (hchain : IsSection11ReductionChain d A_lt u a p h q)
    (hdrop :
      ¬ (A_lt (p (Fin.last n)) (q (Fin.last n)) ∧
          syllableLength d (h (Fin.last n)) = 0)) :
    ∃ ν : ι,
      ∃ x x₁ z z₁ : PushoutI φ,
        x ∈ (of ν).range ∧
          x ∉ (base φ).range ∧
          x₁ ∈ (of ν).range ∧
          x₁ ∉ (base φ).range ∧
          u (Fin.last n) = z * x * q (Fin.last n) ∧
          interleavedProd u a = z₁ * x₁ * q (Fin.last n) * a (Fin.last n) :=
  sorry

/-- Lemma 1-11-3 (3): if `A q_t < A p_t` and `|h_t| = 1`, then the full word factors as
`z₁ * h_t * q_t * a_t` for some prefix `z₁`. -/
-- Proof sketch: the reverse terminal inequality forces the last surviving non-base syllable to be
-- exactly `h_t`. Combining this with the inductive description of the preceding prefix gives the
-- displayed factorization of the total word.
theorem exists_prefix_mul_last_h_mul_last_q_mul_last_a_of_terminal_reverse_case
    (hchain : IsSection11ReductionChain d A_lt u a p h q)
    (hreverse : A_lt (q (Fin.last n)) (p (Fin.last n)))
    (hhlast : syllableLength d (h (Fin.last n)) = 1) :
    ∃ z₁ : PushoutI φ,
      interleavedProd u a = z₁ * h (Fin.last n) * q (Fin.last n) * a (Fin.last n) :=
  sorry

/-- Lemma 1-11-3 (4): every syllable length `|u_i|` is bounded above by the length of the total
word. -/
-- Proof sketch: prove the bound simultaneously with the terminal factorization statements by
-- induction on the truncated reduction chains. At each step, the Section `11` comparison
-- hypotheses bound the new adjacent syllables by the longer partial product, and the induction
-- carries that estimate to the total word.
theorem syllableLength_le_interleavedProd_of_all_entries
    (hchain : IsSection11ReductionChain d A_lt u a p h q)
    (i : Fin (n + 1)) :
    syllableLength d (u i) ≤ syllableLength d (interleavedProd u a) :=
  sorry

end

end Monoid.PushoutI
