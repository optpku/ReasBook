/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance definition_5_4_6_decidableEq : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation theory for relator sets in a free group with a chosen basis.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`, a word
  `s : List (X × Bool)`, and a relator `r ∈ R` represented by `s` followed by exactly `j`
  ordered piece-words.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
  basis, `basis.is_piece R` from Definition `5-2-1` is the chapter owner predicate for piece
  words, and `FreeGroup.toWord` is the canonical reduced-word owner for relators transported by
  `basis.repr`, while `Vector` is the canonical owner for an ordered family of exactly `j`
  pieces.
- `bridge/view`: `(basis.repr r).toWord` and `pieces.toList.flatten` express the textbook word
  decomposition by a literal reduced-word equality saying that the reduced word of `r` is the
  concatenation of the initial segment `s` with exactly `j` ordered piece-words.

Domain sampling:
1. `FreeGroupBasis X F` is the established Chapter `5` owner for relator data with a chosen basis.
2. `FreeGroupBasis.is_piece` from Definition `5-2-1` is the existing owner predicate for the
   piece-words `b₁, ..., bⱼ`.
3. `(basis.repr r).toWord` is the chapter's canonical reduced-word model of a relator `r`.
4. `Vector (List (X × Bool)) j` is the canonical owner for a finite ordered family of exactly
   `j` piece-words, avoiding a separate length-equality witness.
5. `List.flatten` on `pieces.toList` is the natural owner for concatenating those piece-words.

Primitive vs. derived:
- primitive source data: `basis`, `R`, `j`, the word `s`, a relator `r ∈ R`, and an ordered
  family of exactly `j` piece-words whose concatenation follows `s`;
- derived API: the specification theorem unpacking the existential data of a `j`-remnant.
-/

namespace FreeGroupBasis

/-- Definition 5-4-6: a word `s` is a `j`-remnant with respect to `R` and `basis` if some relator
`r ∈ R` is represented by the concatenated word `s b₁ ⋯ bⱼ`, where `b₁, ..., bⱼ` are pieces with
respect to `R`. -/
def is_j_remnant (basis : FreeGroupBasis X F) (R : Set F) (j : ℕ) (s : List (X × Bool)) : Prop :=
  ∃ r ∈ R, ∃ pieces : Vector (List (X × Bool)) j,
    (∀ piece ∈ pieces.toList, basis.is_piece R piece) ∧
      (basis.repr r).toWord = s ++ pieces.toList.flatten

-- Proof sketch: unfold `is_j_remnant`; the theorem is exactly the existential witness data in the
-- definition.
/-- A `j`-remnant is exactly a word that occurs as an initial segment of some relator from `R`,
with the remaining suffix decomposed into exactly `j` pieces. -/
theorem is_j_remnant_iff
    (basis : FreeGroupBasis X F) {R : Set F} {j : ℕ} {s : List (X × Bool)} :
    basis.is_j_remnant R j s ↔
      ∃ r ∈ R, ∃ pieces : Vector (List (X × Bool)) j,
        (∀ piece ∈ pieces.toList, basis.is_piece R piece) ∧
          (basis.repr r).toWord = s ++ pieces.toList.flatten := Iff.rfl

end FreeGroupBasis

end
