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

local instance lemma_5_9_1_decidableEq : DecidableEq X := Classical.decEq X

/-!
Primary domain: word-level small-cancellation estimates for cyclically reduced conjugates of
relators.

Layer triage:
- `source-facing`: a relator `r ∈ R` with a semi-reduced factorization `r = b₁ ⋯ bⱼ c`, where
  the `bᵢ` are pieces, together with a cyclically reduced conjugate `r'` and the maximal
  consecutive subword `c'` of `c` that still appears consecutively in the normal form of `r'`.
- `core/canonical`: `FreeGroupBasis X F` is the chapter owner for the chosen basis,
  `FreeGroupBasis.is_piece` and `C'(\lambda)[basis, R]` from Definition `5-2-1` are the owner
  notions for pieces and the small-cancellation hypothesis, `IsConj` is the owner relation for
  conjugacy, `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced normal
  forms, `SignedLetter X` is the project owner vocabulary for letters of `X^{±1}`, and
  `Vector (List (SignedLetter X)) j` is the chapter's canonical owner for an ordered family of
  exactly `j` piece-words.
- `bridge/view`: `basis.repr r` transports relators in `F` to the canonical free-group model
  `FreeGroup X`, while `List.IsInfix` is the list-level owner for “appears consecutively as a
  subword”.

Domain sampling:
1. `FreeGroupBasis.is_piece` is the established Chapter `5` owner predicate for piece words.
2. `C'(\lambda)[basis, R]` is the chapter owner for the small-cancellation inequality on pieces.
3. `IsConj` and `FreeGroup.IsCyclicallyReduced` are the owner predicates for the cyclically
   reduced conjugate `r'`.
4. `List.IsInfix` is the canonical list-level owner for consecutive subwords, so the maximality
   condition on `c'` should be phrased directly by two infix hypotheses plus a maximality bound on
   common infixes of `c` and `r'.toWord`.
5. `Vector (List (SignedLetter X)) j` from Definition `5-4-6` is the nearby chapter owner for an
   ordered family of exactly `j` piece-words, so the theorem should expose `j` and that `Vector`
   directly rather than re-encoding the same data as a plain `List` plus `pieces.length`.
6. `FreeGroupBasis.is_j_remnant` from Definition `5-4-6` is the nearby chapter owner for the
   initial-segment decomposition `s ++ pieces.toList.flatten`; the present lemma needs the
   source-facing suffix-oriented equality `pieces.toList.flatten ++ c`, so that orientation
   remains an explicit theorem hypothesis instead of a second local wrapper owner.

Primitive vs. derived:
- primitive public data: the basis `basis`, relator set `R`, parameter `lambda`, relator `r`,
  the number `j` of piece factors, the ordered piece family
  `pieces : Vector (List (SignedLetter X)) j`, the tail word `c`, the cyclically reduced
  conjugate `rPrime`, and the candidate maximal subword `cPrime`;
- derived API: the direct piece hypotheses on `pieces`, the source-facing factorization equality
  `(basis.repr r).toWord = pieces.toList.flatten ++ c`, the maximal-common-infix clauses for
  `cPrime`, and the final length inequality.
-/

namespace FreeGroupBasis

-- Proof sketch: use the `C'(\lambda)` estimate on each piece in the initial semi-reduced
-- factorization, compare the total deleted length with `j * \lambda * |r'|`, and use maximality
-- of `cPrime` together with the cyclically reduced conjugacy of `rPrime` to identify the
-- surviving consecutive letters of the tail `c` inside `rPrime.toWord`.
/-- Lemma 5-9-1: if `R` satisfies `C'(\lambda)` and `r ∈ R` has a semi-reduced factorization
`r = b₁ ⋯ bⱼ c` with each `bᵢ` a piece, then any maximal consecutive subword `cPrime` of the tail
`c` that still appears consecutively in the normal form of a cyclically reduced conjugate `rPrime`
of `r` has length strictly greater than `(1 - j \lambda) |rPrime|`, where `j` is the number of
piece factors. -/
theorem maximal_common_consecutive_subword_length_gt_of_condition_c_prime
    (basis : FreeGroupBasis X F) (R : Set F) (lambda : ℝ) {r : F}
    (hR : C'(lambda)[basis, R]) (hr : r ∈ R) (j : ℕ)
    {pieces : Vector (List (SignedLetter X)) j} {c : List (SignedLetter X)}
    (hpieces : ∀ piece ∈ pieces.toList, basis.is_piece R piece)
    (hfactor : (basis.repr r).toWord = pieces.toList.flatten ++ c)
    {rPrime : FreeGroup X} (hconj : IsConj rPrime (basis.repr r))
    (hrPrime_cyclic : FreeGroup.IsCyclicallyReduced rPrime.toWord)
    {cPrime : List (SignedLetter X)}
    (hcPrime_left : cPrime <:+: c) (hcPrime_right : cPrime <:+: rPrime.toWord)
    (hcPrime_max : ∀ ⦃t : List (SignedLetter X)⦄,
      t <:+: c → t <:+: rPrime.toWord → t.length ≤ cPrime.length) :
    (cPrime.length : ℝ) > (1 - (j : ℝ) * lambda) * (rPrime.toWord.length : ℝ) := sorry

end FreeGroupBasis

end
