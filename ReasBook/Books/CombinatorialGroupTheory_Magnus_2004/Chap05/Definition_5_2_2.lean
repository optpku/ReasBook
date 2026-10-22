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

open GroupPresentation

section

variable {X : Type u} {F : Type v} [Group F]

local instance definition_5_2_2_decidableEq : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation conditions for a relator set in a free group with a chosen
basis.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`, the
  symmetrized relator family `R*`, and decompositions of one symmetrized relator into piece-words.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for expressing elements of `F`
  on the chosen basis, and `GroupPresentation.symmetrizedRelatorFamily` is the owner for the
  symmetrized relator family.
- `bridge/view`: `basis.repr '' R` transports the source relators to `FreeGroup X`, while the
  underlying cycle `q.1` of a `CyclicWord X` compares one symmetrized relator with the flattened
  concatenation of piece-words.

Domain sampling:
1. `FreeGroupBasis X F` is the chapter's owner abstraction for a chosen free basis.
2. `GroupPresentation.symmetrizedRelatorFamily` from Proposition `3-11-2` is the chapter owner
   for the symmetrized relator family `R*`.
3. `FreeGroupBasis.is_piece` from Definition `5-2-1` is the chapter owner for a piece word.
4. `CyclicWord X` is the owner abstraction for a symmetrized relator modulo cyclic permutation,
   and `List.flatten` is the natural concatenation owner for a finite list of piece-words.
-/

namespace FreeGroupBasis

/-- Definition 5-2-2: the relator set `R` satisfies the small-cancellation condition `C(p)` with
respect to `basis` if no symmetrized relator from `R*` is the concatenation of fewer than `p`
piece-words. -/
def condition_c (basis : FreeGroupBasis X F) (R : Set F) (p : ℕ) : Prop :=
  ∀ {q : CyclicWord X} (_ : q ∈ symmetrizedRelatorFamily (basis.repr '' R))
      {pieces : List (List (X × Bool))},
    (∀ piece ∈ pieces, basis.is_piece R piece) →
    pieces.length < p →
      q.1 ≠ (pieces.flatten : Cycle (X × Bool))

notation:55 "C(" p ")[" basis ", " R "]" => condition_c basis R p

end FreeGroupBasis

namespace FreeGroupBasis

/-- Under `C(p)`, no symmetrized relator from `R*` is the concatenation of fewer than `p`
piece-words. -/
theorem symmetrized_relator_ne_flatten_of_condition_c
    (basis : FreeGroupBasis X F) {R : Set F} {p : ℕ}
    (hR : C(p)[basis, R]) {q : CyclicWord X}
    (hq : q ∈ symmetrizedRelatorFamily (basis.repr '' R))
    {pieces : List (List (X × Bool))}
    (hpieces : ∀ piece ∈ pieces, basis.is_piece R piece)
    (hlen : pieces.length < p) :
    q.1 ≠ (pieces.flatten : Cycle (X × Bool)) :=
  hR hq hpieces hlen

end FreeGroupBasis

end
