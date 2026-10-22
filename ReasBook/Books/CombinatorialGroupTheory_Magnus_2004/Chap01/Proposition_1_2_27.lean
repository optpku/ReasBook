/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

namespace FreeGroupBasis

variable {ι : Type v} {F : Type u} [Group F] [Finite ι]

/-
Primary domain: finite-rank free groups with a chosen basis and source-facing basis-extension
statements measured by the ambient basis length.

Layer triage:
- `source-facing`: a nonempty subset `A` contained in some free basis extends to a basis `A ∪ B`
  with the complementary basis elements no longer than elements of `A`.
- `core/canonical`: `FreeGroupBasis ι F` is the owner abstraction for the ambient basis and its
  length function, while `IsFreeGroupBasis` is the chapter owner predicate for subset-style bases.
- `bridge/view`: `FreeGroupBasis.isFreeGroupBasis_range` is the chapter bridge from an indexed
  basis to the corresponding subset basis.

Domain sampling:
1. `FreeGroupBasis.repr` is the canonical bridge from the ambient free group to the reduced-word
   model on the chosen basis.
2. `FreeGroupBasis.isFreeGroupBasis_range` in `Definition_1_1_1` is the chapter owner bridge from
   a basis to the subset-style predicate `IsFreeGroupBasis`.
3. `finset_isFreeGroupBasis_iff_card_and_closure_eq_top` in `Proposition_1_2_9` is the owner-side
   finite-rank basis criterion used downstream when the resulting basis is finite.

Primitive vs. derived:
the primitive public data are the chosen finite basis `basis`, the subset `A`, its nonemptiness,
and the hypothesis that `A` lies in some free basis. The completion set `B`, the basis property of
`A ∪ B`, and the accompanying length bounds are derived source-facing output.
-/

-- Keep the `DecidableEq` requirement local: it is only needed to form `FreeGroup.norm` on the
-- reduced words `basis.repr x`, and it should not leak into the public theorem interface.
local instance proposition_1_2_27_decidableEq : DecidableEq ι := Classical.decEq ι

/-- Proposition 1-2-27: let `basis : FreeGroupBasis ι F` be a finite basis of the free group `F`,
and let `A` be a nonempty subset of `F` contained in some free basis. Then `F` has a basis
`A ∪ B` such that every element of `B` has `basis`-length bounded by the `basis`-length of some
element of `A`. This is the source-faithful formulation of the statement that the longest element
of `B` is no longer than the longest element of `A`. -/
-- Layer: source-facing basis-extension statement.
-- Core/canonical owner abstractions: `FreeGroupBasis` for the ambient word-length function and
-- `IsFreeGroupBasis` for the resulting basis `A ∪ B`.
-- Proof sketch: start from a basis containing `A`, Nielsen-reduce the complementary part while
-- keeping the maximal `basis`-length on `A` unchanged, and then use the chapter criterion that a
-- generating `N`-reduced set in a finite-rank free group must consist of basis elements of length
-- `1`; any longer complementary element would contradict the chosen minimal-length completion.
theorem exists_completion_with_length_bound (basis : FreeGroupBasis ι F) (A : Set F)
    (hA : A.Nonempty) (hpart : ∃ S : Set F, A ⊆ S ∧ IsFreeGroupBasis S) :
    ∃ B : Set F, IsFreeGroupBasis (A ∪ B) ∧
      ∀ b ∈ B, ∃ a ∈ A, (basis.repr b).norm ≤ (basis.repr a).norm := sorry

end FreeGroupBasis

end
