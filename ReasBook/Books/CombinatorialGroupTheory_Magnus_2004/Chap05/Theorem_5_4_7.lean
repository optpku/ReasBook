/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

section

variable {X : Type u}

open FreeGroupBasis GroupPresentation

local instance theorem_5_4_7_decidableEq : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: word-level Greendlinger alternatives for classical small-cancellation pairs.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial element `w ∈ N`, and a
  cyclically reduced conjugate `w*` whose cyclic word either lies in the symmetrized relator
  family `R*` or has a decomposition `u₁ s₁ ⋯ uₙ sₙ` with each `sₖ` an `i(sₖ)`-remnant
  satisfying the displayed curvature inequality.
- `core/canonical`: `FreeGroup X` is the owner for reduced words, `Subgroup.normalClosure R` is
  the owner for `N`, `IsConj` is the owner relation for conjugacy,
  `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclic reduction,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family,
  and `List.IsSuffix` / `List.IsInfix` are the canonical list owners for contiguous word
  occurrence and the remaining suffix after such an occurrence,
  and
  `FreeGroupBasis.is_j_remnant` is the chapter owner for the remnant condition attached to each
  segment.
- `bridge/view`: the reusable predicate
  `List.HasOrderedDisjointSublists` packages the repeated source pattern of successive disjoint
  ordered subword occurrences by recursively choosing the suffix left after each segment, and
  the reusable predicate
  `FreeGroup.HasGreendlingerRemnantConfiguration R p q` packages the source-facing decomposition
  as a single `Prop`, using only the direct witness data `(uₖ, sₖ, i(sₖ))` for each segment and
  the rational `List.sum` of the corresponding curvature terms.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the normal closure `N`.
2. `FreeGroup.IsCyclicallyReduced` and `IsConj` are the owner predicates for the cyclically
   reduced conjugate `w*`.
3. `GroupPresentation.symmetrizedRelatorFamily` from Proposition `3-11-2` is the owner for the
   cyclic-word relator family `R*`.
4. `FreeGroupBasis.is_j_remnant` from Definition `5-4-6` is the chapter owner for the statement
   that a word is an `i(sₖ)`-remnant.
5. `C(p)[basis, R]` and `T(q)[basis, R]` from Definitions `5-2-2` and `5-2-3` are the owner
   hypotheses for the small-cancellation assumptions in the theorem.
6. `List.IsSuffix` and `List.IsInfix` are the canonical list owners for contiguous occurrence,
   and `List.HasOrderedDisjointSublists` is the thin recursive bridge used by the sixth- and
   quarter-group source refinements.
-/

namespace List

/-- An ordered family of sublists occurs disjointly in `word` when one can successively split off
the listed parts from left to right, always continuing inside the suffix that remains. -/
def HasOrderedDisjointSublists {α : Type u} (word : List α) : List (List α) → Prop
  | [] => True
  | part :: parts =>
      ∃ right : List α, part ++ right <:+ word ∧ HasOrderedDisjointSublists right parts

end List

namespace FreeGroup

/-- A word `w` has a Greendlinger remnant configuration for the pair `(q, p)` when its reduced
word is an alternating product `u₁ s₁ ⋯ uₙ sₙ`, each `sₖ` is an `i(sₖ)`-remnant with respect to
`R`, and the indices satisfy the displayed curvature inequality
`∑ [p / q + 2 - i(sₖ)] ≥ p`. This is a thin bridge predicate around the direct source witnesses,
not a separate owner structure. -/
def HasGreendlingerRemnantConfiguration (w : FreeGroup X) (R : Set (FreeGroup X)) (p q : ℕ) :
    Prop :=
  ∃ segments : List (List (X × Bool) × List (X × Bool) × ℕ),
    w.toWord = segments.flatMap (fun seg ↦ match seg with | (u, s, _) => u ++ s) ∧
      (∀ seg ∈ segments, match seg with | (_, s, i) => basis.is_j_remnant R i s) ∧
        (p : ℚ) ≤
          (segments.map fun seg ↦ match seg with | (_, _, i) => (p : ℚ) / q + 2 - i).sum

-- Proof sketch: unfold `HasGreendlingerRemnantConfiguration`; the statement is exactly the
-- existential decomposition, remnant conditions, and curvature inequality appearing in the
-- definition.
/-- Unfolding a Greendlinger remnant configuration gives the alternating decomposition of `w`,
the remnant condition on each `sₖ`, and the displayed lower bound on
`∑ [p / q + 2 - i(sₖ)]`. -/
theorem hasGreendlingerRemnantConfiguration_iff (w : FreeGroup X) (R : Set (FreeGroup X))
    (p q : ℕ) :
    w.HasGreendlingerRemnantConfiguration R p q ↔
      ∃ segments : List (List (X × Bool) × List (X × Bool) × ℕ),
        w.toWord = segments.flatMap (fun seg ↦ match seg with | (u, s, _) => u ++ s) ∧
          (∀ seg ∈ segments, match seg with | (_, s, i) => basis.is_j_remnant R i s) ∧
            (p : ℚ) ≤
              (segments.map fun seg ↦ match seg with | (_, _, i) => (p : ℚ) / q + 2 - i).sum :=
  Iff.rfl

end FreeGroup

-- Proof sketch: choose a cyclically reduced conjugate `w*` of `w` with a minimal
-- relator-conjugate diagram. The hypotheses `C(p)` and `T(q)` together with the allowed pairs
-- `(6, 3)`, `(4, 4)`, and `(3, 6)` convert the boundary-region estimate of Theorem `5-4-5` into
-- the displayed inequality for the boundary remnants of that diagram. Reading the corresponding
-- consecutive boundary segments on the boundary cycle of the diagram gives the owner predicate
-- `w*.HasGreendlingerRemnantConfiguration R p q`. If the diagram has a single region, its
-- cyclically reduced boundary word represents an element of the symmetrized relator family `R*`,
-- so the first alternative should be stated through that cyclic-word owner rather than by the
-- raw membership predicate `w* ∈ R`.
/-- Theorem 5-4-7: if `R` satisfies `C(p)` and `T(q)` for one of the pairs `(q, p) = (6, 3)`,
`(4, 4)`, or `(3, 6)`, then every nontrivial element of the normal closure of `R` has a
cyclically reduced conjugate `w*` whose cyclic word either lies in the symmetrized relator
family `R*` or admits a decomposition `u₁ s₁ ⋯ uₙ sₙ` with each `sₖ` an `i(sₖ)`-remnant and
`∑ [p / q + 2 - i(sₖ)] ≥ p`; this second alternative is recorded through the canonical bridge
predicate `w*.HasGreendlingerRemnantConfiguration R p q` rather than by repeating its witness
data inline. -/
theorem greendlinger_remnant_alternative_for_small_cancellation_pairs
    (R : Set (FreeGroup X)) {p q : ℕ}
    (hpair : (q, p) = (6, 3) ∨ (q, p) = (4, 4) ∨ (q, p) = (3, 6))
    (hC : C(p)[basis, R]) (hT : T(q)[basis, R]) {w : FreeGroup X}
    (hw_ne : w ≠ 1) (hw_mem : w ∈ Subgroup.normalClosure R) :
    ∃ wStar : FreeGroup X,
      IsConj wStar w ∧
        ∃ hwStar_cyclic : FreeGroup.IsCyclicallyReduced wStar.toWord,
          ((⟨wStar.toWord, hwStar_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
            wStar.HasGreendlingerRemnantConfiguration R p q) :=
  sorry

end
