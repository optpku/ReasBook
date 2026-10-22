/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_11_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_4_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation

section

variable {X : Type u}

local instance theorem_5_4_8_decidableEq : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: small-cancellation theory in free groups at the word level.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial cyclically reduced word
  `w ∈ N`, together with the alternative that the cyclic word of `w` lies in the symmetrized
  relator family `R*`, and Greendlinger's five sixth-group long-subword alternatives.
- `core/canonical`: `FreeGroup X` is the owner for reduced words, `Subgroup.normalClosure R` is
  the owner for `N`, `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclic reduction,
  `IsConj` is the owner relation for conjugacy,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
  `R*`, `CyclicWord.HasPart` is the owner predicate for a cyclic segment of a symmetrized relator,
  `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
  owner for the recurring fraction-length comparisons against `R*`,
  `basis.is_j_remnant` from Definition `5-4-6` is the chapter owner for remnant pieces, and
  `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the generic Greendlinger
  owner abstraction for small-cancellation pairs, while `C'((1 / 6 : ℝ))[basis, R]` is the
  existing Chapter `5` owner for the small-cancellation
  hypothesis.
- `bridge/view`: the generic `(q, p) = (6, 3)` remnant configuration from Theorem `5-4-7` is
  translated to the source sixth-group alternatives by turning a `j`-remnant under `C'(1 / 6)`
  into a subword longer than `(6 - j) / 6` of a symmetrized relator.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup `N`.
2. `FreeGroup.IsCyclicallyReduced` is the owner predicate for the hypothesis that `w` is
   cyclically reduced and for the cyclically reduced conjugate `w*`.
3. `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
   used in the source `>(5 / 6)`, `>(4 / 6)`, and `>(3 / 6)` comparisons.
4. `List.HasOrderedDisjointSublists` from Theorem `5-4-7` is the shared list-level owner for the
   ordered disjoint occurrence of the long subwords in the source alternatives.
5. `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
   owner for the recurring “longer than `numerator / denominator` of a symmetrized relator”
   comparison.
6. `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the established
   generic owner abstraction whose `(3, 6)` specialization should be kept only as a bridge here.

Primitive vs. derived:
- primitive public data: the relator set `R`, the word `w`, the normal-closure membership
  hypothesis, the cyclic reduction hypothesis, and the `C'(1 / 6)` assumption;
- derived API: the owner-level first alternative
  `⟨w.toWord, hw_cyclic⟩ ∈ symmetrizedRelatorFamily R`, the sixth-group long-subword
  configuration, the direct existential conclusion for a cyclically reduced conjugate, and the
  bridge from the generic `(3, 6)` remnant owner to that source-facing configuration.
-/

namespace FreeGroup

/-- A Greendlinger configuration for a sixth-group is one of Greendlinger's five explicit
long-subword alternatives: two disjoint `>(5 / 6) R` subwords, three disjoint `>(4 / 6) R`
subwords, two disjoint `>(4 / 6) R` subwords together with two disjoint `>(3 / 6) R` subwords,
one disjoint `>(4 / 6) R` subword together with four disjoint `>(3 / 6) R` subwords, or six
disjoint `>(3 / 6) R` subwords. -/
def HasGreendlingerSixthConfiguration (w : FreeGroup X) (R : Set (FreeGroup X)) : Prop :=
  (∃ part₁ part₂ : List (X × Bool),
      List.HasOrderedDisjointSublists w.toWord [part₁, part₂] ∧
        HasLongSymmetrizedRelatorFractionPart R 5 6 part₁ ∧
          HasLongSymmetrizedRelatorFractionPart R 5 6 part₂) ∨
    (∃ part₁ part₂ part₃ : List (X × Bool),
        List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃] ∧
          HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
            HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₃) ∨
      (∃ part₁ part₂ part₃ part₄ : List (X × Bool),
          List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄] ∧
            HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₄) ∨
        (∃ part₁ part₂ part₃ part₄ part₅ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄, part₅] ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₅) ∨
          ∃ part₁ part₂ part₃ part₄ part₅ part₆ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord
              [part₁, part₂, part₃, part₄, part₅, part₆] ∧
              HasLongSymmetrizedRelatorFractionPart R 3 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₅ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₆

-- Proof sketch: unfold `HasGreendlingerSixthConfiguration`; the five disjuncts are exactly the
-- five source alternatives in the theorem.
/-- A sixth-group Greendlinger configuration is exactly one of Greendlinger's five explicit
long-subword alternatives. -/
theorem hasGreendlingerSixthConfiguration_iff (w : FreeGroup X) (R : Set (FreeGroup X)) :
    w.HasGreendlingerSixthConfiguration R ↔
      (∃ part₁ part₂ : List (X × Bool),
          List.HasOrderedDisjointSublists w.toWord [part₁, part₂] ∧
            HasLongSymmetrizedRelatorFractionPart R 5 6 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 5 6 part₂) ∨
        (∃ part₁ part₂ part₃ : List (X × Bool),
            List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃] ∧
              HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₃) ∨
          (∃ part₁ part₂ part₃ part₄ : List (X × Bool),
              List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄] ∧
                HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₂ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₄) ∨
            (∃ part₁ part₂ part₃ part₄ part₅ : List (X × Bool),
                List.HasOrderedDisjointSublists w.toWord [part₁, part₂, part₃, part₄, part₅] ∧
                  HasLongSymmetrizedRelatorFractionPart R 4 6 part₁ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                          HasLongSymmetrizedRelatorFractionPart R 3 6 part₅) ∨
              ∃ part₁ part₂ part₃ part₄ part₅ part₆ : List (X × Bool),
                List.HasOrderedDisjointSublists w.toWord
                  [part₁, part₂, part₃, part₄, part₅, part₆] ∧
                  HasLongSymmetrizedRelatorFractionPart R 3 6 part₁ ∧
                    HasLongSymmetrizedRelatorFractionPart R 3 6 part₂ ∧
                      HasLongSymmetrizedRelatorFractionPart R 3 6 part₃ ∧
                        HasLongSymmetrizedRelatorFractionPart R 3 6 part₄ ∧
                          HasLongSymmetrizedRelatorFractionPart R 3 6 part₅ ∧
                            HasLongSymmetrizedRelatorFractionPart R 3 6 part₆ :=
  Iff.rfl

-- Proof sketch: under `C'(1 / 6)`, every `j`-remnant from Definition `5-4-6` is longer than
-- `(6 - j) / 6` of the corresponding symmetrized relator from `R*`. Rewriting the `(3, 6)`
-- remnant data from Theorem `5-4-7` with these long-subword bounds converts the remnant-index
-- multisets `[1, 1]`, `[2, 2, 2]`, `[2, 2, 3, 3]`, `[2, 3, 3, 3, 3]`, and `[3, 3, 3, 3, 3, 3]`
-- into the source numerator multisets `[5, 5]`, `[4, 4, 4]`, `[4, 4, 3, 3]`, `[4, 3, 3, 3, 3]`,
-- and `[3, 3, 3, 3, 3, 3]`.
/-- Under `C'(1 / 6)`, the generic `(3, 6)` remnant configuration from Theorem `5-4-7` is
equivalent to Greendlinger's five sixth-group long-subword alternatives. -/
theorem hasGreendlingerRemnantConfiguration_sixth_iff
    (R : Set (FreeGroup X)) (hR : C'((1 / 6 : ℝ))[basis, R]) (w : FreeGroup X) :
    w.HasGreendlingerRemnantConfiguration R 3 6 ↔
      w.HasGreendlingerSixthConfiguration R :=
  sorry

end FreeGroup

-- Proof sketch: choose a cyclically reduced conjugate of `w` with a minimal van Kampen diagram
-- over `R`. Under `C'(1 / 6)`, translate boundary pieces into the degree bounds of the chapter's
-- planar small-cancellation lemmas and apply the curvature-counting alternative for `(q, p) =
-- (6, 3)` from Theorem `5-4-7`. If the resulting conjugate `wStar` lies in `R`, then the
-- cyclically reduced cyclic word `⟨w.toWord, hw_cyclic⟩` represents the same conjugacy class as
-- `wStar`, so it lies in `symmetrizedRelatorFamily R`. Otherwise the owner configuration
-- `HasGreendlingerRemnantConfiguration R 3 6` converts via the preceding bridge to one of the
-- five source sixth-group long-subword patterns.
/-- Theorem 5-4-8: if `R` satisfies `C'(1 / 6)` and `w` is a nontrivial cyclically reduced word in
the normal closure of `R`, then either the cyclic word of `w` lies in the symmetrized relator
family `R*`, or some cyclically reduced conjugate of `w` satisfies one of Greendlinger's five
sixth-group long-subword configurations. The existential conclusion is stated directly in terms of
the canonical owners `IsConj` and `IsCyclicallyReduced`, rather than through an extra witness
wrapper. -/
theorem greendlinger_alternatives_for_sixth_groups
    (R : Set (FreeGroup X)) {w : FreeGroup X} (hR : C'((1 / 6 : ℝ))[basis, R])
    (hw_ne : w ≠ 1) (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord)
    (hw_mem : w ∈ Subgroup.normalClosure R) :
    (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
      ∃ wStar : FreeGroup X,
        IsConj wStar w ∧
          FreeGroup.IsCyclicallyReduced wStar.toWord ∧
            wStar.HasGreendlingerSixthConfiguration R := sorry

end
