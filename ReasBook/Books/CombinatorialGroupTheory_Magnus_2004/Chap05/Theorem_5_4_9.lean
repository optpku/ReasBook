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

local instance theorem_5_4_9_decidableEq : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: cyclic-word Greendlinger alternatives for quarter-groups.

Layer triage:
- `source-facing`: a relator set `R`, its normal closure `N`, a nontrivial cyclically reduced word
  `w ∈ N`, the alternative that the cyclic word of `w` lies in the symmetrized relator family
  `R*`, and the two Greendlinger quarter-group long-subword alternatives forced by `C'(1 / 4)`
  together with `T(4)`.
- `core/canonical`: `CyclicWord X` is the owner for cyclically reduced words modulo cyclic
  permutation, `Subgroup.normalClosure R` is the owner for `N`,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the first source alternative,
  `CyclicWord.HasPart` is the Chapter `1` owner for cyclic segments, and
  `GroupPresentation.HasLongSymmetrizedRelatorPart` is the Chapter `3` owner for the canonical
  half-relator comparison, `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` is the owner
  for the remaining non-half fraction comparisons against `R*`, and the Chapter `5` owners
  `C'((1 / 4 : ℝ))[basis, R]` and `T(4)[basis, R]` express the small-cancellation hypotheses.
- `bridge/view`: `List.HasOrderedDisjointSublists` from Theorem `5-4-7` remains the list-level
  ordered-disjoint occurrence predicate, but here it is used only through a thin cyclic-word
  bridge recording that some representative list of the cyclic word contains the required ordered
  family of disjoint parts. The upstream `(4, 4)` remnant owner from Theorem `5-4-7` is then
  bridged to this cyclic-word owner.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup `N`.
2. `CyclicWord X` from Definition `1-4-17` is the chapter owner abstraction for cyclically
   reduced words modulo cyclic permutation, which is the right owner for Greendlinger's
   quarter-word alternatives.
3. `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
   `R*` used in the first alternative and the quarter-length comparisons.
4. `CyclicWord.HasPart` from Proposition `1-7-9` is the owner for a cyclic part of a symmetrized
   relator, so the quarter configuration should be phrased using `SignedLetter X` parts on a
   cyclic word rather than on a chosen list representative.
5. `List.HasOrderedDisjointSublists` from Theorem `5-4-7` is the chapter owner for ordered
   disjoint occurrence on one representative list and therefore belongs only to a bridge layer.
6. `GroupPresentation.HasLongSymmetrizedRelatorPart` from Proposition `3-11-2` is the owner for
   the canonical “longer than half a symmetrized relator” condition.
7. `GroupPresentation.HasLongSymmetrizedRelatorFractionPart` from Proposition `3-11-2` is the
   owner for the remaining numerator-over-denominator symmetrized-relator length comparisons.
8. `FreeGroup.HasGreendlingerRemnantConfiguration` from Theorem `5-4-7` is the upstream generic
   owner for `(4, 4)` witness data, but it is weaker than the explicit cyclic-word quarter
   alternative recorded here.
9. `C'((1 / 4 : ℝ))[basis, R]` and `T(4)[basis, R]` from Definitions `5-2-1` and `5-2-3` are the
   existing owner predicates for the quarter-group hypotheses.

Primitive vs. derived:
- primitive public data: the relator set `R`, the word `w`, the small-cancellation hypotheses,
  cyclic reduction, and normal-closure membership;
- derived API: the owner-level cyclic word `⟨w.toWord, hw_cyclic⟩ : CyclicWord X`, its membership
  in `symmetrizedRelatorFamily R`, the quarter-case long-subword configuration on that cyclic
  owner, and the bridge from the generic `(4, 4)` remnant owner to that cyclic-word
  configuration.
-/

namespace CyclicWord

/-- A cyclic word has the ordered disjoint parts `parts` when some representative list of that
cyclic word contains them successively and disjointly from left to right. -/
def HasOrderedDisjointParts (q : CyclicWord X) (parts : List (List (SignedLetter X))) : Prop :=
  ∃ word : List (SignedLetter X), ((word : Cycle (SignedLetter X)) = q.1) ∧
    List.HasOrderedDisjointSublists word parts

/-- A Greendlinger configuration for a quarter-group is either two ordered disjoint parts each
longer than `3 / 4` of a symmetrized relator from `R*`, or four ordered disjoint parts each
longer than `1 / 2` of a symmetrized relator from `R*`. The owner is the cyclic word itself,
not a chosen reduced-word representative. -/
def HasGreendlingerQuarterConfiguration (q : CyclicWord X) (R : Set (FreeGroup X)) : Prop :=
  (∃ part₁ part₂ : List (SignedLetter X),
      q.HasOrderedDisjointParts [part₁, part₂] ∧
        HasLongSymmetrizedRelatorFractionPart R 3 4 part₁ ∧
          HasLongSymmetrizedRelatorFractionPart R 3 4 part₂) ∨
    ∃ part₁ part₂ part₃ part₄ : List (SignedLetter X),
      q.HasOrderedDisjointParts [part₁, part₂, part₃, part₄] ∧
        HasLongSymmetrizedRelatorPart R part₁ ∧
          HasLongSymmetrizedRelatorPart R part₂ ∧
            HasLongSymmetrizedRelatorPart R part₃ ∧
              HasLongSymmetrizedRelatorPart R part₄

-- Proof sketch: unfold `HasGreendlingerQuarterConfiguration`; the two disjuncts are exactly the
-- two source alternatives in the definition.
/-- A quarter-group Greendlinger configuration is exactly one of the two source long-subword
alternatives. -/
theorem hasGreendlingerQuarterConfiguration_iff (q : CyclicWord X) (R : Set (FreeGroup X)) :
    q.HasGreendlingerQuarterConfiguration R ↔
      (∃ part₁ part₂ : List (SignedLetter X),
          q.HasOrderedDisjointParts [part₁, part₂] ∧
            HasLongSymmetrizedRelatorFractionPart R 3 4 part₁ ∧
              HasLongSymmetrizedRelatorFractionPart R 3 4 part₂) ∨
        ∃ part₁ part₂ part₃ part₄ : List (SignedLetter X),
          q.HasOrderedDisjointParts [part₁, part₂, part₃, part₄] ∧
            HasLongSymmetrizedRelatorPart R part₁ ∧
              HasLongSymmetrizedRelatorPart R part₂ ∧
                HasLongSymmetrizedRelatorPart R part₃ ∧
                  HasLongSymmetrizedRelatorPart R part₄ :=
  Iff.rfl

-- Proof sketch: under `C'(1 / 4)`, every `j`-remnant from Definition `5-4-6` is longer than
-- `(4 - j) / 4` of the corresponding symmetrized relator from `R*`. Rewriting the `(4, 4)`
-- remnant data from Theorem `5-4-7` with these long-subword bounds converts the remnant-index
-- multisets `[1, 1]` and `[2, 2, 2, 2]` into the source alternatives of two `>(3 / 4) R`
-- subwords and four subwords longer than half a symmetrized relator, using the existing Chapter
-- `3` half-relator bridge
-- `hasLongSymmetrizedRelatorPart_iff_hasLongSymmetrizedRelatorFractionPart` in the half-relator
-- case.
/-- Under `C'(1 / 4)`, the generic `(4, 4)` remnant configuration from Theorem `5-4-7` is
equivalent to Greendlinger's two quarter-group long-subword alternatives on the induced cyclic
word. -/
theorem hasGreendlingerRemnantConfiguration_quarter_iff
    (R : Set (FreeGroup X)) (hR_cprime : C'((1 / 4 : ℝ))[basis, R]) {w : FreeGroup X}
    (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord) :
    w.HasGreendlingerRemnantConfiguration R 4 4 ↔
      CyclicWord.HasGreendlingerQuarterConfiguration
        (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) R := sorry

end CyclicWord

-- Proof sketch: choose a minimal van Kampen diagram over `R` for the cyclically reduced word `w`.
-- The hypotheses `C'(1 / 4)` and `T(4)` convert the boundary analysis of that diagram into the
-- quarter-group curvature bounds. Greendlinger's lemma for `(4, 4)` maps then yields either that
-- the cyclic word of `w` lies in the symmetrized relator family `R*`, or that the same cyclic
-- word has the owner configuration obtained by rewriting the `(4, 4)` remnant alternative through
-- the preceding cyclic-word bridge. The representative/conjugacy bookkeeping is absorbed by the
-- owner `CyclicWord X`.
/-- Theorem 5-4-9: if `R` satisfies `C'(1 / 4)` and `T(4)`, and `w` is a nontrivial cyclically
reduced word in the normal closure of `R`, then either the cyclic word of `w` lies in the
symmetrized relator family `R*`, or that same cyclic word satisfies one of Greendlinger's two
quarter-group configurations. The public conclusion stays on the intrinsic cyclic-word owner
rather than introducing a second representative-level conjugacy witness. -/
theorem greendlinger_alternatives_for_quarter_groups
    (R : Set (FreeGroup X)) {w : FreeGroup X}
    (hR_cprime : C'((1 / 4 : ℝ))[basis, R]) (hR_t : T(4)[basis, R]) (hw_ne : w ≠ 1)
    (hw_cyclic : FreeGroup.IsCyclicallyReduced w.toWord)
    (hw_mem : w ∈ Subgroup.normalClosure R) :
    (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) ∈ symmetrizedRelatorFamily R ∨
      CyclicWord.HasGreendlingerQuarterConfiguration
        (⟨w.toWord, hw_cyclic⟩ : CyclicWord X) R := sorry

end
