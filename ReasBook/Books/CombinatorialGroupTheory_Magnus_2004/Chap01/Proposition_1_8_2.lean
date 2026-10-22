/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Monoid.Coprod

section

variable {F : Type u} {R : Type v}
variable [Group F] [Group R]

-- Layer triage:
-- `source-facing`: the word problem in the Section `8` ambient free product `F ∗ R`, tested via
-- the canonical induced coproduct maps attached to split retractions of `R`.
-- `core/canonical`: Proposition `1-8-1` is the owner implication from the universal induced test
-- to `w = 1` under the canonical point-separation hypothesis on those maps,
-- `inducedSplitRetraction` is the induced coproduct map, `inducedRetractionMaps` is the
-- associated family of functions, and `DecidablePred` is Lean's canonical interface for
-- decidability of the word problem.
-- `bridge/view`: the universal induced-retraction test is the contraposed form of Proposition
-- `1-8-1`, derived internally here rather than exposed as a second public owner theorem.
-- Domain sampling:
-- 1. Proposition `1-8-1` supplies the owner implication from the universal test to `w = 1`.
-- 2. `SplitToInfiniteCyclic R` is the chapter owner vocabulary for the split retractions tested in
--    Section `8`.
-- 3. `Set.SeparatesPoints` is mathlib's owner abstraction for the missing separation hypothesis on
--    a family of functions.
-- 4. `DecidablePred` is the canonical owner API for a solvable yes/no problem on a fixed type.

/-- Proposition 1-8-2: in the Section `8` ambient free product `F ∗ R`, the word problem is
decidable once one can decide whether a word maps to `1` under every induced homomorphism coming
from a split retraction of `R` onto the infinite cyclic group, provided those induced maps
separate points of `F ∗ R`. -/
-- Proof sketch: Proposition `1-8-1` turns the universal induced-retraction vanishing test into a
-- sufficient criterion for `w = 1` once the induced maps separate points. The given decision
-- procedure transports across that implication.
@[reducible] def word_problem_decidable_of_decidable_induced_retraction_test
    (hsep : (inducedRetractionMaps F R).SeparatesPoints)
    (htest : DecidablePred fun w : F ∗ R ↦
      ∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1) :
    DecidablePred fun w : F ∗ R ↦ w = 1 :=
  fun w ↦ by
    let _ := htest w
    exact
      decidable_of_iff
        (∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1)
        ⟨fun hw ↦ eq_one_of_forall_induced_retraction_eq_one hsep w hw
          , fun hw ρ ↦ by simp [hw]⟩

end
