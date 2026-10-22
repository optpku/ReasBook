/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace GroupPresentation

section

variable {X₁ : Type u} {X₂ : Type v}
variable {R₁ : Set (FreeGroup X₁)} {R₂ : Set (FreeGroup X₂)}

local notation "G₁" => PresentedGroup R₁
local notation "G₂" => PresentedGroup R₂

-- Layer triage:
-- `source-facing`: two finite presentations of the same group, together with the claim that
-- solvability of the word problem or of the conjugacy problem does not depend on which finite
-- presentation is chosen.
-- `core/canonical`: the owner objects `PresentedGroup R₁` and `PresentedGroup R₂`, the chapter
-- owner predicates `HasSolvableWordProblem` and `HasSolvableConjugacyProblem`, and the owner
-- conjugacy relation `IsConj` on a group.
-- `bridge/view`: "presentations of the same group" is expressed canonically by a multiplicative
-- equivalence `G₁ ≃* G₂`; the internal transport lemmas below isolate the owner-side transport,
-- while the public theorem surface keeps only the invariant presentation-level statements.
-- Domain sampling:
-- 1. `PresentedGroup R` is the mathlib owner abstraction for a group given by generators and
--    relators.
-- 2. `HasSolvableWordProblem R` from Definition `2-1-4` is the chapter owner predicate for the
--    word problem of a presentation.
-- 3. `HasSolvableConjugacyProblem R` is the matching chapter owner predicate for solvability of
--    the conjugacy problem.
-- 4. `IsConj` is the owner relation for conjugacy in a group.
-- 5. `MulEquiv` is the canonical bridge for transporting group-theoretic decidability data
--    between isomorphic presented groups.
-- Primitive vs. derived:
-- the primitive data for the owner-level transport are the two relator sets and an isomorphism
-- between their presented groups; solvable word and conjugacy problems are the chapter's
-- presentation-level computability predicates on coded words, while finiteness of the generator
-- types is the only extra effective hypothesis used by the transport. The source phrase "finite
-- presentation" from Definition `2-1-2` adds relator finiteness as a separate source-facing
-- condition, but that condition is inert for the invariance statement proved here.

section WordProblem

variable [Primcodable X₁] [Primcodable X₂] [Finite X₂]

-- Proof sketch: choose, for each generator of the second finite presentation, a word in the first
-- free group with the same value in the common presented group. Because the target generator type
-- is finite, this gives a finite lookup table for substituting words from `X₂` into words on
-- `X₁`, so the decision procedure for triviality in `PresentedGroup R₁` transports to one for
-- `PresentedGroup R₂`.
private theorem hasSolvableWordProblem_of_mulEquiv
    (e : G₁ ≃* G₂) :
    HasSolvableWordProblem R₁ → HasSolvableWordProblem R₂ := sorry

/-- Bridge lemma: for finite generating sets on both sides, solvability of the word problem is
invariant under an isomorphism of presented groups. -/
theorem hasSolvableWordProblem_iff_mulEquiv [Finite X₁]
    (e : G₁ ≃* G₂) :
    HasSolvableWordProblem R₁ ↔ HasSolvableWordProblem R₂ := by
  constructor
  · exact hasSolvableWordProblem_of_mulEquiv e
  · exact hasSolvableWordProblem_of_mulEquiv e.symm

end WordProblem

section ConjugacyProblem

variable [Primcodable X₁] [Primcodable X₂] [Finite X₂]

-- Proof sketch: choose, for each generator of the second finite presentation, a word in the first
-- free group with the same value after transporting along `e.symm`. This finite substitution table
-- translates pairs of words on `X₂` to pairs of words on `X₁`, and `e` preserves `IsConj`, so a
-- conjugacy algorithm for `R₁` transports to one for `R₂`.
private theorem hasSolvableConjugacyProblem_of_mulEquiv
    (e : G₁ ≃* G₂) :
    HasSolvableConjugacyProblem R₁ → HasSolvableConjugacyProblem R₂ := sorry

/-- Bridge lemma: for finite generating sets on both sides, solvability of the conjugacy problem
is invariant under an isomorphism of presented groups. -/
theorem hasSolvableConjugacyProblem_iff_mulEquiv [Finite X₁]
    (e : G₁ ≃* G₂) :
    HasSolvableConjugacyProblem R₁ ↔ HasSolvableConjugacyProblem R₂ := by
  constructor
  · exact hasSolvableConjugacyProblem_of_mulEquiv e
  · exact hasSolvableConjugacyProblem_of_mulEquiv e.symm

end ConjugacyProblem

section IsomorphismInvariance

variable [Primcodable X₁] [Primcodable X₂] [Finite X₁] [Finite X₂]

-- Proof sketch: the one-way word-problem bridge only needs finiteness of the target generator
-- type, so applying it to `e` and `e.symm` gives a symmetric statement once both generator types
-- are finite. The conjugacy bridge has the same effective transport shape, so it becomes
-- symmetric under the same pair of finiteness hypotheses.
/-- Proposition 2-2-2, core form: along an isomorphism between two presented groups with finite
generating types, solvability of the word problem and of the conjugacy problem are invariant. By
Definition `2-1-2`, this applies in particular to finite presentations. -/
theorem solvable_word_and_conjugacy_problems_iff_mulEquiv
    (e : G₁ ≃* G₂) :
    (HasSolvableWordProblem R₁ ↔ HasSolvableWordProblem R₂) ∧
      (HasSolvableConjugacyProblem R₁ ↔ HasSolvableConjugacyProblem R₂) := by
  exact ⟨hasSolvableWordProblem_iff_mulEquiv e, hasSolvableConjugacyProblem_iff_mulEquiv e⟩

end IsomorphismInvariance

/- Source-facing finite-presentation wording: Definition `2-1-2` identifies a finite presentation
with `Finite X ∧ Set.Finite R`, so Proposition `2-2-2` is the immediate specialization of
`solvable_word_and_conjugacy_problems_iff_mulEquiv` obtained by discarding the inert
`Set.Finite R` hypotheses. -/

end

end GroupPresentation
