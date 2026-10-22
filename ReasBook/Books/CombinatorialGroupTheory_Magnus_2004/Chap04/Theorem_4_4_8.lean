/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algorithmic group theory for finitely presented residually finite groups.

Layer triage:
- `source-facing`: an abstract group `G` together with the textbook assertion that finite
  presentability and residual finiteness imply solvability of the word problem for `G`.
- `core/canonical`: `Group.IsFinitelyPresented G` and `Group.ResiduallyFinite G` are mathlib's
  owner predicates for the two hypotheses, while `PresentedGroup R ≃* G` is the project's
  canonical bridge from a finite-generator presentation to an abstract group.
- `bridge/view`: the chapter's concrete owner predicate for solvability is
  `GroupPresentation.HasSolvableWordProblem R` on a relator set `R`, so the abstract group-level
  property is recorded by the existence of some finite-generator presentation with that property.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's canonical abstract owner for finite presentability.
2. `Group.ResiduallyFinite` is mathlib's canonical abstract owner for residual finiteness.
3. `PresentedGroup R ≃* G` is the project's canonical presentation datum from Definition `2-1-1`.
4. `GroupPresentation.HasSolvableWordProblem R` is the chapter owner predicate for solvability of
   the word problem in a concrete presentation.

Primitive vs. derived:
- primitive public data for the abstract owner: only the ambient group `G`;
- derived bridge data: a finite generator rank `n`, a relator set
  `R : Set (FreeGroup (Fin n))`, and a presentation equivalence `PresentedGroup R ≃* G`.
-/

/-- An abstract group has solvable word problem if some finite-generator presentation of it has
solvable word problem in the chapter's presentation-level sense. -/
def HasSolvableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, ∃ R : Set (FreeGroup (Fin n)), ∃ _ : PresentedGroup R ≃* G,
    GroupPresentation.HasSolvableWordProblem R

/-- An abstract group has solvable conjugacy problem if some finite-generator presentation of it
has solvable conjugacy problem in the chapter's presentation-level sense. -/
def HasSolvableConjugacyProblem (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, ∃ R : Set (FreeGroup (Fin n)), ∃ _ : PresentedGroup R ≃* G,
    GroupPresentation.HasSolvableConjugacyProblem R

variable {G : Type u} [Group G]

-- Proof sketch: the chosen presentation equivalence together with the owner-side solvable word
-- problem for that presentation is exactly the data required by `HasSolvableWordProblem G`.
/-- A solvable word problem for an explicit finite-generator presentation induces a solvable word
problem for the abstract group it presents. -/
theorem hasSolvableWordProblem_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.HasSolvableWordProblem R) :
    HasSolvableWordProblem G := by
  exact ⟨n, R, P, hR⟩

-- Proof sketch: the chosen presentation equivalence together with the owner-side solvable
-- conjugacy problem for that presentation is exactly the data required by
-- `HasSolvableConjugacyProblem G`.
/-- A solvable conjugacy problem for an explicit finite-generator presentation induces a solvable
conjugacy problem for the abstract group it presents. -/
theorem hasSolvableConjugacyProblem_of_presentation
    (n : ℕ) (R : Set (FreeGroup (Fin n))) (P : PresentedGroup R ≃* G)
    (hR : GroupPresentation.HasSolvableConjugacyProblem R) :
    HasSolvableConjugacyProblem G := by
  exact ⟨n, R, P, hR⟩

-- Proof sketch: choose a finite presentation of `G` from `IsFinitelyPresented G`. For that
-- presentation, words equal to `1` are recursively enumerable from the finite relator set, while
-- residual finiteness lets one recursively enumerate the words not equal to `1` by searching over
-- all homomorphisms from `G` to finite groups and checking when the image of the word is
-- nontrivial. Running the two enumerations in parallel yields a decision procedure for the word
-- problem of the chosen finite presentation, which then witnesses `HasSolvableWordProblem G`.
/-- Theorem 4-4-8: a finitely presented residually finite group has solvable word problem. -/
theorem hasSolvableWordProblem_of_isFinitelyPresented_of_residuallyFinite
    (G : Type u) [Group G] [IsFinitelyPresented G] [ResiduallyFinite G] :
    HasSolvableWordProblem G := sorry

end Group
