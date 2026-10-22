/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

namespace GroupPresentation

section

variable {X : Type u} [Primcodable X]

-- Layer triage:
-- `source-facing`: a presentation datum `(X; R)` together with the textbook assertions that
-- triviality and conjugacy of words on the generators are algorithmically decidable from finite
-- signed-word input.
-- `core/canonical`: the chapter owner namespace `GroupPresentation`, the word model
-- `List (X × Bool)` with canonical evaluation `FreeGroup.mk`, the canonical normal form map
-- `FreeGroup.toWord`, and the canonical owner quotient `PresentedGroup R` with its map
-- `PresentedGroup.mk`.
-- `bridge/view`: quotient triviality is the source-facing word problem, normal-closure membership
-- is the equivalent owner-side reformulation given by `PresentedGroup.mk_eq_one_iff`, and
-- quotient-level decidability of conjugacy is only a derived view obtained by choosing word
-- representatives through `PresentedGroup.mk_surjective`.
-- Domain sampling:
-- 1. Definition `2-1-2` keeps the finiteness conditions for presentations at the canonical owner
--    predicates `Finite X` and `Set.Finite R`, while Definition `2-1-3` adds the presentation-
--    level predicate `IsRecursive` in the `GroupPresentation` namespace.
-- 2. `FreeGroup.mk` is the canonical map from finite signed words to `FreeGroup X`.
-- 3. `PresentedGroup R` with `PresentedGroup.mk` is the owner abstraction for the quotient by the
--    normal closure of `R`.
-- 4. `PresentedGroup.mk_eq_one_iff` is the canonical bridge from quotient triviality to
--    membership in `Subgroup.normalClosure R`.
-- 5. `ComputablePred` is mathlib's canonical computability predicate on coded finite input.
-- 6. `FreeGroup.toWord` is the canonical reduced-word representative of a free-group element.
-- Primitive vs. derived:
-- the primitive data are the generator type `X` and relator set `R`; the owner-side computable
-- predicates are quotient triviality on signed words and quotient conjugacy on pairs of signed
-- words, while normal-closure membership and quotient-level decidability are derived bridges.

/-- Definition 2-1-4: a presentation has solvable word problem when the set of finite signed words
whose image in the canonical presented group is trivial is computable. -/
def HasSolvableWordProblem (R : Set (FreeGroup X)) : Prop :=
  ComputablePred fun L : List (X × Bool) ↦ PresentedGroup.mk R (FreeGroup.mk L) = 1

/-- A presentation has solvable word problem exactly when triviality of the canonical quotient image
of a signed word is computable. -/
theorem hasSolvableWordProblem_iff_computable_mk_eq_one (R : Set (FreeGroup X)) :
    HasSolvableWordProblem R ↔
      ComputablePred fun L : List (X × Bool) ↦ PresentedGroup.mk R (FreeGroup.mk L) = 1 :=
  Iff.rfl

/-- A presentation has solvable word problem exactly when membership of a signed word in the normal
closure of the relators is computable. -/
theorem hasSolvableWordProblem_iff_computable_mem_normalClosure (R : Set (FreeGroup X)) :
    HasSolvableWordProblem R ↔
      ComputablePred fun L : List (X × Bool) ↦ FreeGroup.mk L ∈ Subgroup.normalClosure R := by
  constructor
  · intro h
    exact ComputablePred.of_eq h fun L ↦
      (PresentedGroup.mk_eq_one_iff :
        PresentedGroup.mk R (FreeGroup.mk L) = 1 ↔
          FreeGroup.mk L ∈ Subgroup.normalClosure R)
  · intro h
    exact ComputablePred.of_eq h fun L ↦
      (PresentedGroup.mk_eq_one_iff :
        PresentedGroup.mk R (FreeGroup.mk L) = 1 ↔
          FreeGroup.mk L ∈ Subgroup.normalClosure R).symm

/-- A presentation has solvable conjugacy problem when conjugacy of pairs of finite signed words in
the canonical presented group is computable. -/
def HasSolvableConjugacyProblem (R : Set (FreeGroup X)) : Prop :=
  ComputablePred fun L : List (X × Bool) × List (X × Bool) ↦
    IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2))

/-- A presentation has solvable conjugacy problem exactly when conjugacy of the canonical quotient
images of a pair of signed words is computable. -/
theorem hasSolvableConjugacyProblem_iff_computable_isConj_mk (R : Set (FreeGroup X)) :
    HasSolvableConjugacyProblem R ↔
      ComputablePred fun L : List (X × Bool) × List (X × Bool) ↦
        IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2)) :=
  Iff.rfl

/-- The source-facing word-level conjugacy algorithm induces a concrete quotient-level decider for
conjugacy in the canonical presented group. -/
noncomputable instance decidableRelIsConjOfHasSolvableConjugacyProblem
    (R : Set (FreeGroup X)) (h : HasSolvableConjugacyProblem R) :
    DecidableRel (IsConj : PresentedGroup R → PresentedGroup R → Prop) :=
  let _ : DecidableEq X := Classical.decEq _
  let _ : DecidableEq (PresentedGroup R) := Classical.decEq _
  let p : List (X × Bool) × List (X × Bool) → Prop := fun L ↦
    IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2))
  have hp : ComputablePred p := h
  let rep : PresentedGroup R → List (X × Bool) := fun g ↦
    FreeGroup.toWord (Classical.choose (PresentedGroup.mk_surjective R g))
  have hrep : ∀ g : PresentedGroup R, PresentedGroup.mk R (FreeGroup.mk (rep g)) = g := by
    intro g
    dsimp [rep]
    rw [FreeGroup.mk_toWord]
    exact Classical.choose_spec (PresentedGroup.mk_surjective R g)
  fun g h' ↦ by
    have hg : PresentedGroup.mk R (FreeGroup.mk (rep g)) = g := hrep g
    have hh : PresentedGroup.mk R (FreeGroup.mk (rep h')) = h' := hrep h'
    simpa [p, hg, hh] using hp.choose (rep g, rep h')

end

end GroupPresentation
