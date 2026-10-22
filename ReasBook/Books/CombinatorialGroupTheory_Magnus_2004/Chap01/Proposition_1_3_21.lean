/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open QuotientGroup

section

variable {X : Type u} [DecidableEq X]
variable (H : Subgroup (FreeGroup X))
variable {r : FreeGroup X → FreeGroup X → Prop} [Std.Trichotomous r]
variable (T : H.RightTransversal)
variable
  (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
  (hmin :
    ∀ ⦃t w : FreeGroup X⦄,
      t ∈ (T : Set (FreeGroup X)) →
      rightRel H t w →
      ¬ r w t)

/-- Proposition 1-3-21: a right transversal of a subgroup of a free group whose chosen
representative in each right coset is minimal for a trichotomous relation compatible with word
length is a minimal Schreier transversal in the sense of Proposition `1-3-20`, hence in
particular a Schreier transversal. For the textbook well-order criterion, the well-foundedness
part is redundant in this implication. -/
-- Layer triage:
-- `source-facing`: a minimal right transversal `T` for the subgroup `H`.
-- `core/canonical`: `H.RightTransversal`, `FreeGroup.norm`, and `QuotientGroup.rightRel H`.
-- `bridge/view`: the minimal-comparison hypotheses furnish the owner predicate
-- `Subgroup.RightTransversal.IsMinimalSchreier T`, and Proposition `1-3-20` then supplies the Schreier
-- initial-segment conclusion.
-- Domain sampling:
-- 1. `Subgroup.RightTransversal` in mathlib is the owner abstraction for chosen right-coset
--    representatives.
-- 2. `QuotientGroup.rightRel H` is the canonical relation expressing that two elements lie in the
--    same right coset of `H`.
-- 3. `HasInitialSegments` in Proposition `1-3-22` is the chapter owner predicate for the
--    Schreier initial-segment condition.
-- 4. `Subgroup.RightTransversal.IsMinimalSchreier` and
--    `Subgroup.RightTransversal.hasInitialSegments` in Proposition `1-3-20` are the
--    canonical project-level owner declarations for this textbook notion and its consequence.
-- Proof sketch: let `t ∈ T` and let `w` lie in the same right coset. If `w = t` there is nothing
-- to show. Otherwise trichotomy compares `w` and `t`; the hypothesis `hmin`
-- rules out `r w t`, so one must have `r t w`. The length-compatibility hypothesis then yields
-- `norm t ≤ norm w`, which is exactly `Subgroup.RightTransversal.IsMinimalSchreier T`.
-- Proposition `1-3-20`
-- converts that owner statement to the initial-segment formulation.
theorem minimal_rightTransversal_isMinimalSchreier
    (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
    (hmin :
      ∀ ⦃t w : FreeGroup X⦄,
        t ∈ (T : Set (FreeGroup X)) →
        rightRel H t w →
        ¬ r w t) :
    Subgroup.RightTransversal.IsMinimalSchreier T := by
  intro t w ht hw
  rcases trichotomous_of r t w with htw | rfl | hwt
  · exact h_length htw
  · exact le_rfl
  · exact (hmin ht hw hwt).elim

/-- Proposition 1-3-21 in Schreier-transversal form: the minimal-comparison criterion above
implies that the underlying set of representatives is closed under taking initial segments. -/
theorem minimal_rightTransversal_hasInitialSegments
    (h_length : ∀ ⦃w w' : FreeGroup X⦄, r w w' → norm w ≤ norm w')
    (hmin :
      ∀ ⦃t w : FreeGroup X⦄,
        t ∈ (T : Set (FreeGroup X)) →
        rightRel H t w →
        ¬ r w t) :
    HasInitialSegments (T : Set (FreeGroup X)) :=
  Subgroup.RightTransversal.hasInitialSegments <|
    minimal_rightTransversal_isMinimalSchreier H T h_length hmin

end
