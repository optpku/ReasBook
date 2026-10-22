/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} [Group G]

/-- Proposition 1-3-2: if each successor `F (i + 1)` is a subgroup of `F i` containing no element
of any basis of `F i`, then every nontrivial element of `F i` has `b`-word length at least
`i + 1`. -/
-- Layer triage:
-- `source-facing`: a descending chain `F : ℕ → Subgroup G` inside the ambient free group `G`.
-- `core/canonical`: the ambient word-length function attached to `b : FreeGroupBasis ι G`, and
-- the project owner predicate `IsPrimitiveElement` for “belongs to some free basis.”
-- `bridge/view`: each subgroup `F i` is free, so the source phrase “contains no element of any
-- basis of `F i`” is expressed intrinsically as avoidance of primitive elements of `F i`.
-- Proof sketch: argue by induction on `i`. The base case is the usual fact that a nontrivial
-- reduced word in a free basis has length at least `1`. For the induction step, choose a basis of
-- `F i`, rewrite the primitive-element avoidance hypothesis back into the source basis language,
-- use it to rule out length `1`, and then apply the Nielsen-reduction estimates from Section 2 to
-- show the ambient `b`-length grows by at least one.
theorem wordLength_lower_bound_of_descending_subgroups_avoiding_bases
    (F : ℕ → Subgroup G) (hdesc : ∀ i, F (i + 1) ≤ F i)
    (havoid : ∀ i {w : F i}, IsPrimitiveElement w → (w : G) ∉ F (i + 1))
    {ι : Type v} [DecidableEq ι] (b : FreeGroupBasis ι G) {i : ℕ} {w : F i} (hw : w ≠ 1) :
    i + 1 ≤ FreeGroup.norm (b.repr w) := by
  classical
  sorry

/-- A descending chain of subgroups satisfying the basis-avoidance hypothesis has trivial
intersection. -/
-- Proof sketch: for any nontrivial `w` in the intersection, the previous theorem gives
-- `i + 1 ≤ FreeGroup.norm (b.repr w)` for every `i`, contradicting the fixed finite word length of
-- `w` relative to any basis `b` of the ambient free group.
theorem iInf_eq_bot_of_descending_subgroups_avoiding_bases
    [IsFreeGroup G]
    (F : ℕ → Subgroup G) (hdesc : ∀ i, F (i + 1) ≤ F i)
    (havoid : ∀ i {w : F i}, IsPrimitiveElement w → (w : G) ∉ F (i + 1)) :
    (⨅ i, F i) = (⊥ : Subgroup G) := sorry

end
