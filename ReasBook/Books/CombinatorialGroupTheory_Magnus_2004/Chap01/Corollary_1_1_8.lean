/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/-- Corollary 1-1-8: A group is projective exactly when it is free. -/
-- Proof sketch: use Proposition `1-1-7`, which identifies projective groups with retract
-- subgroups of free groups. A retract subgroup of a free group is free by Nielsen–Schreier, and a
-- free group is trivially a retract of itself via the top subgroup inclusion.
theorem projective_group_iff_free_group {G : Type u} [Group G] :
    Projective (GrpCat.of G) ↔ IsFreeGroup G := by
  rw [projective_group_iff_isomorphic_to_retract_of_free_group]
  constructor
  · rintro ⟨F, hF, R, e, _hR⟩
    let _ : IsFreeGroup F := hF
    let _ : IsFreeGroup R := subgroupIsFreeOfIsFree R
    exact IsFreeGroup.ofMulEquiv e.symm
  · intro hG
    exact ⟨GrpCat.of G, hG, ⊤, Subgroup.topEquiv.symm, Subgroup.top_subtype_isSplitMono⟩
