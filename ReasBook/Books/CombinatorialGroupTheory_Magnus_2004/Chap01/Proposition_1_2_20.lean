/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Derived owner bridge: in a free group, two elements commute exactly when they lie in a common
cyclic subgroup. -/
theorem commute_iff_exists_common_zpowers_generator (x y : F) :
    Commute x y ↔ ∃ z : F, x ∈ Subgroup.zpowers z ∧ y ∈ Subgroup.zpowers z := by
  constructor
  · exact exists_common_zpowers_generator_of_commute x y
  · rintro ⟨z, hx, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.refl z).zpow_zpow m n

/-- Proposition 1-2-20: in a free group, commuting defines an equivalence relation on the
nonidentity elements. -/
-- Layer: source-facing statement for an arbitrary free group.
-- Core owner abstractions: `Equivalence`, `Commute`, and `Subgroup.zpowers`.
-- Proof sketch: reflexivity and symmetry are immediate from `Commute.refl` and `Commute.symm`;
-- transitivity is derived through the canonical bridge
-- `commute_iff_exists_common_zpowers_generator`.
theorem commute_equivalence_on_nontrivial_elements :
    Equivalence (fun a b : {x : F // x ≠ 1} ↦ Commute a.1 b.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact Commute.refl a.1
  · intro a b h
    exact h.symm
  · intro a b c hab hbc
    rcases (commute_iff_exists_common_zpowers_generator a.1 b.1).mp hab with ⟨x, hax, hbx⟩
    rcases (commute_iff_exists_common_zpowers_generator b.1 c.1).mp hbc with ⟨y, hby, hcy⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hbx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hby
    have hm0 : m ≠ 0 := by
      intro hm0
      apply b.2
      rw [← hm, hm0, zpow_zero]
    have hn0 : n ≠ 0 := by
      intro hn0
      apply b.2
      rw [← hn, hn0, zpow_zero]
    rcases exists_common_zpowers_generator_of_commute_zpow x y m n hm0 hn0
        (by simp [hm, hn]) with ⟨z, hxz, hyz⟩
    exact (commute_iff_exists_common_zpowers_generator a.1 c.1).mpr
      ⟨z, (Subgroup.zpowers_le.2 hxz) hax, (Subgroup.zpowers_le.2 hyz) hcy⟩

end
