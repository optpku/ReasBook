/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 7.3: the support inequality at `x` is equivalent to the translated
normal-cone inequality on `C - {x}`. -/
lemma support_inequality_iff_sub_singleton_le_zero {C : Set 𝓗} {x u : 𝓗} :
    innerSupremumOn C u ≤ (⟪x, u⟫_ℝ : EReal) ↔
      innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ 0 := by
  constructor
  · intro hsup
    -- Rewrite the support inequality on `C` as pointwise inequalities against the singleton `{x}`.
    have hpoint :
        ∀ y ∈ C, ∀ z ∈ ({x} : Set 𝓗), ⟪y, u⟫_ℝ ≤ ⟪z, u⟫_ℝ :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C ({x} : Set 𝓗) u).1 <| by
        simpa using hsup
    -- Transfer those inequalities to the translate `C - {x}` by expanding `v = y - x`.
    have hsep :
        innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ innerInfimumOn ({0} : Set 𝓗) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({x} : Set 𝓗)) ({0} : Set 𝓗) u).2 <|
        fun v hv z hz ↦ by
          rcases hv with ⟨y, hy, w, hw, rfl⟩
          have hyw : ⟪y, u⟫_ℝ ≤ ⟪w, u⟫_ℝ := hpoint y hy w hw
          have hz' : z = 0 := by simpa using hz
          subst z
          simpa [inner_sub_left] using sub_nonpos.mpr hyw
    simpa using hsep
  · intro hsup
    -- Rewrite the translated inequality as pointwise bounds against `0` on `C - {x}`.
    have hpoint :
        ∀ v ∈ (C - ({x} : Set 𝓗)), ∀ z ∈ ({0} : Set 𝓗), ⟪v, u⟫_ℝ ≤ ⟪z, u⟫_ℝ :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({x} : Set 𝓗)) ({0} : Set 𝓗) u).1 <| by
        simpa using hsup
    -- Evaluate the translated bound at `y - x` to recover the original support inequality at `x`.
    have hsep :
        innerSupremumOn C u ≤ innerInfimumOn ({x} : Set 𝓗) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C ({x} : Set 𝓗) u).2 <|
        fun y hy z hz ↦ by
          have hzx : z = x := by simpa using hz
          subst z
          have hy_sub : y - x ∈ C - ({x} : Set 𝓗) := ⟨y, hy, x, by simp, rfl⟩
          have hyx_zero : ⟪y - x, u⟫_ℝ ≤ ⟪(0 : 𝓗), u⟫_ℝ :=
            hpoint (y - x) hy_sub 0 (by simp)
          have hyx_sub : ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ ≤ 0 := by
            simpa [inner_sub_left] using hyx_zero
          exact sub_nonpos.mp hyx_sub
    simpa using hsep

/-- Helper for Proposition 7.3: at a point of `C`, a nontrivial normal-cone vector is exactly a
nonzero witness of the translated support inequality. -/
lemma normalCone_diff_singleton_nonempty_iff_exists_nonzero {C : Set 𝓗} {x : 𝓗} (hx : x ∈ C) :
    N[C] x \ ({0} : Set 𝓗) ≠ ∅ ↔
      ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ 0 := by
  constructor
  · intro hne
    -- Unpack the nonempty set difference into a concrete nonzero normal vector.
    obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hu' : u ∈ N[C] x ∧ u ∉ ({0} : Set 𝓗) := by
      simpa [Set.mem_diff] using hu
    have hu_normal : innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ 0 := by
      rw [normalCone_of_mem hx] at hu'
      exact hu'.1
    have hu_ne : u ≠ 0 := by
      simpa using hu'.2
    exact ⟨u, hu_ne, hu_normal⟩
  · rintro ⟨u, hu_ne, hu_normal⟩
    -- Repackage the witness back into nonemptiness of the punctured normal cone.
    exact Set.nonempty_iff_ne_empty.mp <| by
      refine ⟨u, ?_⟩
      constructor
      · rw [normalCone_of_mem hx]
        exact hu_normal
      · simp [hu_ne]

/-- Helper for Proposition 7.3: away from `C`, the punctured normal cone is empty because the
normal cone itself is empty. -/
lemma normalCone_diff_singleton_eq_empty_of_not_mem {C : Set 𝓗} {x : 𝓗} (hx : x ∉ C) :
    N[C] x \ ({0} : Set 𝓗) = ∅ := by
  -- Rewrite the normal cone away from `C` and simplify the set difference.
  ext u
  simp [normalCone_of_not_mem hx]

-- Proof sketch: expand `x ∈ spts C` by `mem_supportPoints_iff`, rewrite attainment of the support
-- value as `innerSupremumOn (C - {x}) u ≤ 0`, and then unfold `x ∈ N[C] x` using
-- `normalCone_of_mem`/the definition of `Set.normalCone`.
/-- Proposition 7.3: the support points of `C` are exactly the points of `C` whose normal cone
contains a nonzero vector. -/
theorem supportPoints_eq_setOf_mem_and_nontrivial_normalCone (C : Set 𝓗) :
    spts C = {x ∈ C | N[C] x \ ({0} : Set 𝓗) ≠ ∅} := by
  ext x
  constructor
  · intro hx
    rw [mem_supportPoints_iff] at hx
    rcases hx with ⟨hxC, u, hu_ne, hsupport⟩
    -- Turn the support-point witness into a nonzero vector in the punctured normal cone.
    refine ⟨hxC, ?_⟩
    rw [normalCone_diff_singleton_nonempty_iff_exists_nonzero (C := C) (x := x) hxC]
    refine ⟨u, hu_ne, ?_⟩
    exact
      (support_inequality_iff_sub_singleton_le_zero (C := C) (x := x) (u := u)).1 hsupport
  · rintro ⟨hxC, hnormal⟩
    rw [mem_supportPoints_iff]
    -- Unpack the punctured normal cone into the translated support inequality from the textbook.
    rw [normalCone_diff_singleton_nonempty_iff_exists_nonzero (C := C) (x := x) hxC] at hnormal
    rcases hnormal with ⟨u, hu_ne, hu_normal⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    exact
      (support_inequality_iff_sub_singleton_le_zero (C := C) (x := x) (u := u)).2 hu_normal

-- Proof sketch: use `supportPoints_eq_setOf_mem_and_nontrivial_normalCone` and note that
-- `N[C] x \ {0} ≠ ∅` already forces `x ∈ C`, since `N[C] x = ∅` away from `C`.
/-- The nontriviality of the normal cone already implies membership in `C`, so the previous
description is equivalently the set-valued preimage of `𝓗 \ {0}` under `x ↦ N[C] x`. -/
theorem supportPoints_eq_setOf_nontrivial_normalCone (C : Set 𝓗) :
    spts C = {x : 𝓗 | N[C] x \ ({0} : Set 𝓗) ≠ ∅} := by
  ext x
  constructor
  · intro hx
    -- The first description already records the punctured normal-cone nonemptiness.
    rw [supportPoints_eq_setOf_mem_and_nontrivial_normalCone] at hx
    exact hx.2
  · intro hx
    by_cases hxC : x ∈ C
    · -- On `C`, the previous theorem immediately supplies the desired support-point membership.
      rw [supportPoints_eq_setOf_mem_and_nontrivial_normalCone]
      exact ⟨hxC, hx⟩
    · -- Away from `C`, the punctured normal cone is empty, so the assumed witness is impossible.
      have hempty :
          N[C] x \ ({0} : Set 𝓗) = ∅ :=
        normalCone_diff_singleton_eq_empty_of_not_mem (C := C) (x := x) hxC
      exact False.elim (hx hempty)

end

end Set
