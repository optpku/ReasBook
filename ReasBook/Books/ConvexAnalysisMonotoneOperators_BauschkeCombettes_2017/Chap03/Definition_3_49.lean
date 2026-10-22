/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The `EReal`-valued supremum of the functional `x ↦ ⟪x, u⟫` on `C`. -/
noncomputable abbrev innerSupremumOn (C : Set 𝓗) (u : 𝓗) : EReal :=
  sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

-- Proof sketch: unfold `innerSupremumOn`.
/-- The inner-product supremum on `C` is the supremum of the image of `C` under
`x ↦ ⟪x, u⟫`. -/
theorem innerSupremumOn_eq_sSup_image (C : Set 𝓗) (u : 𝓗) :
    innerSupremumOn C u = sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) := rfl

/-- The inner-product supremum over a singleton is its unique value. -/
@[simp] theorem innerSupremumOn_singleton (x u : 𝓗) :
    innerSupremumOn ({x} : Set 𝓗) u = (⟪x, u⟫_ℝ : EReal) := by
  rw [innerSupremumOn_eq_sSup_image]
  simp

/-- The `EReal`-valued infimum of the functional `x ↦ ⟪x, u⟫` on `D`. -/
noncomputable abbrev innerInfimumOn (D : Set 𝓗) (u : 𝓗) : EReal :=
  sInf ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D)

-- Proof sketch: unfold `innerInfimumOn`.
/-- The inner-product infimum on `D` is the infimum of the image of `D` under
`x ↦ ⟪x, u⟫`. -/
theorem innerInfimumOn_eq_sInf_image (D : Set 𝓗) (u : 𝓗) :
    innerInfimumOn D u = sInf ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D) := rfl

/-- The inner-product infimum over a singleton is its unique value. -/
@[simp] theorem innerInfimumOn_singleton (x u : 𝓗) :
    innerInfimumOn ({x} : Set 𝓗) u = (⟪x, u⟫_ℝ : EReal) := by
  rw [innerInfimumOn_eq_sInf_image]
  simp

/-- The support-function inequality is equivalent to the corresponding pointwise
inner-product inequalities. -/
theorem innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le (C D : Set 𝓗) (u : 𝓗) :
    innerSupremumOn C u ≤ innerInfimumOn D u ↔
      ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  constructor
  · intro hsep x hx y hy
    have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
      rw [innerSupremumOn_eq_sSup_image]
      exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
    have hy_ge : innerInfimumOn D u ≤ (⟪y, u⟫_ℝ : EReal) := by
      rw [innerInfimumOn_eq_sInf_image]
      exact (isGLB_sInf _).1 ⟨y, hy, rfl⟩
    exact_mod_cast le_trans (le_trans hx_le hsep) hy_ge
  · intro hxy
    rw [innerSupremumOn_eq_sSup_image, innerInfimumOn_eq_sInf_image]
    refine (isLUB_sSup _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine (isGLB_sInf _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact show ((⟪x, u⟫_ℝ : EReal) ≤ (⟪y, u⟫_ℝ : EReal)) by
      exact_mod_cast hxy x hx y hy

/-- Definition 3.49: subsets `C` and `D` of a real Hilbert space are separated when some nonzero
vector `u` satisfies `sup_{c ∈ C} ⟪c, u⟫ ≤ inf_{d ∈ D} ⟪d, u⟫`; strong separation and
point-from-set separation are obtained by replacing `≤` with `<` and by taking `C = {x}`. -/
def AreSeparated (C D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u ≤ innerInfimumOn D u

-- Proof sketch: unfold `AreSeparated`.
/-- Two sets are separated exactly when there is a nonzero normal vector whose inner-product
supremum on the first set does not exceed the inner-product infimum on the second. -/
@[simp] theorem areSeparated_iff_exists_nonzero (C D : Set 𝓗) :
    AreSeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u ≤ innerInfimumOn D u := Iff.rfl

/-- Two sets are separated exactly when there is a nonzero normal vector whose inner products on
the first set are pointwise bounded above by those on the second set. -/
theorem areSeparated_iff_exists_nonzero_forall_inner_le (C D : Set 𝓗) :
    AreSeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  rw [areSeparated_iff_exists_nonzero]
  constructor
  · rintro ⟨u, hu, hsep⟩
    exact ⟨u, hu, (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).mp hsep⟩
  · rintro ⟨u, hu, hxy⟩
    exact ⟨u, hu, (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).mpr hxy⟩

/-- A nonzero vector whose inner products on `C` are pointwise bounded above by those on `D`
separates `C` and `D`. -/
theorem areSeparated_of_forall_inner_le {C D : Set 𝓗} {u : 𝓗} (hu : u ≠ 0)
    (hxy : ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ) :
    AreSeparated C D :=
  (areSeparated_iff_exists_nonzero_forall_inner_le C D).2 ⟨u, hu, hxy⟩

/-- A separating support-function inequality yields the corresponding pointwise
inner-product inequalities. -/
theorem forall_inner_le_of_innerSupremumOn_le_innerInfimumOn {C D : Set 𝓗} {u : 𝓗}
    (hsep : innerSupremumOn C u ≤ innerInfimumOn D u) :
    ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ :=
  (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).1 hsep

/-- Two sets are strongly separated when some nonzero vector yields a strict gap between the
corresponding inner-product supremum and infimum. -/
def AreStronglySeparated (C D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u < innerInfimumOn D u

-- Proof sketch: unfold `AreStronglySeparated`.
/-- Two sets are strongly separated exactly when there is a nonzero normal vector whose
inner-product supremum on the first set is strictly smaller than the inner-product infimum on the
second. -/
theorem areStronglySeparated_iff_exists_nonzero (C D : Set 𝓗) :
    AreStronglySeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u < innerInfimumOn D u := Iff.rfl

/-- A point is separated from `D` when some nonzero normal vector bounds its evaluation by the
inner-product infimum on `D`. -/
def IsSeparatedFrom (x : 𝓗) (D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ (⟪x, u⟫_ℝ : EReal) ≤ innerInfimumOn D u

/-- A point is separated from `D` exactly when its singleton is separated from `D`. -/
@[simp] theorem isSeparatedFrom_iff_singleton (x : 𝓗) (D : Set 𝓗) :
    IsSeparatedFrom x D ↔ AreSeparated ({x} : Set 𝓗) D := by
  rw [IsSeparatedFrom, areSeparated_iff_exists_nonzero]
  simp

/-- A point is strongly separated from `D` when some nonzero normal vector yields a strict gap
between its value at `x` and the inner-product infimum on `D`. -/
def IsStronglySeparatedFrom (x : 𝓗) (D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ (⟪x, u⟫_ℝ : EReal) < innerInfimumOn D u

/-- A point is strongly separated from `D` exactly when its singleton is strongly separated from
`D`. -/
theorem isStronglySeparatedFrom_iff_singleton (x : 𝓗) (D : Set 𝓗) :
    IsStronglySeparatedFrom x D ↔ AreStronglySeparated ({x} : Set 𝓗) D := by
  rw [IsStronglySeparatedFrom, areStronglySeparated_iff_exists_nonzero]
  simp
