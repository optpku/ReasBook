/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function Set

section

variable {α : Type u}

/-
Thin compatibility abbreviation retained for downstream call sites.
-/
abbrev fixedPointSetOn (D : Set α) (T : α → α) : Set α :=
  D ∩ fixedPoints T

/-- Definition 4.1: the fixed-point set of `T` in `D` is `D ∩ Function.fixedPoints T`. -/
theorem fixedPointSetOn_eq_inter_fixedPoints (D : Set α) (T : α → α) :
    fixedPointSetOn D T = D ∩ fixedPoints T := rfl

/-- Membership in `fixedPointSetOn D T` means lying in `D` and being fixed by `T`. -/
-- Proof sketch: unfold `fixedPointSetOn` and `fixedPoints`, then simplify membership in
-- the intersection.
@[simp]
theorem mem_fixedPointSetOn_iff {D : Set α} {T : α → α} {x : α} :
    x ∈ fixedPointSetOn D T ↔ x ∈ D ∧ T x = x := by
  simp [fixedPointSetOn, Function.mem_fixedPoints, Function.IsFixedPt]

end

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Definition 4.1(i): `T : D → H` is firmly nonexpansive when it satisfies the residual
inequality on the subtype domain `D`. -/
def IsFirmlyNonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D,
    ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 - ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2

/-- Definition 4.1(i) restated: `IsFirmlyNonexpansiveOn` unfolds to its defining residual
inequality. -/
theorem isFirmlyNonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsFirmlyNonexpansiveOn T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 - ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2 := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is firmly nonexpansive on `D` when its
restriction to `D` is firmly nonexpansive. -/
def FirmlyNonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsFirmlyNonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted map formulation rewrites to
the displayed ambient inequality on `D`. -/
-- Proof sketch: rewrite the subtype residual inequality in ambient coordinates and rearrange.
theorem firmlyNonexpansiveOn_iff {D : Set H} {T : H → H} :
    FirmlyNonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ D,
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  constructor
  · intro h x hx y hy
    have hxy :
        ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖(x - T x) - (y - T y)‖ ^ 2 := by
      simpa using h ⟨x, hx⟩ ⟨y, hy⟩
    nlinarith
  · intro h x y
    have hxy :
        ‖T x - T y‖ ^ 2 + ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      simpa using h x x.2 y y.2
    nlinarith

/-- Definition 4.1(ii): on the subtype domain `D`, the textbook pairwise nonexpansive inequality
is exactly the canonical `LipschitzWith 1` condition. -/
theorem isNonexpansiveOn_iff {D : Set H} {T : D → H} :
    (∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖) ↔ LipschitzWith 1 T := by
  constructor
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y
  · intro hT x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y

/-- Restricting an ambient self-map to `D` identifies the textbook pairwise nonexpansive
inequality with the canonical `LipschitzOnWith 1` condition on `D`. -/
theorem isNonexpansiveOn_restrict_iff_lipschitzOnWith_one {D : Set H} {T : H → H} :
    (∀ x ∈ D, ∀ y ∈ D, ‖T x - T y‖ ≤ ‖x - y‖) ↔ LipschitzOnWith 1 T D := by
  constructor
  · intro hT
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    simpa [dist_eq_norm] using hT x hx y hy
  · intro hT x hx y hy
    simpa [dist_eq_norm] using hT.dist_le_mul x hx y hy

/-- Definition 4.1(iii): `T : D → H` is strictly nonexpansive when it strictly decreases
distances between distinct points of `D`. -/
def IsStrictlyNonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, x ≠ y → ‖T x - T y‖ < ‖(x : H) - y‖

/-- Definition 4.1(iii) restated: `IsStrictlyNonexpansiveOn` unfolds to its defining strict
distance inequality. -/
theorem isStrictlyNonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsStrictlyNonexpansiveOn T ↔
      ∀ x y : D, x ≠ y → ‖T x - T y‖ < ‖(x : H) - y‖ := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is strictly nonexpansive on `D` when its
restriction to `D` is strictly nonexpansive. -/
def StrictlyNonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsStrictlyNonexpansiveOn (fun x : D ↦ T x)

/-- For an ambient self-map, strict nonexpansiveness on the restriction to `D` is equivalent to
the displayed ambient inequality on `D`. -/
-- Proof sketch: rewrite the subtype inequality in ambient coordinates.
theorem strictlyNonexpansiveOn_iff {D : Set H} {T : H → H} :
    StrictlyNonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ‖T x - T y‖ < ‖x - y‖ := by
  constructor
  · intro h x hx y hy hxy
    have hxy' : (⟨x, hx⟩ : D) ≠ ⟨y, hy⟩ := fun hEq ↦ hxy (congrArg Subtype.val hEq)
    simpa using h ⟨x, hx⟩ ⟨y, hy⟩ hxy'
  · intro h x y hxy
    have hxy' : (x : H) ≠ y := fun hEq ↦ hxy (Subtype.ext hEq)
    simpa using h x x.2 y y.2 hxy'

/-- Definition 4.1(iv): `T : D → H` is firmly quasinonexpansive when the firm distance estimate
holds against every fixed point in `D`. -/
def IsFirmlyQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) →
    ‖T x - y‖ ^ 2 + ‖(x : H) - T x‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2

/-- Definition 4.1(iv) restated: `IsFirmlyQuasinonexpansiveOn` unfolds to its defining inequality
against subtype fixed points. -/
theorem isFirmlyQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsFirmlyQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) →
        ‖T x - y‖ ^ 2 + ‖(x : H) - T x‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is firmly quasinonexpansive on `D` when its
restriction to `D` is firmly quasinonexpansive. -/
def FirmlyQuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsFirmlyQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted fixed-point formulation
rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: convert fixed points in `D` into fixed points of the subtype restriction.
theorem firmlyQuasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    FirmlyQuasinonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ fixedPointSetOn D T,
        ‖T x - y‖ ^ 2 + ‖T x - x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    simpa [norm_sub_rev] using h ⟨x, hx⟩ ⟨y, hyD⟩ hyfix
  · intro h x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa [norm_sub_rev] using h x x.2 y hy'

/-- A self-map is firmly quasinonexpansive when it is firmly quasinonexpansive on the whole
space. -/
def FirmlyQuasinonexpansive (T : H → H) : Prop :=
  FirmlyQuasinonexpansiveOn (Set.univ : Set H) T

/-- Unfolding `FirmlyQuasinonexpansive` recovers the whole-space restriction formulation. -/
@[simp] theorem firmlyQuasinonexpansive_iff_firmlyQuasinonexpansiveOn_univ {T : H → H} :
    FirmlyQuasinonexpansive T ↔ FirmlyQuasinonexpansiveOn (Set.univ : Set H) T := by
  rfl

/-- On the whole space, firm quasinonexpansiveness is exactly the standard fixed-point inequality
`‖T x - y‖² + ‖T x - x‖² ≤ ‖x - y‖²` against fixed points `y` of `T`. -/
theorem firmlyQuasinonexpansive_iff {T : H → H} :
    FirmlyQuasinonexpansive T ↔
      ∀ x y : H, T y = y → ‖T x - y‖ ^ 2 + ‖T x - x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  constructor
  · intro h x y hy
    change IsFirmlyQuasinonexpansiveOn (fun z : Set.univ ↦ T z) at h
    simpa [norm_sub_rev] using h ⟨x, by simp⟩ ⟨y, by simp⟩ hy
  · intro h
    change IsFirmlyQuasinonexpansiveOn (fun z : Set.univ ↦ T z)
    intro x y hy
    simpa [norm_sub_rev] using h (x : H) (y : H) hy

/-- Definition 4.1(v): `T : D → H` is quasinonexpansive when it does not increase distance to any
fixed point in `D`. -/
def IsQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) → ‖T x - y‖ ≤ ‖(x : H) - y‖

/-- Definition 4.1(v) restated: `IsQuasinonexpansiveOn` unfolds to its defining distance
inequality against subtype fixed points. -/
theorem isQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) → ‖T x - y‖ ≤ ‖(x : H) - y‖ := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is quasinonexpansive on `D` when its
restriction to `D` is quasinonexpansive. -/
def QuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted fixed-point formulation
rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: convert fixed points in `D` into fixed points of the subtype restriction.
theorem quasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    QuasinonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ fixedPointSetOn D T, ‖T x - y‖ ≤ ‖x - y‖ := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    simpa using h ⟨x, hx⟩ ⟨y, hyD⟩ hyfix
  · intro h x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa using h x x.2 y hy'

/-- A `1`-Lipschitz map on `D` is quasinonexpansive there. -/
theorem LipschitzOnWith.quasinonexpansiveOn {D : Set H} {T : H → H}
    (hT : LipschitzOnWith 1 T D) :
    QuasinonexpansiveOn D T := by
  rw [quasinonexpansiveOn_iff]
  intro x hx y hy
  rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfixed⟩
  have hxy : ‖T x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    simpa [hyfixed, dist_eq_norm] using hT.dist_le_mul x hx y hyD
  simpa using hxy

/-- Definition 4.1(vi): `T : D → H` is strictly quasinonexpansive when every non-fixed point of
`D` moves strictly closer to each fixed point in `D`. -/
def IsStrictlyQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) → T x ≠ (x : H) → ‖T x - y‖ < ‖(x : H) - y‖

/-- Definition 4.1(vi) restated: `IsStrictlyQuasinonexpansiveOn` unfolds to its defining strict
inequality against subtype fixed points. -/
theorem isStrictlyQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsStrictlyQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) → T x ≠ (x : H) → ‖T x - y‖ < ‖(x : H) - y‖ := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is strictly quasinonexpansive on `D` when its
restriction to `D` is strictly quasinonexpansive. -/
def StrictlyQuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsStrictlyQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: strict quasinonexpansiveness of the
restricted map rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: the subtype condition `T x ≠ x` is the same as ambient non-membership in the
-- fixed-point set.
theorem strictlyQuasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    StrictlyQuasinonexpansiveOn D T ↔
      ∀ x ∈ D \ fixedPointSetOn D T, ∀ y ∈ fixedPointSetOn D T, ‖T x - y‖ < ‖x - y‖ := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    have hxnot : T x ≠ x := by
      intro hfix
      exact hx.2 <| mem_fixedPointSetOn_iff.mpr ⟨hx.1, hfix⟩
    simpa using h ⟨x, hx.1⟩ ⟨y, hyD⟩ hyfix hxnot
  · intro h x y hy hnot
    have hx : (x : H) ∈ D \ fixedPointSetOn D T := by
      refine ⟨x.2, ?_⟩
      intro hxfix
      exact hnot <| mem_fixedPointSetOn_iff.mp hxfix |>.2
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa using h x hx y hy'

/-- A strictly quasinonexpansive self-map on `D` is quasinonexpansive there. -/
theorem StrictlyQuasinonexpansiveOn.quasinonexpansiveOn {D : Set H} {T : H → H}
    (hT : StrictlyQuasinonexpansiveOn D T) :
    QuasinonexpansiveOn D T := by
  rw [quasinonexpansiveOn_iff]
  rw [strictlyQuasinonexpansiveOn_iff] at hT
  intro x hx y hy
  by_cases hxFixed : x ∈ fixedPointSetOn D T
  · rw [mem_fixedPointSetOn_iff] at hxFixed
    rcases hxFixed with ⟨_, hxEq⟩
    simp [hxEq]
  · exact le_of_lt (hT x ⟨hx, hxFixed⟩ y hy)

end
