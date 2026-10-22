/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.1.4.1 lives in the affine-nesterovHyperplane / support / point-separation domain.

Sampled owner-style declarations:
- this file's source-facing owner `AffineHyperplane`, whose primitive data are a nonzero normal
  vector and an offset;
- the coordinate carrier bridge `nesterovHyperplane g γ`, used downstream when the source is written in
  normal-offset coordinates;
- mathlib `AffineSubspace`, the ambient carrier-level affine owner;
- mathlib `AffineSubspace.SOppSide`, the ambient side-relation API relative to an affine carrier.

Best owner abstraction:
- `AffineHyperplane`

Primitive data:
- a nonzero normal vector and an offset.

Derived API:
- the carrier and the four half-spaces of an affine nesterovHyperplane;
- supporting and point-separation predicates on the owner;
- the coordinate bridge surface `nesterovHyperplane`, `IsSupportingHyperplane`,
  `SeparatesPointFromWith`, and `StrictlySeparatesPointFromWith`.

`AffineSubspace` and the side-relation API are useful ambient comparison points, but they do not
replace the chapter owner here: the source-facing object carries chosen normal/offset coordinates,
and the later chapter theorems repeatedly reuse that owner-level data directly.
-/

/-- Definition 3.1.4.1: an affine nesterovHyperplane in a real inner-product space is determined by a
nonzero normal vector and an offset. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `ℝⁿ` presentation. The carrier set and the support/separation predicates below are
derived from this owner object. -/
structure AffineHyperplane (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  normal_ne_zero : normal ≠ 0
  offset : ℝ

local notation "HPlane" => AffineHyperplane E

namespace AffineHyperplane

/-- The carrier of an affine nesterovHyperplane is its defining level set. -/
def carrier (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x = H.offset}

/-- An affine nesterovHyperplane coerces to its defining carrier set. This is not `SetLike`, since
different normal/offset pairs can determine the same geometric nesterovHyperplane. -/
instance : Coe (AffineHyperplane E) (Set E) where
  coe H := H.carrier

/-- An affine nesterovHyperplane can be used as its carrier membership predicate. -/
instance : Membership E (AffineHyperplane E) where
  mem H x := x ∈ (H : Set E)

/-- Membership in the coerced set of an affine nesterovHyperplane is exactly its defining level-set
equation. -/
@[simp] theorem mem_coe {H : HPlane} {x : E} :
    x ∈ (H : Set E) ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- Membership in an affine nesterovHyperplane is exactly the defining inner-product equation
`⟪H.normal, x⟫ = H.offset`. -/
@[simp] theorem mem_iff {H : HPlane} {x : E} :
    x ∈ H ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- Membership in the carrier of `H` is exactly the defining inner-product equation
`⟪H.normal, x⟫ = H.offset`. -/
@[simp] theorem mem_carrier_iff {H : HPlane} {x : E} :
    x ∈ H.carrier ↔ inner ℝ H.normal x = H.offset := Iff.rfl

/-- The closed half-space on the lower side of `H`. -/
def closedLowerHalfspace (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x ≤ H.offset}

/-- Membership in the closed lower half-space of `H` is the defining inequality
`⟪H.normal, x⟫ ≤ H.offset`. -/
@[simp] theorem mem_closedLowerHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.closedLowerHalfspace ↔ inner ℝ H.normal x ≤ H.offset := Iff.rfl

/-- The closed half-space on the upper side of `H`. -/
def closedUpperHalfspace (H : HPlane) : Set E :=
  {x | H.offset ≤ inner ℝ H.normal x}

/-- Membership in the closed upper half-space of `H` is the defining inequality
`H.offset ≤ ⟪H.normal, x⟫`. -/
@[simp] theorem mem_closedUpperHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.closedUpperHalfspace ↔ H.offset ≤ inner ℝ H.normal x := Iff.rfl

/-- The open half-space on the lower side of `H`. -/
def openLowerHalfspace (H : HPlane) : Set E :=
  {x | inner ℝ H.normal x < H.offset}

/-- Membership in the open lower half-space of `H` is the defining strict inequality
`⟪H.normal, x⟫ < H.offset`. -/
@[simp] theorem mem_openLowerHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.openLowerHalfspace ↔ inner ℝ H.normal x < H.offset := Iff.rfl

/-- The open half-space on the upper side of `H`. -/
def openUpperHalfspace (H : HPlane) : Set E :=
  {x | H.offset < inner ℝ H.normal x}

/-- Membership in the open upper half-space of `H` is the defining strict inequality
`H.offset < ⟪H.normal, x⟫`. -/
@[simp] theorem mem_openUpperHalfspace_iff {H : HPlane} {x : E} :
    x ∈ H.openUpperHalfspace ↔ H.offset < inner ℝ H.normal x := Iff.rfl

/-- `H` supports `Q` when `Q` lies in the closed lower half-space of `H` and `H` meets `Q`. -/
def IsSupporting (H : HPlane) (Q : Set E) : Prop :=
  Q ⊆ H.closedLowerHalfspace ∧ (Q ∩ H.carrier).Nonempty

namespace IsSupporting

theorem le_offset {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) {x : E} (hx : x ∈ Q) : inner ℝ H.normal x ≤ H.offset := by
  exact h.1 hx

theorem contact_nonempty {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) : (Q ∩ H.carrier).Nonempty :=
  h.2

theorem exists_contact_point {H : HPlane} {Q : Set E}
    (h : H.IsSupporting Q) : ∃ x ∈ Q, inner ℝ H.normal x = H.offset := by
  rcases h.contact_nonempty with ⟨x, hxQ, hxH⟩
  exact ⟨x, hxQ, mem_carrier_iff.mp hxH⟩

end IsSupporting

/-- `H` separates the point `x₀` from `Q` when `Q` lies in the closed lower half-space of `H` and
`x₀` lies on or beyond the opposite side. -/
def SeparatesPointFrom (H : HPlane) (Q : Set E) (x₀ : E) : Prop :=
  Q ⊆ H.closedLowerHalfspace ∧
    x₀ ∈ H.closedUpperHalfspace

/-- `H` strictly separates the point `x₀` from `Q` when one of the two defining inequalities is
strict. -/
def StrictlySeparatesPointFrom (H : HPlane) (Q : Set E) (x₀ : E) : Prop :=
  H.SeparatesPointFrom Q x₀ ∧
    (Q ⊆ H.openLowerHalfspace ∨ x₀ ∈ H.openUpperHalfspace)

end AffineHyperplane

/-- Coordinate bridge for the carrier of the nesterovHyperplane with normal vector `g` and offset `γ`.
When `g = 0`, this level set is `∅` or `Set.univ`, so the mathematically faithful owner notion is
`AffineHyperplane`, not this unrestricted carrier. -/
def nesterovHyperplane (g : E) (γ : ℝ) : Set E :=
  {x | inner ℝ g x = γ}

/-- Membership in `nesterovHyperplane g γ` is exactly the defining inner-product equation
`⟪g, x⟫ = γ`. -/
@[simp] theorem mem_nesterovHyperplane_iff {g x : E} {γ : ℝ} :
    x ∈ nesterovHyperplane g γ ↔ inner ℝ g x = γ := Iff.rfl

@[simp] theorem AffineHyperplane.carrier_eq_hyperplane (H : HPlane) :
    H.carrier = nesterovHyperplane H.normal H.offset := rfl

/-- The nesterovHyperplane `nesterovHyperplane g γ` supports `Q` when `g ≠ 0` and `Q` lies in the closed half-space
`⟪g, x⟫ ≤ γ`, and the nesterovHyperplane actually meets `Q`. -/
def IsSupportingHyperplane (Q : Set E) (g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).IsSupporting Q

namespace IsSupportingHyperplane

theorem ne_zero {Q : Set E} {g : E} {γ : ℝ} (h : IsSupportingHyperplane Q g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem isSupporting {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).IsSupporting Q := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem le_offset {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) {x : E} (hx : x ∈ Q) : inner ℝ g x ≤ γ := by
  simpa using h.isSupporting.le_offset hx

theorem contact_nonempty {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) : (Q ∩ nesterovHyperplane g γ).Nonempty := by
  simpa using h.isSupporting.contact_nonempty

theorem exists_contact_point {Q : Set E} {g : E} {γ : ℝ}
    (h : IsSupportingHyperplane Q g γ) : ∃ x ∈ Q, inner ℝ g x = γ := by
  simpa using h.isSupporting.exists_contact_point

end IsSupportingHyperplane

namespace AffineHyperplane

@[simp] theorem isSupportingHyperplane_iff {H : HPlane} {Q : Set E} :
    IsSupportingHyperplane Q H.normal H.offset ↔ H.IsSupporting Q := by
  constructor
  · intro h
    simpa using h.isSupporting
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

/-- The nesterovHyperplane `nesterovHyperplane g γ` separates the point `x₀` from `Q` when `Q` lies in the closed
half-space `⟪g, x⟫ ≤ γ` and `x₀` lies on or beyond the opposite side. -/
def SeparatesPointFromWith (Q : Set E) (x₀ g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).SeparatesPointFrom Q x₀

namespace SeparatesPointFromWith

theorem ne_zero {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem separatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).SeparatesPointFrom Q x₀ := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem le_offset {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) {x : E} (hx : x ∈ Q) : inner ℝ g x ≤ γ := by
  exact h.separatesPointFrom.1 hx

theorem offset_le {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : SeparatesPointFromWith Q x₀ g γ) : γ ≤ inner ℝ g x₀ := by
  exact h.separatesPointFrom.2

end SeparatesPointFromWith

namespace AffineHyperplane

@[simp] theorem separatesPointFromWith_iff {H : HPlane} {Q : Set E} {x₀ : E} :
    SeparatesPointFromWith Q x₀ H.normal H.offset ↔ H.SeparatesPointFrom Q x₀ := by
  constructor
  · intro h
    simpa using h.separatesPointFrom
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

/-- The nesterovHyperplane `nesterovHyperplane g γ` strictly separates `x₀` from `Q` when it separates `x₀` from
`Q` and at least one of the two defining inequalities is strict. -/
def StrictlySeparatesPointFromWith (Q : Set E) (x₀ g : E) (γ : ℝ) : Prop :=
  ∃ hg : g ≠ 0, (⟨g, hg, γ⟩ : HPlane).StrictlySeparatesPointFrom Q x₀

namespace StrictlySeparatesPointFromWith

theorem ne_zero {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) : g ≠ 0 := by
  rcases h with ⟨hg, _⟩
  exact hg

theorem strictlySeparatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).StrictlySeparatesPointFrom Q x₀ := by
  rcases h with ⟨hg, hH⟩
  simpa using hH

theorem separatesPointFrom {Q : Set E} {x₀ g : E} {γ : ℝ}
    (h : StrictlySeparatesPointFromWith Q x₀ g γ) :
    (⟨g, h.ne_zero, γ⟩ : HPlane).SeparatesPointFrom Q x₀ :=
  h.strictlySeparatesPointFrom.1

end StrictlySeparatesPointFromWith

namespace AffineHyperplane

@[simp] theorem strictlySeparatesPointFromWith_iff {H : HPlane} {Q : Set E} {x₀ : E} :
    StrictlySeparatesPointFromWith Q x₀ H.normal H.offset ↔ H.StrictlySeparatesPointFrom Q x₀ := by
  constructor
  · intro h
    simpa using h.strictlySeparatesPointFrom
  · intro hH
    exact ⟨H.normal_ne_zero, hH⟩

end AffineHyperplane

end
