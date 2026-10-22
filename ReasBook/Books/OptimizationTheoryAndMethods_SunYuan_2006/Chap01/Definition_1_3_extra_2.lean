/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Pointwise RealInnerProductSpace

-- Domain sampling for this file:
-- * Primary domain: convex cones in ordered modules.
-- * Source-facing layer: `SunYuanIsCone` and `positiveHull` keep the textbook set-level notions used in
--   the statement of Definition 1.3-extra-2.
-- * Core/canonical layer: `ConvexCone 𝕜 E` is the bundled owner for convex-cone structure, with
--   `ConvexCone.hull` as the canonical owner of the smallest convex cone containing a set.
-- * Bridge/view layer: `IsConvexCone` is a nonempty set-level view of that bundled owner, while
--   `positiveHull_eq_hull` and `nonnegativeOrthant_eq_positive` connect the source wording to the
--   canonical objects where the semantics agree exactly.

section Chapter01Definition13Extra2

section ConeOwners

variable {𝕜 E : Type*}

/-- Chapter01 Definition 1.3-extra-2 (1): a nonempty set is a cone if it is closed under
multiplication by positive scalars. -/
def SunYuanIsCone (𝕜 : Type*) [Zero 𝕜] [LT 𝕜] [SMul 𝕜 E] (C : Set E) : Prop :=
  Set.Nonempty C ∧ ∀ ⦃a : 𝕜⦄, 0 < a → ∀ ⦃x : E⦄, x ∈ C → a • x ∈ C

/-- Unfolding formula for `SunYuanIsCone`. -/
theorem sunYuanIsCone_iff [Zero 𝕜] [LT 𝕜] [SMul 𝕜 E] {C : Set E} :
    SunYuanIsCone 𝕜 C ↔
      Set.Nonempty C ∧
        (∀ ⦃a : 𝕜⦄, 0 < a → ∀ ⦃x : E⦄, x ∈ C → a • x ∈ C) :=
  Iff.rfl

/-- The positive hull of `S` is the set of positive scalar multiples of points of `S`. -/
def positiveHull (𝕜 : Type*) [Zero 𝕜] [LT 𝕜] [SMul 𝕜 E] (S : Set E) : Set E :=
  { y | ∃ a : 𝕜, 0 < a ∧ ∃ x ∈ S, a • x = y }

section Primitive

/-- Membership in `positiveHull S` is the defining positive-scalar representation. -/
theorem mem_positiveHull_iff [Zero 𝕜] [LT 𝕜] [SMul 𝕜 E] {S : Set E} {y : E} :
    y ∈ positiveHull 𝕜 S ↔ ∃ a : 𝕜, 0 < a ∧ ∃ x ∈ S, a • x = y :=
  Iff.rfl

/-- The positive hull is contained in every source-level cone containing the original set. -/
theorem positiveHull_min [Zero 𝕜] [LT 𝕜] [SMul 𝕜 E] {S C : Set E} (hSC : S ⊆ C)
    (hC : SunYuanIsCone 𝕜 C) : positiveHull 𝕜 S ⊆ C := by
  rintro y ⟨a, ha, x, hx, rfl⟩
  exact hC.2 ha <| hSC hx

end Primitive

section Bundled

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
variable (𝕜)

/-- Chapter01 Definition 1.3-extra-2 (2): a nonempty set is a convex cone if it is already the
carrier of the canonical cone hull of itself. This keeps the source-facing set language while
making `ConvexCone.hull` the core owner abstraction. -/
def IsConvexCone (C : Set E) : Prop :=
  Set.Nonempty C ∧ (ConvexCone.hull 𝕜 C : Set E) = C

variable {𝕜}

/-- Unfolding formula for `IsConvexCone`. -/
theorem isConvexCone_iff_nonempty_hull_eq {C : Set E} :
    IsConvexCone 𝕜 C ↔ Set.Nonempty C ∧ (ConvexCone.hull 𝕜 C : Set E) = C :=
  Iff.rfl

/-- Primitive closure-data characterization of a source-level convex cone. -/
theorem isConvexCone_iff {C : Set E} :
    IsConvexCone 𝕜 C ↔
      SunYuanIsCone 𝕜 C ∧
        (∀ ⦃x y : E⦄, x ∈ C → y ∈ C → x + y ∈ C) := by
  constructor
  · rintro ⟨hC_nonempty, hC_hull⟩
    refine ⟨⟨hC_nonempty, ?_⟩, ?_⟩
    · intro a ha x hx
      have hax_hull : a • x ∈ ConvexCone.hull 𝕜 C :=
        (ConvexCone.hull 𝕜 C).smul_mem ha <| ConvexCone.subset_hull hx
      exact hC_hull ▸ hax_hull
    · intro x y hx hy
      have hxy_hull : x + y ∈ ConvexCone.hull 𝕜 C :=
        (ConvexCone.hull 𝕜 C).add_mem (ConvexCone.subset_hull hx) (ConvexCone.subset_hull hy)
      exact hC_hull ▸ hxy_hull
  · rintro ⟨hCone, hadd⟩
    refine ⟨hCone.1, ?_⟩
    refine Set.Subset.antisymm ?_ ConvexCone.subset_hull
    intro x hx
    let K : ConvexCone 𝕜 E :=
      { carrier := C
        smul_mem' := fun {_} ha {_} hx ↦ hCone.2 ha hx
        add_mem' := fun _ hx _ hy ↦ hadd hx hy }
    exact show x ∈ K from ConvexCone.hull_min subset_rfl hx

/-- The canonical bundled convex cone attached to a source-level convex cone. -/
abbrev IsConvexCone.toConvexCone {C : Set E} (hC : IsConvexCone 𝕜 C) : ConvexCone 𝕜 E :=
  (ConvexCone.hull 𝕜 C).copy C hC.2.symm

/-- A bundled `ConvexCone` with a nonempty carrier satisfies the source-level notion of convex
cone. -/
theorem ConvexCone.toIsConvexCone {C : ConvexCone 𝕜 E}
    (hC_nonempty : Set.Nonempty (C : Set E)) :
    IsConvexCone 𝕜 (C : Set E) := by
  refine ⟨hC_nonempty, Set.Subset.antisymm ?_ ConvexCone.subset_hull⟩
  intro x hx
  exact ConvexCone.hull_min subset_rfl hx

/-- A source-level convex cone agrees with its cone hull. This is a bridge to the canonical owner
`ConvexCone.hull`, not the primitive definition of the notion. -/
theorem IsConvexCone.hull_eq {C : Set E} (hC : IsConvexCone 𝕜 C) :
    (ConvexCone.hull 𝕜 C : Set E) = C :=
  hC.2

@[simp] theorem IsConvexCone.mem_hull_iff {C : Set E} (hC : IsConvexCone 𝕜 C) {x : E} :
    x ∈ ConvexCone.hull 𝕜 C ↔ x ∈ C := by
  simpa using congrArg (fun s : Set E ↦ x ∈ s) hC.hull_eq

/-- A source-level convex cone is, in particular, a source-level cone. -/
theorem IsConvexCone.isCone {C : Set E} (hC : IsConvexCone 𝕜 C) : SunYuanIsCone 𝕜 C :=
  (isConvexCone_iff.1 hC).1

/-- A source-level convex cone is closed under addition. -/
theorem IsConvexCone.add_mem {C : Set E} (hC : IsConvexCone 𝕜 C)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ C :=
  (isConvexCone_iff.1 hC).2 hx hy

end Bundled

/-- A source-level convex cone is convex as a subset. -/
theorem IsConvexCone.convex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    {C : Set E} (hC : IsConvexCone 𝕜 C) : Convex 𝕜 C :=
  hC.toConvexCone.convex

section Field

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The source-level positive hull agrees with mathlib's bundled cone hull on a convex set. -/
theorem positiveHull_eq_hull {S : Set E} (hS : Convex 𝕜 S) :
    positiveHull 𝕜 S = (ConvexCone.hull 𝕜 S : Set E) := by
  ext y
  rw [mem_positiveHull_iff]
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact (ConvexCone.mem_hull_of_convex hS).2 ⟨a, ha, ⟨x, hx, rfl⟩⟩
  · intro hy
    rcases (ConvexCone.mem_hull_of_convex hS).1 hy with ⟨a, ha, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

/-- Every point of `S` belongs to its positive hull, via the scalar `1`. -/
theorem subset_positiveHull {S : Set E} :
    S ⊆ positiveHull 𝕜 S := by
  intro x hx
  exact ⟨1, zero_lt_one, x, hx, one_smul 𝕜 x⟩

/-- The positive hull of a nonempty convex set is a source-level convex cone. -/
theorem isConvexCone_positiveHull {S : Set E}
    (hS_nonempty : Set.Nonempty S) (hS : Convex 𝕜 S) :
    IsConvexCone 𝕜 (positiveHull 𝕜 S) := by
  rw [positiveHull_eq_hull hS]
  exact ConvexCone.toIsConvexCone <|
    Set.Nonempty.mono ConvexCone.subset_hull hS_nonempty

/-- Chapter01 Definition 1.3-extra-2 (4): if `S` is nonempty and convex, then `positiveHull S`
is the smallest convex cone containing `S`. -/
theorem positiveHull_isLeast {S : Set E}
    (hS_nonempty : Set.Nonempty S) (hS : Convex 𝕜 S) :
    IsLeast { C : Set E | IsConvexCone 𝕜 C ∧ S ⊆ C } (positiveHull 𝕜 S) := by
  refine ⟨⟨isConvexCone_positiveHull hS_nonempty hS, subset_positiveHull⟩, ?_⟩
  intro C hC
  exact positiveHull_min hC.2 hC.1.isCone

end Field

end ConeOwners

section Orthants

variable {n : ℕ}

local notation "Coords" => Fin n → ℝ

/-- The source-level nonnegative orthant is exactly the canonical positive cone. -/
theorem nonnegativeOrthant_eq_positive :
    ({ x : Coords | ∀ i : Fin n, 0 ≤ x i } : Set Coords) =
      (ConvexCone.positive ℝ Coords : Set Coords) := by
  ext x
  change (∀ i : Fin n, 0 ≤ x i) ↔ 0 ≤ x
  constructor
  · intro hx i
    exact hx i
  · intro hx
    exact hx

/-- Chapter01 Definition 1.3-extra-2 (5): the nonnegative orthant of `ℝ^n` is a convex cone. -/
theorem isConvexCone_nonnegativeOrthant :
    IsConvexCone ℝ ({ x : Coords | ∀ i : Fin n, 0 ≤ x i } : Set Coords) := by
  have hPositive :
      IsConvexCone ℝ
        ((ConvexCone.positive ℝ Coords : ConvexCone ℝ Coords) : Set Coords) :=
    ConvexCone.toIsConvexCone ⟨0, by
      change 0 ≤ (0 : Coords)
      intro i
      simp⟩
  simpa [nonnegativeOrthant_eq_positive] using hPositive

/-- Chapter01 Definition 1.3-extra-2 (6): the positive orthant of `ℝ^n` is a convex cone. -/
theorem isConvexCone_positiveOrthant :
    IsConvexCone ℝ ({ x : Coords | ∀ i : Fin n, 0 < x i } : Set Coords) := by
  refine isConvexCone_iff.2 ⟨⟨⟨fun _ : Fin n ↦ (1 : ℝ), by simp⟩, ?_⟩, ?_⟩
  · intro a ha x hx i
    simpa using mul_pos ha (hx i)
  · intro x y hx hy i
    exact add_pos (hx i) (hy i)

end Orthants

section HalfSpaces

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The intersection of the closed half-spaces `{x | ⟪x, b i⟫ ≤ 0}` indexed by `ι`. The source's
finite-family formulation is the special case `ι = Fin m`. -/
def halfSpaceIntersection (b : ι → E) : Set E :=
  { x | ∀ i, ⟪x, b i⟫ ≤ (0 : ℝ) }

/-- Membership in `halfSpaceIntersection b` is the defining family of half-space inequalities. -/
theorem mem_halfSpaceIntersection_iff {b : ι → E} {x : E} :
    x ∈ halfSpaceIntersection b ↔ ∀ i, ⟪x, b i⟫ ≤ (0 : ℝ) :=
  Iff.rfl

/-- Chapter01 Definition 1.3-extra-2 (7): any intersection of half-spaces
`{x | ⟪x, b i⟫ ≤ 0}` is a convex cone, hence in particular any finite such intersection. -/
theorem isConvexCone_halfSpaceIntersection (b : ι → E) :
    IsConvexCone ℝ (halfSpaceIntersection b) := by
  refine isConvexCone_iff.2 ⟨⟨⟨0, by simp [halfSpaceIntersection]⟩, ?_⟩, ?_⟩
  · intro a ha x hx i
    have hxi : ⟪x, b i⟫ ≤ (0 : ℝ) := hx i
    simpa [halfSpaceIntersection, real_inner_smul_left] using
      mul_nonpos_of_nonneg_of_nonpos ha.le hxi
  · intro x y hx hy i
    simpa [halfSpaceIntersection, inner_add_left] using add_nonpos (hx i) (hy i)

end HalfSpaces

end Chapter01Definition13Extra2
