/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.12 is source-facing in the chapter's nesterovHyperplane-separation domain.

Primary domain:
- affine hyperplanes and set separation in a real inner-product space. Specializing
  `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation.

Relevant sampled declarations:
- `AffineHyperplane`
- `AffineHyperplane.SeparatesPointFrom`
- `AffineHyperplane.StrictlySeparatesPointFrom`
- `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side`

Best owner abstraction:
- `AffineHyperplane`

Source/core/bridge triage:
- source-facing: the notions that a fixed nesterovHyperplane separates, strictly separates, or strongly
  separates two sets, together with the existential set-level predicates
  `AreSeparable`, `AreStrictlySeparable`, and `AreStronglySeparable`;
- core/canonical: `AffineHyperplane`, whose primitive data are a nonzero normal vector and an
  offset;
- bridge/view: the direct coordinate characterizations
  `areSeparable_iff`, `areStrictlySeparable_iff`, `areStronglySeparable_iff`.

Primitive data:
- the nonzero normal vector and offset packaged by `AffineHyperplane`.

Derived API:
- the owner-level separation predicates on `AffineHyperplane`;
- the existential set-level separation predicates;
- the direct coordinate companion equivalences.

This file now defines the later two-set separation layer directly on top of the upstream owner
`AffineHyperplane`, so the earlier point/support file `Definition_3_1_4_1` no longer carries
extra later-chapter public API. The repeated nesterovHyperplane/support/point-separation clauses from the
textbook entry are already owned by `Definition_3_1_4_1`; this file adds only the genuinely new
two-set separation layer.
-/

local notation "HPlane" => AffineHyperplane E

namespace AffineHyperplane

/-- `H` separates `Q₁` and `Q₂` when they lie in opposite closed half-spaces of `H`. -/
def SeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  Q₁ ⊆ H.closedLowerHalfspace ∧
    Q₂ ⊆ H.closedUpperHalfspace

/-- `H` strictly separates `Q₁` and `Q₂` when it separates them and at least one of the two
defining inequalities is strict. -/
def StrictlySeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  H.SeparatesSets Q₁ Q₂ ∧
    (Q₁ ⊆ H.openLowerHalfspace ∨ Q₂ ⊆ H.openUpperHalfspace)

/-- `H` strongly separates `Q₁` and `Q₂` when they lie in opposite open half-spaces of `H`. -/
def StronglySeparatesSets (H : HPlane) (Q₁ Q₂ : Set E) : Prop :=
  Q₁ ⊆ H.openLowerHalfspace ∧
    Q₂ ⊆ H.openUpperHalfspace

end AffineHyperplane

/-- Definition 3.12 (1): two sets are separable when some nonzero normal vector and offset define
a nesterovHyperplane whose opposite closed half-spaces contain the two sets. -/
def AreSeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.SeparatesSets Q₁ Q₂

/-- Definition 3.12 (2): two sets are strictly separable when some nesterovHyperplane separates them and
at least one of the two half-space inequalities is strict. -/
def AreStrictlySeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.StrictlySeparatesSets Q₁ Q₂

/-- Definition 3.12 (3): two sets are strongly separable when some nesterovHyperplane places them in
opposite open half-spaces; this is the owner-level form of the source inequality
`sup_{x ∈ Q₁} ⟪g, x⟫ < γ < inf_{y ∈ Q₂} ⟪g, y⟫`. -/
def AreStronglySeparable (Q₁ Q₂ : Set E) : Prop :=
  ∃ H : HPlane, H.StronglySeparatesSets Q₁ Q₂

/-- The empty set and any singleton are strongly separable in a nontrivial real inner-product
space. This is the owner-level empty-case companion used by the later point-versus-set corollary.
-/
-- Proof sketch: choose any nonzero normal vector and place the offset one unit below
-- `⟪g, x⟫`, so the lower-side condition is vacuous on `∅` and the singleton lies strictly in the
-- upper open half-space.
theorem areStronglySeparable_empty_singleton [Nontrivial E] (x : E) :
    AreStronglySeparable (∅ : Set E) ({x} : Set E) := by
  obtain ⟨g, hg⟩ := exists_ne (0 : E)
  refine ⟨⟨g, hg, inner ℝ g x - 1⟩, ?_⟩
  constructor
  · intro y hy
    simp at hy
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    change inner ℝ g x - 1 < inner ℝ g x
    linarith

/-- `AreSeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ` defining a
separating nesterovHyperplane. -/
-- Proof sketch: unpack an `AffineHyperplane` witness into its normal vector and offset, and
-- conversely package any nonzero `g` and offset `γ` into the corresponding affine nesterovHyperplane.
theorem areSeparable_iff {Q₁ Q₂ : Set E} :
    AreSeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        (∀ x ∈ Q₁, inner ℝ g x ≤ γ) ∧
          ∀ y ∈ Q₂, γ ≤ inner ℝ g y := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    constructor
    · intro x hx
      exact hH.1 hx
    · intro y hy
      exact hH.2 hy
  · rintro ⟨g, hg, γ, hQ₁, hQ₂⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    constructor
    · intro x hx
      exact hQ₁ x hx
    · intro y hy
      exact hQ₂ y hy

/-- `AreStrictlySeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ`
realizing a strict separation. -/
-- Proof sketch: as in `areSeparable_iff`, pass back and forth between an `AffineHyperplane`
-- witness and its normal-offset coordinates; the strictness disjunction is preserved verbatim.
theorem areStrictlySeparable_iff {Q₁ Q₂ : Set E} :
    AreStrictlySeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        ((∀ x ∈ Q₁, inner ℝ g x ≤ γ) ∧
          ∀ y ∈ Q₂, γ ≤ inner ℝ g y) ∧
            ((∀ x ∈ Q₁, inner ℝ g x < γ) ∨
              ∀ y ∈ Q₂, γ < inner ℝ g y) := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro x hx
        exact hH.1.1 hx
      · intro y hy
        exact hH.1.2 hy
    · rcases hH.2 with hQ₁ | hQ₂
      · left
        intro x hx
        exact hQ₁ hx
      · right
        intro y hy
        exact hQ₂ hy
  · rintro ⟨g, hg, γ, hsep, hstrict⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro x hx
        exact hsep.1 x hx
      · intro y hy
        exact hsep.2 y hy
    · rcases hstrict with hQ₁ | hQ₂
      · left
        intro x hx
        exact hQ₁ x hx
      · right
        intro y hy
        exact hQ₂ y hy

/-- `AreStronglySeparable` is equivalent to the existence of coordinate data `g ≠ 0`, `γ`
realizing a strong separation. -/
-- Proof sketch: unpack or repackage the `AffineHyperplane` witness exactly as in
-- `areSeparable_iff`, using the open-halfspace form of strong separation.
theorem areStronglySeparable_iff {Q₁ Q₂ : Set E} :
    AreStronglySeparable Q₁ Q₂ ↔
      ∃ g : E, ∃ _ : g ≠ 0, ∃ γ : ℝ,
        (∀ x ∈ Q₁, inner ℝ g x < γ) ∧
          ∀ y ∈ Q₂, γ < inner ℝ g y := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨H.normal, H.normal_ne_zero, H.offset, ?_⟩
    constructor
    · intro x hx
      exact hH.1 hx
    · intro y hy
      exact hH.2 hy
  · rintro ⟨g, hg, γ, hQ₁, hQ₂⟩
    refine ⟨⟨g, hg, γ⟩, ?_⟩
    constructor
    · intro x hx
      exact hQ₁ x hx
    · intro y hy
      exact hQ₂ y hy

namespace AreStronglySeparable

/-- Strong separation of `Q` from the singleton `{x}` yields a point-versus-set coordinate
witness: the same normal vector and offset define a separating nesterovHyperplane for `Q` and `x`, and
`x` lies strictly above it. This is the canonical singleton-right bridge from the owner predicate
to the coordinate point-separation API. -/
theorem exists_separatesPointFromWith {Q : Set E} {x : E}
    (h : AreStronglySeparable Q ({x} : Set E)) :
    ∃ g : E, ∃ γ : ℝ, SeparatesPointFromWith Q x g γ ∧ γ < inner ℝ g x := by
  rcases areStronglySeparable_iff.mp h with ⟨g, hg, γ, hQ, hx⟩
  refine ⟨g, γ, ?_, ?_⟩
  · refine ⟨hg, ?_⟩
    constructor
    · intro y hy
      exact (hQ y hy).le
    · exact (hx x (by simp : x ∈ ({x} : Set E))).le
  · simpa using hx x (by simp : x ∈ ({x} : Set E))

end AreStronglySeparable
