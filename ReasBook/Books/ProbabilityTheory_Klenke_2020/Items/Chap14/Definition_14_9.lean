/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory

universe u v

variable {ι : Type u} {Ω : ι → Type v}

/-- Definition 14.9 (3): the rectangular cylinder sets with finite base `J` whose coordinate sets
belong to the prescribed subclasses `ℰ i`. -/
def restrictedRectangularCylinderSetsWithBase (ℰ : ∀ i, Set (Set (Ω i))) (J : Finset ι) :
    Set (Set (∀ i, Ω i)) :=
  (fun A : ∀ j : J, Set (Ω j) ↦ cylinder J (Set.pi univ A)) ''
    Set.pi univ (fun j : J ↦ ℰ j.1)

/- Definition 14.9 (5) and (6): the global rectangular-cylinder owner is
`MeasureTheory.squareCylinders`; the textbook families `𝒵ᴿ` and `𝒵^{ℰ,R}` are its measurable and
`ℰ`-restricted instances. -/
recall MeasureTheory.squareCylinders

/-- Definition 14.9 (8): the family `𝒵_*^{ℰ,R}` of finite unions of rectangular cylinder sets
whose coordinates are chosen from the subclasses `ℰ i`. -/
def finiteUnionRestrictedRectangularCylinderSets (ℰ : ∀ i, Set (Set (Ω i))) :
    Set (Set (∀ i, Ω i)) :=
  {s |
    ∃ S : Finset (Set (∀ i, Ω i)),
      (S : Set (Set (∀ i, Ω i))) ⊆ squareCylinders ℰ ∧
        s = ⋃₀ (S : Set (Set (∀ i, Ω i)))}

-- Proof sketch: unfold the definition and keep the same finite witness family, now recorded in an
-- iff statement.
/-- Membership in `finiteUnionRestrictedRectangularCylinderSets ℰ` is equivalent to being the union
of a finite family of members of `MeasureTheory.squareCylinders ℰ`. -/
theorem mem_finiteUnionRestrictedRectangularCylinderSets_iff
    (ℰ : ∀ i, Set (Set (Ω i))) {s : Set (∀ i, Ω i)} :
    s ∈ finiteUnionRestrictedRectangularCylinderSets ℰ ↔
      ∃ S : Finset (Set (∀ i, Ω i)),
        (S : Set (Set (∀ i, Ω i))) ⊆ squareCylinders ℰ ∧
          s = ⋃₀ (S : Set (Set (∀ i, Ω i))) := by
  rfl

section Measurable

variable [∀ i, MeasurableSpace (Ω i)]

/-- Definition 14.9 (1): the cylinder sets with finite base `J`, i.e. preimages `X_J ⁻¹' A` of
measurable sets in the finite product over `J`. -/
def cylinderSetsWithBase (J : Finset ι) : Set (Set (∀ i, Ω i)) :=
  cylinder J '' {A : Set ((j : J) → Ω j) | MeasurableSet A}

-- Proof sketch: unfold the definition and read off the existential witness for the measurable
-- base set.
/-- Membership in `cylinderSetsWithBase J` means that the set is a cylinder over `J` with a
measurable base. -/
theorem mem_cylinderSetsWithBase_iff {J : Finset ι} {s : Set (∀ i, Ω i)} :
    s ∈ cylinderSetsWithBase J ↔
      ∃ A : Set ((j : J) → Ω j), MeasurableSet A ∧ s = cylinder J A := by
  simp [cylinderSetsWithBase, eq_comm]

/-- Definition 14.9 (2): the rectangular cylinder sets with finite base `J`, obtained by
specializing Definition 14.9 (3) to measurable coordinate sections. -/
def rectangularCylinderSetsWithBase (J : Finset ι) : Set (Set (∀ i, Ω i)) :=
  restrictedRectangularCylinderSetsWithBase (fun i ↦ {s : Set (Ω i) | MeasurableSet s}) J

/- Definition 14.9 (4): the family `𝒵` of all cylinder sets with arbitrary finite base is
`MeasureTheory.measurableCylinders Ω`. -/
recall MeasureTheory.measurableCylinders

/- Membership in the textbook family `𝒵` is exactly `MeasureTheory.mem_measurableCylinders`. -/
recall MeasureTheory.mem_measurableCylinders

/-- Definition 14.9 (7): the family `𝒵_*ᴿ` of finite unions of measurable rectangular cylinder
sets, i.e. the measurable specialization of Definition 14.9 (8). -/
def finiteUnionRectangularCylinderSets : Set (Set (∀ i, Ω i)) :=
  finiteUnionRestrictedRectangularCylinderSets (fun i ↦ {s : Set (Ω i) | MeasurableSet s})

-- Proof sketch: unfold the defining existential quantifier over the finite family of rectangular
-- cylinders.
/-- Membership in `finiteUnionRectangularCylinderSets` is given by a finite family of rectangular
cylinder sets whose union is the target set. -/
theorem mem_finiteUnionRectangularCylinderSets_iff {s : Set (∀ i, Ω i)} :
    s ∈ finiteUnionRectangularCylinderSets ↔
      ∃ S : Finset (Set (∀ i, Ω i)),
        (S : Set (Set (∀ i, Ω i))) ⊆
          squareCylinders (fun i ↦ {t : Set (Ω i) | MeasurableSet t}) ∧
          s = ⋃₀ (S : Set (Set (∀ i, Ω i))) := by
  rfl

-- Proof sketch: unpack the defining witness of a restricted rectangular cylinder and use the
-- measurability hypothesis on each coordinate set to view the same rectangle as an ordinary
-- measurable rectangle.
/-- If each `ℰ i` consists of measurable sets, then every `ℰ`-rectangular cylinder with base `J`
is an ordinary rectangular cylinder with the same base. -/
theorem restrictedRectangularCylinderSetsWithBase_subset_rectangularCylinderSetsWithBase
    (ℰ : ∀ i, Set (Set (Ω i))) (hℰ : ∀ i, ℰ i ⊆ {s : Set (Ω i) | MeasurableSet s})
    (J : Finset ι) :
    restrictedRectangularCylinderSetsWithBase ℰ J ⊆ rectangularCylinderSetsWithBase J := by
  intro s hs
  rcases hs with ⟨A, hA, rfl⟩
  refine ⟨A, ?_, rfl⟩
  have hA' : ∀ j : J, A j ∈ ℰ j.1 := by
    simpa [Set.mem_pi] using hA
  have hA'' : ∀ j : J, MeasurableSet (A j) := fun j ↦ hℰ j.1 (hA' j)
  simpa [rectangularCylinderSetsWithBase, restrictedRectangularCylinderSetsWithBase, Set.mem_pi]
    using hA''

-- Proof sketch: use monotonicity of `squareCylinders` with respect to the coordinate-set families
-- and the hypothesis `hℰ`.
/-- If each `ℰ i` consists of measurable sets, then every `ℰ`-rectangular cylinder belongs to the
full family of rectangular cylinders. -/
theorem restrictedRectangularCylinderSets_subset_rectangularCylinderSets
    (ℰ : ∀ i, Set (Set (Ω i))) (hℰ : ∀ i, ℰ i ⊆ {s : Set (Ω i) | MeasurableSet s}) :
    squareCylinders ℰ ⊆
      squareCylinders (fun i ↦ {s : Set (Ω i) | MeasurableSet s}) := by
  intro s hs
  rcases hs with ⟨J, A, hA, rfl⟩
  refine ⟨J, A, ?_, rfl⟩
  have hA' : ∀ i, A i ∈ ℰ i := by
    simpa [Set.mem_pi] using hA
  have hA'' : ∀ i, MeasurableSet (A i) := fun i ↦ hℰ i (hA' i)
  simpa [Set.mem_pi] using hA''

end Measurable
