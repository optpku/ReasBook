/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_13
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Classical
open FreeGroupBasis

set_option autoImplicit false

noncomputable section

namespace FGroupPresentation

/-
Primary domain: combinatorial group theory of finite presentations of `F`-groups.

Layer triage:
- `source-facing`: a concrete finite presentation on generators `x_i` and `y_j` with torsion
  relators `x_i ^ {m_i}` and one final relator `x_1 ... x_p q`, where `q` is an orientable or
  nonorientable quadratic surface word.
- `core/canonical`: `PresentedGroup` is the owner object for groups given by generators and
  relators, `IsFGroup` from Definition `3-5-3` is the owner predicate for the hypothesis,
  `(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct` is the chapter owner for the orientable
  surface relator, and `SurfaceGroup.nonorientableRelator` is the chapter owner for the
  nonorientable surface relator.
- `bridge/view`: the theorem below expresses the textbook normal form as a concrete pair of
  canonical relator families for `PresentedGroup`.

Domain sampling:
1. `PresentedGroup` is the canonical mathlib object for a group with a specified presentation.
2. `IsFGroup` from Definition `3-5-3` is the project owner predicate for the hypothesis.
3. `(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct` from Proposition `1-6-8` is the
   project owner relator for the orientable surface word, so this file should not rebuild it by
   hand with `Fin (2 * g)` arithmetic.
4. `SurfaceGroup.nonorientableRelator` from Proposition `2-5-13` is the project owner relator for
   the nonorientable surface word.
Primitive vs. derived:
- primitive data: the torsion exponents `m : Fin p → ℕ` and the canonical surface relator from
  the orientable or nonorientable branch;
- derived API: the relator families `orientableStandardRelators` and
  `nonorientableStandardRelators` built by adjoining the torsion relators and the ordered product
  `x₁ ⋯ xₚ`.
-/

/-- The ordered product `x_1 ... x_p` of the torsion generators. -/
def xProduct (p : ℕ) (Y : Type*) : FreeGroup (Fin p ⊕ Y) :=
  (List.ofFn fun i : Fin p ↦ FreeGroup.of (Sum.inl i)).prod

/-- The torsion relators `x_i ^ {m_i}` appearing in the normal form presentation. -/
def torsionRelators {p : ℕ} {Y : Type*} (m : Fin p → ℕ) : Set (FreeGroup (Fin p ⊕ Y)) :=
  Set.range fun i : Fin p ↦ FreeGroup.of (Sum.inl i) ^ m i

/-- The orientable relator family from Proposition `3-5-4`, using the canonical paired-index
surface relator from Proposition `1-6-8`. -/
def orientableStandardRelators (p g : ℕ) (m : Fin p → ℕ) :
    Set (FreeGroup (Fin p ⊕ (Fin g ⊕ Fin g))) :=
  torsionRelators m ∪
    {xProduct p (Fin g ⊕ Fin g) *
      FreeGroup.map Sum.inr (ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct}

/-- The nonorientable relator family from Proposition `3-5-4`, using the canonical nonorientable
surface relator from Proposition `2-5-13`. -/
def nonorientableStandardRelators (p g : ℕ) (m : Fin p → ℕ) :
    Set (FreeGroup (Fin p ⊕ Fin g)) :=
  torsionRelators m ∪
    {xProduct p (Fin g) *
      FreeGroup.map Sum.inr (SurfaceGroup.nonorientableRelator g)}

@[simp] theorem xProduct_zero (Y : Type*) :
    xProduct 0 Y = 1 := by
  simp [xProduct]

@[simp] theorem torsionRelators_zero (Y : Type*) :
    torsionRelators (fun i : Fin 0 ↦ nomatch i) = (∅ : Set (FreeGroup (Fin 0 ⊕ Y))) := by
  ext w
  simp [torsionRelators]

@[simp] theorem orientableStandardRelators_zero (g : ℕ) :
    orientableStandardRelators 0 g (fun i ↦ nomatch i) =
      {FreeGroup.map Sum.inr (ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} := by
  simp [orientableStandardRelators]

@[simp] theorem nonorientableStandardRelators_zero (g : ℕ) :
    nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
      {FreeGroup.map Sum.inr (SurfaceGroup.nonorientableRelator g)} := by
  simp [nonorientableStandardRelators]

@[simp] theorem freeGroupCongr_emptySum_map_inr {Y : Type*} (w : FreeGroup Y) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w) = w := by
  calc
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w)
      = FreeGroup.map (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w) := rfl
    _ = FreeGroup.map ((Equiv.emptySum (Fin 0) Y) ∘ Sum.inr) w := by
      rw [FreeGroup.map.comp]
    _ = FreeGroup.map (fun y ↦ y) w := by
      refine congrArg (fun f ↦ FreeGroup.map f w) ?_
      ext y
      simp
    _ = w := FreeGroup.map.id' w

@[simp] theorem freeGroupCongr_emptySum_image_orientableStandardRelators_zero (g : ℕ) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g)) ''
      orientableStandardRelators 0 g (fun i ↦ nomatch i) =
        {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} := by
  rw [orientableStandardRelators_zero, Set.image_singleton]
  rw [freeGroupCongr_emptySum_map_inr]

@[simp] theorem freeGroupCongr_emptySum_image_nonorientableStandardRelators_zero (g : ℕ) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g)) ''
      nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
        {SurfaceGroup.nonorientableRelator g} := by
  rw [nonorientableStandardRelators_zero, Set.image_singleton]
  rw [freeGroupCongr_emptySum_map_inr]

/-- The torsion-free orientable standard presentation is the canonical orientable surface-group
owner from Chapter `2`. -/
def orientableStandardMulEquivSurfaceGroup (g : ℕ) :
    PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      SurfaceGroup.Orientable g := by
  let e :=
    PresentedGroup.equivPresentedGroup
      (orientableStandardRelators 0 g (fun i ↦ nomatch i))
      (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g))
  let hrels :
      FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g)) ''
        orientableStandardRelators 0 g (fun i ↦ nomatch i) =
          {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} :=
    freeGroupCongr_emptySum_image_orientableStandardRelators_zero g
  show PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      PresentedGroup {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct}
  exact
    cast
      (congrArg
        (fun S ↦
          PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
            PresentedGroup S)
        hrels)
      e

/-- The torsion-free nonorientable standard presentation is the canonical nonorientable
surface-group owner from Chapter `2`. -/
def nonorientableStandardMulEquivSurfaceGroup (g : ℕ) :
    PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      SurfaceGroup.Nonorientable g := by
  let e :=
    PresentedGroup.equivPresentedGroup
      (nonorientableStandardRelators 0 g (fun i ↦ nomatch i))
      (Equiv.emptySum (Fin 0) (Fin g))
  let hrels :
      FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g)) ''
        nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
          {SurfaceGroup.nonorientableRelator g} :=
    freeGroupCongr_emptySum_image_nonorientableStandardRelators_zero g
  show PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      PresentedGroup {SurfaceGroup.nonorientableRelator g}
  exact
    cast
      (congrArg
        (fun S ↦
          PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
            PresentedGroup S)
        hrels)
      e

variable {G : Type u} [Group G]

/-- Proposition 3-5-4: every `F`-group admits either an orientable standard presentation with
relator family `x_i ^ {m_i}` together with `x_1 ... x_p [y_1, y_2] ... [y_{2g-1}, y_{2g}]`, or a
nonorientable standard presentation with relator family `x_i ^ {m_i}` together with
`x_1 ... x_p y_1^2 ... y_g^2`, with all exponents `m_i > 1`. -/
-- Proof sketch: begin with the strictly quadratic relator-root presentation furnished by
-- `IsFGroup`, apply the Nielsen normalization cited in the text to isolate the torsion generators
-- `x_i`, and then use the final Tietze transformation introducing `x_p` so that the last relator
-- becomes `x_1 ... x_p q`; the cyclic quadratic word `q` is either the orientable or the
-- nonorientable surface word.
theorem exists_standard_surface_presentation_of_isFGroup (hG : IsFGroup G) :
    (∃ (p g : ℕ) (m : Fin p → ℕ),
      ∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
        ∀ i, 1 < m i) ∨
    (∃ (p g : ℕ) (m : Fin p → ℕ),
      ∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
        ∀ i, 1 < m i) := sorry

/-- A standard surface presentation of the form exhibited in Proposition `3-5-4` makes the
ambient group into an `F`-group. -/
-- Proof sketch: rewrite the displayed standard presentation as the finite presentation required by
-- Definition `3-5-3`. The relator roots are the torsion generators together with the surface
-- relator, which form a finite strictly quadratic system with cyclic star graph by the
-- normalization analysis behind Proposition `3-5-4`.
theorem isFGroup_of_standardSurfacePresentation
    (hG :
      (∃ (p g : ℕ) (m : Fin p → ℕ),
        ∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
          ∀ i, 1 < m i) ∨
      (∃ (p g : ℕ) (m : Fin p → ℕ),
        ∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
          ∀ i, 1 < m i)) :
    IsFGroup G := sorry

end FGroupPresentation
