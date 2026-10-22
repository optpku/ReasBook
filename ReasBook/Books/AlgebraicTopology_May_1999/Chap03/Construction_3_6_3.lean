/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Theorem_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/-- The source-facing object `fH` of `E(G/H)`, represented by an arrow `f : b ⟶ x`, viewed inside
the canonical owner `CategoryOfElements (associatedAction b (End b ⧸ H))`. -/
abbrev orbitSubgroupCoveringObjOfHom (b : B) (H : Subgroup (End b)) {x : B} (f : b ⟶ x) :
    (associatedAction b (End b ⧸ H)).Elements :=
  ⟨x, Quotient.mk'' (f, ((1 : End b) : End b ⧸ H))⟩

/-- Construction 3.6.3: an element `h ∈ H` defines the corresponding morphism `fH ⟶ f'H` in the
orbit covering, realized in the canonical category-of-elements owner. -/
noncomputable def orbitSubgroupCoveringHomOfSubgroup (b : B) (H : Subgroup (End b))
    {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (h : H) :
    orbitSubgroupCoveringObjOfHom b H f ⟶ orbitSubgroupCoveringObjOfHom b H f' :=
  CategoryOfElements.homMk _ _ (inv f ≫ h.1 ≫ f') <| by
    change Quotient.mk'' (f ≫ inv f ≫ h.1 ≫ f', ((1 : End b) : End b ⧸ H)) =
      Quotient.mk'' (f', ((1 : End b) : End b ⧸ H))
    apply Quotient.sound
    change MulAction.orbitRel (End b) ((b ⟶ x') × (End b ⧸ H))
      (f ≫ inv f ≫ h.1 ≫ f', ((1 : End b) : End b ⧸ H)) (f', ((1 : End b) : End b ⧸ H))
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
    refine ⟨(h : End b), ?_⟩
    ext
    · change (h : End b) • (f ≫ inv f ≫ h.1 ≫ f') = f'
      rw [orbitCoveringHomMulAction_smul]
      simp
    · change (h : End b) • ((1 : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H)
      apply QuotientGroup.eq.mpr
      simp [h.2]

/-- The canonical projection from `E(G/H)` to `B` sends the morphism determined by `h ∈ H` to the
base-groupoid arrow `f⁻¹ ≫ h ≫ f'`. -/
@[simp] theorem orbitSubgroupCoveringProjection_map_homOfSubgroup (b : B)
    (H : Subgroup (End b)) {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (h : H) :
    (CategoryOfElements.π (associatedAction b (End b ⧸ H))).map
        (orbitSubgroupCoveringHomOfSubgroup b H f f' h) =
      inv f ≫ h.1 ≫ f' :=
  rfl

/-- A base-groupoid arrow `g : x ⟶ x'` occurs as a morphism `fH ⟶ f'H` in `E(G/H)` exactly when
it has the form `f⁻¹ ≫ h ≫ f'` for some `h ∈ H`. -/
theorem exists_orbitSubgroupCoveringHom_iff (b : B) (H : Subgroup (End b))
    {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (g : x ⟶ x') :
    (∃ α : orbitSubgroupCoveringObjOfHom b H f ⟶ orbitSubgroupCoveringObjOfHom b H f',
      (CategoryOfElements.π (associatedAction b (End b ⧸ H))).map α = g) ↔
        ∃ h : H, g = inv f ≫ h.1 ≫ f' := by
  constructor
  · rintro ⟨α, rfl⟩
    have hα := CategoryOfElements.map_snd α
    change Quotient.mk'' (f ≫ α.1, ((1 : End b) : End b ⧸ H)) =
      Quotient.mk'' (f', ((1 : End b) : End b ⧸ H)) at hα
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_symm] at hα
    rcases hα with ⟨k, hk⟩
    have hk_fst : (k : End b) • (f ≫ α.1) = f' := by
      simpa using congrArg Prod.fst hk
    have hk_snd : (k : End b) • ((1 : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H) := by
      simpa using congrArg Prod.snd hk
    have hk_mem : (k : End b) ∈ H := by
      have hk' : ((k : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H) := by
        simpa using hk_snd
      rw [QuotientGroup.eq] at hk'
      simpa using H.inv_mem hk'
    have hk_fst' : f ≫ α.1 = (k : End b) ≫ f' := by
      calc
        f ≫ α.1 = (k : End b) ≫ ((k : End b)⁻¹ ≫ (f ≫ α.1)) := by simp
        _ = (k : End b) ≫ f' := by
          rw [orbitCoveringHomMulAction_smul] at hk_fst
          simpa [Category.assoc] using congrArg ((· ≫ ·) (k : End b)) hk_fst
    refine ⟨⟨k, hk_mem⟩, ?_⟩
    calc
      α.1 = inv f ≫ (f ≫ α.1) := by simp
      _ = inv f ≫ ((k : End b) ≫ f') := by rw [hk_fst']
      _ = inv f ≫ (k : End b) ≫ f' := by simp
  · rintro ⟨h, rfl⟩
    exact ⟨orbitSubgroupCoveringHomOfSubgroup b H f f' h, rfl⟩
