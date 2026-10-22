/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

-- Declarations for this item will be appended below by the statement pipeline.

-- Layer triage:
-- `source-facing`: a group `G`, a type `X` of defining generators, a set `R` of relators in the
-- free group on `X`, and the assertion that `(X; R)` presents `G` via a chosen equivalence
-- `PresentedGroup R ≃* G`.
-- `core/canonical`: `PresentedGroup R`, `PresentedGroup.of`, `PresentedGroup.closure_range_of`,
-- `PresentedGroup.mk_eq_one_iff`, and `Subgroup.normalClosure`.
-- `bridge/view`: the chosen presentation equivalence transports the canonical generators of
-- `PresentedGroup R` to the defining generators in `G`, and `FreeGroup.lift` evaluates words in
-- those generators.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for a group given by generators `X` and
--    relators `R`.
-- 2. `PresentedGroup.of` is the canonical image of a defining generator in the presented group.
-- 3. `PresentedGroup.closure_range_of` is the canonical statement that these images generate the
--    presented group.
-- 4. `PresentedGroup.mk_eq_one_iff` identifies the consequences of the relators with the normal
--    closure of `R`.
-- Primitive vs. derived:
-- the primitive source data are the generators `X`, the relator set `R`, and the chosen
-- identification `PresentedGroup R ≃* G`; the defining-generator subset of `G` and the
-- relator/consequence equations are derived from that canonical owner-side datum, so no parallel
-- alias for the equivalence is introduced.

variable {G : Type u} [Group G] {X : Type v} {R : Set (FreeGroup X)}

namespace PresentedGroup

/-- A presented group on finitely many generators is finitely generated. -/
instance instFG [Finite X] (R : Set (FreeGroup X)) : Group.FG (PresentedGroup R) := by
  change Group.FG (FreeGroup X ⧸ Subgroup.normalClosure R)
  infer_instance

end PresentedGroup

/- Definition 2-1-1: a presentation of `G` with defining generators `X` and defining relators `R`
is a chosen multiplicative equivalence from the canonical presented group `PresentedGroup R` to
`G`. The file uses the canonical type expression `PresentedGroup R ≃* G` directly rather than
introducing a duplicate alias. -/
#check (PresentedGroup R ≃* G)

namespace GroupPresentation

variable (P : PresentedGroup R ≃* G)

/-- The image in `G` of a defining generator under a chosen presentation. -/
abbrev generatorImage : X → G :=
  fun x ↦ P (PresentedGroup.of x)

private theorem generatorImage_comp_mk :
    P.toMonoidHom.comp (PresentedGroup.mk R) = FreeGroup.lift (generatorImage P) := by
  ext x
  simp [generatorImage, PresentedGroup.of]

-- Proof sketch: transport `PresentedGroup.closure_range_of R` across the presentation equivalence
-- `P`; the image of the canonical generator set is exactly `Set.range (generatorImage P)`, so its
-- subgroup closure is all of `G`.
/-- The images of the defining generators generate the whole group. -/
theorem closure_range_generatorImage_eq_top :
    Subgroup.closure (Set.range (generatorImage P)) = ⊤ := by
  have hmap :
      Subgroup.map P.toMonoidHom
          (Subgroup.closure (Set.range (PresentedGroup.of : X → PresentedGroup R))) =
        Subgroup.closure (Set.range (generatorImage P)) := by
    rw [MonoidHom.map_closure]
    change
      Subgroup.closure
          (P.toMonoidHom '' Set.range (PresentedGroup.of : X → PresentedGroup R)) =
      Subgroup.closure (Set.range (generatorImage P))
    congr 1
    ext g
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨PresentedGroup.of x, ⟨x, rfl⟩, rfl⟩
  calc
    Subgroup.closure (Set.range (generatorImage P)) =
        Subgroup.map P.toMonoidHom
          (Subgroup.closure (Set.range (PresentedGroup.of : X → PresentedGroup R))) := by
            exact hmap.symm
    _ = Subgroup.map P.toMonoidHom ⊤ := by
          rw [PresentedGroup.closure_range_of]
    _ = MonoidHom.range P.toMonoidHom := by
          rw [← MonoidHom.range_eq_map]
    _ = ⊤ := MonoidHom.range_eq_top.2 P.surjective

-- Proof sketch: in `PresentedGroup R`, every relator maps to `1` by
-- `PresentedGroup.one_of_mem`. Apply the presentation equivalence `P` to that equality and
-- identify the resulting evaluation map on `FreeGroup X` with `FreeGroup.lift (generatorImage P)`.
/-- Every defining relator evaluates to the identity in the presented group. -/
theorem relator_eq_one {r : FreeGroup X} (hr : r ∈ R) :
    FreeGroup.lift (generatorImage P) r = 1 := by
  have hmk : PresentedGroup.mk R r = 1 := PresentedGroup.one_of_mem hr
  rw [← generatorImage_comp_mk]
  change P (PresentedGroup.mk R r) = 1
  simpa using congrArg P hmk

-- Proof sketch: membership in `Subgroup.normalClosure R` is equivalent to triviality in
-- `PresentedGroup R` by `PresentedGroup.mk_eq_one_iff`. Apply `P` to that canonical equality and
-- rewrite the resulting map as `FreeGroup.lift (generatorImage P)`.
/-- Every consequence of the defining relators evaluates to the identity in the presented group. -/
theorem consequence_eq_one {w : FreeGroup X}
    (hw : w ∈ Subgroup.normalClosure R) :
    FreeGroup.lift (generatorImage P) w = 1 := by
  have hmk : PresentedGroup.mk R w = 1 := PresentedGroup.mk_eq_one_iff.mpr hw
  rw [← generatorImage_comp_mk]
  change P (PresentedGroup.mk R w) = 1
  simpa using congrArg P hmk

end GroupPresentation
