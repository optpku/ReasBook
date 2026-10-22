/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_8

universe u

open QuotientGroup

-- Declarations for this item will be appended below by the statement pipeline.

-- Layer triage:
-- `source-facing`: an actual `2`-complex `C`, a base vertex `v : C.skeleton`, and a
-- presentation map `φ : FreeGroup X →* π(C, v)` whose kernel is exactly the normal closure of the
-- relators `R`; the proposition states that the based fundamental group of this presentation
-- complex is the presented group on `(X; R)`.
-- `core/canonical`: `TwoComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for
-- the based fundamental group, `PresentedGroup R` is mathlib's owner for the group presented by
-- relators `R`, and `Subgroup.normalClosure R` is the canonical relator subgroup.
-- `bridge/view`: `quotientKerEquivOfSurjective` and `quotientMulEquivOfEq` provide the quotient
-- comparison proving the source-facing identification.
-- Primitive vs. derived:
-- primitive data: the actual `TwoComplex`, the base vertex, the surjective map
-- `φ : FreeGroup X →* π(C, v)`, and the kernel description `φ.ker = Subgroup.normalClosure R`;
-- derived API: the canonical presentation equivalence `PresentedGroup R ≃* π(C, v)` and its
-- generator-image companion theorem.
-- Domain sampling:
-- 1. `TwoComplex.fundamentalGroup`, written `π(C, v)`, from Definition `3-2-8` is the chapter
--    owner for the based fundamental group.
-- 2. `PresentedGroup R`, together with `PresentedGroup.mk` and `PresentedGroup.of`, is the
--    canonical quotient owner for generators-and-relations groups.
-- 3. `Subgroup.normalClosure R` is the canonical owner for the relator subgroup of `FreeGroup X`.
-- 4. `quotientKerEquivOfSurjective` and `quotientMulEquivOfEq` are the canonical quotient
--    equivalences turning the kernel calculation into an actual multiplicative equivalence.

namespace TwoComplex

/-- Proposition 3-2-11: if the based fundamental group of a presentation complex `K(X; R)` is the
quotient of `FreeGroup X` by the normal closure of the relators `R`, then that fundamental group
is canonically isomorphic to the presented group `PresentedGroup R`. -/
noncomputable def fundamentalGroupMulEquivPresentedGroup
    {X : Type u} {R : Set (FreeGroup X)} (C : TwoComplex) (v : C.skeleton)
    (φ : FreeGroup X →* π(C, v))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.normalClosure R) :
    PresentedGroup R ≃* π(C, v) :=
  (quotientMulEquivOfEq hker.symm).trans (quotientKerEquivOfSurjective φ hφ)

/-- The canonical presentation equivalence sends each presented generator to the corresponding loop
generator in `π(C, v)`. -/
-- Proof sketch: unfold `fundamentalGroupMulEquivPresentedGroup`; it is the quotient
-- identification followed by the first-isomorphism-theorem map, so `PresentedGroup.of x` is sent
-- to `φ (FreeGroup.of x)`.
theorem fundamentalGroupMulEquivPresentedGroup_apply_of
    {X : Type u} {R : Set (FreeGroup X)} (C : TwoComplex) (v : C.skeleton)
    (φ : FreeGroup X →* π(C, v))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.normalClosure R)
    (x : X) :
    fundamentalGroupMulEquivPresentedGroup C v φ hφ hker (PresentedGroup.of x) =
      φ (FreeGroup.of x) := by
  rw [fundamentalGroupMulEquivPresentedGroup, PresentedGroup.of]
  change
    quotientKerEquivOfSurjective φ hφ
        ((quotientMulEquivOfEq hker.symm) ((PresentedGroup.mk R) (FreeGroup.of x))) =
      φ (FreeGroup.of x)
  have hmk :
      (quotientMulEquivOfEq hker.symm) ((PresentedGroup.mk R) (FreeGroup.of x)) =
        QuotientGroup.mk (FreeGroup.of x) := by
    change
      (quotientMulEquivOfEq hker.symm) (QuotientGroup.mk (FreeGroup.of x)) =
        QuotientGroup.mk (FreeGroup.of x)
    exact quotientMulEquivOfEq_mk hker.symm (FreeGroup.of x)
  rw [hmk]
  rfl

end TwoComplex
