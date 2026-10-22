/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {F : Type u} [Group F] {X : Type v}

namespace FreeGroupBasis

/-- The set of basis indices moved by an automorphism. -/
def movedBasisSupport (basis : FreeGroupBasis X F) (α : MulAut F) : Set X :=
  {x | α (basis x) ≠ basis x}

private theorem finite_moved_one (basis : FreeGroupBasis X F) :
    (basis.movedBasisSupport (1 : MulAut F)).Finite := sorry

private theorem finite_moved_mul (basis : FreeGroupBasis X F) {α β : MulAut F}
    (hα : (basis.movedBasisSupport α).Finite)
    (hβ : (basis.movedBasisSupport β).Finite) :
    (basis.movedBasisSupport (α * β)).Finite := sorry

private theorem finite_moved_inv (basis : FreeGroupBasis X F) {α : MulAut F}
    (hα : (basis.movedBasisSupport α).Finite) :
    (basis.movedBasisSupport α⁻¹).Finite := sorry

/-- The automorphisms moving only finitely many elements of the chosen basis. -/
def finiteMovedSubgroup (basis : FreeGroupBasis X F) : Subgroup (MulAut F) where
  carrier := {α | (basis.movedBasisSupport α).Finite}
  one_mem' := finite_moved_one basis
  mul_mem' := fun hα hβ ↦ finite_moved_mul basis hα hβ
  inv_mem' := fun hα ↦ finite_moved_inv basis hα

@[simp] theorem mem_finiteMovedSubgroup (basis : FreeGroupBasis X F) (α : MulAut F) :
    α ∈ basis.finiteMovedSubgroup ↔ (basis.movedBasisSupport α).Finite :=
  Iff.rfl

end FreeGroupBasis

namespace FreeGroupBasis

/-- Proposition 1-4-2: the elementary Nielsen subgroup for `basis` is exactly the subgroup of
automorphisms moving only finitely many elements of that chosen basis. -/
-- Layer triage:
-- `bridge/view`: this proposition identifies the subgroup owner
-- `basis.elementaryNielsenAutomorphismSubgroup` from Proposition `1-4-1` with the basis-owned
-- finite-support subgroup `basis.finiteMovedSubgroup`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the canonical owner object for a chosen free basis of `F`.
-- 2. `MulAut F` is the canonical automorphism group of `F`.
-- 3. `basis.elementaryNielsenAutomorphismSubgroup` from Proposition `1-4-1` is the project owner
--    for the subgroup `Aut_f(F)` attached to `basis`.
-- 4. `Subgroup (MulAut F)` is the canonical owner level for a subgroup of automorphisms, so the
--    finite-moved condition should be packaged as `basis.finiteMovedSubgroup` rather than exposed
--    through a parallel predicate wrapper.
-- Primitive/derived split:
-- the primitive owner declarations are the moved-index set `basis.movedBasisSupport` and the two
-- subgroups `basis.elementaryNielsenAutomorphismSubgroup` and `basis.finiteMovedSubgroup`;
-- the finite-support membership test is derived canonically from
-- `FreeGroupBasis.mem_finiteMovedSubgroup`.

theorem elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup
    (basis : FreeGroupBasis X F) :
    basis.elementaryNielsenAutomorphismSubgroup = basis.finiteMovedSubgroup := sorry

/-- Membership in the elementary Nielsen subgroup is equivalent to moving only finitely many basis
elements. -/
theorem mem_elementaryNielsenAutomorphismSubgroup_iff
    (basis : FreeGroupBasis X F) (α : MulAut F) :
    α ∈ basis.elementaryNielsenAutomorphismSubgroup ↔ (basis.movedBasisSupport α).Finite := by
  rw [elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup,
    FreeGroupBasis.mem_finiteMovedSubgroup]

end FreeGroupBasis

end
