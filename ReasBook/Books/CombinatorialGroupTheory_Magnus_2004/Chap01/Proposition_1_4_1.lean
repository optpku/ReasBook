/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {F : Type u} [Group F] {X : Type v}

namespace FreeGroupBasis

/-- The `(T1)` inversion automorphism relative to `basis`. -/
private def invertElementaryNielsenEndomorphism
    (basis : FreeGroupBasis X F) (x : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then (basis x)⁻¹ else basis z

@[simp] private theorem invertElementaryNielsenEndomorphism_apply_self
    (basis : FreeGroupBasis X F) (x : X) :
    invertElementaryNielsenEndomorphism basis x (basis x) = (basis x)⁻¹ := by
  letI : DecidableEq X := Classical.decEq X
  simp [invertElementaryNielsenEndomorphism]

@[simp] private theorem invertElementaryNielsenEndomorphism_apply_of_ne
    (basis : FreeGroupBasis X F) {x z : X} (hz : z ≠ x) :
    invertElementaryNielsenEndomorphism basis x (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [invertElementaryNielsenEndomorphism, hz]

/-- The `(T1)` inversion automorphism relative to `basis`. -/
def elementaryNielsenInversion
    (basis : FreeGroupBasis X F) (x : X) : MulAut F :=
  MonoidHom.toMulEquiv
    (invertElementaryNielsenEndomorphism basis x)
    (invertElementaryNielsenEndomorphism basis x)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [MonoidHom.comp_apply, hz])
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [MonoidHom.comp_apply, hz])

/-- The inversion automorphism sends the chosen basis element `basis x` to its inverse. -/
@[simp] theorem elementaryNielsenInversion_apply_self
    (basis : FreeGroupBasis X F) (x : X) :
    elementaryNielsenInversion basis x (basis x) = (basis x)⁻¹ := by
  simp [elementaryNielsenInversion]

/-- The inversion automorphism fixes every basis element other than `basis x`. -/
@[simp] theorem elementaryNielsenInversion_apply_of_ne
    (basis : FreeGroupBasis X F) {x z : X} (hz : z ≠ x) :
    elementaryNielsenInversion basis x (basis z) = basis z := by
  simp [elementaryNielsenInversion, hz]

/-- The `(T2)` transvection endomorphism relative to `basis`. -/
private def multiplyElementaryNielsenEndomorphism
    (basis : FreeGroupBasis X F) (x y : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then basis x * basis y else basis z

/-- The inverse endomorphism for the `(T2)` transvection relative to `basis`. -/
private def multiplyElementaryNielsenEndomorphismInv
    (basis : FreeGroupBasis X F) (x y : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then basis x * (basis y)⁻¹ else basis z

@[simp] private theorem multiplyElementaryNielsenEndomorphism_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) :
    multiplyElementaryNielsenEndomorphism basis x y (basis x) = basis x * basis y := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphism]

@[simp] private theorem multiplyElementaryNielsenEndomorphism_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) {z : X} (hz : z ≠ x) :
    multiplyElementaryNielsenEndomorphism basis x y (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphism, hz]

@[simp] private theorem multiplyElementaryNielsenEndomorphismInv_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) :
    multiplyElementaryNielsenEndomorphismInv basis x y (basis x) =
      basis x * (basis y)⁻¹ := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphismInv]

@[simp] private theorem multiplyElementaryNielsenEndomorphismInv_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) {z : X} (hz : z ≠ x) :
    multiplyElementaryNielsenEndomorphismInv basis x y (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphismInv, hz]

/-- The `(T2)` transvection automorphism relative to `basis`. -/
def elementaryNielsenTransvection
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) : MulAut F :=
  MonoidHom.toMulEquiv
    (multiplyElementaryNielsenEndomorphism basis x y)
    (multiplyElementaryNielsenEndomorphismInv basis x y)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst z
        rw [MonoidHom.comp_apply, multiplyElementaryNielsenEndomorphism_apply_fst, map_mul,
          multiplyElementaryNielsenEndomorphismInv_apply_fst,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hxy.symm]
        simp
      · rw [MonoidHom.comp_apply,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hz,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hz]
        simp)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst z
        rw [MonoidHom.comp_apply, multiplyElementaryNielsenEndomorphismInv_apply_fst, map_mul,
          map_inv, multiplyElementaryNielsenEndomorphism_apply_fst,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hxy.symm]
        simp
      · rw [MonoidHom.comp_apply,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hz,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hz]
        simp)

/-- The transvection sends the moved basis element to its product with the companion basis
element. -/
@[simp] theorem elementaryNielsenTransvection_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    elementaryNielsenTransvection basis x y hxy (basis x) = basis x * basis y := by
  simp [elementaryNielsenTransvection]

/-- The transvection fixes every basis element other than the moved one. -/
@[simp] theorem elementaryNielsenTransvection_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) {z : X} (hz : z ≠ x) :
    elementaryNielsenTransvection basis x y hxy (basis z) = basis z := by
  simp [elementaryNielsenTransvection, hz]

/-- The inverse transvection sends the moved basis element to its product with the inverse of the
companion basis element. -/
@[simp] theorem elementaryNielsenTransvection_inv_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    (elementaryNielsenTransvection basis x y hxy)⁻¹ (basis x) =
      basis x * (basis y)⁻¹ := by
  simp [elementaryNielsenTransvection]

/-- The inverse transvection fixes every basis element other than the moved one. -/
@[simp] theorem elementaryNielsenTransvection_inv_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) {z : X} (hz : z ≠ x) :
    (elementaryNielsenTransvection basis x y hxy)⁻¹ (basis z) = basis z := by
  simp [elementaryNielsenTransvection, hz]

/-- The subgroup `Aut_f(F)` generated by the elementary Nielsen automorphisms relative to the
chosen basis `basis`. -/
def elementaryNielsenAutomorphismSubgroup (basis : FreeGroupBasis X F) : Subgroup (MulAut F) :=
  Subgroup.closure
    (Set.range (basis.elementaryNielsenInversion) ∪
      Set.range fun xy : {p : X × X // p.1 ≠ p.2} ↦
        basis.elementaryNielsenTransvection xy.1.1 xy.1.2 xy.2)

/-- Each inversion generator belongs to the elementary Nielsen automorphism subgroup. -/
theorem elementaryNielsenInversion_mem_subgroup
    (basis : FreeGroupBasis X F) (x : X) :
    basis.elementaryNielsenInversion x ∈ basis.elementaryNielsenAutomorphismSubgroup := by
  exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

/-- Each transvection generator belongs to the elementary Nielsen automorphism subgroup. -/
theorem elementaryNielsenTransvection_mem_subgroup
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    basis.elementaryNielsenTransvection x y hxy ∈ basis.elementaryNielsenAutomorphismSubgroup := by
  exact Subgroup.subset_closure (Or.inr ⟨⟨(x, y), hxy⟩, rfl⟩)

/-- Proposition 1-4-1: the subgroup generated by the elementary Nielsen automorphisms is dense in
`Aut(F)` for the pointwise topology on finite families, meaning that every automorphism can be
matched on any prescribed finite family of elements. -/
-- Layer triage:
-- `source-facing`: a free group `F` with basis `basis : FreeGroupBasis X F`, a finite family
-- `u : ι → F` indexed by an arbitrary finite type, and an automorphism `α : MulAut F`.
-- `core/canonical`: the automorphism group `MulAut F` together with the canonical basis owner
-- abstraction `FreeGroupBasis X F`, with generated subgroup owner `Subgroup.closure` and the
-- canonical finite-family interface `ι → F` under `[Finite ι]`.
-- `bridge/view`: the internal generator set is the concrete `(T1)` inversion and `(T2)`
-- transvection automorphism families relative to `basis`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the canonical owner
--    abstraction for a chosen free basis of `F`.
-- 2. `MulAut F` in `Mathlib/Algebra/Group/End` is the canonical automorphism group of `F`.
-- 3. `FreeGroupBasis.lift` provides the canonical basis-determined endomorphisms used to realize
--    the regular Nielsen generators as actual automorphisms.
-- 4. `FreeGroupBasis.ext_hom` shows that endomorphisms of a free group are determined by their
--    values on a basis, matching the source proof strategy and the inverse checks above.
-- Primitive/derived split:
-- the public owner object is only `basis.elementaryNielsenAutomorphismSubgroup`;
-- the finite family itself is primitive source data and should therefore stay at the canonical
-- owner level `ι → F` for arbitrary `[Fintype ι]`; the private generator families above are
-- implementation-level bridge data for the subgroup owner.
-- Proof sketch: reduce to the finite subfamily of basis elements needed to write the given finite
-- family `u`, apply Nielsen reduction to the corresponding finite tuple of basis images under
-- `α⁻¹`, and read the resulting regular Nielsen transformation as an element of the subgroup
-- generated by the elementary Nielsen automorphisms. The source calculation then shows that this
-- element agrees with `α` on the prescribed family.
theorem exists_elementaryNielsenAutomorphism_eq_on_finite_family
    (basis : FreeGroupBasis X F) {ι : Type*} [Finite ι] (u : ι → F) (α : MulAut F) :
    ∃ β ∈ basis.elementaryNielsenAutomorphismSubgroup, ∀ i, β (u i) = α (u i) := sorry

/-- If the chosen free basis is finite, then the subgroup generated by the elementary Nielsen
automorphisms is the whole automorphism group. -/
-- Proof sketch: apply the density theorem to the finite family consisting of all basis elements.
-- An automorphism of `F` is determined by its values on `basis`, so agreement on that finite
-- family forces equality. Hence every automorphism belongs to the generated subgroup.
theorem elementaryNielsenAutomorphismSubgroup_eq_top_of_finite
    (basis : FreeGroupBasis X F) [Finite X] :
    basis.elementaryNielsenAutomorphismSubgroup = ⊤ := sorry

end FreeGroupBasis

end
