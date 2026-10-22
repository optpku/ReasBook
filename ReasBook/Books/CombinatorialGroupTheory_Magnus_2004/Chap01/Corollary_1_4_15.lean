/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open LinearMap

section

variable {F : Type u} [Group F]
variable {n : ℕ}

-- Layer triage for Corollary 1-4-15:
-- `source-facing`: a basis `basis : FreeGroupBasis (Fin n) F` and a finite subgroup
-- `G ≤ MulAut F`.
-- `core/canonical`: the restricted homomorphism `basis.toGL.restrict G` and mathlib's owner
-- equivalence `MonoidHom.ofInjective` from an injective homomorphism to its range.
-- `bridge/view`: `FreeGroupBasis.toGL` from Corollary `1-4-16`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.toGL` is the chapter owner map from `MulAut F` to `GL (Fin n) ℤ`.
-- 2. `Subgroup.orderOf_coe` is the canonical comparison between element orders in a subgroup and
--    in the ambient group.
-- 3. `MonoidHom.ofInjective` is the owner equivalence from a group to the range of an injective
--    homomorphism, with owner companion lemma `MonoidHom.ofInjective_apply`.
--
-- Primitive vs. derived:
-- the primitive source data are the chosen basis and the finite subgroup `G`; injectivity of the
-- restricted representation is the substantive theorem, while the isomorphism onto the image is
-- derived canonically from `MonoidHom.ofInjective`.

/-- The restriction of the canonical abelianization representation of `Aut(F)` to a finite
subgroup is injective. -/
-- Proof sketch: if `φ : G` maps to the identity matrix, then its underlying automorphism of `F`
-- acts trivially on the abelianization. Because `G` is finite, `φ` has finite order, so the
-- kernel-torsion theorem from Corollary `1-4-16` forces `φ = 1`.
theorem toGL_restrict_injective_of_finite_subgroup
    (basis : FreeGroupBasis (Fin n) F) (G : Subgroup (MulAut F)) [Finite G] :
    Function.Injective (basis.toGL.restrict G) := by
  intro φ ψ hφψ
  let δ : G := φ * ψ⁻¹
  have hδ_toGL : basis.toGL (δ : MulAut F) = 1 := by
    simpa [δ, MonoidHom.map_mul] using
      congrArg (fun g : GL (Fin n) ℤ ↦ g * (basis.toGL ψ)⁻¹) hφψ
  have hδ_fin : IsOfFinOrder δ := isTorsion_of_finite δ
  have hδ_fin' : IsOfFinOrder (δ : MulAut F) := by
    rw [← orderOf_pos_iff, Subgroup.orderOf_coe, orderOf_pos_iff]
    exact hδ_fin
  have hδ_order :
      orderOf (basis.toGL (δ : MulAut F)) = orderOf (δ : MulAut F) :=
    basis.orderOf_toGL_eq (δ : MulAut F) hδ_fin'
  have hδ_eq_one : (δ : MulAut F) = 1 := by
    rw [← orderOf_eq_one_iff, ← hδ_order]
    simp [hδ_toGL]
  exact Subtype.ext <| eq_of_mul_inv_eq_one <| by simpa [δ] using hδ_eq_one

/- Corollary 1-4-15: after choosing a rank-`n` basis of the free group `F`, the natural map from
`Aut(F)` to `GL (Fin n) ℤ` carries each finite subgroup of `Aut(F)` isomorphically onto its image
subgroup of `GL (Fin n) ℤ`, via the canonical owner equivalence
`MonoidHom.ofInjective (toGL_restrict_injective_of_finite_subgroup basis G)`. -/
#check
  (fun (basis : FreeGroupBasis (Fin n) F) (G : Subgroup (MulAut F)) [Finite G] ↦
    (MonoidHom.ofInjective (toGL_restrict_injective_of_finite_subgroup basis G) :
      G ≃* (basis.toGL.restrict G).range))

end
