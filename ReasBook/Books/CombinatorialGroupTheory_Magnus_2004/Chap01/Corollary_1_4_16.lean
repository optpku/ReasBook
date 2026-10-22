/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_4_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open LinearMap.GeneralLinearGroup Matrix.GeneralLinearGroup MulEquiv

variable {F : Type u} [Group F]
variable {n N : ℕ}

namespace FreeGroupBasis

/-- The canonical equivalence from automorphisms of `Abelianization F` to `GL (Fin n) ℤ`,
obtained by passing through additive automorphisms and then expressing the induced `ℤ`-linear
automorphism in the standard basis of the free abelian group of rank `n`. -/
private noncomputable def abelianizationToGL (basis : FreeGroupBasis (Fin n) F) :
    MulAut (Abelianization F) ≃* GL (Fin n) ℤ :=
  let addAutToGL :
      AddAut (Additive (Abelianization F)) ≃*
        LinearMap.GeneralLinearGroup ℤ (Additive (Abelianization F)) :=
    ({ toFun := fun φ ↦ φ.toIntLinearEquiv
       invFun := fun ψ ↦ ψ.toAddEquiv
       left_inv := by
         intro φ
         ext a
         rfl
       right_inv := by
         intro ψ
         ext a
         rfl
       map_mul' := by
         intro φ ψ
         ext a
         rfl } : AddAut (Additive (Abelianization F)) ≃*
         (Additive (Abelianization F) ≃ₗ[ℤ] Additive (Abelianization F))).trans
      (generalLinearEquiv ℤ (Additive (Abelianization F))).symm
  let reprAbAdd : Additive (Abelianization F) ≃+ FreeAbelianGroup (Fin n) :=
    toAdditive <| basis.repr.abelianizationCongr
  let reprAb : Additive (Abelianization F) ≃ₗ[ℤ] FreeAbelianGroup (Fin n) :=
    reprAbAdd.toIntLinearEquiv
  (AddAutAdditive (Abelianization F)).symm.trans
    (addAutToGL.trans <| (congrLinearEquiv reprAb).trans <|
      (toLin' (FreeAbelianGroup.basis (Fin n))).symm)

/-- The source-facing bridge from automorphisms of a free group of rank `n` to `GL (Fin n) ℤ`,
factored through the canonical owner map on abelianizations. -/
noncomputable def toGL (basis : FreeGroupBasis (Fin n) F) : MulAut F →* GL (Fin n) ℤ :=
  let abelianizationToGL := basis.abelianizationToGL
  abelianizationToGL.toMonoidHom.comp (MulAut.abelianization F)

/-- The canonical matrix attached to a finite-order automorphism of a rank-`n` free group has the
same order as the automorphism itself. -/
theorem orderOf_toGL_eq
    (basis : FreeGroupBasis (Fin n) F) (φ : MulAut F) (hφ : IsOfFinOrder φ) :
    orderOf (basis.toGL φ) = orderOf φ := by
  letI : IsFreeGroup F := basis.isFreeGroup
  let abelianizationToGL := basis.abelianizationToGL
  rw [orderOf_eq_orderOf_iff]
  intro k
  constructor
  · intro hk
    have hgl : basis.toGL (φ ^ k) = 1 := by
      simpa [MonoidHom.map_pow] using hk
    have hab : MulAut.abelianization F (φ ^ k) = 1 := by
      apply abelianizationToGL.injective
      simpa [toGL] using hgl
    have hIA : φ ^ k ∈ MulAut.IA F := hab
    let ψ : MulAut.IA F := ⟨φ ^ k, hIA⟩
    have hψfin : IsOfFinOrder ψ := by
      rw [isOfFinOrder_iff_pow_eq_one]
      obtain ⟨m, hm, hpow⟩ := (hφ.pow (n := k)).exists_pow_eq_one
      refine ⟨m, hm, ?_⟩
      apply Subtype.ext
      simpa [ψ] using hpow
    letI : IsMulTorsionFree (MulAut.IA F) := ia_isMulTorsionFree
    exact congrArg Subtype.val <| IsOfFinOrder.eq_one' hψfin
  · intro hk
    simpa [MonoidHom.map_pow] using congrArg basis.toGL hk

end FreeGroupBasis

/-- Corollary 1-4-16: if a free group of rank `n` has an automorphism of positive finite order
`N`, then `GL (Fin n) ℤ` has an element of order `N`. -/
-- Layer triage:
-- `source-facing`: a free group `F` equipped with `basis : FreeGroupBasis (Fin n) F`, an
-- automorphism of `F` of exact order `N`, and the resulting existence of an element of
-- `GL (Fin n) ℤ` of exact order `N`.
-- `core/canonical`: `MulAut F`, `MulAut.abelianization F`, the basis-induced linear equivalence
-- from `Additive (Abelianization F)` to `FreeAbelianGroup (Fin n)`, and the matrix owner group
-- `GL (Fin n) ℤ`.
-- `bridge/view`: `FreeGroupBasis.toGL` is the canonical passage from a rank-`n` free-group
-- automorphism to the corresponding integral matrix.
-- Domain sampling:
-- 1. `FreeGroupBasis (Fin n) F` is the chapter owner abstraction for “a free group of rank `n`”.
-- 2. `MulAut.abelianization F` is the owner map from automorphisms of `F` to automorphisms of its
--    abelianization.
-- 3. `FreeAbelianGroup.basis (Fin n)` is the canonical basis on the free abelian group of rank
--    `n`.
-- 4. `Matrix.GeneralLinearGroup.toLin'` is the owner equivalence between `GL (Fin n) ℤ` and the
--    `ℤ`-linear general linear group of a module with basis `Fin n`.
-- Primitive vs. derived:
-- the primitive source data is the basis `basis : FreeGroupBasis (Fin n) F` and the explicit
-- automorphism `φ : MulAut F`; the free-group structure is canonically derived from
-- `basis.isFreeGroup`; the matrix in `GL (Fin n) ℤ` is derived canonically via `basis.toGL`.
theorem exists_gl_element_of_order_of_free_group_automorphism
    (basis : FreeGroupBasis (Fin n) F)
    (hN : 0 < N)
    (hF : ∃ φ : MulAut F, orderOf φ = N) :
    ∃ g : GL (Fin n) ℤ, orderOf g = N := by
  obtain ⟨φ, hφ⟩ := hF
  have hφ_fin : IsOfFinOrder φ := orderOf_pos_iff.mp <| hφ ▸ hN
  exact ⟨basis.toGL φ, hφ ▸ basis.orderOf_toGL_eq φ hφ_fin⟩

end
