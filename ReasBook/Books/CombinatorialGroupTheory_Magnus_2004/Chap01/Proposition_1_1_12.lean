/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup

section

variable {G : Type u} [Group G]

/-- Proposition 1-1-12, owner form: the subset of `Subgroup.closure X` cut out by `X` is a free
basis exactly when the canonical homomorphism from the free group on `X` into `G` is injective. -/
-- Layer triage:
-- `source-facing`: the reduced-word criterion stated below.
-- `core/canonical`: the induced homomorphism `FreeGroup.lift ((↑) : X → G)` and the owner basis
-- object on its range.
-- `bridge/view`: `FreeGroup.closure_eq_range` identifies that range with `Subgroup.closure X`,
-- while the subtype `{x : Subgroup.closure X | (x : G) ∈ X}` records the original generating set
-- inside the closure.
--
-- Domain sampling:
-- 1. `FreeGroup.closure_eq_range` is the canonical owner identification of the subgroup generated
--    by a subset with the range of the induced free-group homomorphism.
-- 2. `MonoidHom.ofInjective` is the canonical owner equivalence from an injective homomorphism to
--    its range.
-- 3. `FreeGroupBasis.ofFreeGroup` is the owner basis of a free group.
-- 4. `FreeGroupBasis.isFreeGroupBasis_range` is the chapter bridge from an owner basis to the
--    subset-style basis predicate.
--
-- Primitive vs. derived:
-- the primitive source data are only the subset `X` and the induced homomorphism
-- `FreeGroup.lift ((↑) : X → G)`. The basis on `Subgroup.closure X` and the reduced-word
-- criterion are derived API.
theorem closure_preimage_isFreeGroupBasis_iff_injective_lift
    (X : Set G) :
    IsFreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} ↔
      Function.Injective (FreeGroup.lift (Subtype.val : X → G)) := by
  let φ : FreeGroup X →* G := FreeGroup.lift (Subtype.val : X → G)
  have hφ_range : φ.range = Subgroup.closure X := by
    simpa [φ] using (FreeGroup.closure_eq_range X).symm
  constructor
  · intro hBasis
    let basis :
        FreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} (Subgroup.closure X) :=
      FreeGroupBasis.ofUniqueLift {x : Subgroup.closure X | (x : G) ∈ X} Subtype.val hBasis
    let e : {x : Subgroup.closure X | (x : G) ∈ X} ≃ X :=
      { toFun := fun x ↦ ⟨x.1.1, x.2⟩
        invFun := fun x ↦ ⟨⟨x.1, Subgroup.subset_closure x.2⟩, x.2⟩
        left_inv := fun x ↦ by
          cases x
          rfl
        right_inv := fun x ↦ rfl }
    let ψ : Subgroup.closure X →* FreeGroup X :=
      basis.lift (FreeGroup.of ∘ e)
    have hcomp :
        ψ.comp (φ.codRestrict (Subgroup.closure X) fun x ↦ hφ_range ▸ ⟨x, rfl⟩) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      have hψ :=
        congr_fun (basis.lift.symm_apply_apply (FreeGroup.of ∘ e))
          ⟨⟨x.1, Subgroup.subset_closure x.property⟩, x.property⟩
      simpa [ψ, e]
    intro x y hxy
    have hxy' :
        φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x =
          φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y :=
      Subtype.ext hxy
    have hx :
        ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x) = x := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : FreeGroup X →* FreeGroup X ↦ f x) hcomp
    have hy :
        ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y) = y := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : FreeGroup X →* FreeGroup X ↦ f y) hcomp
    calc
      x = ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x) := hx.symm
      _ = ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y) := by
        simpa using congrArg ψ hxy'
      _ = y := hy
  · intro hφ
    let basis : FreeGroupBasis X (Subgroup.closure X) :=
      (FreeGroupBasis.ofFreeGroup X).map
        ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφ_range))
    have hrange :
        Set.range basis = {x : Subgroup.closure X | (x : G) ∈ X} := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp [basis, MonoidHom.ofInjective_apply]
      · intro hy
        refine ⟨⟨y.1, hy⟩, ?_⟩
        ext
        simp [basis, MonoidHom.ofInjective_apply]
    rw [← hrange]
    exact (FreeGroupBasis.isFreeGroupBasis_range basis : IsFreeGroupBasis (Set.range basis))

/-- Proposition 1-1-12: A subset `X` is a basis for the subgroup it generates if and only if every
nonempty reduced word in `X^{±1}` has nontrivial product.

In this reduced-word bridge formulation, the textbook disjointness hypothesis `X ∩ X⁻¹ = ∅` is
redundant: it is already forced by the nontrivial-product condition. -/
-- Proof sketch: combine the owner criterion
-- `closure_preimage_isFreeGroupBasis_iff_injective_lift` with the free-group normal form theorem.
-- Injectivity rules out a nonempty reduced word evaluating to `1`, and conversely any kernel
-- element has a canonical reduced representative given by `toWord`.
theorem closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word
    (X : Set G) :
    IsFreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} ↔
      ∀ w : List (X × Bool), w ≠ [] →
        IsReduced w →
        lift Subtype.val (mk w) ≠ 1 := by
  classical
  rw [closure_preimage_isFreeGroupBasis_iff_injective_lift]
  constructor
  · intro hφ w hw hred htriv
    have hmk : (mk w : FreeGroup X) = 1 := hφ (by simpa using htriv)
    have hword : (mk w : FreeGroup X).toWord = [] := by
      simp [hmk]
    exact hw <| by simpa [toWord_mk, hred.reduce_eq] using hword
  · intro hφ x y hxy
    by_cases hword : (x * y⁻¹).toWord = []
    · exact (mul_inv_eq_one.mp <| (toWord_eq_nil_iff.mp hword))
    · have htriv : lift Subtype.val (x * y⁻¹) = 1 := by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, hxy, mul_inv_cancel]
      have :=
        hφ (x * y⁻¹).toWord hword isReduced_toWord
          (by simpa [mk_toWord] using htriv)
      exact False.elim this

end
