/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_12
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_11_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open scoped Pointwise

-- Layer triage:
-- `source-facing`: the ambient group `F`, the subset `S`, the generation hypothesis
-- `Subgroup.closure S = ⊤`, the inverse-disjointness hypothesis `Disjoint S S⁻¹`, and the
-- Section `11` owner property on `S ∪ S⁻¹`.
-- `core/canonical`: `IsFreeGroupBasis S` from Definition `1-1-1`,
-- `closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word` from Proposition `1-1-12`,
-- `Set.HasNontrivialNoncancellingProducts (S ∪ S⁻¹)` from Proposition `1-11-20`, and
-- `Subgroup.closure`.
-- `bridge/view`: none. The long quantified word hypothesis is already owned by the Section `11`
-- subset property, and the inverse-disjointness hypothesis is the source-facing bridge from
-- Section `11` noncancelling words to the Chapter `1-1` reduced-word owner criterion.
--
-- Domain sampling:
-- 1. `IsFreeGroupBasis` is the chapter owner abstraction for the textbook claim that `S` is a
--    basis of the ambient free group.
-- 2. `Subgroup.closure S = ⊤` is the canonical way to state that `S` generates `F`.
-- 3. `closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word` is the chapter owner bridge
--    from reduced words in the letters of `S` to the basis conclusion.
-- 4. `Set.HasNontrivialNoncancellingProducts` from Proposition `1-11-20` is the owner
--    abstraction for the Section `11` nontrivial-word hypothesis.

section

variable {F : Type u} [Group F]

/-- Corollary 1-11-21: if `S` generates `F`, is disjoint from its inverse set, and every nonempty
noncancelling word in letters from `S ∪ S⁻¹` has nontrivial product, then `S` is a basis for the
free group `F`. -/
-- Proof sketch: use Proposition `1-1-12` to reduce the basis claim on the generated subgroup to
-- nontriviality of reduced words in the letters of `S`. The inverse-disjointness hypothesis turns
-- reduced signed words on `S` into Section `11` noncancelling products in `S ∪ S⁻¹`, so the owner
-- hypothesis `hprod` supplies the required nontriviality. Finally `hgen` identifies the generated
-- subgroup with the whole ambient group `F`.
theorem isFreeGroupBasis_of_closure_eq_top_of_nontrivial_noncancelling_products
    (S : Set F) (hgen : Subgroup.closure S = ⊤)
    (hdisj : Disjoint S S⁻¹)
    (hprod : Set.HasNontrivialNoncancellingProducts (S ∪ S⁻¹)) :
    IsFreeGroupBasis S := by
  let T : Set (Subgroup.closure S) := {x | (x : F) ∈ S}
  have hT : IsFreeGroupBasis T := by
    rw [closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word]
    intro w hw hred
    let eval : S × Bool → F := fun x ↦ cond x.2 x.1.1 x.1.1⁻¹
    have hmem : ∀ u ∈ w.map eval, u ∈ S ∪ S⁻¹ := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨x, hx, rfl⟩
      dsimp [eval]
      by_cases hx2 : x.2
      · left
        show (bif x.2 then (x.1 : F) else (x.1 : F)⁻¹) ∈ S
        have hxmem : (x.1 : F) ∈ S := x.1.2
        simpa [hx2] using hxmem
      · right
        rw [Set.mem_inv]
        show (bif x.2 then (x.1 : F) else (x.1 : F)⁻¹)⁻¹ ∈ S
        have hxmem : (x.1 : F) ∈ S := x.1.2
        simpa [hx2] using hxmem
    have hchain : (w.map eval).IsChain (fun u v ↦ u * v ≠ 1) := by
      rw [FreeGroup.IsReduced] at hred
      exact List.isChain_map_of_isChain eval (fun a b hab hmul ↦ by
        rw [Set.disjoint_left] at hdisj
        cases ha : a.2 <;> cases hb : b.2
        · have hEq : (a.1 : F) = (b.1 : F)⁻¹ := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact inv_mul_eq_one.mp hmul
          exact hdisj b.1.2 <| by
            rw [Set.mem_inv]
            simpa [hEq] using a.1.2
        · have hEq : (a.1 : F) = b.1 := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact inv_mul_eq_one.mp hmul
          have hbool : false = true := by
            simpa [ha, hb] using hab (Subtype.ext hEq)
          cases hbool
        · have hEq : (a.1 : F) = b.1 := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact mul_inv_eq_one.mp hmul
          have hbool : true = false := by
            simpa [ha, hb] using hab (Subtype.ext hEq)
          cases hbool
        · have hEq : (b.1 : F) = (a.1 : F)⁻¹ := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact (mul_eq_one_iff_eq_inv').mp hmul
          exact hdisj a.1.2 <| by
            rw [Set.mem_inv]
            simpa [hEq] using b.1.2) hred
    have hne : (w.map eval).prod ≠ (1 : F) :=
      hprod.prod_ne_one (by simpa [eval] using hw) hmem hchain
    simpa [eval, lift_mk] using hne
  intro H _ φ
  let eS : T ≃ S :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, Subgroup.subset_closure x.2⟩, x.2⟩
      left_inv := fun x ↦ by
        cases x
        rfl
      right_inv := fun x ↦ rfl }
  let eF : Subgroup.closure S ≃* F := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  let ψ : T → H := fun x ↦ φ (eS x)
  rcases hT ψ with ⟨ψStar, hψStar, hψUnique⟩
  refine ⟨ψStar.comp eF.symm.toMonoidHom, ?_, ?_⟩
  · intro s
    have hs : (eF.symm s.1 : Subgroup.closure S) = ⟨s.1, Subgroup.subset_closure s.2⟩ := by
      ext
      simp [eF]
    simpa [ψ, eS, hs] using hψStar (eS.symm s)
  · intro γ hγ
    have hcomp : γ.comp eF.toMonoidHom = ψStar := by
      apply hψUnique
      intro x
      simpa [ψ, eS, eF] using hγ (eS x)
    ext g
    have := congrArg (fun f : Subgroup.closure S →* H ↦ f (eF.symm g)) hcomp
    simpa [eF] using this

end
