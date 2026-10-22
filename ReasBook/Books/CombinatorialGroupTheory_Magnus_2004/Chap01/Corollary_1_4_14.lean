/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_4_13
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_18
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/- Corollary 1-4-14: if `F` is a free group, then the IA-subgroup `IA(F)` of `Aut(F)` is torsion
free. -/
-- Layer triage:
-- `source-facing`: the textbook subgroup `IA(F)` of automorphisms acting trivially on the
-- abelianization, together with the assertion that this group has no nontrivial finite-order
-- elements.
-- `core/canonical`: the subgroup `MulAut.IA F` and the finite-order predicate `IsOfFinOrder`.
-- `bridge/view`: Corollary `1-4-13` supplies the canonical quotient-owner statement that
-- `IA(F) / JA(F)` is torsion free, while the inner automorphism subgroup is the owner declaration
-- `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` from Proposition `1-4-5` is the owner object for the subgroup `IA(F)`.
-- 2. `MulAut.innerAutomorphismSubgroup F` is the canonical subgroup of inner automorphisms used
--    in Corollary `1-4-13`.
-- 3. `IsOfFinOrder` is mathlib's canonical predicate for finite-order elements.
-- 4. `normalizer_zpowers_isCyclic` is the chapter owner theorem detecting when a nontrivial
--    central element would force the ambient free group to be cyclic.
-- Primitive vs. derived:
-- the only primitive datum is the free group `F`; the subgroup `MulAut.IA F` is the canonical
-- derived object attached to the abelianization action, and no basis or rank choice belongs in
-- the public header.
-- Proof sketch: first show privately that the inner automorphism subgroup is torsion free. If `F`
-- were cyclic, that subgroup would be trivial; otherwise any element in the kernel of
-- `MulAut.conj` would be a nontrivial central element, and Proposition `1-2-21` would force `F`
-- to be cyclic, a contradiction. Hence `MulAut.conj` is injective and its range inherits
-- torsion-freeness from `F`. For a finite-order element of `IA(F)`, Corollary `1-4-13` makes its
-- image in `IA(F) / JA(F)` trivial, so the element lies in the inner automorphism subgroup; the
-- private torsion-freeness result then forces the element itself to be trivial.
private theorem conj_eq_one_implies_eq_one_of_not_isCyclic
    (hnotcyc : ¬ IsCyclic F) {x : F} (hconj : MulAut.conj x = 1) : x = 1 := by
  by_contra hx
  have hx_center : x ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : x * y * x⁻¹ = y := by
      simpa [MulAut.conj_apply] using congrArg (fun σ : MulAut F ↦ σ y) hconj
    have hxy : x * y = y * x := by
      calc
        x * y = (x * y * x⁻¹) * x := by simp [mul_assoc]
        _ = y * x := by rw [hy]
    exact hxy.symm
  have hnormal : (Subgroup.zpowers x : Subgroup F).Normal := by
    refine ⟨?_⟩
    intro a ha b
    rcases Subgroup.mem_zpowers_iff.mp ha with ⟨n, rfl⟩
    have hbx : Commute b x := by
      exact (commute_iff_eq b x).2 (Subgroup.mem_center_iff.mp hx_center b)
    have hbxn : Commute b (x ^ n) := hbx.zpow_right n
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    simp [mul_assoc, hbxn.eq]
  let H : Subgroup F := Subgroup.zpowers x
  have hnormalizer_top : Subgroup.normalizer (Subgroup.zpowers x : Set F) = ⊤ := by
    letI : H.Normal := by
      simpa [H] using hnormal
    have htop : Subgroup.normalizer (H : Set F) = ⊤ := Subgroup.normalizer_eq_top H
    simpa [H] using htop
  have hcyc_top : IsCyclic (⊤ : Subgroup F) := by
    have hcyc_normalizer : IsCyclic ↥(Subgroup.normalizer (Subgroup.zpowers x : Set F)) :=
      normalizer_zpowers_isCyclic x hx
    rwa [hnormalizer_top] at hcyc_normalizer
  have hcyc : IsCyclic F :=
    isCyclic_of_surjective (⊤ : Subgroup F).subtype <| fun y ↦ ⟨⟨y, by simp⟩, rfl⟩
  exact hnotcyc hcyc

private instance innerAutomorphismSubgroup_isMulTorsionFree :
    IsMulTorsionFree (JA(F)) := by
  by_cases hcyc : IsCyclic F
  · letI : IsCyclic F := hcyc
    letI : Std.Commutative (· * · : F → F → F) := IsCyclic.isMulCommutative.is_comm
    letI : Subsingleton ↥(JA(F)) := by
      refine ⟨fun α β ↦ ?_⟩
      apply Subtype.ext
      have hα : α.1 = 1 := by
        rcases α.2 with ⟨a, ha⟩
        calc
          α.1 = MulAut.conj a := ha.symm
          _ = 1 := by
            ext x
            calc
              (MulAut.conj a) x = a * (x * a⁻¹) := by
                simp [MulAut.conj_apply, mul_assoc]
              _ = (a * a⁻¹) * x := by ac_rfl
              _ = x := by simp
              _ = (1 : MulAut F) x := by rfl
      have hβ : β.1 = 1 := by
        rcases β.2 with ⟨b, hb⟩
        calc
          β.1 = MulAut.conj b := hb.symm
          _ = 1 := by
            ext x
            calc
              (MulAut.conj b) x = b * (x * b⁻¹) := by
                simp [MulAut.conj_apply, mul_assoc]
              _ = (b * b⁻¹) * x := by ac_rfl
              _ = x := by simp
              _ = (1 : MulAut F) x := by rfl
      exact hα.trans hβ.symm
    infer_instance
  · let e : F ≃* JA(F) :=
        MulEquiv.ofBijective
          ((MulAut.conj : F →* MulAut F).rangeRestrict)
          ⟨by
              intro g h hgh
              have hconj : MulAut.conj g = MulAut.conj h := congrArg Subtype.val hgh
              have hdiv : MulAut.conj (g * h⁻¹) = 1 := by
                calc
                  MulAut.conj (g * h⁻¹) = MulAut.conj g * (MulAut.conj h)⁻¹ := by simp
                  _ = 1 := by rw [hconj]; simp
              have hEq : g * h⁻¹ = 1 := conj_eq_one_implies_eq_one_of_not_isCyclic hcyc hdiv
              exact eq_of_mul_inv_eq_one hEq,
            (MulAut.conj : F →* MulAut F).rangeRestrict_surjective⟩
    exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

private theorem ia_eq_one_of_isOfFinOrder_aux {α : MulAut.IA F} (hα_fin : IsOfFinOrder α) :
    α = 1 := by
  by_contra hα_ne
  let G := MulAut.IA F
  let N : Subgroup G :=
    (JA(F)).subgroupOf G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  letI : IsMulTorsionFree (G ⧸ N) := by
    simpa [N] using ia_quotient_inner_isMulTorsionFree
  have hq_eq : q α = 1 := IsOfFinOrder.eq_one' (q.isOfFinOrder hα_fin)
  have hN : α ∈ N := (QuotientGroup.eq_one_iff α).mp hq_eq
  let β : JA(F) := ⟨α.1, hN⟩
  have hβ_fin : IsOfFinOrder β := by
    rw [isOfFinOrder_iff_pow_eq_one] at hα_fin ⊢
    obtain ⟨n, hn, hpow⟩ := hα_fin
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val hpow
  have hβ_eq : β = 1 := IsOfFinOrder.eq_one' hβ_fin
  have hβ_val : α.1 = 1 := by
    simpa [β] using congrArg Subtype.val hβ_eq
  apply hα_ne
  apply Subtype.ext
  exact hβ_val

/-- Corollary 1-4-14: if `F` is a free group, then `IA(F)` is torsion free. -/
theorem ia_isMulTorsionFree : IsMulTorsionFree (MulAut.IA F) := by
  sorry

end
