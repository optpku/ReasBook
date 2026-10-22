/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_21
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open AddSubgroup
open scoped IsMulCommutative

variable {G : Type u} [Group G]

private theorem isCyclic_of_isMulCommutative_of_centralizer_le [IsFreeGroup G]
    {A : Subgroup G} (hA : IsMulCommutative A)
    (hcentralizer : Subgroup.centralizer (A : Set G) ≤ A) : IsCyclic A := by
  letI : IsMulCommutative A := hA
  rcases A.bot_or_exists_ne_one with hA_bot | ⟨a, ha, ha1⟩
  · subst hA_bot
    infer_instance
  let N : Subgroup G := Subgroup.normalizer (Subgroup.zpowers a : Set G)
  have hza : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 ha
  have hA_le_N : A ≤ N := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxA : x ∈ A := hza hx
      have hbx : b * x = x * b := setLike_mul_comm hb hxA
      simpa [mul_assoc, hbx]
        using hx
    · intro hx
      have hxA : b * x * b⁻¹ ∈ A := hza hx
      have hxA' : x ∈ A := by
        have : b⁻¹ * (b * x * b⁻¹) * b ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hb) hxA) hb
        simpa [mul_assoc] using this
      have hbx : b * x = x * b := setLike_mul_comm hb hxA'
      simpa [mul_assoc, hbx]
        using hx
  have hNcyc : IsCyclic N := by
    simpa [N] using normalizer_zpowers_isCyclic a ha1
  letI : IsCyclic N := hNcyc
  have hN_le_centralizer : N ≤ Subgroup.centralizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hbx : (⟨b, hb⟩ : N) * ⟨x, hA_le_N hx⟩ = ⟨x, hA_le_N hx⟩ * ⟨b, hb⟩ := by
      simpa using mul_comm (⟨b, hb⟩ : N) ⟨x, hA_le_N hx⟩
    exact (congrArg Subtype.val hbx).symm
  have hN_le_A : N ≤ A := fun b hb ↦ hcentralizer (hN_le_centralizer hb)
  have hNA : N = A := le_antisymm hN_le_A hA_le_N
  exact hNA ▸ hNcyc

/-- Proposition 1-9-3: in the abstract-length-function setting of Section `9`, every maximal
abelian subgroup is additively isomorphic to an additive subgroup of `ℝ`. -/
-- Layer triage:
-- `source-facing`: a maximal abelian subgroup `A` of a group carrying the Section `9` owner
-- predicate `IsAbstractLengthFunction length`.
-- `core/canonical`: `IsAbstractLengthFunction length`, `IsMulCommutative A` together with the
-- self-centralizing condition `Subgroup.centralizer (A : Set G) ≤ A`, the freeness bridge
-- `isFreeGroup_of_abstractLengthFunction`, the free-group cyclicity theorem
-- `normalizer_zpowers_isCyclic`, and the canonical additive embedding `Int.castAddHom ℝ`.
-- `bridge/view`: express maximal abelianity through the centralizer owner API, pass from the
-- Section `9` owner abstraction to the induced free-group structure on `G`, identify `A` with the
-- cyclic normalizer of a nontrivial element it contains, and compare the resulting cyclic additive
-- group with the image of `ℤ` in `ℝ`.
-- Domain sampling:
-- 1. `IsAbstractLengthFunction length` is the chapter owner abstraction for Section `9`, so the
--    proposition should consume it directly rather than primitive ordered-group hypotheses on `A`.
-- 2. `Subgroup.centralizer` together with
--    `Subgroup.le_centralizer_iff_isMulCommutative` is mathlib's owner API for subgroup abelianity
--    and self-centralizing maximality, so the local wrapper is redundant.
-- 3. `isFreeGroup_of_abstractLengthFunction` is the canonical upgrade from the Section `9`
--    hypotheses to the ambient free-group owner abstraction.
-- 4. `normalizer_zpowers_isCyclic` is the earlier Chapter `1` cyclicity result that captures the
--    free-group structure behind maximal abelian subgroups.
-- 5. `Int.castAddHom ℝ` is the canonical additive embedding of `ℤ` into `ℝ`, and
--    `AddSubgroup.equivMapOfInjective` is the owner bridge from a subgroup to its image.
-- Proof sketch: Proposition `1-9-1` upgrades the ambient group to a free group. In a free group,
-- an abelian self-centralizing subgroup agrees with the cyclic normalizer of any nontrivial
-- element it contains, so it is cyclic. A nontrivial cyclic subgroup of a free group is torsion
-- free, hence canonically isomorphic to `ℤ`; composing that isomorphism with the image of
-- `Int.castAddHom ℝ` yields the required additive subgroup of `ℝ`.
theorem maximal_abelian_subgroup_addEquiv_addSubgroup_real
    (length : G → ℕ) [IsAbstractLengthFunction length]
    (A : Subgroup G) (hA : IsMulCommutative A)
    (hcentralizer : Subgroup.centralizer (A : Set G) ≤ A) :
    ∃ H : AddSubgroup ℝ, Nonempty (Additive A ≃+ H) := by
  letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
  by_cases hA_bot : A = ⊥
  · haveI : Subsingleton A := by
      rw [hA_bot]
      infer_instance
    let e0 : Additive A →+ (⊥ : AddSubgroup ℝ) :=
      { toFun := fun _ ↦ 0
        map_zero' := rfl
        map_add' := fun _ _ ↦ by simp }
    refine ⟨⊥, ⟨AddEquiv.ofBijective e0 ?_⟩⟩
    constructor
    · intro x y hxy
      exact Subsingleton.elim x y
    · intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ y
  · have hcyc : IsCyclic A := isCyclic_of_isMulCommutative_of_centralizer_le hA hcentralizer
    haveI : IsAddCyclic (Additive A) := isAddCyclic_additive_iff.2 hcyc
    letI : IsFreeGroup A := subgroupIsFreeOfIsFree A
    letI : IsMulTorsionFree A := by
      let e := IsFreeGroup.toFreeGroup A
      exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective
    obtain ⟨g, hg⟩ : ∃ g : Additive A, AddSubgroup.zmultiples g = ⊤ :=
      isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
    have hA_nontrivial : Nontrivial A := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hA_bot with ⟨a, ha1⟩
      exact ⟨⟨a, 1, ha1⟩⟩
    letI : Nontrivial A := hA_nontrivial
    have hg0 : g ≠ 0 := by
      intro hg0
      rw [hg0, AddSubgroup.zmultiples_zero_eq_bot] at hg
      exact bot_ne_top hg
    have hginj : Function.Injective (zmultiplesHom (Additive A) g) := by
      have hgfin : ¬ IsOfFinAddOrder g := by
        have hg1 : Multiplicative.ofAdd g ≠ 1 := by
          simpa using hg0
        rw [← isOfFinOrder_ofAdd_iff]
        exact not_isOfFinOrder_of_isMulTorsionFree hg1
      have hginj' : Function.Injective (fun n : ℤ ↦ n • g) :=
        injective_zsmul_iff_not_isOfFinAddOrder.mpr hgfin
      intro m n hmn
      exact hginj' hmn
    have hgsurj : Function.Surjective (zmultiplesHom (Additive A) g) := by
      refine AddMonoidHom.range_eq_top.mp ?_
      simpa using hg
    let eA : ℤ ≃+ Additive A := AddEquiv.ofBijective (zmultiplesHom (Additive A) g) ⟨hginj, hgsurj⟩
    let H : AddSubgroup ℝ := (⊤ : AddSubgroup ℤ).map (Int.castAddHom ℝ)
    let eZ : ℤ ≃+ H :=
      (AddSubgroup.topEquiv : (⊤ : AddSubgroup ℤ) ≃+ ℤ).symm.trans
        ((⊤ : AddSubgroup ℤ).equivMapOfInjective (Int.castAddHom ℝ) Int.cast_injective)
    exact ⟨H, ⟨eA.symm.trans eZ⟩⟩

end
