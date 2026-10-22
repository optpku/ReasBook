/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Subgroup

section

variable {G : Type u} [Group G]

private theorem subgroup_eq_top_of_basis_subset {ι : Type*} (b : FreeGroupBasis ι G)
    {K : Subgroup G} (hbK : ∀ i, b i ∈ K) :
    K = ⊤ := by
  let φ : G →* K := b.lift fun i ↦ ⟨b i, hbK i⟩
  have hsubtype_comp : K.subtype.comp φ = MonoidHom.id G := by
    apply b.ext_hom
    simp [φ]
  apply top_unique
  intro g _
  have hg : ((φ g : K) : G) = g := by
    simpa [φ] using DFunLike.congr_fun hsubtype_comp g
  exact hg.symm ▸ (φ g).2

private theorem basis_element_not_mem_proper_characteristic_subgroup {ι : Type*}
    (b : FreeGroupBasis ι G) {H : Subgroup G} (hproper : H < ⊤) (hchar : H.Characteristic)
    (i : ι) :
    b i ∉ H := by
  let _ : DecidableEq ι := Classical.decEq _
  intro hiH
  have hall : ∀ j, b j ∈ H := by
    intro j
    let φ : G ≃* G :=
      (b.repr.trans (FreeGroup.freeGroupCongr (Equiv.swap i j))).trans b.repr.symm
    have hle := (characteristic_iff_le_comap.mp hchar) φ
    have hφi : φ (b i) ∈ H := hle hiH
    simpa [φ] using hφi
  have htop : H = ⊤ := subgroup_eq_top_of_basis_subset b hall
  exact hproper.ne htop

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-3: for a descending chain of subgroups of a free group, if each successor is a
proper characteristic subgroup of its predecessor, then the intersection of the chain is trivial.
-/
-- Layer triage:
-- `source-facing`: the descending chain `FSeries : ℕ → Subgroup F`.
-- `core/canonical`: the subgroup lattice infimum `⨅ i, FSeries i`.
-- `bridge/view`: Proposition 1-3-2 already packages the owner theorem for descending chains that
-- avoid primitive elements of each stage, so this item only supplies the characteristic-subgroup
-- bridge from basis elements to that owner-level avoidance hypothesis.
theorem iInf_eq_bot_of_descending_proper_characteristic_subgroups
    (FSeries : ℕ → Subgroup F) (hproper : ∀ i, FSeries (i + 1) < FSeries i)
    (hchar : ∀ i, ((FSeries (i + 1)).subgroupOf (FSeries i)).Characteristic) :
    (⨅ i, FSeries i) = ⊥ := by
  have hdesc : ∀ i, FSeries (i + 1) ≤ FSeries i := fun i ↦ (hproper i).le
  have havoid : ∀ i {w : FSeries i}, IsPrimitiveElement w → (w : F) ∉ FSeries (i + 1) := by
    intro i w hw
    rcases hw with ⟨κ, B, k, rfl⟩
    let H : Subgroup (FSeries i) := (FSeries (i + 1)).subgroupOf (FSeries i)
    have hHproper : H < ⊤ := by
      refine lt_of_le_of_ne le_top ?_
      intro hEq
      have hle : FSeries i ≤ FSeries (i + 1) := subgroupOf_eq_top.1 hEq
      exact (hproper i).ne (le_antisymm (hproper i).le hle)
    simpa [H] using basis_element_not_mem_proper_characteristic_subgroup B hHproper (hchar i) k
  exact iInf_eq_bot_of_descending_subgroups_avoiding_bases FSeries hdesc havoid

end

end
