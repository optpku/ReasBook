/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {F : Type u} [Group F]

open CategoryTheory

namespace Subgroup

/-- Definition 1-2-28: The subgroups `F₁` and `F₂` are free factors of `F`, equivalently `F`
is the free product `F₁ * F₂`, when there are generating sets `X₁` and `X₂` with
`Subgroup.closure X₁ = F₁`, `Subgroup.closure X₂ = F₂`, `X₁ ∩ X₂ = ∅`, and `X₁ ∪ X₂` a basis of
`F`. -/
-- Layer: source-facing definition.
-- Core/canonical owner abstraction: `IsFreeGroupBasis` for the union `X₁ ∪ X₂`.
def AreFreeFactors (F₁ F₂ : Subgroup F) : Prop :=
  ∃ X₁ X₂ : Set F,
    closure X₁ = F₁ ∧ closure X₂ = F₂ ∧ Disjoint X₁ X₂ ∧ IsFreeGroupBasis (X₁ ∪ X₂)

/-- A subgroup `H` is a free factor of an overgroup `G` when `H ≤ G` and the transported subgroup
`H.subgroupOf G` has a complementary free factor inside `G`. -/
-- Layer: bridge/view from the source-facing two-factor decomposition `AreFreeFactors` to the
-- one-sided overgroup relation used throughout Hall's theorem and its corollaries.
def IsFreeFactorOf (H G : Subgroup F) : Prop :=
  H ≤ G ∧ ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K

/-- Unpack the owner relation “`H` is a free factor of `G`”. -/
theorem isFreeFactorOf_iff {H G : Subgroup F} :
    H.IsFreeFactorOf G ↔ H ≤ G ∧ ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K :=
  Iff.rfl

/-- Free-factor decompositions are symmetric in the two factors. -/
theorem AreFreeFactors.symm {F₁ F₂ : Subgroup F} :
    AreFreeFactors F₁ F₂ ↔ AreFreeFactors F₂ F₁ := by
  constructor
  · rintro ⟨X₁, X₂, hX₁, hX₂, hdisj, hbasis⟩
    refine ⟨X₂, X₁, hX₂, hX₁, hdisj.symm, ?_⟩
    exact (Set.union_comm X₁ X₂) ▸ hbasis
  · rintro ⟨X₂, X₁, hX₂, hX₁, hdisj, hbasis⟩
    refine ⟨X₁, X₂, hX₁, hX₂, hdisj.symm, ?_⟩
    exact (Set.union_comm X₂ X₁) ▸ hbasis

/-- A free-product decomposition by free factors exhibits the ambient group as free. -/
-- Proof sketch: unpack the defining generating sets `X₁` and `X₂`; their union is a free basis of
-- `F`, so `IsFreeGroupBasis.isFreeGroup` gives the desired free-group structure on the ambient
-- group.
theorem AreFreeFactors.isFreeGroup {F₁ F₂ : Subgroup F} (h : AreFreeFactors F₁ F₂) :
    IsFreeGroup F := by
  rcases h with ⟨X₁, X₂, -, -, -, hX⟩
  exact hX.isFreeGroup

/-- A free factor of an overgroup is, in particular, a subgroup of that overgroup. -/
theorem IsFreeFactorOf.le {H G : Subgroup F} (h : H.IsFreeFactorOf G) : H ≤ G :=
  h.1

/-- A free factor of an overgroup comes with a complementary free factor in that overgroup. -/
theorem IsFreeFactorOf.exists_complement {H G : Subgroup F} (h : H.IsFreeFactorOf G) :
    ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K :=
  h.2

/-- A subgroup of a free group admits a complementary free factor exactly when its inclusion has a
left inverse. -/
-- Layer: bridge/view from the source-facing free-factor relation to the chapter owner abstraction
-- `Function.LeftInverse` for subgroup inclusions. The categorical split-mono formulation is
-- derived from `subtype_isSplitMono_iff_exists_leftInverse`, so it is not kept as a parallel
-- primitive bridge here.
theorem exists_complement_iff_exists_leftInverse [IsFreeGroup F] (F₁ : Subgroup F) :
    (∃ F₂ : Subgroup F, AreFreeFactors F₁ F₂) ↔
      ∃ ρ : F →* F₁, Function.LeftInverse ρ F₁.subtype := by
  sorry

/-- The inclusion of either side of a free-factor decomposition is split. -/
theorem AreFreeFactors.left_isSplitMono {F₁ F₂ : Subgroup F}
    (h : AreFreeFactors F₁ F₂) : IsSplitMono (GrpCat.ofHom F₁.subtype) := by
  let _ : IsFreeGroup F := h.isFreeGroup
  rw [subtype_isSplitMono_iff_exists_leftInverse]
  exact (exists_complement_iff_exists_leftInverse F₁).mp ⟨F₂, h⟩

/-- The right-hand factor in a free-factor decomposition also has split inclusion. -/
theorem AreFreeFactors.right_isSplitMono {F₁ F₂ : Subgroup F}
    (h : AreFreeFactors F₁ F₂) : IsSplitMono (GrpCat.ofHom F₂.subtype) :=
  (AreFreeFactors.symm.mp h).left_isSplitMono

/-- If `H` is a free factor of `G`, then its inclusion into `G` is split. -/
theorem IsFreeFactorOf.isSplitMono {H G : Subgroup F} (h : H.IsFreeFactorOf G) :
    IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := by
  rcases h.exists_complement with ⟨K, hK⟩
  exact hK.left_isSplitMono

private def retractToFreeFactor {H G : Subgroup F} (h : H.IsFreeFactorOf G)
    (ρ : G →* H.subgroupOf G) : G →* H :=
  (subgroupOfEquivOfLe h.le).toMonoidHom.comp ρ

/-- A free factor of a finitely generated overgroup is finitely generated. -/
-- Layer: derived owner API for `Subgroup.IsFreeFactorOf`.
theorem IsFreeFactorOf.fg {H G : Subgroup F} [Group.FG G] (h : H.IsFreeFactorOf G) :
    Group.FG H := by
  have hsplit : IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := h.isSplitMono
  rw [subtype_isSplitMono_iff_exists_leftInverse] at hsplit
  rcases hsplit with ⟨ρ, hρ⟩
  let e : H.subgroupOf G ≃* H := subgroupOfEquivOfLe h.le
  let ρ' : G →* H := retractToFreeFactor h ρ
  have hsurj : Function.Surjective ρ' := by
    intro x
    refine ⟨(e.symm x).1, ?_⟩
    simpa using congrArg e (hρ (e.symm x))
  exact Group.fg_of_surjective hsurj

/-- A free factor of a finitely generated overgroup has rank at most that of the overgroup. -/
-- Layer: derived owner API for `Subgroup.IsFreeFactorOf`, obtained from the retraction supplied by
-- `IsFreeFactorOf.isSplitMono` and the canonical owner theorem `Group.rank_le_of_surjective`.
theorem IsFreeFactorOf.rank_le {H G : Subgroup F} [Group.FG H] [Group.FG G]
    (h : H.IsFreeFactorOf G) : Group.rank H ≤ Group.rank G := by
  have hsplit : IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := h.isSplitMono
  rw [subtype_isSplitMono_iff_exists_leftInverse] at hsplit
  rcases hsplit with ⟨ρ, hρ⟩
  let e : H.subgroupOf G ≃* H := subgroupOfEquivOfLe h.le
  let ρ' : G →* H := retractToFreeFactor h ρ
  have hsurj : Function.Surjective ρ' := by
    intro x
    refine ⟨(e.symm x).1, ?_⟩
    simpa using congrArg e (hρ (e.symm x))
  exact Group.rank_le_of_surjective ρ' hsurj

end Subgroup
