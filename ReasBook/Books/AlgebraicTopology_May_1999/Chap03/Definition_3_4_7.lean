/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open QuotientGroup

variable (G : Type u) [Group G]

/-- Definition 3.4.7: the orbit category `O(G)` has as objects the canonical transitive `G`-sets
`G ⧸ H`, encoded by subgroups `H ≤ G`. The owner is distinct from `Subgroup G`; the subgroup
encoding is a view of the objects, not the orbit category itself. -/
@[ext]
structure orbitCategory : Type u where
  toSubgroup : Subgroup G

notation "O(" G ")" => orbitCategory G

attribute [coe] orbitCategory.toSubgroup

namespace orbitCategory

instance : CoeTC (O(G)) (Subgroup G) := ⟨orbitCategory.toSubgroup⟩

instance : HasQuotient G (O(G)) := ⟨fun H ↦ G ⧸ (H : Subgroup G)⟩

instance (H : O(G)) : CoeTC G (G ⧸ H) :=
  show CoeTC G (G ⧸ (H : Subgroup G)) from inferInstance

instance (H : O(G)) : MulAction G (G ⧸ H) :=
  show MulAction G (G ⧸ (H : Subgroup G)) from inferInstance

instance instIsPretransitiveQuotient (H : O(G)) : MulAction.IsPretransitive G (G ⧸ H) :=
  show MulAction.IsPretransitive G (G ⧸ (H : Subgroup G)) from inferInstance

instance (H : O(G)) [TopologicalSpace G] : TopologicalSpace (G ⧸ H) :=
  show TopologicalSpace (G ⧸ (H : Subgroup G)) from inferInstance

theorem toSubgroup_injective : Function.Injective ((↑) : O(G) → Subgroup G)
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : SetLike (O(G)) G where
  coe H := H.toSubgroup.carrier
  coe_injective' H K h := by
    apply toSubgroup_injective
    exact SetLike.ext' h

instance : SubgroupClass (O(G)) G where
  mul_mem {H} := H.toSubgroup.mul_mem
  one_mem H := H.toSubgroup.one_mem
  inv_mem {H} := H.toSubgroup.inv_mem

instance : PartialOrder (O(G)) := .ofSetLike (O(G)) G

end orbitCategory

/-- Morphisms in the orbit category are the `G`-equivariant maps between the quotient `G`-sets. -/
instance : Category (O(G)) where
  Hom H K := G ⧸ H →[G] G ⧸ K
  id H := MulActionHom.id G
  comp f g := MulActionHom.comp g f

/-- Every object of the orbit category is a transitive `G`-set. -/
theorem orbitCategory_obj_isTransitive (H : O(G)) :
    MulAction.IsTransitive G (G ⧸ H) :=
  ⟨⟨((1 : G) : G ⧸ H)⟩, inferInstance⟩
