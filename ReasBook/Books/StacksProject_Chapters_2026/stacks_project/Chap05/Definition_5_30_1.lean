module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for topological groups:
- inspected owner declarations: `IsTopologicalGroup`, `ContinuousMul`, `ContinuousInv`,
  `ContinuousMonoidHom`
- core/canonical owner: `IsTopologicalGroup`
- primitive data: `ContinuousMul`, `ContinuousInv`
- canonical morphism owner and surface: `ContinuousMonoidHom`, written `G →ₜ* H`
- source-facing bridge: `isTopologicalGroup_iff_continuousMul_continuousInv`

Layer triage:
- `source-facing`: continuity of multiplication and inversion
- `core/canonical`: `IsTopologicalGroup`
- `bridge/view`: the companion theorem unpacking the owner into its primitive mixins

This item should keep the canonical owner as the main entry, use the primitive mixins only as
companion data, and state the morphism notion by the canonical type expression `G →ₜ* H`.
-/

/- Definition 5.30.1 (1): the Stacks notion of a topological group is the canonical mathlib
typeclass `IsTopologicalGroup`. -/
recall IsTopologicalGroup

/- Primitive data for the canonical owner `IsTopologicalGroup`: continuity of multiplication. -/
recall ContinuousMul

/- Primitive data for the canonical owner `IsTopologicalGroup`: continuity of inversion. -/
recall ContinuousInv

/-
Definition 5.30.1 (2): the canonical owner for homomorphisms of topological groups is
`ContinuousMonoidHom`.
-/
recall ContinuousMonoidHom

variable {G : Type u} [TopologicalSpace G] [Group G]

/-- Definition 5.30.1 (1): a topological group is exactly a group with a topology for which
multiplication and inversion are continuous. -/
theorem isTopologicalGroup_iff_continuousMul_continuousInv :
    IsTopologicalGroup G ↔ ContinuousMul G ∧ ContinuousInv G := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hMul, hInv⟩
    exact { toContinuousMul := hMul, toContinuousInv := hInv }

variable {H : Type v} [TopologicalSpace H] [Group H]

/- Definition 5.30.1 (2): a homomorphism of topological groups is written `G →ₜ* H`. -/
#check (G →ₜ* H)
