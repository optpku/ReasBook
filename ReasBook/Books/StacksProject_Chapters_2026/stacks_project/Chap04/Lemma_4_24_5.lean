module

public import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.5:
- primary domain: adjunctions and preservation of (co)limits;
- sampled owner API:
  `Adjunction.leftAdjoint_preservesColimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `Adjunction.functorialityAdjunction`,
  `Adjunction.functorialityAdjunction'`;
- source-facing layer: the Stacks statement that an adjoint pair `u ⊣ v` has `u` preserving
  colimits and `v` preserving limits;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: the cocone and cone functoriality adjunctions used upstream to prove the owner
  theorems.

Primitive-vs-derived split:
- primitive data: an adjunction `u ⊣ v`;
- derived API: the preservation-of-colimits and preservation-of-limits instances attached to that
  adjunction. No local wrapper or reformulation is needed here.
-/

/- Source/core/bridge triage for Lemma 4.24.5:
- `source-facing`: the textbook assertion that left adjoints preserve colimits and right adjoints
  preserve limits;
- `core/canonical`: the owner theorems
  `Adjunction.leftAdjoint_preservesColimits` and
  `Adjunction.rightAdjoint_preservesLimits`;
- `bridge/view`: the explicit finite-exactness consequences are handled downstream in
  `Lemma_4_24_6`, so this file should remain a pure recall of the owner API.
-/

/- Lemma 4.24.5: for an adjunction `u ⊣ v`, the left adjoint `u` preserves colimits and the right
adjoint `v` preserves limits. These are exactly the canonical mathlib theorems
`Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits`. -/
recall Adjunction.leftAdjoint_preservesColimits
recall Adjunction.rightAdjoint_preservesLimits

end CategoryTheory
