module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {J : Type u₁} [Category.{v₁} J] [IsConnected J]
variable {C : Type u₂} [Category.{v₂} C]
variable {X : C} (M : J ⥤ Over X)

/- Domain-style sampling for Lemma 4.16.2:
- primary domain: connected limits in slice categories, with the slice projection `Over.forget X`
  as the ambient owner functor;
- sampled owner API:
  `Over.createsLimitsOfShapeForgetOfIsConnected`,
  `Over.preservesLimitsOfShape_forget_of_isConnected`,
  `PreservesLimitsOfShape.preservesLimit`;
- best owner abstraction: the connected-limit preservation instance on `Over.forget X`;
- primitive data: the connected diagram shape `J`, the slice projection `Over.forget X`, and the
  owner instance `PreservesLimitsOfShape J (Over.forget X)`;
- derived API: for each fixed diagram `M : J ⥤ Over X`, the specialized instance
  `PreservesLimit M (Over.forget X)`.

The statement in this file lives at the `bridge/view` layer: it specializes the ambient owner
instance to one diagram, so it should reuse `PreservesLimitsOfShape.preservesLimit` rather than
introducing a local wrapper or restating the universal property.
-/

/- Source/core/bridge triage for Lemma 4.16.2:
- `source-facing`: the specialized preservation statement for a fixed connected diagram
  `M : J ⥤ Over X`.
- `core/canonical`: the owner instance
  `Over.preservesLimitsOfShape_forget_of_isConnected`.
- `bridge/view`: the derived instance `PreservesLimit M (Over.forget X)`, obtained from
  `PreservesLimitsOfShape.preservesLimit`.
-/

/- Lemma 4.16.2: if `M : J ⥤ Over X` is a diagram indexed by a connected category and `M` has a
limit in `Over X`, then after forgetting to `C` the underlying diagram has the same limit. This is
the canonical connected-limit preservation instance on `Over.forget X`, specialized to `M`. -/
#check (inferInstance : PreservesLimit M (Over.forget X))

end CategoryTheory
