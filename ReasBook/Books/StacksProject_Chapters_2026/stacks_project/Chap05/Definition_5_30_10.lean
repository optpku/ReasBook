module

import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Topology.Algebra.Module.LinearMap

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Domain-style sampling for topological modules:
- bundled owner abstraction: `TopModuleCat R`
- owner object fields: `IsTopologicalAddGroup`, `ContinuousSMul`
- source-facing constructor data for `TopModuleCat.of`: `ContinuousAdd`, `ContinuousSMul`
- canonical constructor from unbundled data: `TopModuleCat.of`
- canonical morphism owner: `ContinuousLinearMap`, written `M →L[R] N`

Layer triage:
- `source-facing`: the Stacks condition that addition and scalar multiplication are continuous
- `core/canonical`: `TopModuleCat R` and `ContinuousLinearMap`
- `bridge/view`: the theorem below identifying the source-facing additive datum `ContinuousAdd`
  with the additive-group field `IsTopologicalAddGroup` used by the owner

For the source-facing unbundled notion of topological `R`-module, the primitive data is
`ContinuousAdd` together with `ContinuousSMul`. The bundled owner `TopModuleCat R` stores the
additive part as `IsTopologicalAddGroup`; over a ring, continuity of negation is derived from
scalar multiplication by `-1`, so `TopModuleCat.of` is the canonical bridge from the source-facing
data to the owner.
-/

/- Definition 5.30.10: the canonical bundled category of topological `R`-modules over a
topological ring is `TopModuleCat R`. -/
recall TopModuleCat

/- Source-facing additive constructor datum for topological `R`-modules: continuity of addition. -/
recall ContinuousAdd

/- Scalar-action datum for topological `R`-modules, both in the source-facing formulation and in
the owner `TopModuleCat R`: continuity of scalar multiplication. -/
recall ContinuousSMul

/- The canonical constructor `TopModuleCat.of` packages the source-facing data into the owner
`TopModuleCat R`. -/
recall TopModuleCat.of

/- The canonical morphism owner for topological `R`-modules is `ContinuousLinearMap`. -/
recall ContinuousLinearMap

section

/-- Definition 5.30.10: in an `R`-module with continuous scalar multiplication, the source-facing
continuity-of-addition condition is equivalent to the additive-group field
`IsTopologicalAddGroup M` used by `TopModuleCat.of`. -/
theorem continuousAdd_iff_isTopologicalAddGroup
    (R : Type u) [Ring R] [TopologicalSpace R]
    {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M] :
    ContinuousAdd M ↔ IsTopologicalAddGroup M := by
  constructor
  · intro hAdd
    exact
      { toContinuousAdd := hAdd
        toContinuousNeg := ContinuousNeg.of_continuousConstSMul R M }
  · intro hAddGroup
    exact hAddGroup.toContinuousAdd

end

section

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul R N]

/- Definition 5.30.10: a homomorphism of topological `R`-modules is the canonical bundled type
`M →L[R] N` of continuous linear maps. -/
#check (M →L[R] N)

end
