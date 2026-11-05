module

public import Mathlib.Topology.KrullDimension

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/-
Domain-style sampling for equidimensionality on topological spaces:
- earlier chapter owner: `topologicalKrullDim`, recalled in `Definition_5_10_1`
- mathlib owner for irreducible components: `irreducibleComponents`
- component closedness bridge: `isClosed_of_mem_irreducibleComponents`
- singleton-component bridge for irreducible spaces: `irreducibleComponents_eq_singleton`
- no earlier project/mathlib owner for equidimensionality itself, so this file should own the
  source-facing predicate and build it from the canonical component owner

Layer triage:
- `source-facing`: `EquidimensionalSpace`
- `core/canonical`: the canonical owner type `irreducibleComponents X`
- `bridge/view`: coercing a component `Z : irreducibleComponents X` to the subset `(Z : Set X)`

Primitive data belongs only to `EquidimensionalSpace.topologicalKrullDim_eq`; set-membership
restatements are derived API and do not need to remain as parallel public owners.
-/

/-- Definition 5.10.5: a topological space is equidimensional if every irreducible component of
the space has the same topological Krull dimension. -/
class EquidimensionalSpace (X : Type u) [TopologicalSpace X] : Prop where
  topologicalKrullDim_eq (Z₁ Z₂ : irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂

variable [EquidimensionalSpace X]

/-- Textbook-form bridge: in an equidimensional space, any two irreducible components viewed as
subsets have the same topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents {Z₁ Z₂ : Set X}
    (hZ₁ : Z₁ ∈ irreducibleComponents X) (hZ₂ : Z₂ ∈ irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂ :=
  EquidimensionalSpace.topologicalKrullDim_eq ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩

/-- An irreducible topological space is equidimensional. -/
instance [IrreducibleSpace X] : EquidimensionalSpace X where
  topologicalKrullDim_eq Z₁ Z₂ := by
    letI : Subsingleton (irreducibleComponents X) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    simpa using
      congrArg (fun Z : irreducibleComponents X ↦ topologicalKrullDim Z)
        (Subsingleton.elim Z₁ Z₂)

end TopologicalSpace
