module

public import Mathlib.Topology.Irreducible
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for irreducible components under open maps:
- primary domain: irreducible subsets and irreducible components in point-set topology
- owner abstraction: `irreducibleComponentsEquivOfIsPreirreducibleFiber`
- same-domain declarations inspected:
  `irreducibleComponents`,
  `preimage_mem_irreducibleComponents_of_isPreirreducible_fiber`,
  `image_mem_irreducibleComponents_of_isPreirreducible_fiber`,
  `irreducibleComponentsEquivOfIsPreirreducibleFiber`

Layer triage:
- `source-facing`: Lemma 5.8.15, stated with irreducible fibers
- `core/canonical`: the owner equivalence
  `irreducibleComponentsEquivOfIsPreirreducibleFiber`
- `bridge/view`: the specialization from irreducible fibers to preirreducible fibers together
  with the induced surjectivity witness

Primitive data for the owner theorem is continuity, openness, preirreducible fibers, and
surjectivity. The stronger source hypothesis that every fiber is irreducible supplies the last two
inputs, so this file should recall the owner and keep only that thin source-facing specialization.
-/

/- Canonical recall: the owner theorem for irreducible components under a continuous open map is
`irreducibleComponentsEquivOfIsPreirreducibleFiber`. -/
recall irreducibleComponentsEquivOfIsPreirreducibleFiber

omit [TopologicalSpace Y] in
/-- If every fiber of `f` over a point of `Y` is irreducible, then `f` is surjective. -/
-- Proof sketch: any irreducible fiber is nonempty, so for each `y` one extracts a point in
-- `f ⁻¹' {y}` and hence a preimage of `y`.
theorem surjective_of_isIrreducible_fibers
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) : Function.Surjective f := by
  intro y
  -- Convert nonemptiness of the singleton fiber into membership of `y` in the range of `f`.
  have hy_mem_range : y ∈ Set.range f := by
    exact Set.preimage_singleton_nonempty.mp (hfibers y).nonempty
  -- Unpack range membership to obtain the required preimage witness.
  exact Set.mem_range.mp hy_mem_range

/-- Lemma 5.8.15: a continuous open map whose fibers are irreducible induces a bijection between
the irreducible components of `Y` and those of `X`; equivalently, it induces a canonical order
isomorphism between them. -/
def irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) :
    irreducibleComponents Y ≃o irreducibleComponents X :=
  irreducibleComponentsEquivOfIsPreirreducibleFiber f hcont hopen
    (fun y ↦ (hfibers y).isPreirreducible) (surjective_of_isIrreducible_fibers hfibers)

/-- This specialization is definitionally the canonical equivalence coming from preirreducible
fibers and surjectivity. -/
-- Proof sketch: unfold the specialized definition and compare it with the recalled owner
-- equivalence.
theorem irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers_def
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) :
    irreducibleComponentsEquiv_of_isOpenMap_of_irreducibleFibers hcont hopen hfibers =
      irreducibleComponentsEquivOfIsPreirreducibleFiber f hcont hopen
        (fun y ↦ (hfibers y).isPreirreducible)
        (surjective_of_isIrreducible_fibers hfibers) := by
  -- The specialized definition is exactly the recalled owner equivalence.
  rfl

end
