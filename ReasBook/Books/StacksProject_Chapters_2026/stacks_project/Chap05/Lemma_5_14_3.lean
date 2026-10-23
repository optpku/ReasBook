module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u w

namespace TopCat

section

variable {J : Type v} [Category.{w} J]
variable {F : J ⥤ TopCat.{max v u}} (c : Cone F)
variable [IsCofiltered J]

/-
Domain-style sampling for cofiltered limits in `TopCat`:
- primary domain: categorical limits of topological spaces built from set-level limits and induced
  topologies;
- inspected owner declarations:
  `TopCat.nonempty_isLimit_iff_eq_induced`,
  `TopCat.isTopologicalBasis_cofiltered_limit`,
  `TopCat.isLimitConeOfForget`.
- best owner abstraction: `IsLimit c` in `TopCat`, with the induced-topology criterion as the
  canonical bridge from the underlying limit in `Type`.

Primitive-vs-derived split:
- primitive data: the set-level limit cone together with the equality identifying the topology on
  `c.pt` with the canonical infimum topology;
- derived API: the resulting `TopCat` limit proof and the preimage-basis presentation used to prove
  that topology equality.

Source/core/bridge triage:
- `source-facing`: Lemma 5.14.3, asserting that a cone in `TopCat` is limiting once the underlying
  cone of sets is limiting and the pulled-back opens form a basis;
- `core/canonical`: `TopCat.nonempty_isLimit_iff_eq_induced`;
- `bridge/view`: `TopCat.isTopologicalBasis_cofiltered_limit`, specialized to the basis of all
  open subsets upstairs.
-/

def preimageBasis (c : Cone F) : Set (Set c.pt) :=
  {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}

lemma topology_eq_iInf_induced_of_preimage_basis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis (preimageBasis c)) :
    c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  let c' : Cone F := TopCat.coneOfConeForget ((forget TopCat).mapCone c)
  let T : ∀ j, Set (Set (F.obj j)) := fun j ↦ {V : Set (F.obj j) | IsOpen V}
  have h_basis' :=
    TopCat.isTopologicalBasis_cofiltered_limit F c'
      (TopCat.isLimitConeOfForget ((forget TopCat).mapCone c) h_limit)
      T (fun _ ↦ TopologicalSpace.isTopologicalBasis_opens)
      (fun i ↦ by
        change Set.univ ∈ T i
        simp [T])
      (fun i U₁ U₂ hU₁ hU₂ ↦ by
        simpa [T] using hU₁.inter hU₂)
      (fun i j f V hV ↦ by
        simpa [T] using hV.preimage (F.map f).hom.continuous)
  have h_eq₁ : c.pt.str = TopologicalSpace.generateFrom (preimageBasis c) := h_basis.eq_generateFrom
  have h_eq₂ :
      c'.pt.str = TopologicalSpace.generateFrom (preimageBasis c') :=
    h_basis'.eq_generateFrom
  have hB : preimageBasis c = preimageBasis c' := by
    ext U
    constructor <;> rintro ⟨j, V, hV, rfl⟩ <;> exact ⟨j, V, hV, rfl⟩
  have h_eq : c.pt.str = c'.pt.str := by
    rw [h_eq₁, h_eq₂, hB]
    rfl
  simpa [c', TopCat.topologicalSpaceConePtOfConeForget] using h_eq

/-- Lemma 5.14.3: if the underlying cone of sets is limiting and the pulled-back open subsets from
the cone projections form a topological basis on the cone point, then the cone is limiting in
`TopCat`. The cofiltered hypothesis is retained to match the Stacks Project statement.

The canonical `TopCat` limit cone on the underlying set-level limit is
`TopCat.coneOfConeForget ((forget TopCat).mapCone c)`. The basis hypothesis identifies its
induced topology with the given topology on `c.pt`, so the standard `TopCat` limit criterion
applies. -/
noncomputable def isLimit_of_underlying_limit_of_preimage_basis
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V}) :
    IsLimit c := by
  classical
  exact Classical.choice <|
    (TopCat.nonempty_isLimit_iff_eq_induced c h_limit).2
      (topology_eq_iInf_induced_of_preimage_basis c h_limit h_basis)

-- Proof sketch: apply the `fac` field of the limit proof produced by
-- `isLimit_of_underlying_limit_of_preimage_basis`.
/-- The limiting cone supplied by the preimage-basis criterion has the expected projection
factorization property. -/
theorem isLimit_of_underlying_limit_of_preimage_basis_fac
    (h_limit : IsLimit ((forget TopCat).mapCone c))
    (h_basis :
      IsTopologicalBasis
        {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = c.π.app j ⁻¹' V})
    (s : Cone F) (j : J) :
    (isLimit_of_underlying_limit_of_preimage_basis c h_limit h_basis).lift s ≫ c.π.app j =
      s.π.app j := by
  -- The constructed limiting cone already carries the universal factorization identities.
  exact (isLimit_of_underlying_limit_of_preimage_basis c h_limit h_basis).fac s j

end

end TopCat
