module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Cardinal
open Set

universe u v

/- Domain-style sampling for Hausdorff cardinal bounds from dense subsets:
- primary domain: Hausdorff separation and cardinal bounds coming from dense range data
- sampled owner declarations:
  `DenseRange.subset_closure_image_preimage_of_isOpen`,
  `t2_separation`,
  `closure_minimal`,
  `Cardinal.lift_mk_le'`,
  `Cardinal.mk_set`
- best owner abstraction: this item is `source-facing`; there is no earlier project or mathlib
  owner theorem with this exact interface, so the result should be stated directly and proved from
  the canonical dense-range/separation/cardinal API above
- primitive data: `DenseRange f` and the Hausdorff structure on `Y`
- derived API: the one-off injective map `y ↦ {s : Set X | y ∈ closure (f '' s)}` into
  `Set (Set X)`, which should remain proof scaffolding rather than a separate local owner
-/
section

variable {X : Type u} {Y : Type v} [TopologicalSpace Y] [T2Space Y] {f : X → Y}

/-- Lemma 5.25.1: if `f : X → Y` has dense range and `Y` is Hausdorff, then the cardinality of
`Y` is at most the cardinality of the double powerset of `X`. -/
theorem cardinalMk_le_powerset_powerset_of_denseRange
    (hdense : DenseRange f) :
    lift.{u} #Y ≤ lift.{v} #(Set (Set X)) := by
  refine Cardinal.lift_mk_le'.2 ⟨{
    toFun := fun y : Y ↦ { s : Set X | y ∈ closure (f '' s) }
    inj' := ?_ }⟩
  intro y₁ y₂ hEq
  by_contra hne
  rcases t2_separation hne with ⟨U, V, hU, hV, hy₁U, hy₂V, hUV⟩
  let s : Set X := f ⁻¹' U
  have hy₁s : y₁ ∈ closure (f '' s) := by
    simpa [s] using hdense.subset_closure_image_preimage_of_isOpen hU hy₁U
  have hclosureV : closure (f '' s) ⊆ Vᶜ := by
    refine closure_minimal ?_ hV.isClosed_compl
    rintro _ ⟨x, hx, rfl⟩ hyV
    exact hUV.le_bot ⟨hx, hyV⟩
  have hy₂nots : y₂ ∉ closure (f '' s) := fun hy₂s ↦ hclosureV hy₂s hy₂V
  exact hy₂nots <| by
    change s ∈ (fun y : Y ↦ { s : Set X | y ∈ closure (f '' s) }) y₂
    exact hEq ▸ (show s ∈ (fun y : Y ↦ { s : Set X | y ∈ closure (f '' s) }) y₁ from hy₁s)

/-- Cardinal-arithmetic companion to `cardinalMk_le_powerset_powerset_of_denseRange`. -/
theorem cardinalMk_le_powerpower_of_denseRange
    (hdense : DenseRange f) :
    lift.{u} #Y ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ lift.{v} #X) := by
  simpa [Cardinal.mk_set] using cardinalMk_le_powerset_powerset_of_denseRange hdense

end
