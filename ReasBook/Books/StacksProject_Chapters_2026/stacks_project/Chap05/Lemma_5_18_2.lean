module

public import Mathlib.Topology.JacobsonSpace

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Jacobson spaces:
- source-facing hypothesis: closed points are dense in each singleton closure
- core/canonical owner: `JacobsonSpace X`
- primitive owner field: `closure_inter_closedPoints`
- bridge/view: this theorem maps the singleton-closure density hypothesis to the owner
  `JacobsonSpace X`

Primitive data belongs to the owner `JacobsonSpace X`. This lemma should therefore conclude the
owner by supplying the primitive field `closure_inter_closedPoints` directly, rather than by
rebuilding a parallel wrapper API or routing through the locally closed companion criterion.
-/

-- Proof sketch: supply the owner field `closure_inter_closedPoints`. For a closed subset `Z` and
-- `x ∈ Z`, the closure of `{x}` stays inside `Z`; the density hypothesis on `closure {x}` then
-- puts `x` in the closure of `Z ∩ closedPoints X`. This yields
-- `closure (Z ∩ closedPoints X) = Z`.
/-- Lemma 5.18.2: if for every point `x`, the closed points of `X` are dense in `closure {x}`,
then `X` is a Jacobson space. -/
theorem jacobsonSpace_of_dense_closedPoints_in_singleton_closure
    (hDense : ∀ x : X, closure (closure ({x} : Set X) ∩ closedPoints X) = closure ({x} : Set X)) :
    JacobsonSpace X := by
  refine ⟨?_⟩
  intro Z hZ
  refine subset_antisymm ?_ ?_
  · exact hZ.closure_subset_iff.mpr inter_subset_left
  · intro x hxZ
    have hclosure : closure ({x} : Set X) ⊆ Z :=
      hZ.closure_subset_iff.mpr (singleton_subset_iff.2 hxZ)
    have hx : x ∈ closure (closure ({x} : Set X) ∩ closedPoints X) := by
      simpa [hDense x] using (subset_closure (by simp : x ∈ ({x} : Set X)))
    exact (closure_mono <| inter_subset_inter hclosure subset_rfl) hx
