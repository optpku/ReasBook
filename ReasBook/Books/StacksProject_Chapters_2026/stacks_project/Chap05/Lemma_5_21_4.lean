module

public import Mathlib.Topology.Sets.OpenCover

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for nowhere dense locality on open covers:
- primary domain: general topology of nowhere dense subsets and open-cover locality
- owner abstraction for a fixed cover: `TopologicalSpace.IsOpenCover`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_mem`,
  `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`,
  `Opens.isOpenEmbedding'`,
  `IsOpenMap.preimage_closure_eq_closure_preimage`

Layer triage:
- `source-facing`: `isNowhereDense_of_isOpenCover`
- `core/canonical`: `IsNowhereDense`
- `bridge/view`: restriction to the open subspaces `U i`

Primitive data is only the subset `T`; the local subspace statements are derived from the owner
predicate by restricting along the subtype maps of the cover members. The owner-level theorem on
`TopologicalSpace.IsOpenCover` should therefore remain the main API, and the textbook one-way
statement should be a thin consequence.
-/

namespace TopologicalSpace.IsOpenCover

/-- Helper for Lemma 5.21.4: restricting `interior (closure T)` to an open subspace matches the
interior of the closure of the restricted set. -/
private theorem preimage_interior_closure_eq {U : Opens X} {T : Set X} :
    (((Subtype.val) : U → X) ⁻¹' interior (closure T) : Set U) =
      interior (closure (((Subtype.val) : U → X) ⁻¹' T)) := by
  let hopen : IsOpenMap ((↑) : U → X) := U.isOpenEmbedding'.isOpenMap
  -- Pull interior and closure through the subtype map of the open subspace.
  calc
    Subtype.val ⁻¹' interior (closure T)
        = interior (Subtype.val ⁻¹' closure T) := by
            simpa using
              hopen.preimage_interior_eq_interior_preimage continuous_subtype_val (closure T)
    _ = interior (closure (Subtype.val ⁻¹' T)) := by
          simpa using congrArg interior
            (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val T)

variable {ι : Type v} {U : ι → Opens X} {T : Set X}

/-- Nowhere density is local on an open cover. -/
theorem isNowhereDense_iff_coe_preimage (hU : IsOpenCover U) :
    IsNowhereDense T ↔ ∀ i, IsNowhereDense (((Subtype.val) : U i → X) ⁻¹' T) := by
  constructor
  · intro hT i
    -- Restrict the global empty-interior statement to each open member of the cover.
    simpa [IsNowhereDense, preimage_interior_closure_eq] using
      congrArg (preimage ((Subtype.val) : U i → X)) hT
  · intro hT
    -- If a point lay in `interior (closure T)`, some cover member would inherit a contradiction.
    rw [IsNowhereDense]
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have hTi : (((Subtype.val) : U i → X) ⁻¹' interior (closure T) : Set (U i)) = ∅ := by
      rw [preimage_interior_closure_eq]
      simpa [IsNowhereDense] using hT i
    have hx' : (⟨x, hi⟩ : U i) ∈
        (((Subtype.val) : U i → X) ⁻¹' interior (closure T) : Set (U i)) := by
      simpa using hx
    rw [hTi] at hx'
    exact hx'

end TopologicalSpace.IsOpenCover

-- Proof sketch: if `interior (closure T)` were nonempty, some cover member `U i` would meet it.
-- Intersecting with that open set identifies the resulting open subset with an open subset of the
-- closure of `Subtype.val ⁻¹' T` inside the subspace `U i`, contradicting the nowhere denseness
-- assumption there.
/-- Lemma 5.21.4: if an open cover of `X` restricts a subset `T` to a nowhere dense subset on
each member, then `T` is nowhere dense in `X`. -/
theorem isNowhereDense_of_isOpenCover
    {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) {T : Set X}
    (hT : ∀ i, IsNowhereDense (((↑) : U i → X) ⁻¹' T)) :
    IsNowhereDense T :=
  -- The owner-level equivalence already identifies global nowhere density with local nowhere
  -- density on each member of the open cover.
  (hU.isNowhereDense_iff_coe_preimage).2 hT
