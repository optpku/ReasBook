module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.Prespectral

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

/-
Domain-style sampling for Jacobson behavior of prespectral `T₀` spaces:
- inspected owner declarations already upstream: `JacobsonSpace X`, `closedPoints X`,
  `jacobsonSpace_iff_locallyClosed`
- inspected ambient support API in the spectral/compact domain:
  `PrespectralSpace.isTopologicalBasis`, `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: a non-Jacobson prespectral `T₀` space has a non-closed point with locally
  closed singleton
- `core/canonical`: `JacobsonSpace X` and the owner set `closedPoints X`
- `bridge/view`: `IsLocallyClosed.exists_mem_isLocallyClosed_singleton` extracts a locally closed
  singleton from a nonempty locally closed subset by shrinking to a compact open neighborhood and
  applying the closed-point existence theorem in that compact subspace

Primitive data in the public theorem are only the ambient space assumptions and the negated owner
property `¬ JacobsonSpace X`. The compact-open neighborhood and compact-subspace closed point are
derived internally, so this file should not introduce any parallel public wrapper around Jacobson
spaces or closed points.
-/

variable {X : Type u} [TopologicalSpace X] [T0Space X] [PrespectralSpace X]

/-- A nonempty locally closed subset of a prespectral `T₀` space contains a point whose singleton
is locally closed. -/
theorem IsLocallyClosed.exists_mem_isLocallyClosed_singleton
    {Z : Set X} (hZ' : IsLocallyClosed Z) (hZ : Z.Nonempty) :
    ∃ x, x ∈ Z ∧ IsLocallyClosed ({x} : Set X) := by
  obtain ⟨U, C, hU, hC, rfl⟩ := hZ'
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨V, hV, hxV, hVU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx.1 hU
  have hVC_nonempty : ((Subtype.val : V → X) ⁻¹' C).Nonempty := ⟨⟨x, hxV⟩, hx.2⟩
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp hV.2
  obtain ⟨y, hyC, hyclosed⟩ :=
    (hC.preimage continuous_subtype_val).exists_closed_singleton hVC_nonempty
  refine ⟨y, ⟨hVU y.2, hyC⟩, ?_⟩
  simpa using
    hyclosed.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
      hV.1.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed

-- Proof sketch: contrapose `jacobsonSpace_iff_locallyClosed` to get a nonempty locally closed
-- subset `Z` containing no closed point of `X`. Choose `x ∈ Z`, shrink to a compact open
-- neighborhood inside `Z` using the compact-open basis, and apply the closed-point existence
-- theorem for nonempty compact `T₀` spaces to that compact subspace. The resulting point has
-- locally closed singleton in `X`, and it is not in `closedPoints X` because `Z` contains no
-- closed point of `X`.
/-- Lemma 5.18.3: if a Kolmogorov space with a basis of quasi-compact opens is not Jacobson, then
there exists a non-closed point whose singleton is locally closed. -/
theorem exists_nonclosed_point_with_locallyClosed_singleton_of_not_jacobsonSpace
    (hX : ¬ JacobsonSpace X) :
    ∃ x, x ∉ closedPoints X ∧ IsLocallyClosed ({x} : Set X) := by
  rw [jacobsonSpace_iff_locallyClosed] at hX
  push Not at hX
  obtain ⟨Z, hZ, hZ', hZ₀⟩ := hX
  obtain ⟨x, hxZ, hxloc⟩ :=
    hZ'.exists_mem_isLocallyClosed_singleton hZ
  refine ⟨x, fun hxclosed ↦ ?_, hxloc⟩
  have hx : x ∈ Z ∩ closedPoints X := ⟨hxZ, hxclosed⟩
  rw [hZ₀] at hx
  exact hx
