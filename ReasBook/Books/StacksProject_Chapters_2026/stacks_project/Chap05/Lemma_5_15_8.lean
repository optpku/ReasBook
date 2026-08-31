module

public import Mathlib.Topology.Constructible

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology
open scoped Set.Notation

universe u

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {T : Set X}

/-
Domain-style sampling for constructible pullbacks along retrocompact subspace inclusions:
- primary domain: constructible subsets, retrocompact opens, and spectral maps into a prespectral
  space
- sampled canonical declarations:
  `Topology.IsConstructible.preimage`,
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`,
  `TopologicalSpace.IsTopologicalBasis.isInducing`,
  `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`
- best owner abstraction: `Topology.IsConstructible.preimage` is the main owner for constructible
  pullbacks, and the supporting retrocompact-preimage bridge belongs at the
  `IsInducing`/`IsSpectralMap` layer rather than as a subtype-specific helper

Layer triage:
- `source-facing`: the trace of a constructible subset on a retrocompact subspace
- `core/canonical`: `Topology.IsConstructible.preimage`
- `bridge/view`: `Subtype.val : T → X`, viewed canonically through
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`

Primitive data for the public statement are the constructible subset `E`, the retrocompact subset
`T`, and the ambient prespectral structure on `X`. The compact-open basis induced on the source of
an inducing spectral map is derived API and should be exposed once at that owner level rather than
packaged as a subtype-only local lemma.
-/

private theorem isRetrocompact_preimage_of_isSpectralMap
    {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf_ind : IsInducing f) (hf_spec : IsSpectralMap f)
    {U : Set X} (hU_open : IsOpen U) (hU_retro : IsRetrocompact U) :
    IsRetrocompact (f ⁻¹' U) := by
  let basisY : Set (Set Y) := Set.preimage f '' {V : Set X | IsOpen V ∧ IsCompact V}
  have hBasisY : IsTopologicalBasis basisY :=
    PrespectralSpace.isTopologicalBasis.isInducing hf_ind
  intro V hV_comp hV_open
  obtain ⟨s, hsV⟩ :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open basisY hBasisY V hV_comp hV_open
  rw [hsV, Set.sUnion_image]
  have hEq :
      (f ⁻¹' U ∩ ⋃ W ∈ (↑s : Set basisY), ((W : basisY) : Set Y)) =
        ⋃ W ∈ (↑s : Set basisY), (f ⁻¹' U ∩ ((W : basisY) : Set Y)) := by
    ext y
    simp
  rw [hEq]
  refine s.isCompact_biUnion fun W _ ↦ ?_
  rcases W.2 with ⟨W', hW', hW_eq⟩
  rw [← hW_eq]
  rw [show f ⁻¹' U ∩ f ⁻¹' W' = f ⁻¹' (U ∩ W') by ext y; rfl]
  exact hf_spec.isCompact_preimage_of_isOpen (hU_open.inter hW'.1) (hU_retro hW'.2 hW'.1)

-- Proof sketch: apply `Topology.IsConstructible.preimage` to the subtype map `Subtype.val : T → X`.
-- For a compact open `U ⊆ X`, use the compact-open basis hypothesis on the subspace `T` to show
-- that `(Subtype.val) ⁻¹' U = U ∩ T` is retrocompact in `T`; then pull back the constructible set
-- `E` along the subtype inclusion.
/-- Lemma 5.15.8: if `T ⊆ X` is retrocompact and compact open subsets form a topological basis of
`X`, then the trace of a constructible subset `E ⊆ X` on the subspace `T` is constructible in
`T`. The ambient compact-open-basis hypothesis is expressed canonically as `[PrespectralSpace X]`.
-/
theorem IsConstructible.preimage_subtypeVal_of_isRetrocompact
    {E : Set X} (hE : IsConstructible E) (hT : IsRetrocompact T) :
    IsConstructible (T ↓∩ E) :=
  let hSubtype : IsSpectralMap (Subtype.val : T → X) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hT
  hE.preimage continuous_subtype_val
    (fun _ hs_open hs_retro ↦
      isRetrocompact_preimage_of_isSpectralMap IsInducing.subtypeVal hSubtype hs_open hs_retro)

end

end Topology
