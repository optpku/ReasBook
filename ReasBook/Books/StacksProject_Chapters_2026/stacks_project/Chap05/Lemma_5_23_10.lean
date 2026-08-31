module

public import Mathlib.Topology.Spectral.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-
Domain-style sampling for products of spectral spaces:
- primary domain: spectral spaces and their owner ingredients `PrespectralSpace`,
  `QuasiSeparatedSpace`, and `QuasiSober`
- owner declarations inspected:
  `SpectralSpace`,
  `PrespectralSpace.isTopologicalBasis`,
  `PrespectralSpace.of_isTopologicalBasis'`,
  `QuasiSeparatedSpace.of_isTopologicalBasis`,
  `IsTopologicalBasis.prod`
- best owner abstraction: the public owner remains `SpectralSpace`, while the product proof is
  assembled from the canonical owner ingredients already built into its structure
- primitive data: compact-open rectangles in the product and the generic-point behavior of
  irreducible closed subsets under the two projections
- derived API: the product `SpectralSpace` instance itself

Layer triage:
- `source-facing`: Lemma 5.23.10, asserting that products of spectral spaces are spectral
- `core/canonical`: `SpectralSpace` together with its ingredient classes
  `PrespectralSpace`, `QuasiSeparatedSpace`, and `QuasiSober`
- `bridge/view`: the rectangle-basis and projection-to-generic-point constructions used to build
  the owner instance
-/

/-- Identify compact-open rectangles with the product basis indexed by compact opens in each
factor. -/
private theorem compactOpenRect_image2_eq :
    Set.image2 (· ×ˢ ·) { U : Set X | IsOpen U ∧ IsCompact U }
        { V : Set Y | IsOpen V ∧ IsCompact V } =
      Set.range
        (fun p : CompactOpens X × CompactOpens Y ↦
          ((p.1 ×ˢ p.2 : CompactOpens (X × Y)) : Set (X × Y))) := by
  have hX :
      (Set.range fun U : CompactOpens X ↦ (U : Set X)) =
        { U : Set X | IsOpen U ∧ IsCompact U } := by
    ext U
    constructor
    · rintro ⟨V, rfl⟩
      exact ⟨V.isOpen, V.isCompact⟩
    · intro hU
      exact ⟨⟨⟨U, hU.2⟩, hU.1⟩, rfl⟩
  have hY :
      (Set.range fun V : CompactOpens Y ↦ (V : Set Y)) =
        { V : Set Y | IsOpen V ∧ IsCompact V } := by
    ext V
    constructor
    · rintro ⟨W, rfl⟩
      exact ⟨W.isOpen, W.isCompact⟩
    · intro hV
      exact ⟨⟨⟨V, hV.2⟩, hV.1⟩, rfl⟩
  simpa [hX, hY] using
    (Set.image2_range
      (fun U V ↦ U ×ˢ V)
      (fun U : CompactOpens X ↦ (U : Set X))
      (fun V : CompactOpens Y ↦ (V : Set Y)))

section Prespectral

variable [PrespectralSpace X] [PrespectralSpace Y]

/-- Compact-open rectangles form a topological basis on the product of prespectral spaces. -/
private theorem compactOpenRect_isTopologicalBasis :
    IsTopologicalBasis
      (Set.range
        (fun p : CompactOpens X × CompactOpens Y ↦
          ((p.1 ×ˢ p.2 : CompactOpens (X × Y)) : Set (X × Y)))) := by
  simpa [compactOpenRect_image2_eq] using
    (show IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U } from
      PrespectralSpace.isTopologicalBasis).prod
      (show IsTopologicalBasis { V : Set Y | IsOpen V ∧ IsCompact V } from
        PrespectralSpace.isTopologicalBasis)

/-- The product of prespectral spaces is prespectral. -/
private instance prespectralSpaceProd : PrespectralSpace (X × Y) :=
  PrespectralSpace.of_isTopologicalBasis'
    compactOpenRect_isTopologicalBasis
    fun p ↦ p.1.isCompact.prod p.2.isCompact

/-- The product of quasi-separated prespectral spaces is quasi-separated. -/
private instance quasiSeparatedSpaceProd [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace (X × Y) :=
  QuasiSeparatedSpace.of_isTopologicalBasis compactOpenRect_isTopologicalBasis fun p q ↦ by
    simpa [Set.prod_inter_prod, Set.inter_comm] using
      (p.1.isCompact.inter_of_isOpen q.1.isCompact p.1.isOpen q.1.isOpen).prod
        (p.2.isCompact.inter_of_isOpen q.2.isCompact p.2.isOpen q.2.isOpen)

end Prespectral

section QuasiSober

variable [QuasiSober X] [QuasiSober Y]

/-- The product of quasi-sober spaces is quasi-sober. -/
private instance quasiSoberProd : QuasiSober (X × Y) where
  sober {S} hS hSclosed := by
    have hSx : IsIrreducible (Prod.fst '' S) := hS.image Prod.fst continuous_fst.continuousOn
    have hSy : IsIrreducible (Prod.snd '' S) := hS.image Prod.snd continuous_snd.continuousOn
    let hx : X := hSx.genericPoint
    let hy : Y := hSy.genericPoint
    have hfst : IsGenericPoint hx (closure (Prod.fst '' S)) :=
      by simpa [hx] using hSx.isGenericPoint_genericPoint_closure
    have hsnd : IsGenericPoint hy (closure (Prod.snd '' S)) :=
      by simpa [hy] using hSy.isGenericPoint_genericPoint_closure
    have hxy_mem : (hx, hy) ∈ S := by
      have hxy_closure : (hx, hy) ∈ closure S := by
        rw [mem_closure_iff]
        intro U hU hxyU
        rcases isOpen_prod_iff.mp hU hx hy hxyU with ⟨U₁, U₂, hU₁, hU₂, hxU₁, hyU₂, hsub⟩
        have hSU₁ : (S ∩ (U₁ ×ˢ (Set.univ : Set Y))).Nonempty := by
          rcases mem_closure_iff.1 hfst.mem U₁ hU₁ hxU₁ with ⟨x, hxU₁, hxS⟩
          rcases hxS with ⟨p, hpS, rfl⟩
          exact ⟨p, ⟨hpS, ⟨hxU₁, Set.mem_univ _⟩⟩⟩
        have hSU₂ : (S ∩ ((Set.univ : Set X) ×ˢ U₂)).Nonempty := by
          rcases mem_closure_iff.1 hsnd.mem U₂ hU₂ hyU₂ with ⟨y, hyU₂, hyS⟩
          rcases hyS with ⟨p, hpS, rfl⟩
          exact ⟨p, ⟨hpS, ⟨Set.mem_univ _, hyU₂⟩⟩⟩
        have hSrect : (S ∩ (U₁ ×ˢ U₂)).Nonempty := by
          convert hS.isPreirreducible (U₁ ×ˢ (Set.univ : Set Y))
            ((Set.univ : Set X) ×ˢ U₂)
            (hU₁.prod isOpen_univ) (isOpen_univ.prod hU₂) hSU₁ hSU₂ using 1
          ext p
          simp [Set.prod_inter_prod, Set.inter_comm]
        rcases hSrect with ⟨p, hpS, hpRect⟩
        exact ⟨p, ⟨hsub hpRect, hpS⟩⟩
      simpa [hSclosed.closure_eq] using hxy_closure
    refine ⟨(hx, hy), ?_⟩
    rw [isGenericPoint_iff_specializes]
    intro p
    constructor
    · intro hp
      have hclosure : closure ({(hx, hy)} : Set (X × Y)) ⊆ S :=
        hSclosed.closure_subset_iff.mpr (by simp [hxy_mem])
      exact hclosure hp.mem_closure
    · intro hp
      exact (hfst.specializes <| subset_closure ⟨p, hp, rfl⟩).prod
        (hsnd.specializes <| subset_closure ⟨p, hp, rfl⟩)

end QuasiSober

section Spectral

variable [SpectralSpace X] [SpectralSpace Y]

-- Proof sketch: the product inherits `T₀` and quasi-compactness from the factors. For
-- quasi-sobriety, an irreducible closed subset of `X × Y` has generic point given by the generic
-- points of the closures of its projections. For the compact-open basis, use rectangles `U × V`
-- with `U` and `V` quasi-compact open in the factors.
/-- Lemma 5.23.10 (Stacks tag `0907`): the product of two spectral spaces is spectral. -/
instance spectralSpace_prod : SpectralSpace (X × Y) where
  toT0Space := inferInstance
  toCompactSpace := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance

end Spectral

end
