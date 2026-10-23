module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Connected.Separation

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology

universe u

/- Domain-style sampling for the constructible topology of spectral spaces:
- owner declarations in mathlib: `constructibleTopology`, `WithConstructibleTopology`,
  `compactSpace_withConstructibleTopology`
- spectral compact-open basis owner: `PrespectralSpace.isTopologicalBasis`
- separation owner API: `TotallySeparatedSpace`, together with the derived instances
  `TotallySeparatedSpace.t2Space` and `TotallySeparatedSpace.totallyDisconnectedSpace`

Layer triage:
- `source-facing`: Lemma 5.23.2 states that the constructible topology on a spectral space is
  compact Hausdorff and totally disconnected
- `core/canonical`: the owner object is `WithConstructibleTopology X`
- `bridge/view`: the explicit `@T2Space X (constructibleTopology X)`,
  `@TotallyDisconnectedSpace X (constructibleTopology X)`, and
  `@CompactSpace X (constructibleTopology X)` statements are the source-facing view of those owner
  instances

Primitive data is just the spectral-space compact-open basis plus mathlib's constructible-topology
owner. Compactness is already owned upstream by mathlib, so this file only adds the missing
clopen/separation layer and then exposes the Stacks-style conjunction as derived API.
-/

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- In a spectral space, every constructible subset is clopen for the constructible topology. -/
theorem isClopen_constructibleTopology_of_isConstructible {s : Set X} (hs : IsConstructible s) :
    @IsClopen X (constructibleTopology X) s := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUretro =>
    refine ⟨?_, hUretro.isCompact.isOpen_constructibleTopology_of_isOpen hUopen⟩
    let s : Set X := Uᶜ
    have hsClosed : IsClosed s := by
      simpa [s] using hUopen.isClosed_compl
    have hsCompact : IsCompact sᶜ := by
      simpa [s] using hUretro.isCompact
    have hUcompl_open : IsOpen[constructibleTopology X] Uᶜ := by
      simpa [s] using hsCompact.isOpen_constructibleTopology_of_isClosed hsClosed
    simpa using @IsOpen.isClosed_compl X (constructibleTopology X) Uᶜ hUcompl_open
  | union s _ t _ hs ht =>
    exact @IsClopen.union X (constructibleTopology X) s t hs ht
  | compl s _ hs =>
    exact @IsClopen.compl X (constructibleTopology X) s hs

/-- If `X` is spectral, then the constructible topology on `X` is totally separated. -/
instance :
    TotallySeparatedSpace (WithConstructibleTopology X) := by
  classical
  have hBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U } :=
    PrespectralSpace.isTopologicalBasis
  refine totallySeparatedSpace_iff_exists_isClopen.2 ?_
  intro x y hxy
  have hxyBasis : ∃ V, V ∈ { U : Set X | IsOpen U ∧ IsCompact U } ∧ ¬ (x ∈ V ↔ y ∈ V) := by
    by_contra hxyBasis
    apply hxy
    apply (TopologicalSpace.IsTopologicalBasis.eq_iff hBasis).2
    intro s hs
    by_contra hxys
    exact hxyBasis ⟨s, hs, hxys⟩
  obtain ⟨V, hV, hxyV⟩ := hxyBasis
  have hVclopen : @IsClopen X (constructibleTopology X) V :=
    isClopen_constructibleTopology_of_isConstructible (hV.2.isConstructible hV.1)
  by_cases hxV : x ∈ V
  · have hyV : y ∉ V := by
      intro hyV
      exact hxyV (by simp [hxV, hyV])
    exact ⟨V, hVclopen, hxV, hyV⟩
  · have hyV : y ∈ V := by
      by_contra hyV
      exact hxyV (by simp [hxV, hyV])
    have hVcompl : @IsClopen X (constructibleTopology X) Vᶜ :=
      @IsClopen.compl X (constructibleTopology X) V hVclopen
    exact ⟨Vᶜ, hVcompl, by simpa using hxV, by simpa using hyV⟩

/-- Lemma 5.23.2 (1): if `X` is spectral, then the constructible topology on `X` is Hausdorff. -/
-- Proof sketch: derive `T2Space` from the already available totally separated instance on
-- `WithConstructibleTopology X`.
theorem constructibleTopology_t2Space_of_spectralSpace :
    @T2Space X (constructibleTopology X) := by
  -- The clopen-separation argument above already gives total separation on the owner type.
  have hT2 : T2Space (WithConstructibleTopology X) := inferInstance
  -- Transport the owner instance back to the explicit constructible topology on `X`.
  simpa [WithConstructibleTopology] using hT2

/-- Lemma 5.23.2 (2): if `X` is spectral, then the constructible topology on `X` is totally
disconnected. -/
-- Proof sketch: use the derived `TotallyDisconnectedSpace` instance coming from the totally
-- separated constructible topology.
theorem constructibleTopology_totallyDisconnectedSpace_of_spectralSpace :
    @TotallyDisconnectedSpace X (constructibleTopology X) := by
  -- Total separation of the owner type immediately yields total disconnectedness.
  have hTotDisc : TotallyDisconnectedSpace (WithConstructibleTopology X) := inferInstance
  -- Rewrite the owner type back to the explicit constructible topology on `X`.
  simpa [WithConstructibleTopology] using hTotDisc

/-- Lemma 5.23.2 (3): if `X` is spectral, then the constructible topology on `X` is
quasi-compact. -/
-- Proof sketch: transport the upstream compactness instance for `WithConstructibleTopology X`
-- back to the constructible topology on `X`.
theorem constructibleTopology_compactSpace_of_spectralSpace :
    @CompactSpace X (constructibleTopology X) := by
  -- Mathlib already owns compactness for the constructible-topology wrapper.
  have hCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
  -- Transport that compactness instance to the explicit constructible topology.
  simpa [WithConstructibleTopology] using hCompact

end
