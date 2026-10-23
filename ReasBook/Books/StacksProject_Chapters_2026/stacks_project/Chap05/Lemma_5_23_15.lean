module

public import Mathlib.Topology.Spectral.Basic
public import stacks_project.Chap05.Lemma_5_8_16
import Mathlib.Order.CompletePartialOrder

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Topology

/-
Domain-style sampling for soberification and spectral transfer:
- primary domain: soberification via `IrreducibleCloseds X`, viewed through the lattice of open
  subsets;
- sampled owner declarations:
  `toIrreducibleCloseds_opensComap_bijective`,
  `TopologicalSpace.Opens.comap`,
  `PrespectralSpace.isBasis_opens`,
  `QuasiSeparatedSpace.inter_isCompact`;
- best owner abstraction: the key owner here is the order isomorphism on opens induced by
  `toIrreducibleCloseds`; compactness, Noetherianity, prespectrality, quasi-separatedness, and
  spectrality of `IrreducibleCloseds X` are all derived API transported across that owner;
- primitive-vs-derived split: the primitive data for this file is only the open-lattice
  equivalence; the various topological typeclass instances are derived from it and should not be
  packaged as separate wrapper data.

Layer triage:
- `source-facing`: the Stacks claims that soberification preserves quasi-compactness, the compact
  open basis, quasi-separatedness, and Noetherianity;
- `core/canonical`: `Opens`, `CompactSpace`, `NoetherianSpace`, `PrespectralSpace`,
  `QuasiSeparatedSpace`, and `SpectralSpace`;
- `bridge/view`: `toIrreducibleCloseds` and the induced order isomorphism on opens.
-/

section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Lemma 5.23.15: compactness of an open subset of the soberification follows from
compactness of its pullback along `toIrreducibleCloseds`. -/
lemma isCompact_of_isCompact_comap_toIrreducibleCloseds
    (V : Opens (IrreducibleCloseds X))
    (hV : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X))) :
    IsCompact (V : Set (IrreducibleCloseds X)) := by
  -- Pull back an arbitrary open cover of `V` to the corresponding open of `X`.
  rw [isCompact_iff_finite_subcover]
  intro ι U hUo hcover
  let f : C(X, IrreducibleCloseds X) := toIrreducibleCloseds
  let Uo : ι → Opens (IrreducibleCloseds X) := fun i ↦ ⟨U i, hUo i⟩
  have hcover_comap :
      ((((Opens.comap f) V : Opens X) : Set X)) ⊆
        ⋃ i, ((((Opens.comap f) (Uo i) : Opens X) : Set X)) := by
    intro x hx
    have hxV : f x ∈ (V : Set (IrreducibleCloseds X)) := by
      simpa [Opens.mem_comap] using hx
    rcases Set.mem_iUnion.1 (hcover hxV) with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, by simpa [Uo, Opens.mem_comap] using hxi⟩
  obtain ⟨t, ht⟩ :=
    hV.elim_finite_subcover
      (fun i ↦ ((((Opens.comap f) (Uo i) : Opens X) : Set X)))
      (fun i ↦ ((Opens.comap f) (Uo i)).isOpen)
      hcover_comap
  let W : Opens (IrreducibleCloseds X) := ⨆ i : {i // i ∈ t}, Uo i.1
  have hcomap_le' :
      (Opens.comap f) V ≤ ⨆ i : {i // i ∈ t}, (Opens.comap f) (Uo i.1) := by
    -- Reindex the finite subcover by the subtype associated to the chosen `Finset`.
    intro x hx
    rcases Set.mem_iUnion₂.1 (ht hx) with ⟨i, hi, hxi⟩
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  have hcomapW :
      (Opens.comap f) W = ⨆ i : {i // i ∈ t}, (Opens.comap f) (Uo i.1) := by
    ext x
    simp [W]
  have hcomap_le : (Opens.comap f) V ≤ (Opens.comap f) W := by
    rw [hcomapW]
    exact hcomap_le'
  have hV_le_W : V ≤ W := by
    -- Injectivity of `Opens.comap` reflects the inclusion after packaging it as an inf-equality.
    have hinj := (toIrreducibleCloseds_opensComap_bijective (X := X)).1
    apply inf_eq_left.mp
    apply hinj
    calc
      (Opens.comap f) (V ⊓ W) = (Opens.comap f) V ⊓ (Opens.comap f) W := by simp
      _ = (Opens.comap f) V := inf_eq_left.mpr hcomap_le
  -- Push the finite source-side cover back to the original cover of `V`.
  refine ⟨t, ?_⟩
  intro Z hZ
  have hZW : Z ∈ W := hV_le_W hZ
  rcases Opens.mem_iSup.1 hZW with ⟨i, hZi⟩
  exact Set.mem_iUnion₂.2 ⟨i.1, i.2, hZi⟩

/-- Helper for Lemma 5.23.15: a compact open of `X` yields a compact basic open on the
soberification. -/
lemma basicOpen_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsCompact (IrreducibleCloseds.basicOpen U) := by
  -- Rewrite the pulled-back basic open as `U`, then invoke compactness transfer.
  let V : Opens (IrreducibleCloseds X) :=
    ⟨IrreducibleCloseds.basicOpen U, (isOpen_iff_exists_basicOpen).2 ⟨U, rfl⟩⟩
  have hpre :
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X)) = U := by
    simpa [V, Opens.coe_comap] using preimage_basicOpen_toIrreducibleClosedsFun (X := X) U
  have hcomap : IsCompact ((((Opens.comap
      (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) : Set X)) := by
    rw [hpre]
    exact hU
  simpa [V] using isCompact_of_isCompact_comap_toIrreducibleCloseds (X := X) V hcomap

/-- Helper for Lemma 5.23.15: compact basic opens coming from `CompactOpens X` form a
topological basis on the soberification. -/
lemma isTopologicalBasis_compact_basicOpen [PrespectralSpace X] :
    IsTopologicalBasis
      (Set.range fun U : CompactOpens X ↦ IrreducibleCloseds.basicOpen U.toOpens) := by
  -- Transport the compact-open neighborhood basis from `X` through `basicOpen`.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, rfl⟩
    exact (isOpen_iff_exists_basicOpen).2 ⟨U.toOpens, rfl⟩
  · intro Z s hZ hs
    obtain ⟨U, rfl⟩ := (isOpen_iff_exists_basicOpen).1 hs
    rcases hZ with ⟨x, hxZ, hxU⟩
    obtain ⟨K, hK, hxK, hKU⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxU U.isOpen
    let Kc : CompactOpens X := ⟨⟨K, hK.2⟩, hK.1⟩
    refine ⟨IrreducibleCloseds.basicOpen Kc.toOpens, ⟨Kc, rfl⟩, ?_, ?_⟩
    · exact ⟨x, hxZ, hxK⟩
    · exact IrreducibleCloseds.basicOpen_mono hKU

/-- Helper for Lemma 5.23.15: intersections of compact basic opens on the soberification are
compact once `X` is quasi-separated. -/
lemma compact_inter_compact_basicOpen [QuasiSeparatedSpace X] (U V : CompactOpens X) :
    IsCompact (IrreducibleCloseds.basicOpen U.toOpens ∩ IrreducibleCloseds.basicOpen V.toOpens) := by
  -- Identify the target intersection with the basic open of the source-side compact
  -- intersection.
  have hUV :
      IsCompact (((U.toOpens ⊓ V.toOpens : Opens X) : Set X)) := by
    exact
      QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
        U.toOpens.isOpen U.isCompact V.toOpens.isOpen V.isCompact
  simpa [IrreducibleCloseds.basicOpen_inf] using
    basicOpen_isCompact (X := X) (U := U.toOpens ⊓ V.toOpens) hUV

-- Proof sketch: the soberification map induces a bijection on opens. Since this bijection commutes
-- with arbitrary unions, quasi-compactness of the soberification space transfers across it, so
-- compactness of `X` gives compactness of `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (1): if `X` is quasi-compact, then the soberification space
`IrreducibleCloseds X` is quasi-compact. In Lean this is the canonical `CompactSpace`
instance. -/
instance irreducibleCloseds_compactSpace [CompactSpace X] :
    CompactSpace (IrreducibleCloseds X) := by
  -- Apply compactness transfer to the universal open `⊤`.
  apply (isCompact_univ_iff).1
  have htop : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) ⊤ : Opens X) :
        Set X)) := by
    simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set X))
  simpa using
    isCompact_of_isCompact_comap_toIrreducibleCloseds
      (X := X) (V := (⊤ : Opens (IrreducibleCloseds X))) htop

-- Proof sketch: the open-bijection property of the soberification map transfers compact opens and
-- their pairwise intersections from `X` to `IrreducibleCloseds X`. Together with the quasi-sober
-- and `T₀` structure from Lemma 5.8.16 and compactness from part (1), this yields a spectral
-- structure on `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (2): if `X` is quasi-compact, has a basis of quasi-compact opens, and the
intersection of two quasi-compact opens is quasi-compact, then `IrreducibleCloseds X` is
spectral. The textbook hypotheses are expressed canonically by
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. -/
instance irreducibleCloseds_spectralSpace [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] : SpectralSpace (IrreducibleCloseds X) := by
  -- Build the prespectral and quasi-separated structures from compact basic opens.
  let hPrespectral : PrespectralSpace (IrreducibleCloseds X) :=
    PrespectralSpace.of_isTopologicalBasis
      (isTopologicalBasis_compact_basicOpen (X := X))
      (by
        rintro _ ⟨U, rfl⟩
        exact basicOpen_isCompact (X := X) U.toOpens U.isCompact)
  let hQuasiSeparated : QuasiSeparatedSpace (IrreducibleCloseds X) :=
    QuasiSeparatedSpace.of_isTopologicalBasis
      (isTopologicalBasis_compact_basicOpen (X := X))
      (compact_inter_compact_basicOpen (X := X))
  -- The soberification already carries `T₀` and quasi-sober structures from Lemma 5.8.16.
  exact
    @SpectralSpace.mk (IrreducibleCloseds X) inferInstance inferInstance inferInstance inferInstance
      hQuasiSeparated hPrespectral

-- Proof sketch: the soberification map gives a bijection on opens, so the ascending chain
-- condition on open subsets transfers from `X` to `IrreducibleCloseds X`.
/-- The soberification space `IrreducibleCloseds X` of a Noetherian space is again Noetherian. -/
instance irreducibleCloseds_noetherianSpace [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) := by
  -- Noetherianity is equivalent to compactness of every open, which transfers across `c⁻¹`.
  rw [TopologicalSpace.noetherianSpace_iff_opens]
  intro V
  have hV : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X)) := NoetherianSpace.isCompact _
  exact isCompact_of_isCompact_comap_toIrreducibleCloseds (X := X) V hV

-- Proof sketch: combine the transferred Noetherianity of `IrreducibleCloseds X` with the
-- quasi-sober and `T₀` properties from Lemma 5.8.16. Mathlib's Noetherian-space instances provide
-- compactness, a basis of compact opens, and quasi-separatedness, so `IrreducibleCloseds X` is
-- spectral as well.
/-- Lemma 5.23.15 (3): if `X` is Noetherian, then `IrreducibleCloseds X` is a Noetherian
spectral space. -/
theorem irreducibleCloseds_noetherian_and_spectral [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) ∧ SpectralSpace (IrreducibleCloseds X) := by
  exact ⟨inferInstance, inferInstance⟩

end
