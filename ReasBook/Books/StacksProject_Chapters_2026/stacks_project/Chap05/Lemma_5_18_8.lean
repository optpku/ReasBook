module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.JacobsonSpace
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_18_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

universe u

section

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

local macro "X₀" : term => `(closedPoints X)

/-
Domain-style sampling for constructible traces on the closed-point subspace of a Jacobson space:
- primary domain: constructible subsets, retrocompact opens, and closed-point traces in Jacobson
  spaces;
- sampled owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn`;
- best owner abstractions: the ambient Jacobson owner `JacobsonSpace X` and the constructible-set
  owner predicate `Topology.IsConstructible`; the closed-point trace itself is the canonical bridge
  `X₀ ↓∩ E`.

Layer triage:
- `source-facing`: the constructible closed-point trace correspondence of Lemma 5.18.8;
- `core/canonical`: `JacobsonSpace X` and `IsConstructible`;
- `bridge/view`: the subtype trace `X₀ ↓∩ E` together with the finite-union bridge from
  `Lemma_5_18_7`.

Primitive data is only the ambient Jacobson structure and the owner predicate `IsConstructible`.
The finite-union-of-locally-closed decomposition and the closed-point trace bijection on those
finite unions are derived API, so this file should phrase its public statements through the
canonical trace notation `X₀ ↓∩ E` and reuse the upstream owner-facing bridge rather than spelling
out a parallel subtype-preimage surface.
-/

-- Proof sketch: combine `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn` with
-- `Topology.IsConstructible.isFiniteUnionOfLocallyClosed` and the canonical generator description
-- of constructible subsets by open retrocompact subsets. The trace surface should be stated using
-- the canonical subtype-trace notation `X₀ ↓∩ E`.
/-- Helper for Lemma 5.18.8: an open subset containing all closed points of a Jacobson space is
the whole space. -/
private lemma eq_univ_of_isOpen_of_closedPoints_subset {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {U : Set Y} (hU : IsOpen U) (hclosed : closedPoints Y ⊆ U) :
    U = Set.univ := by
  -- The Jacobson property forces the closed complement to be empty once it misses all closed
  -- points.
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_contra hx
  have hclosure : closure (Uᶜ ∩ closedPoints Y) = Uᶜ :=
    closure_inter_closedPoints hU.isClosed_compl
  have htrace_empty : Uᶜ ∩ closedPoints Y = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hy.1 (hclosed hy.2)
  have hx' : x ∈ closure (Uᶜ ∩ closedPoints Y) := by
    simpa [hclosure] using hx
  simpa [htrace_empty] using hx'

/-- Helper for Lemma 5.18.8: compactness of a Jacobson space is detected on its closed points. -/
private lemma isCompact_univ_iff_isCompact_closedPoints {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] :
    IsCompact (Set.univ : Set Y) ↔ IsCompact (closedPoints Y) := by
  rw [isCompact_iff_finite_subcover, isCompact_iff_finite_subcover]
  constructor
  · intro hcompact ι V hVopen hcover
    -- Upgrade an open cover of the closed points to an open cover of the whole Jacobson space.
    have hUnionOpen : IsOpen (⋃ i, V i) := isOpen_iUnion hVopen
    have hUnionEq : (⋃ i, V i) = (Set.univ : Set Y) :=
      eq_univ_of_isOpen_of_closedPoints_subset hUnionOpen <| by
        simpa using hcover
    obtain ⟨t, ht⟩ := hcompact V hVopen <| by simpa [hUnionEq]
    exact ⟨t, Set.Subset.trans (by simp) ht⟩
  · intro hcompact ι V hVopen hcover
    -- A finite subcover of the closed points already covers the whole space by the same argument.
    have hcover_closed : closedPoints Y ⊆ ⋃ i, V i :=
      Set.Subset.trans (by simp) hcover
    obtain ⟨t, ht⟩ := hcompact V hVopen hcover_closed
    have hFiniteOpen : IsOpen (⋃ i ∈ t, V i) := isOpen_biUnion fun i _ ↦ hVopen i
    have hFiniteEq : (⋃ i ∈ t, V i) = (Set.univ : Set Y) :=
      eq_univ_of_isOpen_of_closedPoints_subset hFiniteOpen ht
    exact ⟨t, by simpa [hFiniteEq]⟩

/-- Helper for Lemma 5.18.8: for an open subset, compactness is equivalent to compactness of its
closed-point trace. -/
private lemma isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen {U : Set X}
    (hU : IsOpen U) :
    IsCompact U ↔ IsCompact (X₀ ↓∩ U) := by
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  have hClosedPointsImage : IsCompact (closedPoints U) ↔ IsCompact (X₀ ∩ U : Set X) := by
    rw [Subtype.isCompact_iff]
    have hpre : ((↑) : U → X) ⁻¹' X₀ = closedPoints U :=
      hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have himage : ((↑) '' (closedPoints U) : Set X) = X₀ ∩ U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ ((↑) : U → X) ⁻¹' X₀ := by
          rw [hpre]
          exact hy
        exact ⟨hy', y.2⟩
      · intro hx
        have hx' : (⟨x, hx.2⟩ : U) ∈ closedPoints U := by
          rw [← hpre]
          exact hx.1
        exact ⟨⟨x, hx.2⟩, hx', rfl⟩
    simpa [himage, Set.inter_comm]
  have hTraceImage : IsCompact (X₀ ↓∩ U) ↔ IsCompact (X₀ ∩ U : Set X) := by
    rw [Subtype.isCompact_iff]
    have himage : ((↑) '' (X₀ ↓∩ U) : Set X) = X₀ ∩ U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    simpa [himage]
  -- Move to the open subspace `U`, compare compactness there, and transport both sides back to
  -- the ambient space.
  calc
    IsCompact U ↔ IsCompact (Set.univ : Set U) := by rw [isCompact_iff_isCompact_univ]
    _ ↔ IsCompact (closedPoints U) := isCompact_univ_iff_isCompact_closedPoints
    _ ↔ IsCompact (X₀ ∩ U : Set X) := hClosedPointsImage
    _ ↔ IsCompact (X₀ ↓∩ U) := hTraceImage.symm

/-- Helper for Lemma 5.18.8: tracing an open subset to the closed-point subspace preserves and
reflects retrocompactness. -/
private lemma isRetrocompact_trace_iff_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (X₀ ↓∩ U) := by
  constructor
  · intro hUretro
    intro V hVcompact hVopen
    rcases isOpen_induced_iff.mp hVopen with ⟨W, hWopen, hWtrace⟩
    -- Lift the compact open subset of `X₀` to a compact open subset of `X`.
    have hWtraceCompact : IsCompact (X₀ ↓∩ W) := by
      simpa [hWtrace] using hVcompact
    have hWcompact : IsCompact W :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hWopen).2 hWtraceCompact
    have hUWcompact : IsCompact (U ∩ W) := hUretro hWcompact hWopen
    have hUWopen : IsOpen (U ∩ W) := hU.inter hWopen
    have hTraceCompact : IsCompact (X₀ ↓∩ (U ∩ W)) :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hUWopen).1 hUWcompact
    -- Rewrite the trace through intersections inside the closed-point subtype.
    simpa [hWtrace, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hTraceCompact
  · intro htrace
    intro V hVcompact hVopen
    -- Test retrocompactness on a compact open `V` by passing to the trace on `X₀`.
    have hTraceVcompact : IsCompact (closedPoints X ↓∩ V) :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hVopen).1 hVcompact
    have hTraceVopen : IsOpen (closedPoints X ↓∩ V) := hVopen.preimage continuous_subtype_val
    have hTraceUVcompact : IsCompact ((X₀ ↓∩ U) ∩ (closedPoints X ↓∩ V)) :=
      htrace hTraceVcompact hTraceVopen
    have hUVopen : IsOpen (U ∩ V) := hU.inter hVopen
    have hTraceCompact : IsCompact (X₀ ↓∩ (U ∩ V)) := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hTraceUVcompact
    exact (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hUVopen).2 hTraceCompact

/-- Helper for Lemma 5.18.8: every open retrocompact subset of the closed-point subspace lifts to
an open retrocompact subset of the ambient Jacobson space. -/
private lemma trace_open_retrocompact_lift {V : Set X₀}
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V) :
    ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧ V = X₀ ↓∩ U := by
  rcases isOpen_induced_iff.mp hVopen with ⟨U, hUopen, hUtrace⟩
  have hTraceRetro : IsRetrocompact (X₀ ↓∩ U) := by
    simpa [hUtrace] using hVretro
  have hUretro : IsRetrocompact U := (isRetrocompact_trace_iff_of_isOpen hUopen).2 hTraceRetro
  exact ⟨U, hUopen, hUretro, hUtrace.symm⟩

/-- Lemma 5.18.8: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijective, inclusion-preserving correspondence between constructible subsets of `X` and
constructible subsets of `X₀`. -/
theorem isConstructible_preimage_closedPoints_bijOn :
    Set.BijOn
      (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set X₀ | IsConstructible F} := by
  -- Route correction: surjectivity is proved by constructible induction on open retrocompact
  -- generators, not by the earlier false global `iff` route.
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    -- Constructible subsets stay constructible after tracing to the closed-point subtype.
    induction hE using IsConstructible.empty_union_induction with
    | open_retrocompact U hUopen hUretro =>
        exact ((isRetrocompact_trace_iff_of_isOpen hUopen).1 hUretro).isConstructible
          (hUopen.preimage continuous_subtype_val)
    | union s hs t ht hs' ht' =>
        simpa using hs'.union ht'
    | compl s hs hs' =>
        simpa using hs'.compl
  · intro E hE E' hE' htrace
    -- Reduce injectivity to the finite-union correspondence from Lemma 5.18.7.
    have hsubset : E ⊆ E' :=
      (finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
        hE.isFiniteUnionOfLocallyClosed hE'.isFiniteUnionOfLocallyClosed).1 <| by
          simpa [htrace]
    have hsubset' : E' ⊆ E :=
      (finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
        hE'.isFiniteUnionOfLocallyClosed hE.isFiniteUnionOfLocallyClosed).1 <| by
          simpa [htrace]
    exact Set.Subset.antisymm hsubset hsubset'
  · intro F hF
    -- Lift constructible subsets of `X₀` by the same generator induction.
    induction hF using IsConstructible.empty_union_induction with
    | open_retrocompact V hVopen hVretro =>
        rcases trace_open_retrocompact_lift hVopen hVretro with ⟨U, hUopen, hUretro, hUtrace⟩
        exact ⟨U, hUretro.isConstructible hUopen, hUtrace.symm⟩
    | union s hs t ht hs' ht' =>
        rcases hs' with ⟨E, hE, hEtrace⟩
        rcases ht' with ⟨E', hE', hEtrace'⟩
        refine ⟨E ∪ E', hE.union hE', ?_⟩
        ext x
        simp [hEtrace, hEtrace']
    | compl s hs hs' =>
        rcases hs' with ⟨E, hE, hEtrace⟩
        refine ⟨Eᶜ, hE.compl, ?_⟩
        ext x
        simp [hEtrace]

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the constructible bijection theorem to `E \ E'`, using that constructible
-- subsets are closed under Boolean operations.
/-- The constructible closed-point trace correspondence reflects and preserves inclusion. -/
theorem isConstructible_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := by
  -- Use the finite-union reflection theorem after converting constructible sets to that API.
  exact finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
    hE.isFiniteUnionOfLocallyClosed hE'.isFiniteUnionOfLocallyClosed

-- Proof sketch: the forward implication is the `MapsTo` direction of the constructible
-- closed-point trace bijection above. For the converse, use its surjectivity.
/-- A constructible subset of a Jacobson space has constructible trace on the closed-point
subspace. The converse requires restricting to traces that actually come from constructible
ambient subsets; it is supplied by the bijection theorem above, not by an arbitrary fixed ambient
subset with the same closed-point trace. -/
theorem isConstructible_preimage_closedPoints_subtypeVal {E : Set X} (hE : IsConstructible E) :
    IsConstructible (X₀ ↓∩ E) := by
  -- This is exactly the `MapsTo` part of the bijection.
  exact isConstructible_preimage_closedPoints_bijOn.mapsTo hE

-- Proof sketch: for an open subset `U`, constructibility is equivalent to retrocompactness, so the
-- previous constructible closed-point trace equivalence upgrades directly to the open
-- retrocompactness statement.
/-- Tracing an open subset to the closed-point subspace preserves and reflects retrocompactness in
a Jacobson space. -/
theorem isRetrocompact_iff_preimage_closedPoints_subtypeVal_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (X₀ ↓∩ U) := by
  -- Reuse the compactness bridge on open subspaces.
  exact isRetrocompact_trace_iff_of_isOpen hU

end
