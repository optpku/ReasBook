module

public import stacks_project.Chap05.Definition_5_10_1
import Mathlib.Order.CompletePartialOrder

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for global versus local topological Krull dimension:
- primary domain: topological Krull dimension on a space and its localization at a point via open
  neighbourhoods;
- inspected owner declarations:
  `topologicalKrullDim`,
  `Order.krullDim_eq_iSup_coheight`,
  `Order.coheight_eq_krullDim_Ici`,
  `subset_closure_inter_of_isPreirreducible_of_isOpen`,
  `TopologicalSpace.IrreducibleCloseds.map`;
- best owner abstraction: the global owner is `topologicalKrullDim X`, with the hard inequality
  proved by passing through the canonical `Order.coheight` of irreducible closed subsets and
  restricting those subsets to open neighbourhoods of a chosen point through the ambient subtype
  map.

Layer triage:
- `source-facing`: `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`;
- `core/canonical`: `topologicalKrullDim`, `Order.krullDim_eq_iSup_coheight`, and
  `Order.coheight_le_krullDim`;
- `bridge/view`: the local owner `topologicalKrullDimAt`, its infimum API from
  `Definition_5_10_1`, and the density statement
  `subset_closure_inter_of_isPreirreducible_of_isOpen`.

Primitive data are only the ambient space and its open neighbourhoods. The local infimum
`topologicalKrullDimAt` already provides the source-facing owner; the restriction argument should
therefore stay inside the canonical poset of irreducible closed subsets rather than introducing a
parallel chain package.
-/

/-- Helper for Lemma 5.10.2: the preimage of an irreducible closed subset along the subtype map of
an open set is irreducible as soon as the open set meets the subset. -/
private theorem restrictOpenIrreducibleClosed_isIrreducible
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    IsIrreducible (Subtype.val ⁻¹' (Y : Set X) : Set U) := by
  -- Convert nonemptiness of the intersection with `U` into nonemptiness of the intersection with
  -- the range of the subtype map, so the standard preimage lemma applies.
  have hRange : Set.range (Subtype.val : U → X) = (U : Set X) := by
    ext x
    simp
  have hYU' : ((Y : Set X) ∩ Set.range (Subtype.val : U → X)).Nonempty := by
    simpa [hRange] using hYU
  simpa using Y.isIrreducible.preimage U.isOpenEmbedding' hYU'

/-- Helper for Lemma 5.10.2: intersecting an irreducible closed subset with an open that meets it
defines an irreducible closed subset of the corresponding open subspace. -/
private noncomputable def restrictOpenIrreducibleClosed
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Y : Set X),
    restrictOpenIrreducibleClosed_isIrreducible Y U hYU,
    Y.isClosed.preimage continuous_subtype_val⟩

/-- Helper for Lemma 5.10.2: the carrier of the restricted irreducible closed subset is the
expected preimage under the subtype map. -/
@[simp] private theorem coe_restrictOpenIrreducibleClosed
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    (restrictOpenIrreducibleClosed Y U hYU : Set U) = Subtype.val ⁻¹' (Y : Set X) :=
  rfl

/-- Helper for Lemma 5.10.2: if an open set meets `Y`, then it meets every irreducible closed set
containing `Y`. -/
private theorem inter_nonempty_of_le
    (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) (hYT : Y ≤ T) :
    ((T : Set X) ∩ (U : Set X)).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

/-- Helper for Lemma 5.10.2: when an irreducible closed subset meets an open, its intersection with
that open is dense in the subset. -/
theorem closure_inter_eq_of_irreducibleClosed_meets_open
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    closure ((Y : Set X) ∩ (U : Set X)) = (Y : Set X) := by
  -- One inclusion uses closedness of `Y`; the other is the standard density lemma for nonempty
  -- opens in a preirreducible subspace.
  apply Subset.antisymm
  · exact closure_minimal inter_subset_left Y.isClosed
  ·
    exact subset_closure_inter_of_isPreirreducible_of_isOpen
      Y.isIrreducible.isPreirreducible U.isOpen hYU

/-- Helper for Lemma 5.10.2: an irreducible closed subset through `x` contributes its coheight to
every open neighbourhood of `x`. -/
private theorem coheight_le_topologicalKrullDim_openNhdsOf_of_mem
    (Y : IrreducibleCloseds X) {x : X} (hx : x ∈ (Y : Set X)) (U : OpenNhdsOf x) :
    Order.coheight Y ≤ topologicalKrullDim U := by
  -- Restrict every irreducible closed superset of `Y` to the neighbourhood `U`; this gives an
  -- injective monotone map on the upper interval above `Y`.
  have hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty := ⟨x, hx, U.2⟩
  let f : Set.Ici Y → IrreducibleCloseds U := fun T ↦
    restrictOpenIrreducibleClosed T.1 U.toOpens (inter_nonempty_of_le Y T.1 U.toOpens hYU T.2)
  have hf_mono : Monotone f := by
    intro A B hAB
    simpa [f, coe_restrictOpenIrreducibleClosed] using Set.preimage_mono hAB
  have hmap :
      ∀ T : Set.Ici Y,
        TopologicalSpace.IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val
          (f T) = T.1 := by
    intro T
    have hRange : Set.range (Subtype.val : U → X) = (U : Set X) := by
      ext z
      simp
    have hImage :
        (Subtype.val : U → X) '' (Subtype.val ⁻¹' ((T.1 : IrreducibleCloseds X) : Set X)) =
          ((T.1 : IrreducibleCloseds X) : Set X) ∩ Set.range (Subtype.val : U → X) := by
      ext z
      simp
    -- Mapping the restriction back to `X` recovers the original irreducible closed set because
    -- the intersection with `U` is dense in that set.
    apply IrreducibleCloseds.ext
    rw [TopologicalSpace.IrreducibleCloseds.coe_map]
    rw [coe_restrictOpenIrreducibleClosed]
    calc
      closure ((Subtype.val : U → X) '' (Subtype.val ⁻¹' ((T.1 : IrreducibleCloseds X) : Set X))) =
          closure ((((T.1 : IrreducibleCloseds X) : Set X) ∩ Set.range (Subtype.val : U → X))) := by
            simp [hImage]
      _ = closure ((((T.1 : IrreducibleCloseds X) : Set X) ∩ (U : Set X))) := by
            rw [hRange]
      _ = ((T.1 : IrreducibleCloseds X) : Set X) := by
            exact closure_inter_eq_of_irreducibleClosed_meets_open T.1 U.toOpens
              (inter_nonempty_of_le Y T.1 U.toOpens hYU T.2)
  have hf_injective : Function.Injective f := by
    intro A B hAB
    -- Applying the ambient map back to `X` shows that equal restrictions come from equal ambient
    -- irreducible closed subsets.
    apply Subtype.ext
    simpa [hmap A, hmap B] using congrArg
      (TopologicalSpace.IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val) hAB
  rw [Order.coheight_eq_krullDim_Ici]
  simpa [topologicalKrullDim] using
    Order.krullDim_le_of_strictMono f (hf_mono.strictMono_of_injective hf_injective)

/-- Helper for Lemma 5.10.2: an irreducible closed subset through `x` contributes its coheight to
the local Krull dimension at `x`. -/
private theorem coheight_le_topologicalKrullDimAt_of_mem
    (Y : IrreducibleCloseds X) {x : X} (hx : x ∈ (Y : Set X)) :
    Order.coheight Y ≤ topologicalKrullDimAt x := by
  -- Bound the local infimum by showing that every neighbourhood of `x` has dimension at least the
  -- coheight of `Y`.
  refine le_iInf fun U ↦ ?_
  exact coheight_le_topologicalKrullDim_openNhdsOf_of_mem Y hx U

-- Proof sketch: the hard inequality chooses a point on an irreducible closed subset witnessing
-- global coheight and restricts the upper interval above that subset to every neighbourhood of the
-- point; the easy inequality evaluates the infimum defining `topologicalKrullDimAt` at `⊤`.
/-- Lemma 5.10.2: the Krull dimension of a topological space is the supremum of the local Krull
dimensions at its points. -/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt
    {X : Type u} [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    -- Route correction: replace the earlier shortcut through the later open-restriction lemma by a
    -- direct restriction argument inside the upper interval above each irreducible closed subset.
    refine iSup_le fun Y ↦ ?_
    obtain ⟨x, hx⟩ := Y.isIrreducible.nonempty
    exact le_iSup_of_le x (coheight_le_topologicalKrullDimAt_of_mem Y hx)
  · refine iSup_le fun x ↦ ?_
    let U : OpenNhdsOf x := ⊤
    have hU : topologicalKrullDim U ≤ topologicalKrullDim X := by
      -- The total space is itself an open neighbourhood of `x`, so the local infimum is bounded
      -- by the global dimension.
      simpa [U] using topologicalKrullDim_subspace_le X (Set.univ : Set X)
    exact (topologicalKrullDimAt_le x U).trans hU
