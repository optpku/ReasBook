module

public import Mathlib.Topology.Sets.OpenCover
public import stacks_project.Chap05.Definition_5_11_4
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocallyClosed
import stacks_project.Chap05.Lemma_5_11_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Order
open TopologicalSpace.IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity locality:
- chapter owner: `CatenarySpace X` from `Definition_5_11_4`
- same-domain chapter companion: `catenarySpace_iff`
- mathlib locality pattern for open subspaces: `IsLocallyClosed.locallyCompactSpace`
- mathlib owner-level open-cover locality patterns:
  `TopologicalSpace.IsOpenCover.jacobsonSpace_iff` and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`

Layer triage:
- `source-facing`: the existential open-cover statement `Lemma 5.11.5`
- `core/canonical`: the owner class `CatenarySpace`
- `bridge/view`: restriction to an open subspace and locality on a fixed open cover

Primitive data belongs to `CatenarySpace`; the restriction and open-cover statements are derived
API for that owner. The locally closed restriction theorem is a reusable bridge/view companion for
the source-facing “moreover” clause, while the public surface keeps the owner-level fixed-cover
theorem and the source-facing existential restatement.
-/

/-- Helper for Lemma 5.11.5: if an open set meets a smaller irreducible closed subset, then it
also meets every larger irreducible closed subset. -/
private theorem inter_nonempty_of_le (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) (hYT : Y ≤ T) :
    ((T : Set X) ∩ U).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

/-- Helper for Lemma 5.11.5: mapping a restricted irreducible closed subset back to the ambient
space recovers the original subset. -/
@[simp] private theorem map_restrictOpen_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val
      (Y.restrictOpen U hYU) = Y := by
  -- The intersection with the open is dense in the irreducible closed set, so taking closure after
  -- mapping back to the ambient space returns the original set.
  apply IrreducibleCloseds.ext
  rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_restrictOpen]
  calc
    closure ((Subtype.val : U → X) '' (Subtype.val ⁻¹' (Y : Set X))) =
        closure (((Y : Set X) ∩ Set.range (Subtype.val : U → X))) := by
          congr 1
          ext x
          simp
    _ = closure ((Y : Set X) ∩ U) := by
          congr 1
          ext x
          simp
    _ = (Y : Set X) := by
          apply Subset.antisymm
          · exact closure_minimal inter_subset_left Y.isClosed
          · exact subset_closure_inter_of_isPreirreducible_of_isOpen
              Y.isIrreducible.isPreirreducible U.isOpen hYU

/-- Helper for Lemma 5.11.5: restricting the ambient image of an irreducible closed subset of an
open subspace gives back the original subset. -/
@[simp] private theorem restrictOpen_map_eq (U : Opens X) (Y : IrreducibleCloseds U)
    (hYU : (((IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Y :
      IrreducibleCloseds X) : Set X) ∩ U).Nonempty) :
    (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Y).restrictOpen U hYU = Y := by
  -- Route correction: instead of unfolding the subtype twice, use the embedding formula
  -- `closure_eq_preimage_closure_image` for the open embedding `Subtype.val : U → X`.
  have hEmbedding := U.isOpenEmbedding'.isEmbedding
  apply IrreducibleCloseds.ext
  ext x
  change x ∈
      Subtype.val ⁻¹'
        closure ((Subtype.val : U → X) '' ((Y : IrreducibleCloseds U) : Set U)) ↔
    x ∈ ((Y : IrreducibleCloseds U) : Set U)
  rw [← hEmbedding.closure_eq_preimage_closure_image (((Y : IrreducibleCloseds U) : Set U))]
  simp [Y.isClosed.closure_eq]

/-- Helper for Lemma 5.11.5: an interval of irreducible closed subsets in an open subspace is
order-isomorphic to the corresponding interval of their ambient closures. -/
private noncomputable def open_subspace_interval_orderIso (U : Opens X)
    {S S' : IrreducibleCloseds U} (_hSS' : S ≤ S') :
    Set.Icc S S' ≃o
      Set.Icc
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') := by
  classical
  let x : U := Classical.choose S.isIrreducible.nonempty
  have hx : x ∈ (S : Set U) := Classical.choose_spec S.isIrreducible.nonempty
  let hSU :
      (((IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S :
        IrreducibleCloseds X) : Set X) ∩ U).Nonempty := by
    refine ⟨x, ?_, x.2⟩
    rw [IrreducibleCloseds.coe_map]
    exact subset_closure ⟨x, hx, rfl⟩
  let e :
      Set.Icc S S' ≃
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') :=
    { toFun := fun Z : Set.Icc S S' ↦
      show
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') from
      ⟨IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1,
        IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1,
        IrreducibleCloseds.map_mono continuous_subtype_val Z.2.2⟩
      invFun := fun T :
          Set.Icc
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') ↦
      show Set.Icc S S' from
      ⟨T.1.restrictOpen U (inter_nonempty_of_le
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) T.1 U hSU T.2.1),
        by
          intro x hx
          change (x : X) ∈ (T.1 : Set X)
          exact T.2.1 (by
            show (x : X) ∈
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S : Set X)
            rw [IrreducibleCloseds.coe_map]
            exact subset_closure ⟨x, hx, rfl⟩),
        by
          intro x hx
          have hx' : (x : X) ∈ (T.1 : Set X) := by
            simpa [IrreducibleCloseds.coe_restrictOpen] using hx
          have hx'' :
              x ∈
                Subtype.val ⁻¹'
                  closure ((Subtype.val : U → X) '' ((S' : IrreducibleCloseds U) : Set U)) := by
            simpa [IrreducibleCloseds.coe_map] using T.2.2 hx'
          rw [← U.isOpenEmbedding'.isEmbedding.closure_eq_preimage_closure_image
            (((S' : IrreducibleCloseds U) : Set U))] at hx''
          simpa [S'.isClosed.closure_eq] using hx''⟩
      left_inv := by
        intro Z
        apply Subtype.ext
        simpa [hSU] using restrictOpen_map_eq U Z.1
          (inter_nonempty_of_le
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1) U hSU
            (IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1))
      right_inv := by
        intro T
        apply Subtype.ext
        simpa using map_restrictOpen_eq T.1 U
          (inter_nonempty_of_le
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) T.1 U hSU T.2.1) }
  exact e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((A.1.restrictOpen U
            (inter_nonempty_of_le
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) A.1 U hSU
              A.2.1) : Set U) ⊆
          (B.1.restrictOpen U
            (inter_nonempty_of_le
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) B.1 U hSU
              B.2.1) : Set U))
      intro x hx
      simpa [IrreducibleCloseds.coe_restrictOpen] using hAB
        (by simpa [IrreducibleCloseds.coe_restrictOpen] using hx))

/-- Helper for Lemma 5.11.5: relative codimension is unchanged when passing between an interval in
an open subspace and the corresponding interval of ambient closures. -/
private theorem codimBetween_open_eq (U : Opens X) {S S' : IrreducibleCloseds U} (hSS' : S ≤ S') :
    codimBetween S S' hSS' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS') := by
  -- Compare both codimensions through the Krull dimensions of the corresponding intervals.
  apply WithBot.coe_injective
  calc
    codimBetween S S' hSS' = krullDim (Set.Icc S S') :=
      codimBetween_eq_krullDim hSS'
    _ =
        krullDim
          (Set.Icc
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')) :=
      Order.krullDim_eq_of_orderIso (open_subspace_interval_orderIso U hSS')
    _ =
        codimBetween
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
          (IrreducibleCloseds.map_mono continuous_subtype_val hSS') :=
      (codimBetween_eq_krullDim (IrreducibleCloseds.map_mono continuous_subtype_val hSS')).symm

/-- Helper for Lemma 5.11.5: open subspaces of catenary spaces are catenary. -/
private theorem catenarySpace_opens [CatenarySpace X] (U : Opens X) : CatenarySpace U := by
  refine ⟨?_, ?_⟩
  · intro S S' hSS'
    -- Transport the interval to the ambient space and reuse the ambient finiteness statement.
    have hfinite :
        codimBetween
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
            (IrreducibleCloseds.map_mono continuous_subtype_val hSS') < ⊤ :=
      CatenarySpace.finite_codimBetween
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS')
    simpa [codimBetween_open_eq U hSS'] using hfinite
  · intro S S' hSS' s hs
    -- Send a maximal chain in the local interval to the ambient interval, apply catenarity there,
    -- and then rewrite the codimension back through the interval order isomorphism.
    let e := open_subspace_interval_orderIso U hSS'
    have hsImage : IsMaxChain (· ≤ ·) (e '' s) := IsMaxChain.image e hs
    have hlen :
        (e '' s).encard =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
                (IrreducibleCloseds.map_mono continuous_subtype_val hSS')) +
            1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS') (e '' s) hsImage
    calc
      s.encard = (e '' s).encard := by rw [e.injective.encard_image]
      _ =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
                (IrreducibleCloseds.map_mono continuous_subtype_val hSS')) +
            1 := hlen
      _ = ENat.toNat (codimBetween S S' hSS') + 1 := by
          rw [codimBetween_open_eq U hSS']

/-- Helper for Lemma 5.11.5: for a closed subtype, mapping an irreducible closed subset to the
ambient space is just its set-theoretic image. -/
private theorem map_subtype_val_eq_image_of_isClosed {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) =
      (Subtype.val : S → X) '' (T : Set S) := by
  -- The image of a closed subset of a closed subtype is closed in the ambient space, so the
  -- closure built into `IrreducibleCloseds.map` does not enlarge the set.
  rw [IrreducibleCloseds.coe_map, closure_eq_iff_isClosed]
  exact hS.isClosedMap_subtype_val _ T.isClosed

/-- Helper for Lemma 5.11.5: an ambient irreducible closed subset contained in a closed subtype
pulls back to an irreducible closed subset of that subtype. -/
private noncomputable def preimage_irreducibleClosed_of_subset {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds X) (hTS : (T : Set X) ⊆ S) : IrreducibleCloseds S := by
  refine ⟨Subtype.val ⁻¹' (T : Set X), ?_, T.isClosed.preimage continuous_subtype_val⟩
  -- The pullback is homeomorphic to `T` because `T` already lies in the range of the subtype map.
  let e : (Subtype.val ⁻¹' (T : Set X) : Set S) ≃ₜ (T : Set X) :=
    hS.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphOfSubsetRange fun x hx ↦
      ⟨⟨x, hTS hx⟩, rfl⟩
  exact (isIrreducible_iff_irreducibleSpace).2 <|
    (e.irreducibleSpace_iff).2 (Subtype.irreducibleSpace T.isIrreducible)

/-- Helper for Lemma 5.11.5: the ambient image of an irreducible closed subset of a closed
subspace still lies inside that closed subspace. -/
private theorem map_subtype_val_subset_of_isClosed {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) ⊆ S := by
  -- After rewriting the mapped subset as an image, membership is immediate from the subtype data.
  rw [map_subtype_val_eq_image_of_isClosed hS T]
  rintro x ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 5.11.5: an interval of irreducible closed subsets in a closed subspace is
order-isomorphic to the corresponding ambient interval. -/
private noncomputable def closed_subspace_interval_order_iso {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (_hTT' : T ≤ T') :
    Set.Icc T T' ≃o
      Set.Icc
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') := by
  classical
  let e :
      Set.Icc T T' ≃
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') :=
    { toFun := fun Z ↦
        -- Map each irreducible closed subset of the subtype to its ambient image.
        ⟨IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.2⟩
      invFun := fun Z ↦
        -- Pull back ambient subsets using that the upper endpoint already lies in `S`.
        let ZS :
            IrreducibleCloseds S :=
          preimage_irreducibleClosed_of_subset hS Z.1
            (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T'))
        ⟨ZS,
          by
            intro x hx
            change (x : X) ∈ (Z.1 : Set X)
            have hxT :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
                    Set X) := by
              rw [map_subtype_val_eq_image_of_isClosed hS T]
              exact ⟨x, hx, rfl⟩
            exact Z.2.1 hxT,
          by
            intro x hx
            have hxZ : (x : X) ∈ (Z.1 : Set X) := by
              simpa using hx
            have hxT' :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T' :
                    Set X) := Z.2.2 hxZ
            rw [map_subtype_val_eq_image_of_isClosed hS T'] at hxT'
            rcases hxT' with ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            simpa [hyx'] using hy⟩
      left_inv := by
        intro Z
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        -- Pulling back the ambient image along the injective subtype map recovers the same set.
        change
          (x : X) ∈
              (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1 : Set X) ↔
            x ∈ (Z.1 : Set S)
        rw [map_subtype_val_eq_image_of_isClosed hS Z.1]
        simp
      right_inv := by
        intro Z
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        -- The pulled-back set maps back to `Z` because every point of `Z` already lies in `S`.
        rw [map_subtype_val_eq_image_of_isClosed hS
          (preimage_irreducibleClosed_of_subset hS Z.1
            (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T')))]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T') hx⟩, ?_, rfl⟩
          exact hx }
  exact e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((preimage_irreducibleClosed_of_subset hS A.1
            (Set.Subset.trans A.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S) ⊆
          (preimage_irreducibleClosed_of_subset hS B.1
            (Set.Subset.trans B.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S))
      intro x hx
      exact hAB (by simpa using hx))

/-- Helper for Lemma 5.11.5: relative codimension is unchanged when passing between a closed
subspace interval and the corresponding ambient interval. -/
private theorem codimBetween_closed_eq {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') := by
  -- Compare both codimensions through the Krull dimensions of the order-isomorphic intervals.
  apply WithBot.coe_injective
  calc
    codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
      codimBetween_eq_krullDim hTT'
    _ =
        krullDim
          (Set.Icc
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')) :=
      Order.krullDim_eq_of_orderIso (closed_subspace_interval_order_iso hS hTT')
    _ =
        codimBetween
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
          (IrreducibleCloseds.map_mono continuous_subtype_val hTT') :=
      (codimBetween_eq_krullDim (IrreducibleCloseds.map_mono continuous_subtype_val hTT')).symm

/-- Helper for Lemma 5.11.5: closed subspaces of catenary spaces are catenary. -/
theorem IsClosed.catenarySpace_subtype [CatenarySpace X] {S : Set X}
    (hS : IsClosed S) : CatenarySpace S := by
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    -- Transport finite codimension to the ambient interval inside `X`.
    have hfinite :
        codimBetween
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
            (IrreducibleCloseds.map_mono continuous_subtype_val hTT') < ⊤ :=
      CatenarySpace.finite_codimBetween
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT')
    simpa [codimBetween_closed_eq hS hTT'] using hfinite
  · intro T T' hTT' s hs
    -- Compare maximal chains through the interval order isomorphism to the ambient interval.
    let e := closed_subspace_interval_order_iso hS hTT'
    have hsImage : IsMaxChain (· ≤ ·) (e '' s) := IsMaxChain.image e hs
    have hlen :
        (e '' s).encard =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
                (IrreducibleCloseds.map_mono continuous_subtype_val hTT')) +
            1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') (e '' s) hsImage
    calc
      s.encard = (e '' s).encard := by rw [e.injective.encard_image]
      _ =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
                (IrreducibleCloseds.map_mono continuous_subtype_val hTT')) +
            1 := hlen
      _ = ENat.toNat (codimBetween T T' hTT') + 1 := by
          rw [codimBetween_closed_eq hS hTT']

/-- Helper for Lemma 5.11.5: a homeomorphism transports catenarity across spaces. -/
private noncomputable def irreducibleCloseds_orderIso_of_homeomorph {X' : Type v}
    [TopologicalSpace X'] (e : X ≃ₜ X') : IrreducibleCloseds X ≃o IrreducibleCloseds X' := by
  let e' : IrreducibleCloseds X ≃ IrreducibleCloseds X' :=
    { toFun := fun T ↦ IrreducibleCloseds.map e e.continuous T
      invFun := fun T ↦ IrreducibleCloseds.map e.symm e.symm.continuous T
      left_inv := by
        intro T
        apply IrreducibleCloseds.ext
        rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_map]
        -- A homeomorphism maps closed sets to closed sets and the inverse cancels set-theoretically.
        rw [closure_eq_iff_isClosed.mpr (e.isClosedMap _ T.isClosed), Set.image_image]
        simpa using T.isClosed.closure_eq
      right_inv := by
        intro T
        apply IrreducibleCloseds.ext
        rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_map]
        rw [closure_eq_iff_isClosed.mpr (e.symm.isClosedMap _ T.isClosed), Set.image_image]
        simpa using T.isClosed.closure_eq }
  exact e'.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono e.continuous hAB)
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono e.symm.continuous hAB)

/-- Helper for Lemma 5.11.5: an order isomorphism restricts to the corresponding intervals. -/
private noncomputable def orderIso_interval {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a b : α) : Set.Icc a b ≃o Set.Icc (e a) (e b) where
  toFun x := ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
  invFun y := ⟨e.symm y.1, by simpa using e.symm.monotone y.2.1, by
    simpa using e.symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_rel_iff' := by
    intro x y
    simpa using e.le_iff_le

namespace Homeomorph

/-- Helper for Lemma 5.11.5: homeomorphic spaces have the same catenary property. -/
theorem catenarySpace {X' : Type v} [TopologicalSpace X'] (e : X ≃ₜ X')
    [CatenarySpace X] : CatenarySpace X' := by
  let eI : IrreducibleCloseds X' ≃o IrreducibleCloseds X :=
    irreducibleCloseds_orderIso_of_homeomorph e.symm
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    let eInt := orderIso_interval eI T T'
    -- Transport the codimension computation through the interval order isomorphism from `e.symm`.
    have hfinite : codimBetween (eI T) (eI T') (eI.monotone hTT') < ⊤ :=
      CatenarySpace.finite_codimBetween (eI.monotone hTT')
    have hcodim :
        codimBetween T T' hTT' = codimBetween (eI T) (eI T') (eI.monotone hTT') := by
      apply WithBot.coe_injective
      calc
        codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
          codimBetween_eq_krullDim hTT'
        _ = krullDim (Set.Icc (eI T) (eI T')) :=
          Order.krullDim_eq_of_orderIso eInt
        _ = codimBetween (eI T) (eI T') (eI.monotone hTT') :=
          (codimBetween_eq_krullDim (eI.monotone hTT')).symm
    simpa [hcodim] using hfinite
  · intro T T' hTT' s hs
    -- Send a maximal chain through the interval equivalence induced by the homeomorphism.
    let eInt := orderIso_interval eI T T'
    have hsImage : IsMaxChain (· ≤ ·) (eInt '' s) := IsMaxChain.image eInt hs
    have hlen :
        (eInt '' s).encard =
          ENat.toNat (codimBetween (eI T) (eI T') (eI.monotone hTT')) + 1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (eI.monotone hTT') (eInt '' s) hsImage
    have hcodim :
        codimBetween T T' hTT' = codimBetween (eI T) (eI T') (eI.monotone hTT') := by
      apply WithBot.coe_injective
      calc
        codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
          codimBetween_eq_krullDim hTT'
        _ = krullDim (Set.Icc (eI T) (eI T')) :=
          Order.krullDim_eq_of_orderIso eInt
        _ = codimBetween (eI T) (eI T') (eI.monotone hTT') :=
          (codimBetween_eq_krullDim (eI.monotone hTT')).symm
    calc
      s.encard = (eInt '' s).encard := by rw [eInt.injective.encard_image]
      _ = ENat.toNat (codimBetween (eI T) (eI T') (eI.monotone hTT')) + 1 := hlen
      _ = ENat.toNat (codimBetween T T' hTT') + 1 := by rw [hcodim]

end Homeomorph

-- Proof sketch: write a locally closed subset as an open subset of its closure. Closed irreducible
-- subsets of the subtype correspond to closed irreducible subsets of the ambient space meeting the
-- locally closed piece, and the interval of irreducible closed subsets is preserved under this
-- correspondence.
/-- A locally closed subspace of a catenary space is catenary. This is the reusable bridge/view
form of the “moreover” clause in Lemma 5.11.5. -/
protected theorem IsLocallyClosed.catenarySpace [CatenarySpace X] {Y : Set X}
    (hY : IsLocallyClosed Y) : CatenarySpace Y := by
  -- Route correction: first descend catenarity to `closure Y`, then restrict to the open subset
  -- cut out by `Y`, and only at the end transport back along the canonical homeomorphism.
  let V : Opens (closure Y) := ⟨Subtype.val ⁻¹' Y, hY.isOpen_preimage_val_closure⟩
  let eV : V ≃ₜ ((closure Y) ∩ Y : Set X) :=
    (Homeomorph.setCongr (by
      ext y
      constructor
      · intro hy
        exact ⟨y.2, hy⟩
      · intro hy
        exact hy.2)).trans
      (isClosed_closure.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphOfSubsetRange
        fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let eY : Y ≃ₜ ((closure Y) ∩ Y : Set X) :=
    Homeomorph.setCongr (by
      ext y
      constructor
      · intro hy
        exact ⟨subset_closure hy, hy⟩
      · intro hy
        exact hy.2)
  let e : Y ≃ₜ V := eY.trans eV.symm
  letI : CatenarySpace (closure Y) := isClosed_closure.catenarySpace_subtype
  haveI : CatenarySpace V := catenarySpace_opens V
  -- The locally closed subtype is homeomorphic to the corresponding open subset of its closure.
  exact e.symm.catenarySpace

namespace TopologicalSpace.IsOpenCover

-- Proof sketch: the forward implication restricts catenarity to each open member of the cover
-- using the open-subspace theorem above. For the converse, compare irreducible closed chains in
-- `X` with their restrictions to a cover member meeting the lower endpoint.
/-- Catenarity is local on the target for open covers. -/
theorem catenarySpace_iff {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) :
    CatenarySpace X ↔ ∀ i, CatenarySpace (U i) := by
  constructor
  · intro hX i
    haveI : CatenarySpace X := hX
    exact catenarySpace_opens (U i)
  · intro hCat
    refine ⟨?_, ?_⟩
    · intro T T' hTT'
      -- Choose a cover member meeting the lower endpoint so the whole interval restricts there.
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      obtain ⟨i, hxi⟩ := hU.exists_mem x
      let TU : IrreducibleCloseds (U i) := T.restrictOpen (U i) ⟨x, hx, hxi⟩
      let T'U : IrreducibleCloseds (U i) :=
        T'.restrictOpen (U i) (inter_nonempty_of_le T T' (U i) ⟨x, hx, hxi⟩ hTT')
      have hTUU : TU ≤ T'U := by
        intro y hy
        exact hTT' (by simpa [TU, T'U, IrreducibleCloseds.coe_restrictOpen] using hy)
      haveI : CatenarySpace (U i) := hCat i
      have hfinite : codimBetween TU T'U hTUU < ⊤ :=
        CatenarySpace.finite_codimBetween hTUU
      have hcodim :
          codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
        -- Compare the restricted interval with the ambient interval via the open-subspace order
        -- isomorphism, then rewrite the codomain interval using `map_restrictOpen_eq`.
        let e :=
          (open_subspace_interval_orderIso (U i) hTUU).trans <|
            OrderIso.setCongr
              (Set.Icc
                (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val TU)
                (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val T'U))
              (Set.Icc T T') (by simp [TU, T'U])
        apply WithBot.coe_injective
        calc
          codimBetween TU T'U hTUU = krullDim (Set.Icc TU T'U) :=
            codimBetween_eq_krullDim hTUU
          _ = krullDim (Set.Icc T T') := Order.krullDim_eq_of_orderIso e
          _ = codimBetween T T' hTT' := (codimBetween_eq_krullDim hTT').symm
      simpa [hcodim] using hfinite
    · intro T T' hTT' s hs
      -- Restrict the whole interval to one cover member through the lower endpoint, apply the
      -- local catenary length formula there, and transport the answer back to `X`.
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      obtain ⟨i, hxi⟩ := hU.exists_mem x
      let TU : IrreducibleCloseds (U i) := T.restrictOpen (U i) ⟨x, hx, hxi⟩
      let T'U : IrreducibleCloseds (U i) :=
        T'.restrictOpen (U i) (inter_nonempty_of_le T T' (U i) ⟨x, hx, hxi⟩ hTT')
      have hTUU : TU ≤ T'U := by
        intro y hy
        exact hTT' (by simpa [TU, T'U, IrreducibleCloseds.coe_restrictOpen] using hy)
      haveI : CatenarySpace (U i) := hCat i
      let e :=
        (open_subspace_interval_orderIso (U i) hTUU).trans <|
          OrderIso.setCongr
            (Set.Icc
              (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val TU)
              (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val T'U))
            (Set.Icc T T') (by simp [TU, T'U])
      have hsLocal : IsMaxChain (· ≤ ·) (e.symm '' s) := IsMaxChain.image e.symm hs
      have hlenLocal :
          (e.symm '' s).encard = ENat.toNat (codimBetween TU T'U hTUU) + 1 :=
        CatenarySpace.maximalIrreducibleClosedChainsHaveLength hTUU (e.symm '' s) hsLocal
      have hcodim :
          codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
        apply WithBot.coe_injective
        calc
          codimBetween TU T'U hTUU = krullDim (Set.Icc TU T'U) :=
            codimBetween_eq_krullDim hTUU
          _ = krullDim (Set.Icc T T') := Order.krullDim_eq_of_orderIso e
          _ = codimBetween T T' hTT' := (codimBetween_eq_krullDim hTT').symm
      calc
        s.encard = (e.symm '' s).encard := by rw [e.symm.injective.encard_image]
        _ = ENat.toNat (codimBetween TU T'U hTUU) + 1 := hlenLocal
        _ = ENat.toNat (codimBetween T T' hTT') + 1 := by rw [hcodim]

end TopologicalSpace.IsOpenCover

-- Proof sketch: the canonical owner-level locality statement is
-- `TopologicalSpace.IsOpenCover.catenarySpace_iff`. The forward implication chooses a trivial open
-- cover, while the converse applies that theorem to the given cover.
/-- Lemma 5.11.5: a topological space is catenary if and only if it admits an open cover by
catenary open subspaces.
This is the source-facing existential bridge for the canonical locality theorem
`TopologicalSpace.IsOpenCover.catenarySpace_iff`. -/
theorem catenarySpace_iff_hasOpenCoverByCatenarySpaces :
    CatenarySpace X ↔
      ∃ (ι : Type v) (U : ι → Opens X), IsOpenCover U ∧ ∀ i, CatenarySpace (U i) := by
  constructor
  · intro hX
    haveI : CatenarySpace X := hX
    refine ⟨ULift Unit, fun _ ↦ (⊤ : Opens X), ?_, ?_⟩
    · simp [TopologicalSpace.IsOpenCover]
    · intro i
      simpa using catenarySpace_opens (⊤ : Opens X)
  · rintro ⟨ι, U, hU, hUcat⟩
    exact hU.catenarySpace_iff.2 hUcat
