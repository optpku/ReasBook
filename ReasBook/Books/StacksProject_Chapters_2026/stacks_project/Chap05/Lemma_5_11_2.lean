module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for codimension under open restriction:
- primary domain: irreducible closed subsets under open-subspace inclusion, measured by
  `Order.coheight`
- inspected owner declarations:
  `TopologicalSpace.IrreducibleCloseds.map`,
  `TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing`,
  `Order.coheight_orderIso`,
  `subset_closure_inter_of_isPreirreducible_of_isOpen`
- best owner abstraction: `IrreducibleCloseds` together with the canonical ambient map
  `IrreducibleCloseds.map` along an inducing/open embedding, and codimension as `coheight`

Layer triage:
- `source-facing`: restriction of an irreducible closed subset to an open subspace, and the
  codimension invariance statement
- `core/canonical`: `IrreducibleCloseds`, `IrreducibleCloseds.map`, and `Order.coheight`
- `bridge/view`: `restrictOpen`, which is the inverse-side view of the canonical map on
  irreducible closed subsets for the open embedding `Subtype.val : U → X`

Primitive data is just the irreducible closed set and the open embedding. The order comparison on
upper intervals is derived API, so the codimension statement should be proved through the canonical
owner abstractions rather than through a parallel chain-length wrapper.
-/

namespace TopologicalSpace.IrreducibleCloseds

/-- The irreducible closed subset of an open subspace obtained by intersecting an ambient
irreducible closed subset that meets the open. -/
def restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Y : Set X),
    by
      have hYU' : ((Y : Set X) ∩ Set.range (Subtype.val : U → X)).Nonempty := by
        simpa using hYU
      simpa using Y.isIrreducible.preimage U.isOpenEmbedding' hYU',
    Y.isClosed.preimage continuous_subtype_val⟩

@[simp] theorem coe_restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    (Y.restrictOpen U hYU : Set U) = Subtype.val ⁻¹' (Y : Set X) :=
  rfl

end TopologicalSpace.IrreducibleCloseds

open TopologicalSpace.IrreducibleCloseds

private theorem inter_nonempty_of_le (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) (hYT : Y ≤ T) : ((T : Set X) ∩ U).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

private theorem closure_inter_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : closure ((Y : Set X) ∩ U) = (Y : Set X) := by
  apply Subset.antisymm
  · exact closure_minimal (inter_subset_left) Y.isClosed
  ·
    exact subset_closure_inter_of_isPreirreducible_of_isOpen
      Y.isIrreducible.isPreirreducible U.isOpen hYU

private noncomputable def restrictOpenIciOrderIso (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : Set.Ici (Y.restrictOpen U hYU) ≃o Set.Ici Y :=
  let e : Set.Ici (Y.restrictOpen U hYU) ≃ Set.Ici Y :=
    { toFun := fun Z ↦
        ⟨IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1, by
          change (Y : Set X) ⊆
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1 : Set X)
          rw [IrreducibleCloseds.coe_map]
          calc
            (Y : Set X) = closure ((Y : Set X) ∩ U) := (closure_inter_eq Y U hYU).symm
            _ ⊆ closure ((Subtype.val : U → X) '' (Z.1 : Set U)) := by
              refine closure_mono ?_
              intro x hx
              have hx' : (⟨x, hx.2⟩ : U) ∈ (Y.restrictOpen U hYU : Set U) := by
                simpa [coe_restrictOpen] using hx.1
              exact ⟨⟨x, hx.2⟩, Z.2 hx', rfl⟩
        ⟩
      invFun := fun T ↦
        ⟨T.1.restrictOpen U (inter_nonempty_of_le Y T.1 U hYU T.2), by
          intro x hx
          exact T.2 (by simpa [coe_restrictOpen] using hx)
        ⟩
      left_inv := by
        intro Z
        have hEmbedding := U.isOpenEmbedding'.isEmbedding
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        change x ∈
            Subtype.val ⁻¹'
              closure ((Subtype.val : U → X) '' ((Z.1 : IrreducibleCloseds U) : Set U)) ↔
          x ∈ ((Z.1 : IrreducibleCloseds U) : Set U)
        rw [← hEmbedding.closure_eq_preimage_closure_image
          (((Z.1 : IrreducibleCloseds U) : Set U))]
        simp [Z.1.isClosed.closure_eq]
      right_inv := by
        intro T
        have hTU : ((T.1 : Set X) ∩ U).Nonempty := inter_nonempty_of_le Y T.1 U hYU T.2
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        simp [IrreducibleCloseds.coe_map, coe_restrictOpen, Set.image_preimage_eq_inter_range,
          closure_inter_eq T.1 U hTU] }
  e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((A.1.restrictOpen U (inter_nonempty_of_le Y A.1 U hYU A.2) : Set U) ⊆
          (B.1.restrictOpen U (inter_nonempty_of_le Y B.1 U hYU B.2) : Set U))
      intro x hx
      simpa [coe_restrictOpen] using hAB (by simpa [coe_restrictOpen] using hx))

-- Proof sketch: by Definition 5.11.1, codimension is `coheight`, equivalently the Krull dimension
-- of the upper interval by `Order.coheight_eq_krullDim_Ici`. The map
-- `T ↦ closure (Subtype.val '' T)` gives an order isomorphism between the intervals above
-- `Y.restrictOpen U hYU` in `IrreducibleCloseds U` and above `Y` in `IrreducibleCloseds X`.
/-- Lemma 5.11.2: if an irreducible closed subset `Y` meets an open subspace `U`, then its
codimension, expressed canonically as `coheight`, is unchanged after restricting to `U`. -/
theorem codim_irreducibleClosed_restrictOpen_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    coheight Y = coheight (Y.restrictOpen U hYU) := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  simpa using Order.krullDim_eq_of_orderIso (restrictOpenIciOrderIso Y U hYU).symm
