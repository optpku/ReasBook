module

public import Mathlib.Topology.Sober
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Example_5_8_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u

section

variable {Z : Type u}
variable (z : Z)

/- Domain-style sampling for Example 5.8.12:
- primary domain: topologies defined by closed sets, quasi-sobriety, and the cofinite topology on
  the punctured subspace;
- inspected owner declarations:
  `TopologicalSpace.ofClosed`,
  `CofiniteTopology.isClosed_iff`,
  `QuasiSober`,
  `infinite_cofiniteTopology_not_quasiSober`;
- best owner abstraction: the source-facing owner is the topology
  `finiteClosedAwayFromPointTopology z`, while the type synonym `FiniteClosedAwayFromPoint z` is
  only the thin bridge needed to attach that topology to the original carrier, in the same style as
  `CofiniteTopology`;
- primitive-vs-derived split: the primitive data is only the closed-set presentation of
  `finiteClosedAwayFromPointTopology z`; the type synonym, the `T₀` and quasi-sober structure, and the
  punctured cofinite comparison are derived bridge/API on `FiniteClosedAwayFromPoint z`.

Source/core/bridge triage:
- `source-facing`: the topology whose closed sets are `Z` and the finite subsets of `Z \ {z}`;
- `core/canonical`: `TopologicalSpace.ofClosed`, `T0Space`, `QuasiSober`, and
  `CofiniteTopology`;
- `bridge/view`: the owner type synonym `FiniteClosedAwayFromPoint z`, the punctured-subspace comparison
  theorem, and the source-facing closed-set characterization theorem.
-/

/-- The family of closed sets for the topology in Example 5.8.12: either all of `Z`, or a finite
subset of `Z \ {z}`. -/
def finiteClosedAwayFromPointClosedSets : Set (Set Z) :=
  { s | s = univ ∨ s.Finite ∧ s ⊆ ({z} : Set Z)ᶜ }

/-- The empty set is closed in the topology of Example 5.8.12. -/
-- Proof sketch: `∅` is finite and is contained in `Z \ {z}`.
theorem finiteClosedAwayFromPointClosedSets_empty_mem :
    ∅ ∈ finiteClosedAwayFromPointClosedSets z := by
  right
  exact ⟨finite_empty, by simp⟩

/-- Arbitrary intersections of closed sets remain closed for the topology of Example 5.8.12. -/
-- Proof sketch: if every set in the family is `univ`, then the intersection is `univ`. Otherwise
-- pick one finite member; the full intersection is contained in that finite set and still avoids
-- `z`.
theorem finiteClosedAwayFromPointClosedSets_sInter_mem {A : Set (Set Z)}
    (hA : A ⊆ finiteClosedAwayFromPointClosedSets z) :
    ⋂₀ A ∈ finiteClosedAwayFromPointClosedSets z := by
  classical
  by_cases hAll : ∀ s ∈ A, s = univ
  · left
    apply eq_univ_of_forall
    intro x
    exact mem_sInter.2 fun t ht ↦ by simp [hAll t ht]
  · obtain ⟨s, hs⟩ := not_forall.mp hAll
    obtain ⟨hsA, hs_ne⟩ := not_forall.mp hs
    rcases hA hsA with rfl | ⟨hsFinite, hsSubset⟩
    · exact (hs_ne rfl).elim
    right
    refine ⟨hsFinite.subset <| sInter_subset_of_mem hsA, ?_⟩
    exact (sInter_subset_of_mem hsA).trans hsSubset

/-- Finite unions of closed sets remain closed for the topology of Example 5.8.12. -/
-- Proof sketch: the union of two finite subsets of `Z \ {z}` is again finite and still avoids
-- `z`, while `univ` is absorbing for unions.
theorem finiteClosedAwayFromPointClosedSets_union_mem {A B : Set Z}
    (hA : A ∈ finiteClosedAwayFromPointClosedSets z)
    (hB : B ∈ finiteClosedAwayFromPointClosedSets z) :
    A ∪ B ∈ finiteClosedAwayFromPointClosedSets z := by
  rcases hA with rfl | ⟨hAFinite, hASubset⟩
  · left
    simp
  rcases hB with rfl | ⟨hBFinite, hBSubset⟩
  · left
    simp
  right
  exact ⟨hAFinite.union hBFinite, union_subset hASubset hBSubset⟩

/-- The topology from Example 5.8.12 whose closed sets are `Z` and the finite subsets of
`Z \ {z}`. -/
@[reducible] def finiteClosedAwayFromPointTopology : TopologicalSpace Z :=
  TopologicalSpace.ofClosed (finiteClosedAwayFromPointClosedSets z)
    (finiteClosedAwayFromPointClosedSets_empty_mem z)
    (fun _ hA ↦ finiteClosedAwayFromPointClosedSets_sInter_mem z hA)
    (fun _ hA _ hB ↦ finiteClosedAwayFromPointClosedSets_union_mem z hA hB)

/-- The point set `Z` equipped with the topology from Example 5.8.12. -/
def FiniteClosedAwayFromPoint (_ : Z) := Z

instance : TopologicalSpace (FiniteClosedAwayFromPoint z) :=
  finiteClosedAwayFromPointTopology z

namespace FiniteClosedAwayFromPoint

local notation "X" => FiniteClosedAwayFromPoint z
local notation "U" => {x : X // x ≠ z}

/-- The closed subsets of `FiniteClosedAwayFromPoint z` are exactly `univ` and the finite subsets
of `Z \ {z}`. -/
theorem isClosed_iff {s : Set X} :
    IsClosed s ↔ s = univ ∨ s.Finite ∧ s ⊆ ({z} : Set X)ᶜ := by
  constructor
  · intro hs
    have hs' : sᶜᶜ ∈ finiteClosedAwayFromPointClosedSets z := hs.1
    simpa [finiteClosedAwayFromPointClosedSets, Set.subset_def] using hs'
  · intro hs
    rw [← isOpen_compl_iff]
    change sᶜᶜ ∈ finiteClosedAwayFromPointClosedSets z
    simpa [finiteClosedAwayFromPointClosedSets, Set.subset_def] using hs

private theorem isClosed_singleton_of_ne {x : X} (hx : x ≠ z) :
    IsClosed ({x} : Set X) := by
  rw [isClosed_iff]
  right
  refine ⟨finite_singleton x, ?_⟩
  intro y hy
  simp only [mem_singleton_iff] at hy
  simpa [hy] using hx

private theorem closure_singleton_eq_univ :
    closure ({z} : Set X) = univ := by
  rcases (isClosed_iff z).1 isClosed_closure with h | ⟨_, h⟩
  · exact h
  · exfalso
    have hz : (show X from z) ∈ closure ({show X from z} : Set X) :=
      subset_closure (by simp)
    have hz' : (show X from z) ∈ ({show X from z} : Set X)ᶜ := h hz
    exact hz' (by simp)

private theorem closure_singleton_eq_of_ne {x : X} (hx : x ≠ z) :
    closure ({x} : Set X) = ({x} : Set X) :=
  (isClosed_singleton_of_ne z hx).closure_eq

/-- The punctured subspace of `FiniteClosedAwayFromPoint z` agrees with the canonical cofinite
topology on `Z \ {z}`. -/
theorem punctured_eq_cofiniteTopology :
    (inferInstance : TopologicalSpace U) =
      (inferInstance : TopologicalSpace (CofiniteTopology U)) := by
  apply TopologicalSpace.ext_isClosed
  intro s
  constructor
  · intro hs
    rcases isClosed_induced_iff.mp hs with ⟨t, ht, rfl⟩
    rw [isClosed_iff] at ht
    rcases ht with rfl | ⟨ht, _⟩
    · exact CofiniteTopology.isClosed_iff.2 <| Or.inl rfl
    · exact CofiniteTopology.isClosed_iff.2 <| Or.inr <|
        Finite.preimage_embedding ⟨Subtype.val, Subtype.val_injective⟩ ht
  · intro hs
    rcases (CofiniteTopology.isClosed_iff).1 hs with rfl | hs
    · exact isClosed_univ
    · refine isClosed_induced_iff.2 ?_
      refine ⟨(↑) '' s, ?_, preimage_image_eq _ Subtype.val_injective⟩
      rw [isClosed_iff]
      right
      refine ⟨Finite.image (Subtype.val : U → X) hs, ?_⟩
      rintro x ⟨y, hy, rfl⟩
      exact y.2

/-- The space `FiniteClosedAwayFromPoint z` is Kolmogorov. -/
instance : T0Space X := by
  rw [t0Space_iff_or_notMem_closure]
  intro x y hxy
  by_cases hx : x = z
  · have hy : y ≠ z := by
      simpa [hx] using hxy.symm
    left
    rw [closure_singleton_eq_of_ne z hy]
    simpa [hx] using hxy
  · right
    rw [closure_singleton_eq_of_ne z hx]
    simpa using hxy.symm

/-- The space `FiniteClosedAwayFromPoint z` is quasi-sober. -/
instance : QuasiSober X where
  sober {S} hS hSClosed := by
    rcases (isClosed_iff z).1 hSClosed with rfl | ⟨hSFinite, hSAway⟩
    · exact ⟨show X from z, by
        simpa [isGenericPoint_def] using closure_singleton_eq_univ z⟩
    · obtain ⟨x, hxS⟩ := hS.nonempty
      have hxz : x ≠ z := by
        simpa using hSAway hxS
      have hSDiffClosed : IsClosed (S \ {x}) := by
        rw [isClosed_iff]
        right
        refine ⟨hSFinite.subset diff_subset, ?_⟩
        exact diff_subset.trans hSAway
      have hSSubset : S ⊆ ({x} : Set X) ∪ (S \ {x}) := by
        intro y hyS
        by_cases hyx : y = x
        · simp [hyx]
        · right
          exact ⟨hyS, hyx⟩
      have hSingle : S ⊆ ({x} : Set X) := by
        rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hS.isPreirreducible)
            ({x} : Set X) (S \ {x})
            (isClosed_singleton_of_ne z hxz) hSDiffClosed hSSubset with h | h
        · exact h
        · exact (h hxS).2.elim rfl
      have hEq : S = ({x} : Set X) :=
        subset_antisymm hSingle (singleton_subset_iff.2 hxS)
      exact ⟨x, by rw [isGenericPoint_def, hEq, closure_singleton_eq_of_ne z hxz]⟩

/-- Example 5.8.12 (1): the topology whose closed sets are `Z` and the finite subsets of
`Z \ {z}` is sober, expressed canonically by `T₀` and quasi-sobriety. In particular, this
recovers the source statement for infinite `Z`. -/
-- Proof sketch: show first that the topology is `T₀`, with `z` topologically distinguished from
-- every other point. Then classify irreducible closed subsets: they are either `univ`, with
-- generic point `z`, or singletons away from `z`, whose unique point is generic.
theorem sober :
    T0Space X ∧ QuasiSober X :=
  ⟨inferInstance, inferInstance⟩

section Infinite

variable [Infinite Z]

/-- Example 5.8.12 (2): the induced topology on the subspace `Z \ {z}` is not quasi-sober. -/
-- Proof sketch: after removing `z`, the induced topology is the cofinite topology on an infinite
-- set. The whole space is irreducible and closed, but in a cofinite `T₁` space every singleton is
-- closed, so no point has dense singleton closure and hence `univ` has no generic point.
theorem punctured_not_quasiSober :
    ¬ QuasiSober U := by
  haveI : Infinite U := by
    simpa using (finite_singleton z).infinite_compl.to_subtype
  change ¬ @QuasiSober U (inferInstance : TopologicalSpace U)
  rw [punctured_eq_cofiniteTopology]
  change ¬ QuasiSober (CofiniteTopology U)
  exact infinite_cofiniteTopology_not_quasiSober

end Infinite

end FiniteClosedAwayFromPoint

end
