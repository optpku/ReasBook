module

public import stacks_project.Chap05.Definition_5_28_3
import Mathlib.Topology.LocallyClosed
import stacks_project.Chap05.Remark_5_28_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for finite stratification refinements of locally closed partitions:
- inspected project declarations:
  `LocallyClosedPartition`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`,
  `IsStratification.toLocallyClosedPartition`, and
  `IsClosedInitialFamily.frontier_isStratification`
- best owner abstraction: `IsClosedInitialFamily`

Layer triage:
- `source-facing`: the indexed-stratification statement of Lemma 5.28.6
- `core/canonical`: `IsClosedInitialFamily`
- `bridge/view`: `IsClosedInitialFamily.frontier_isStratification` together with
  `IsStratification.toLocallyClosedPartition`

Primitive data are only the finite locally closed partition `P` and the refinement relation to the
eventual stratification. Any auxiliary closed initial family used to construct the ordered strata,
as well as the resulting index type and closure-order bookkeeping, belongs to derived bridge data
rather than the public owner of this source item.
-/

namespace LocallyClosedPartition

-- Proof sketch: replace the finite partition by a finite closed initial family built from the
-- closures of unions of parts, apply `IsClosedInitialFamily.frontier_isStratification`, and then
-- recover refinement of `P` through `IsStratification.toLocallyClosedPartition`.
/-- Lemma 5.28.6: every finite locally closed partition of a topological space is refined by a
finite stratification. -/
theorem exists_finite_stratification_refining (P : LocallyClosedPartition X)
    (hPfinite : P.toSet.Finite) :
    ∃ (I : Type u) (_ : Finite I) (_ : PartialOrder I) (strata : I → Set X)
      (hstrata : IsStratification strata), hstrata.toLocallyClosedPartition ≤ P := by
  classical
  let _ : Fintype P.toSet := hPfinite.fintype
  let G : Type u := P.toSet × Bool
  let generator : G → Set X := fun g ↦
    if g.2 then closure (g.1 : Set X) \ (g.1 : Set X) else closure (g.1 : Set X)
  let I : Type u := OrderDual (Set G)
  let Z : I → Set X := fun A ↦ ⋂ g ∈ (show Set G from A), generator g
  -- Route correction: use the source proof's finite intersection family of closures and
  -- boundaries, not the earlier sketch based on closures of unions of parts.
  have hZ : IsClosedInitialFamily Z := by
    refine
      { isClosed := ?_
        iUnion_eq_univ := ?_
        locallyFinite := locallyFinite_of_finite Z
        inter_eq_iUnion := ?_ }
    · intro A
      -- Each member of the family is an intersection of closed generators.
      refine isClosed_biInter ?_
      intro g hg
      by_cases hgBool : g.2
      · have hloc : IsLocallyClosed (g.1 : Set X) := P.locallyClosed g.1
        simpa [generator, hgBool, coborder] using hloc.isOpen_coborder.isClosed_compl
      · simp [generator, hgBool]
    · -- The empty index set contributes `univ`, so the family covers `X`.
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        refine Set.mem_iUnion.2 ?_
        refine ⟨OrderDual.toDual (∅ : Set G), ?_⟩
        simp only [Z, Set.mem_iInter]
        intro g hg
        cases hg
    · intro A B
      let A0 : Set G := A
      let B0 : Set G := B
      -- Reverse inclusion turns intersections into unions over larger generator sets.
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxA, hxB⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨OrderDual.toDual (A0 ∪ B0), ?_⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨?_, ?_⟩
        · constructor
          · exact subset_union_left
          · exact subset_union_right
        · have hxA' : ∀ g ∈ A0, x ∈ generator g := by
            simpa [Z, A0] using hxA
          have hxB' : ∀ g ∈ B0, x ∈ generator g := by
            simpa [Z, B0] using hxB
          simp only [Z, Set.mem_iInter]
          intro g hg
          rcases hg with hg | hg
          · exact hxA' g hg
          · exact hxB' g hg
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨K, hxK⟩
        rcases Set.mem_iUnion.1 hxK with ⟨hK, hxK⟩
        rcases hK with ⟨hAK, hBK⟩
        have hxK' : ∀ g ∈ (show Set G from K), x ∈ generator g := by
          simpa [Z] using hxK
        constructor
        · simp only [Z, Set.mem_iInter]
          intro g hg
          exact hxK' g (hAK hg)
        · simp only [Z, Set.mem_iInter]
          intro g hg
          exact hxK' g (hBK hg)
  let strata : IsClosedInitialFamily.frontierIndex Z → Set X := IsClosedInitialFamily.frontierStrata Z
  let hstrata : IsStratification strata := IsClosedInitialFamily.frontier_isStratification hZ
  refine ⟨IsClosedInitialFamily.frontierIndex Z, inferInstance, inferInstance, strata, hstrata, ?_⟩
  rw [LocallyClosedPartition.le_iff_forall_exists_mem_subset]
  intro s hs
  change s ∈ Set.range strata at hs
  rcases hs with ⟨i, rfl⟩
  rcases i.2 with ⟨x, hxFrontier⟩
  rcases (P.isPartition.2 x) with ⟨t, htx, ht_unique⟩
  refine ⟨t, htx.1, ?_⟩
  let A0 : Set G := i.1
  let gClosure : G := (⟨t, htx.1⟩, false)
  let gBoundary : G := (⟨t, htx.1⟩, true)
  have hxA : x ∈ Z i.1 := by
    simpa [IsClosedInitialFamily.frontier, Z] using hxFrontier.1
  have hxA' : ∀ g ∈ A0, x ∈ generator g := by
    simpa [Z, A0] using hxA
  -- The closure generator of the ambient partition piece must already belong to the index set.
  have hgClosure_mem : gClosure ∈ A0 := by
    by_contra hgClosure_not_mem
    have hxClosure : x ∈ generator gClosure := by
      simpa [generator, gClosure] using subset_closure htx.2
    have hxStrict : x ∈ Z (OrderDual.toDual (A0 ∪ {gClosure})) := by
      simp only [Z, Set.mem_iInter]
      intro g hg
      rcases hg with hg | rfl
      · exact hxA' g hg
      · exact hxClosure
    have hlt : OrderDual.toDual (A0 ∪ {gClosure}) ∈ Set.Iio i.1 := by
      change A0 ⊂ A0 ∪ {gClosure}
      simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
        Set.ssubset_insert hgClosure_not_mem
    exact hxFrontier.2 <| Set.mem_iUnion.2 ⟨OrderDual.toDual (A0 ∪ {gClosure}), Set.mem_iUnion.2 ⟨hlt, hxStrict⟩⟩
  -- The boundary generator cannot belong to the index set because `x` lies in the partition piece.
  have hgBoundary_not_mem : gBoundary ∉ A0 := by
    intro hgBoundary_mem
    have hxBoundary : x ∈ generator gBoundary := hxA' gBoundary hgBoundary_mem
    have : x ∉ closure t \ t := by
      simp [htx.2]
    exact this <| by simpa [generator, gBoundary] using hxBoundary
  intro y hy
  have hyA : y ∈ Z i.1 := by
    simpa [IsClosedInitialFamily.frontier, Z] using hy.1
  have hyA' : ∀ g ∈ A0, y ∈ generator g := by
    simpa [Z, A0] using hyA
  have hyClosure : y ∈ closure t := by
    have : y ∈ generator gClosure := hyA' gClosure hgClosure_mem
    simpa [generator, gClosure] using this
  by_contra hy_not_mem
  -- If `y` left the chosen partition piece, the boundary generator would create a smaller frontier.
  have hyBoundary : y ∈ generator gBoundary := by
    exact by
      simpa [generator, gBoundary, hy_not_mem] using And.intro hyClosure hy_not_mem
  have hyStrict : y ∈ Z (OrderDual.toDual (A0 ∪ {gBoundary})) := by
    simp only [Z, Set.mem_iInter]
    intro g hg
    rcases hg with hg | rfl
    · exact hyA' g hg
    · exact hyBoundary
  have hlt : OrderDual.toDual (A0 ∪ {gBoundary}) ∈ Set.Iio i.1 := by
    change A0 ⊂ A0 ∪ {gBoundary}
    simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
      Set.ssubset_insert hgBoundary_not_mem
  exact hy.2 <| Set.mem_iUnion.2 ⟨OrderDual.toDual (A0 ∪ {gBoundary}), Set.mem_iUnion.2 ⟨hlt, hyStrict⟩⟩

end LocallyClosedPartition

end
