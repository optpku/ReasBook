module

public import stacks_project.Chap05.Definition_5_9_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/- Domain-style sampling for Lemma 5.9.6:
- primary domain: Noetherian topological spaces and local connectedness
- sampled owner declarations:
  `TopologicalSpace.LocallyNoetherianSpace.exists_mem_nhds_subset`,
  `TopologicalSpace.locallyConnectedSpace_iff_connected_subsets`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
  `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`
- best owner abstraction: the core owner is `TopologicalSpace.LocallyConnectedSpace`; the source
  hypothesis is the chapter owner `TopologicalSpace.LocallyNoetherianSpace`
- primitive data: a Noetherian neighborhood around each point
- derived API: a preconnected neighborhood basis, hence a `LocallyConnectedSpace` instance

Layer triage:
- `source-facing`: Lemma 5.9.6, asserting that locally Noetherian spaces are locally connected
- `core/canonical`: `TopologicalSpace.LocallyConnectedSpace`
- `bridge/view`: the private construction of a preconnected neighborhood inside a Noetherian space

There is no upstream owner theorem in mathlib for the Noetherian-to-locally-connected bridge, so
this file exposes that bridge as the public owner instance
`TopologicalSpace.NoetherianSpace.locallyConnectedSpace` and then uses it for the source-facing
locally Noetherian statement.
-/

private theorem exists_preconnected_mem_nhds [NoetherianSpace X] (x : X) :
    ∃ V : Set X, V ∈ 𝓝 x ∧ IsPreconnected V := by
  classical
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let R : irreducibleComponents X → irreducibleComponents X → Prop :=
    fun A B ↦ ((A : Set X) ∩ (B : Set X)).Nonempty
  let T : Set (irreducibleComponents X) := {A | Relation.ReflTransGen R Z A}
  let V : Set X := ⋃ A ∈ T, (A : Set X)
  have hR_symm : Symmetric R := fun A B h ↦ by
    simpa [R, inter_comm] using h
  have hT_path {A B : irreducibleComponents X} (hA : A ∈ T)
      (hAB : Relation.ReflTransGen R A B) :
      B ∈ T ∧
        Relation.ReflTransGen
          (fun A B : irreducibleComponents X ↦
            (((A : Set X) ∩ (B : Set X)).Nonempty) ∧ A ∈ T) A B := by
    induction hAB generalizing hA with
    | refl =>
        exact ⟨hA, .refl⟩
    | @tail B C hAB hBC ih =>
        rcases ih hA with ⟨hB, hAB'⟩
        exact ⟨hB.tail hBC, hAB'.tail ⟨hBC, hB⟩⟩
  have hT_preconnected (A : irreducibleComponents X) (hA : A ∈ T) :
      IsPreconnected (A : Set X) :=
    A.2.1.isConnected.isPreconnected
  have hV_preconnected : IsPreconnected V := by
    have hpre : IsPreconnected (⋃ A ∈ T, (A : Set X)) := by
      refine IsPreconnected.biUnion_of_reflTransGen
        (fun A hA ↦ hT_preconnected A hA) ?_
      intro A hA B hB
      have hAZ : Relation.ReflTransGen R A Z :=
        (Relation.ReflTransGen.symmetric hR_symm) hA
      exact (hT_path hA (hAZ.trans hB)).2
    simpa [V] using hpre
  haveI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let U : Set (irreducibleComponents X) := Tᶜ
  have hU_finite : U.Finite := Set.toFinite U
  have hU_union_closed : IsClosed (⋃ A ∈ U, (A : Set X)) := by
    simpa [Set.sUnion_image] using
      (hU_finite.image fun A : irreducibleComponents X ↦ (A : Set X)).isClosed_biUnion
        fun W hW ↦ by
          rcases hW with ⟨A, hAU, rfl⟩
          simpa using isClosed_of_mem_irreducibleComponents (A : Set X) A.2
  have hV_eq : V = (⋃ A ∈ U, (A : Set X))ᶜ := by
    ext y
    constructor
    · intro hy hyU
      rcases mem_iUnion₂.1 hy with ⟨A, hAT, hyA⟩
      rcases mem_iUnion₂.1 hyU with ⟨B, hBU, hyB⟩
      exact hBU (hAT.tail <| by
        simpa [R, inter_comm] using (show ((A : Set X) ∩ B).Nonempty from ⟨y, hyA, hyB⟩))
    · intro hy
      have hy' : y ∈ ⋃₀ irreducibleComponents X := by
        simp [sUnion_irreducibleComponents]
      rcases mem_sUnion.1 hy' with ⟨A, hA, hyA⟩
      let A' : irreducibleComponents X := ⟨A, hA⟩
      by_cases hAT : A' ∈ T
      · exact mem_iUnion₂.2 ⟨A', hAT, hyA⟩
      · exact False.elim (hy (mem_iUnion₂.2 ⟨A', hAT, hyA⟩))
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact hU_union_closed.isOpen_compl
  have hxV : x ∈ V := by
    exact mem_iUnion₂.2 ⟨Z, .refl, mem_irreducibleComponent⟩
  exact ⟨V, hV_open.mem_nhds hxV, hV_preconnected⟩

/-- A Noetherian topological space is locally connected. -/
instance NoetherianSpace.locallyConnectedSpace [NoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  let x' : U := ⟨x, mem_of_mem_nhds hU⟩
  letI : NoetherianSpace U := inferInstance
  rcases exists_preconnected_mem_nhds x' with ⟨V, hV, hVconn⟩
  let W : Set X := Subtype.val '' V
  have hW_nhdsWithin : W ∈ 𝓝[U] x := by
    simpa [W] using (mem_nhds_subtype_iff_nhdsWithin).1 hV
  have hW_nhds : W ∈ 𝓝 x := by
    rwa [nhdsWithin_eq_nhds.2 hU] at hW_nhdsWithin
  refine ⟨W, hW_nhds, hVconn.image _ continuous_subtype_val.continuousOn, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact z.2

attribute [instance 100] NoetherianSpace.locallyConnectedSpace

/-- Lemma 5.9.6: a locally Noetherian topological space is locally connected. -/
instance locallyConnectedSpace_of_locallyNoetherianSpace [LocallyNoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  rcases LocallyNoetherianSpace.exists_mem_nhds_subset x hU with ⟨E, hE, hEU, hE_noeth⟩
  letI : NoetherianSpace E := hE_noeth
  let x' : E := ⟨x, mem_of_mem_nhds hE⟩
  letI : LocallyConnectedSpace E := NoetherianSpace.locallyConnectedSpace
  rcases
      (locallyConnectedSpace_iff_connected_subsets.mp (show LocallyConnectedSpace E from inferInstance))
        x' Set.univ Filter.univ_mem with
    ⟨V, hV, hV_preconnected, _⟩
  let W : Set X := Subtype.val '' V
  have hW_subset : W ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hEU z.2
  have hW_within : W ∈ 𝓝[E] x := by
    simpa [W] using (mem_nhds_subtype_iff_nhdsWithin).1 hV
  have hW : W ∈ 𝓝 x := by
    rwa [nhdsWithin_eq_nhds.2 hE] at hW_within
  refine ⟨W, hW, hV_preconnected.image _ continuous_subtype_val.continuousOn, hW_subset⟩

end TopologicalSpace
