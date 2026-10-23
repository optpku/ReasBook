module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.JacobsonSpace
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.FiniteUnionOfLocallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for Jacobson subspaces defined by local constructibility:
- primary domain: locally constructible subsets and Jacobson spaces
- inspected owner-level declarations:
  `Topology.IsLocallyConstructible`,
  `Topology.IsEmbedding.isLocallyClosed_iff`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `JacobsonSpace.of_isOpenEmbedding`
- best owner abstraction: `Topology.IsLocallyConstructible`

Layer triage:
- `source-facing`: Lemma 5.18.5, asserting that a subspace locally given by unions of locally
  closed subsets is Jacobson and that its closed points are already closed in the ambient space
- `core/canonical`: `Topology.IsLocallyConstructible`, `Topology.IsConstructible`, and
  `JacobsonSpace`
- `bridge/view`: the finite-union-of-locally-closed decomposition of constructible neighborhoods
  together with the canonical subtype traces `U ↓∩ T`

Primitive data belongs to the owner predicate `IsLocallyConstructible`; the source phrase “locally
a union of locally closed subsets” is derived API recovered from
`IsConstructible.isFiniteUnionOfLocallyClosed` on each neighborhood. The constructible case is an
internal bridge: it should feed the local theorem, not survive as a parallel public owner.
-/

/-- Helper for Lemma 5.18.5: a constructible subspace of a Jacobson space is Jacobson. -/
private theorem jacobsonSpace_subtype_of_isConstructible_aux [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) :
    JacobsonSpace T := by
  -- Reduce Jacobsonness to the closed-point criterion on nonempty locally closed subsets.
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨W, hW, hWZ⟩ :=
    IsEmbedding.subtypeVal.isLocallyClosed_iff.1 hZ'
  obtain ⟨n, S, hS, hT_eq⟩ := hT.isFiniteUnionOfLocallyClosed.exists_eq_iUnion
  -- Identify the image of `Z` in `X` with the ambient trace `W ∩ T`.
  have himage_eq : ((↑) : T → X) '' Z = W ∩ T := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzW : (z : X) ∈ W := by
        have : (z : X) ∈ W ∩ Set.range ((↑) : T → X) := by
          rw [hWZ]
          exact ⟨z, hz, rfl⟩
        exact this.1
      exact ⟨hzW, z.2⟩
    · rintro ⟨hxW, hxT⟩
      rw [← hWZ]
      exact ⟨hxW, ⟨⟨x, hxT⟩, rfl⟩⟩
  have himage_iUnion : ((↑) : T → X) '' Z = ⋃ i, W ∩ S i := by
    calc
      ((↑) : T → X) '' Z = W ∩ T := himage_eq
      _ = W ∩ ⋃ i, S i := by rw [hT_eq]
      _ = ⋃ i, W ∩ S i := by rw [inter_iUnion]
  -- A nonempty image meets one locally closed constructible piece, where Jacobsonness of `X`
  -- supplies a point closed in `X`.
  have himage_nonempty : (((↑) : T → X) '' Z).Nonempty := by
    rcases hZ with ⟨z, hz⟩
    exact ⟨(z : X), ⟨z, hz, rfl⟩⟩
  rw [himage_iUnion, Set.nonempty_iUnion] at himage_nonempty
  obtain ⟨i, hi⟩ := himage_nonempty
  obtain ⟨x, hx, hxclosed⟩ :=
    nonempty_inter_closedPoints hi (hW.inter (hS i))
  have hximage : x ∈ ((↑) : T → X) '' Z := by
    rw [himage_iUnion]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  rcases hximage with ⟨z, hz, rfl⟩
  refine ⟨z, hz, ?_⟩
  rw [mem_closedPoints_iff]
  convert (mem_closedPoints_iff.1 hxclosed).preimage continuous_subtype_val using 1
  ext w
  simp [Subtype.ext_iff]

/-- Helper for Lemma 5.18.5: in the constructible case, closed points of the subspace are already
closed in the ambient space. -/
private theorem closedPoints_subset_preimage_closedPoints_of_isConstructible_aux [JacobsonSpace X]
    {T : Set X} (hT : IsConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  -- Turn the singleton `{x}` in the subspace into an ambient locally closed singleton.
  have hx' : IsLocallyClosed ({x} : Set T) := by
    refine ⟨univ, {x}, isOpen_univ, ?_, by ext y; simp⟩
    exact mem_closedPoints_iff.1 hx
  obtain ⟨W, hW, hWsingleton⟩ :=
    IsEmbedding.subtypeVal.isLocallyClosed_iff.1 hx'
  obtain ⟨n, S, hS, hT_eq⟩ := hT.isFiniteUnionOfLocallyClosed.exists_eq_iUnion
  have hxT : (x : X) ∈ T := x.2
  have hxUnion : (x : X) ∈ ⋃ i, S i := by simpa [hT_eq] using hxT
  rw [Set.mem_iUnion] at hxUnion
  obtain ⟨i, hxi⟩ := hxUnion
  -- On the constructible piece containing `x`, the ambient trace collapses to the singleton.
  have hWT : W ∩ T = ({(x : X)} : Set X) := by
    ext y
    constructor
    · intro hy
      have hyImage : y ∈ ((↑) : T → X) '' ({x} : Set T) := by
        rw [← hWsingleton]
        exact ⟨hy.1, ⟨⟨y, hy.2⟩, rfl⟩⟩
      rcases hyImage with ⟨z, hz, rfl⟩
      simpa using congrArg Subtype.val hz
    · intro hy
      subst hy
      have hxImage : (x : X) ∈ ((↑) : T → X) '' ({x} : Set T) := ⟨x, by simp, rfl⟩
      have hxWT' : (x : X) ∈ W ∩ Set.range ((↑) : T → X) := by
        rw [hWsingleton]
        exact hxImage
      exact ⟨hxWT'.1, x.2⟩
  have hpiece_eq : W ∩ S i = ({(x : X)} : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyWT : y ∈ W ∩ T := by
        refine ⟨hy.1, ?_⟩
        rw [hT_eq]
        exact Set.mem_iUnion.2 ⟨i, hy.2⟩
      simpa [hWT] using hyWT
    · intro y hy
      have hyx : y = x := by simpa using hy
      subst hyx
      have hxWT : (x : X) ∈ W ∩ T := by
        rw [hWT]
        simp
      exact ⟨hxWT.1, hxi⟩
  have hxLoc : IsLocallyClosed ({(x : X)} : Set X) := by
    rw [← hpiece_eq]
    exact hW.inter (hS i)
  show x.1 ∈ closedPoints X
  simpa [mem_closedPoints_iff] using
    (isClosed_singleton_of_isLocallyClosed_singleton hxLoc : IsClosed ({(x : X)} : Set X))

/-- Lemma 5.18.5: if `X` is Jacobson and `T ⊆ X` is locally constructible on `X` (equivalently,
locally on `X` a union of locally closed subsets), then the subspace `T` is Jacobson. -/
theorem jacobsonSpace_subtype_of_isLocallyConstructible
    [JacobsonSpace X] {T : Set X} (hT : IsLocallyConstructible T) :
    JacobsonSpace T := by
  -- Follow the source proof via property (*): every nonempty locally closed subset of `T`
  -- contains a point closed in the ambient space `X`.
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨U, hxU, hU, hUT⟩ := hT x
  have hxUmem : (x : X) ∈ U := mem_of_mem_nhds hxU
  -- Compare the open neighborhood of `x` inside `T` with the ambient trace `U ↓∩ T`.
  let V : Opens T := ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val⟩
  let eV : V ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp [V])).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.2⟩, rfl⟩)
  let eU : (U ↓∩ T) ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp)).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let e : V ≃ₜ U ↓∩ T := eV.trans eU.symm
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  haveI : JacobsonSpace (U ↓∩ T) := jacobsonSpace_subtype_of_isConstructible_aux hUT
  have hVJacobson : JacobsonSpace V := JacobsonSpace.of_isOpenEmbedding e.isOpenEmbedding
  -- Restrict `Z` to this neighborhood, obtain a closed point there, then transport it back to `T`
  -- and finally to `X`.
  have hZV_nonempty : ((V : Set T) ↓∩ Z).Nonempty := ⟨⟨x, hxUmem⟩, hx⟩
  have hZV' : IsLocallyClosed ((V : Set T) ↓∩ Z) := hZ'.preimage continuous_subtype_val
  obtain ⟨y, hyZ, hyclosed⟩ :=
    (jacobsonSpace_iff_locallyClosed.mp hVJacobson) ((V : Set T) ↓∩ Z) hZV_nonempty hZV'
  refine ⟨y, hyZ, ?_⟩
  have hyC : e y ∈ closedPoints (U ↓∩ T) := by
    exact (preimage_closedPoints_subset e.symm.injective e.symm.continuous) <| by
      simpa using hyclosed
  have hyUclosed : e y ∈ (U ↓∩ T) ↓∩ closedPoints U :=
    (closedPoints_subset_preimage_closedPoints_of_isConstructible_aux hUT) hyC
  have hpreU : ((↑) : U → X) ⁻¹' closedPoints X = closedPoints U :=
    hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
  have hyX' : ((e y : U) : X) ∈ closedPoints X := by
    have : (e y : U) ∈ ((↑) : U → X) ⁻¹' closedPoints X := by
      simpa [hpreU] using hyUclosed
    simpa using this
  have hyeq : ((e y : U) : X) = y := by
    have hEq : eU (e y) = eV y := by
      simp [e]
    have hEq' := congrArg (fun z : (U ∩ T : Set X) ↦ (z : X)) hEq
    simpa [eV, eU, V] using hEq'
  rw [mem_closedPoints_iff]
  convert (mem_closedPoints_iff.1 hyX').preimage continuous_subtype_val using 1
  ext w
  simp [Subtype.ext_iff, hyeq]

/-- If `X` is Jacobson and `T ⊆ X` is locally constructible on `X`, then every closed point of the
subspace `T` is a closed point of `X`. -/
theorem closedPoints_subset_preimage_closedPoints_of_isLocallyConstructible
    [JacobsonSpace X] {T : Set X} (hT : IsLocallyConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  obtain ⟨U, hxU, hU, hUT⟩ := hT x
  have hxUmem : (x : X) ∈ U := mem_of_mem_nhds hxU
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  haveI : JacobsonSpace (U ↓∩ T) := jacobsonSpace_subtype_of_isConstructible_aux hUT
  -- Reuse the same local chart as above and push the closed-point statement through it.
  let V : Opens T := ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val⟩
  let eV : V ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp [V])).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.2⟩, rfl⟩)
  let eU : (U ↓∩ T) ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp)).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let e : V ≃ₜ U ↓∩ T := eV.trans eU.symm
  have hxV : (⟨x, hxUmem⟩ : V) ∈ closedPoints V := by
    rw [mem_closedPoints_iff]
    convert (mem_closedPoints_iff.1 hx).preimage continuous_subtype_val using 1
    ext w
    simp [Subtype.ext_iff]
  have hxC : e ⟨x, hxUmem⟩ ∈ closedPoints (U ↓∩ T) := by
    exact (preimage_closedPoints_subset e.symm.injective e.symm.continuous) <| by
      simpa using hxV
  have hxUclosed : e ⟨x, hxUmem⟩ ∈ (U ↓∩ T) ↓∩ closedPoints U :=
    (closedPoints_subset_preimage_closedPoints_of_isConstructible_aux hUT) hxC
  have hpreU : ((↑) : U → X) ⁻¹' closedPoints X = closedPoints U :=
    hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
  have hxX' : ((e ⟨x, hxUmem⟩ : U) : X) ∈ closedPoints X := by
    have : (e ⟨x, hxUmem⟩ : U) ∈ ((↑) : U → X) ⁻¹' closedPoints X := by
      simpa [hpreU] using hxUclosed
    simpa using this
  have hxeq : ((e ⟨x, hxUmem⟩ : U) : X) = x := by
    have hEq : eU (e ⟨x, hxUmem⟩) = eV ⟨x, hxUmem⟩ := by
      simp [e]
    have hEq' := congrArg (fun z : (U ∩ T : Set X) ↦ (z : X)) hEq
    simpa [eV, eU, V] using hEq'
  show x.1 ∈ closedPoints X
  simpa [hxeq] using hxX'
