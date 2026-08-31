module

public import Mathlib.Topology.Constructible
import Mathlib.Data.Finite.Sum
import stacks_project.Chap05.Lemma_5_15_10
import stacks_project.Chap05.Lemma_5_15_11

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {E : Set X} {F : Set E}

/- Domain-style sampling for constructible subsets inside constructible subspaces:
- primary domain: constructible subsets, subtype inclusions, and the owner `Topology.IsConstructible`
  API for passing between a subspace and the ambient space;
- sampled canonical declarations:
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isClosedEmbedding`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isConstructible`,
  `Topology.IsConstructible.isRetrocompact`;
- best owner abstraction: the public statement should be the constructible image of the canonical
  map `Subtype.val : E → X`, not a separate global coercion wrapper;
- primitive-vs-derived split: the primitive data are the constructible ambient subspace `E` and
  the constructible subset `F ⊆ E`. The ambient subset `(F : Set X)` is derived from the owner
  map as `Subtype.val '' F`.

Layer triage:
- `source-facing`: Lemma 5.15.12, asserting that a constructible subset of a constructible
  subspace is constructible in the ambient space;
- `core/canonical`: `Topology.IsConstructible` together with image theorems for maps such as
  `Subtype.val`;
- `bridge/view`: the coercion `Set E → Set X`, which should be secondary to the image statement.
-/

/-- Helper for Lemma 5.15.12: a constructible subspace of a prespectral space is again
prespectral. -/
private theorem prespectralSpace_subtype_of_isConstructible {S : Set X}
    (hS : IsConstructible S) : PrespectralSpace S := by
  -- The subtype map of a retrocompact subset is spectral, so the compact-open basis descends.
  let hSpec : IsSpectralMap (Subtype.val : S → X) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hS.isRetrocompact
  exact PrespectralSpace.of_isInducing (Subtype.val : S → X) IsInducing.subtypeVal hSpec

/-- Helper for Lemma 5.15.12: a constructible subset is a finite union of locally closed pieces
`U \ V` with `U` and `V` open retrocompact. -/
private theorem exists_finite_iUnion_eq_retrocompact_open_sdiff {S : Set X}
    (hS : IsConstructible S) :
    ∃ ι : Type u, ∃ _ : Finite ι, ∃ Z : ι → Set X,
      (∀ i, ∃ U V : Set X,
        IsOpen U ∧ IsRetrocompact U ∧ IsOpen V ∧ IsRetrocompact V ∧ Z i = U \ V) ∧
      S = ⋃ i, Z i := by
  -- Work directly with the Boolean-closure definition so the generators stay retrocompact.
  change S ∈ BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} at hS
  refine BooleanSubalgebra.closure_sdiff_sup_induction
    (⟨
      fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩
    ⟩ : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U})
    (by simp) (by simp) ?_ ?_ S hS
  · intro U hU V hV
    -- A single generator difference already has the required form.
    refine ⟨PUnit, inferInstance, fun _ ↦ U \ V, ?_, ?_⟩
    · intro _
      exact ⟨U, V, hU.1, hU.2, hV.1, hV.2, rfl⟩
    · ext x
      simp
  · intro s hs t ht hs_ind ht_ind
    -- Finite unions are handled by concatenating the finite index sets.
    rcases hs_ind with ⟨ιs, hιs, Zs, hZs, rfl⟩
    rcases ht_ind with ⟨ιt, hιt, Zt, hZt, rfl⟩
    letI := hιs
    letI := hιt
    refine ⟨ιs ⊕ ιt, inferInstance, Sum.elim Zs Zt, ?_, ?_⟩
    · intro i
      cases i with
      | inl i => simpa using hZs i
      | inr i => simpa using hZt i
    · simp [iUnion_sum]

/-- Helper for Lemma 5.15.12: a constructible subset of a locally closed piece `U \ V` with `U`
and `V` open retrocompact has constructible image in the ambient space. -/
private theorem image_subtypeVal_of_retrocompact_open_sdiff {U V : Set X}
    (hU_open : IsOpen U) (hU_retro : IsRetrocompact U)
    (hV_open : IsOpen V) (hV_retro : IsRetrocompact V)
    {S : Set ↥(U \ V)} (hS : IsConstructible S) :
    IsConstructible (Subtype.val '' S) := by
  let i : ↥(U \ V) → U := Set.inclusion (show U \ V ⊆ U by intro x hx; exact hx.1)
  have hi_closed : IsClosedEmbedding i := by
    -- Inside `U`, the piece `U \ V` is closed because its complement is the open trace of `V`.
    refine Topology.IsClosedEmbedding.inclusion (show U \ V ⊆ U by intro x hx; exact hx.1) ?_
    have hOpen : IsOpen ((U : Set X) ↓∩ V) := by
      simpa [Subtype.preimage_coe_inter_self] using hV_open.preimage continuous_subtype_val
    simpa [Subtype.preimage_coe_inter_self, sdiff_eq, inter_assoc, inter_left_comm, inter_comm] using
      hOpen.isClosed_compl
  have hi_compl : IsRetrocompact (range i)ᶜ := by
    -- The complement of that closed embedding is the trace of the retrocompact open `V` on `U`.
    have : IsRetrocompact ((U : Set X) ↓∩ V) := by
      simpa [Subtype.preimage_coe_inter_self] using
        hV_retro.preimage_of_isOpenEmbedding hU_open.isOpenEmbedding_subtypeVal
    have hRangeCompl : (range i)ᶜ = ((U : Set X) ↓∩ V) := by
      ext x
      simp [i]
    rw [hRangeCompl]
    exact this
  have hSU : IsConstructible (i '' S) := hS.image_of_isClosedEmbedding hi_closed hi_compl
  have hOpenEmbedding : IsOpenEmbedding (Subtype.val : U → X) := hU_open.isOpenEmbedding_subtypeVal
  have hImageInX : IsConstructible ((Subtype.val : U → X) '' (i '' S)) :=
    hSU.image_of_isOpenEmbedding hOpenEmbedding (by simpa using hU_retro)
  -- Compose the closed-subspace and open-subspace images to recover the ambient image in `X`.
  simpa [i, Set.image_image] using hImageInX

/-- Lemma 5.15.12: in a topological space whose quasi-compact opens form a basis, equivalently
`[PrespectralSpace X]`, the image in `X` of a constructible subset of a constructible subspace `E`
is constructible. The canonical public surface uses the subtype inclusion `Subtype.val : E → X`
rather than a separate coercion wrapper. -/
theorem IsConstructible.image_subtypeVal_of_isConstructible
    (hF : IsConstructible F) (hE : IsConstructible E) :
    IsConstructible (Subtype.val '' F) := by
  -- Decompose the ambient constructible set `E` into finitely many locally closed pieces `U \ V`.
  obtain ⟨ι, hι, Z, hZ, hcover⟩ := exists_finite_iUnion_eq_retrocompact_open_sdiff hE
  letI := hι
  letI : PrespectralSpace E := prespectralSpace_subtype_of_isConstructible hE
  have hPiece :
      ∀ i, IsConstructible ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i)))) := by
    intro i
    obtain ⟨U, V, hU_open, hU_retro, hV_open, hV_retro, hZi_eq⟩ := hZ i
    have hZi_constructible : IsConstructible (Z i) := by
      -- Each cover piece is constructible because it is a difference of open retrocompact sets.
      simpa [hZi_eq] using
        (hU_retro.isConstructible hU_open).sdiff (hV_retro.isConstructible hV_open)
    have hEi : IsConstructible (E ↓∩ Z i) :=
      hZi_constructible.preimage_subtypeVal_of_isConstructible hE
    have hFi : IsConstructible ((E ↓∩ Z i) ↓∩ F) :=
      -- Restrict `F` from `E` to the constructible piece `E ∩ Z i`.
      hF.preimage_subtypeVal_of_isConstructible hEi
    have hZi_subset : Z i ⊆ E := by
      intro x hx
      rw [hcover]
      exact mem_iUnion_of_mem i hx
    let e : (E ↓∩ Z i) ≃ₜ Z i :=
      { toEquiv :=
          { toFun := fun x ↦ ⟨x.1.1, x.2⟩
            invFun := fun z ↦ ⟨⟨z.1, hZi_subset z.2⟩, z.2⟩
            left_inv := by
              intro x
              cases x with
              | mk x hx =>
                  cases x with
                  | mk x hxE => rfl
            right_inv := by
              intro z
              cases z with
              | mk z hz => rfl }
        continuous_toFun := by
          -- Both directions only forget or restore redundant subtype data.
          fun_prop
        continuous_invFun := by
          fun_prop }
    let e' : (E ↓∩ Z i) ≃ₜ ↥(U \ V) := e.trans (Homeomorph.ofEqSubtypes hZi_eq)
    have hFi' : IsConstructible (e' '' (((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i))) :=
      -- Transport the trace of `F` across the canonical identification with the ambient piece.
      hFi.image_of_isOpenEmbedding e'.isOpenEmbedding
        (by simpa using (IsRetrocompact.univ : IsRetrocompact (range e')))
    -- The reduced `U \ V` case now places this transported trace back inside `X`.
    simpa [e', e, Set.image_image] using
      image_subtypeVal_of_retrocompact_open_sdiff hU_open hU_retro hV_open hV_retro hFi'
  have hUnion :
      IsConstructible (⋃ i, ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i))))) :=
    IsConstructible.iUnion hPiece
  have hEq :
      (Subtype.val '' F) = ⋃ i, ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i)))) := by
    -- Reassemble the ambient image of `F` from the images of its traces on the finite cover.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyCover : y.1 ∈ ⋃ i, Z i := by
        simpa [hcover] using y.2
      rcases mem_iUnion.1 hyCover with ⟨i, hi⟩
      refine mem_iUnion.2 ⟨i, ?_⟩
      exact ⟨⟨y, hi⟩, hy, rfl⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
  rw [hEq]
  exact hUnion

end

end Topology
