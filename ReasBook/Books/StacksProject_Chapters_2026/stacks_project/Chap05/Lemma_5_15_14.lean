module

public import Mathlib.Topology.Constructible
import stacks_project.Chap05.Lemma_5_15_11
import stacks_project.Chap05.Lemma_5_15_12

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X]

/- Domain-style sampling for constructibility on finite constructible covers:
- primary domain: constructible subsets of prespectral spaces and their behavior under subtype
  restriction and re-embedding;
- sampled declarations:
  `Topology.IsConstructible.iUnion`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isConstructible`,
  `Topology.IsConstructible.image_subtypeVal_of_isConstructible`,
  `Subtype.image_preimage_val`;
- best owner abstraction: `Topology.IsConstructible` is the owner predicate; the finite-cover
  reconstruction is derived API built from the subtype pullback/image lemmas and finite union;
- primitive-vs-derived split:
  primitive data: the finite constructible family `Z`, the covering inclusion of `E`, and the
    constructible traces `Z i ↓∩ E`;
  derived API: the ambient pieces `Subtype.val '' (Z i ↓∩ E) = Z i ∩ E` and the reconstruction
    `⋃ i, Z i ∩ E = E`.

Layer triage:
- `source-facing`: Lemma 5.15.14, the finite constructible-cover locality statement;
- `core/canonical`: `Topology.IsConstructible`;
- `bridge/view`: the subtype inclusion `Subtype.val : Z i → X` together with
  `Subtype.image_preimage_val`.
-/

-- Proof sketch: apply Lemma `5.15.11` to restrict a constructible subset of `X` to each
-- constructible covering piece. Conversely, use Lemma `5.15.12` to view each constructible trace
-- as a constructible subset of `X`, then recover `E` as the finite union of those pieces over a
-- finite constructible cover of `E`.
/-- Lemma 5.15.14: in a space whose quasi-compact opens form a basis, equivalently
`[PrespectralSpace X]`, a subset `E ⊆ X` is
constructible iff its trace on each member of a finite constructible cover of `E` is constructible
in that member. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i)) {E : Set X}
    (hcover : E ⊆ ⋃ i, Z i) :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := by
  constructor
  · intro hE i
    exact hE.preimage_subtypeVal_of_isConstructible (hZ i)
  · intro hE
    have hUnion : IsConstructible (⋃ i, Z i ∩ E) :=
      IsConstructible.iUnion fun i ↦ by
        simpa [Subtype.image_preimage_val] using
          (hE i).image_subtypeVal_of_isConstructible (hZ i)
    have hcover' : (⋃ i, Z i) ∩ E = E := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨hcover hx, hx⟩
    simpa [← iUnion_inter, hcover'] using hUnion

/-- Textbook cover-of-`X` corollary of Lemma 5.15.14. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover_of_iUnion_eq_univ
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i))
    (hcover : (⋃ i, Z i) = (univ : Set X)) {E : Set X} :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := by
  refine isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover Z hZ ?_
  intro x hx
  simp [hcover]
