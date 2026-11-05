module

public import Mathlib.Topology.Sober
public import stacks_project.Chap05.FiniteUnionOfLocallyClosed
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for dense traces on irreducible subspaces:
- primary domain: irreducible subsets, generic points, dense traces, and finite unions of locally
  closed subsets;
- sampled canonical declarations:
  `IsGenericPoint.mem_open_set_iff`,
  `IsGenericPoint.mem_closed_set_iff`,
  `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`,
  `Set.preimage_val_eq_univ_of_subset`,
  `IsLocallyClosed.isOpen_preimage_val_closure`;
- best owner abstractions: `IsGenericPoint` owns the pointwise generic-point criterion, while
  `IsIrreducible` is the natural owner for the irreducible-subspace dense/open-dense dichotomy;
- primitive-vs-derived split: the primitive inputs are the irreducible set or generic point,
  together with the finite locally closed decomposition of `E`; the open dense trace is derived
  data and should be exposed via `Opens Z`, with the trace written through the canonical subtype
  notation `Z ↓∩ E` rather than raw subtype preimages.

Layer triage:
- `source-facing`: the irreducible-subspace dense/open-dense criterion;
- `core/canonical`: `IsIrreducible`, `IsGenericPoint`, and `Opens`;
- `bridge/view`: the canonical subtype trace `Z ↓∩ E` together with the finite locally closed
  decomposition supplied by `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`.
-/

-- Proof sketch: write `E ∩ Z` as a finite union of locally closed subsets of the irreducible
-- subspace `Z`; one dense locally closed piece is then open in its closure, hence yields an open
-- dense subset of `Z`.
/-- Helper for Lemma 5.15.15: a locally closed subset stays locally closed after restricting to a
subspace. -/
lemma trace_piece_isLocallyClosed {Z A : Set X} (hA : IsLocallyClosed A) :
    IsLocallyClosed (Z ↓∩ A) := by
  -- Pull the locally closed subset back along the subtype map `Z → X`.
  simpa using hA.preimage continuous_subtype_val

/-- Helper for Lemma 5.15.15: in an irreducible space, a dense finite union has a dense member. -/
lemma exists_dense_piece_of_dense_iUnion {Y : Type u} [TopologicalSpace Y] [IrreducibleSpace Y]
    {n : ℕ} {T : Fin n → Set Y} (hT_dense : Dense (⋃ i, T i)) :
    ∃ i, Dense (T i) := by
  classical
  let s : Finset (Set Y) := Finset.univ.image fun i ↦ closure (T i)
  have hs_cover : (univ : Set Y) ⊆ ⋃₀ (s : Set (Set Y)) := by
    -- Rewrite density of the union as a finite closed cover of the whole space by the closures.
    rw [← hT_dense.closure_eq, closure_iUnion_of_finite]
    simp [s]
  obtain ⟨W, hW_mem, hW_cover⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ Y) s
      (fun W hW ↦ by
        rcases Finset.mem_image.mp hW with ⟨i, -, rfl⟩
        exact isClosed_closure)
      hs_cover
  rcases Finset.mem_image.mp hW_mem with ⟨i, -, rfl⟩
  -- The chosen closure contains `univ`, so that piece is dense.
  have hTi_closure : closure (T i) = (univ : Set Y) :=
    Set.Subset.antisymm (subset_univ _) hW_cover
  have hTi_dense : Dense (T i) := dense_iff_closure_eq.2 hTi_closure
  exact ⟨i, hTi_dense⟩

/-- Helper for Lemma 5.15.15: a dense locally closed subset is already an open dense subset. -/
lemma exists_open_dense_subset_of_dense_isLocallyClosed {Y : Type u} [TopologicalSpace Y]
    {s : Set Y} (hs_dense : Dense s) (hs_lc : IsLocallyClosed s) :
    ∃ U : Opens Y, Dense (U : Set Y) ∧ (U : Set Y) ⊆ s := by
  have hs_open : IsOpen s := by
    -- A locally closed set is open in its closure, and density identifies that closure with `univ`.
    simpa [hs_dense.closure_eq] using hs_lc.isOpen_preimage_val_closure
  let U : Opens Y := ⟨s, hs_open⟩
  -- Package the set itself as the required open dense subset.
  exact ⟨U, by simpa [U] using hs_dense, subset_rfl⟩

/-- Lemma 5.15.15: if `Z` is irreducible and `E` is a finite union of locally closed subsets of
`X`, then `E ∩ Z` contains an open dense subset of `Z` if and only if `E ∩ Z` is dense in `Z`. -/
theorem IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} (hZ : IsIrreducible Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    (∃ U : Opens Z, Dense (U : Set Z) ∧ (U : Set Z) ⊆ Z ↓∩ E) ↔ Dense (Z ↓∩ E) := by
  constructor
  · rintro ⟨U, hU_dense, hU_subset⟩
    -- An open dense subtrace is in particular a dense subset of the whole trace.
    exact Dense.mono hU_subset hU_dense
  · intro hZE_dense
    classical
    letI : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    obtain ⟨n, S, hS_lc, hE_eq⟩ := hE.exists_eq_iUnion
    let T : Fin n → Set Z := fun i ↦ Z ↓∩ S i
    have hT_lc : ∀ i, IsLocallyClosed (T i) := by
      intro i
      -- Restrict each ambient locally closed piece to the irreducible subtype `Z`.
      exact trace_piece_isLocallyClosed (hS_lc i)
    have hT_dense : Dense (⋃ i, T i) := by
      -- Normalize the trace of the finite union into the union of the trace pieces.
      simpa [T, hE_eq] using hZE_dense
    obtain ⟨i, hTi_dense⟩ := exists_dense_piece_of_dense_iUnion hT_dense
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      exists_open_dense_subset_of_dense_isLocallyClosed hTi_dense (hT_lc i)
    refine ⟨U, hU_dense, ?_⟩
    -- The dense open piece sits inside one trace component, hence inside the full trace.
    exact hU_subset.trans <| by
      simpa [T, hE_eq] using (Set.subset_iUnion T i)

-- Proof sketch: if `ξ` is a generic point of `Z`, then membership `ξ ∈ E` is equivalent to the
-- trace `E ∩ Z` being dense in `Z`; combine the generic-point characterization of dense subsets of
-- an irreducible space with the locally closed decomposition of `E`.
/-- For a generic point `ξ` of `Z`, a finite union of locally closed subsets has dense trace on
`Z` exactly when `ξ` belongs to it. -/
theorem IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} {ξ : X} (hξ : IsGenericPoint ξ Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    Dense (Z ↓∩ E) ↔ ξ ∈ E := by
  let ξZ : Z := ⟨ξ, hξ.mem⟩
  have hξZ : IsGenericPoint ξZ (Set.univ : Set Z) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simpa [subtype_specializes_iff] using
      (hξ.specializes_iff_mem : ξ ⤳ (y : X) ↔ (y : X) ∈ Z)
  constructor
  · intro hDense
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (hξ.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed hE).2
        hDense
    haveI : Nonempty Z := ⟨ξZ⟩
    have hU_nonempty : (U : Set Z).Nonempty := hU_dense.nonempty
    have hξU : ξZ ∈ U := by
      exact (hξZ.mem_open_set_iff U.2).2 (by simpa using hU_nonempty)
    exact hU_subset hξU
  · intro hξE
    rw [Subtype.dense_iff]
    have hξ_closure : ξ ∈ closure (Z ∩ E) := subset_closure ⟨hξ.mem, hξE⟩
    simpa [Subtype.image_preimage_val] using
      (hξ.mem_closed_set_iff isClosed_closure).1 hξ_closure
