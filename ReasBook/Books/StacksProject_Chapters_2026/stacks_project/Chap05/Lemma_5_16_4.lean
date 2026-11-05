module

public import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_16_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for constructible neighborhoods detected by irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, local neighborhoods, and dense traces
  on irreducible closed subspaces;
- sampled owner declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  `TopologicalSpace.IrreducibleCloseds`,
  the canonical trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`;
- primitive vs. derived split: the primitive datum is the owner predicate `IsConstructible E`; the
  dense-trace criterion is derived local API on the canonical bridge object
  `Y : IrreducibleCloseds X`, so the numbered item should live as an owner theorem rather than as a
  parallel global wrapper.

Layer triage:
- `source-facing`: the Stacks criterion for when a constructible subset is a neighborhood of a
  point;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: dense traces on `IrreducibleCloseds X` via `(Y : Set X) ↓∩ E`.
-/

-- Proof sketch: if `E ∈ 𝓝 x`, then its trace on any irreducible closed subspace through `x`
-- contains a neighborhood of `x` in that subspace, hence is dense there. Conversely, among closed
-- subsets through `x` on which the trace is not a neighborhood, choose a minimal one using
-- Noetherianity; prove it is irreducible, use the dense-trace hypothesis and the previous lemma
-- that a dense constructible subset of an irreducible Noetherian space contains a nonempty open,
-- and derive a contradiction.
omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: an ambient neighborhood of `x` restricts to a dense trace on every
irreducible closed subspace through `x`. -/
lemma dense_trace_of_mem_nhds {E : Set X} {x : X} (hEx : E ∈ 𝓝 x)
    (Y : IrreducibleCloseds X) (hxY : x ∈ Y) :
    Dense ((Y : Set X) ↓∩ E) := by
  -- Pull the ambient neighborhood back to the irreducible closed subspace.
  have hTraceNhds : ((Y : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxY⟩ : Y) := by
    simpa using (preimage_coe_mem_nhds_subtype.2 (nhdsWithin_le_nhds hEx))
  rcases mem_nhds_iff.mp hTraceNhds with ⟨U, hU_subset, hU_open, hxU⟩
  letI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
  -- Any nonempty open subset of an irreducible space is dense.
  exact Dense.mono hU_subset (hU_open.dense ⟨⟨x, hxY⟩, hxU⟩)

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: a neighborhood of the trace on a smaller closed subspace can be
lifted to an ambient open neighborhood whose restriction still lands in the target trace. -/
lemma trace_mem_nhds_parent_of_trace_mem_nhds_closed {E : Set X} {A Y : Closeds X}
    (hAY : A ≤ Y) {x : X} (hxA : x ∈ A)
    (hA : ((A : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxA⟩ : A)) :
    ∃ V : Opens Y, (⟨x, hAY hxA⟩ : Y) ∈ V ∧
      (V : Set Y) ∩ ((Y : Set X) ↓∩ (A : Set X)) ⊆ ((Y : Set X) ↓∩ E) := by
  -- Realize the neighborhood on `A` as the pullback of an ambient neighborhood in `X`.
  have hA' :=
    (mem_nhds_subtype (A : Set X) ⟨x, hxA⟩ (((A : Set X) ↓∩ E) : Set A)).1 hA
  rcases hA' with ⟨u, hu, hpre⟩
  rcases mem_nhds_iff.mp hu with ⟨s, hs_subset, hs_open, hxs⟩
  let V : Opens Y := ⟨(Y : Set X) ↓∩ s, hs_open.preimage continuous_subtype_val⟩
  refine ⟨V, ?_, ?_⟩
  · -- The lifted ambient open set still contains `x`.
    simpa [V] using hxs
  · -- Points of `V` lying in `A` map back into the trace on `A`, hence into `E`.
    intro y hy
    rcases hy with ⟨hyV, hyA⟩
    have hys : y.1 ∈ s := by
      simpa [V] using hyV
    have hyA' : y.1 ∈ A := by
      simpa [Set.mem_preimage, Set.mem_inter_iff] using hyA
    have hmemU : (⟨y.1, hyA'⟩ : A) ∈ Subtype.val ⁻¹' u := by
      change y.1 ∈ u
      exact hs_subset hys
    have hmemTrace : (⟨y.1, hyA'⟩ : A) ∈ ((A : Set X) ↓∩ E) := hpre hmemU
    simpa [Set.mem_preimage, Set.mem_inter_iff] using hmemTrace

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: removing an open subtrace from a closed subspace leaves a proper
closed complement inside the ambient space. -/
lemma proper_closed_of_open_trace_complement (Y : Closeds X) (U : Opens Y)
    (hU_nonempty : (U : Set Y).Nonempty) :
    ∃ A : Closeds X, A < Y ∧ ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
  -- Build the closed complement in the ambient space as the image of the complement inside `Y`.
  let Aset : Set X := (Subtype.val : Y → X) '' ((U : Set Y)ᶜ)
  have hAclosed : IsClosed Aset :=
    Y.2.isClosedMap_subtype_val _ U.2.isClosed_compl
  let A : Closeds X := ⟨Aset, hAclosed⟩
  have hAY : (A : Set X) ⊆ Y := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hTrace : ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
    -- The image of the closed complement inside `Y` is exactly that complement.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, hzEq⟩
      have hzEq' : z = y := by
        apply Subtype.ext
        simpa using hzEq
      simpa [hzEq'] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hAneY : A ≠ Y := by
    -- A point of the nonempty open subset witnesses that the complement is proper.
    intro hAYeq
    have hUnivEq : (Set.univ : Set Y) = (U : Set Y)ᶜ := by
      calc
        (Set.univ : Set Y) = ((Y : Set X) ↓∩ (A : Set X)) := by
          ext y
          simp [hAYeq]
        _ = (U : Set Y)ᶜ := hTrace
    obtain ⟨y, hyU⟩ := hU_nonempty
    have hyCompl : y ∈ (U : Set Y)ᶜ := by
      simpa [hUnivEq] using (show y ∈ (Set.univ : Set Y) from trivial)
    exact hyCompl hyU
  exact ⟨A, lt_of_le_of_ne hAY hAneY, hTrace⟩

/-- Lemma 5.16.4: for a constructible subset `E` of a Noetherian topological space `X`, `E` is a
neighborhood of `x` if and only if for every irreducible closed subset `Y` of `X` containing `x`,
the trace of `E` on the subspace `Y` is dense in `Y`. -/
theorem IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace
    {E : Set X} (hE : IsConstructible E) {x : X} :
    E ∈ 𝓝 x ↔
      ∀ Y : IrreducibleCloseds X, x ∈ Y →
        Dense ((Y : Set X) ↓∩ E) := by
  constructor
  · intro hEx Y hxY
    -- Restrict the ambient neighborhood to the irreducible closed trace.
    exact dense_trace_of_mem_nhds hEx Y hxY
  · intro hDense
    -- Follow the source proof by induction on closed subsets through `x`.
    have hTraceNhds :
        ∀ Y : Closeds X, ∀ hxY : x ∈ Y, ((Y : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxY⟩ : Y) := by
      intro Y
      induction Y using WellFoundedLT.induction with
      | ind Y ih =>
          intro hxY
          by_cases hYirred : IsIrreducible (Y : Set X)
          · -- In the irreducible case, use the dense-trace hypothesis and split off an open piece.
            let Z : IrreducibleCloseds X := ⟨(Y : Set X), hYirred, Y.2⟩
            have hDenseY : Dense ((Y : Set X) ↓∩ E) := by
              simpa [Z] using hDense Z hxY
            rcases hE.exists_nonemptyOpen_subset_trace_or_not_dense Z with
              hOpen | hNotDense
            · rcases hOpen with ⟨U, hU_nonempty, hU_subset⟩
              by_cases hxU : (⟨x, hxY⟩ : Y) ∈ U
              · -- If the open trace already contains `x`, it is the desired neighborhood.
                exact mem_nhds_iff.2 ⟨U, hU_subset, U.2, hxU⟩
              · -- Otherwise remove that open piece and appeal to induction on the closed complement.
                obtain ⟨A, hAYlt, hAtrace⟩ :=
                  proper_closed_of_open_trace_complement Y U hU_nonempty
                have hxA : x ∈ A := by
                  have hxAtrace : (⟨x, hxY⟩ : Y) ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                    rw [hAtrace]
                    exact hxU
                  simpa [Set.mem_preimage, Set.mem_inter_iff] using hxAtrace
                have hA_nhds :
                    ((A : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxA⟩ : A) :=
                  ih A hAYlt hxA
                obtain ⟨V, hxV, hV_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) hAYlt.le hxA hA_nhds
                have hUnionSubset :
                    (U : Set Y) ∪ (V : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  rcases hy with hyU | hyV
                  · exact hU_subset hyU
                  · by_cases hyU : y ∈ (U : Set Y)
                    · exact hU_subset hyU
                    · have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                        rw [hAtrace]
                        exact hyU
                      exact hV_subset ⟨hyV, hyA⟩
                exact mem_nhds_iff.2 ⟨(U : Set Y) ∪ (V : Set Y), hUnionSubset, U.2.union V.2,
                  Or.inr hxV⟩
            · exact False.elim (hNotDense hDenseY)
          · -- If the closed subset is reducible, glue the smaller closed pieces through `x`.
            have hYnonempty : ((Y : Set X) : Set X).Nonempty := ⟨x, hxY⟩
            have hYnotPreirred : ¬ IsPreirreducible (Y : Set X) := by
              intro hYpreirred
              exact hYirred ⟨hYnonempty, hYpreirred⟩
            simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hYnotPreirred
            obtain ⟨Z₁, Z₂, hZ₁_closed, hZ₂_closed, hY_subset, hZ₁_proper, hZ₂_proper⟩ :=
              hYnotPreirred
            lift Z₁ to Closeds X using hZ₁_closed
            lift Z₂ to Closeds X using hZ₂_closed
            by_cases hxZ₁ : x ∈ Z₁
            · by_cases hxZ₂ : x ∈ Z₂
              · -- If `x` lies in both pieces, intersect the two induced neighborhoods.
                have hA₁_nhds :
                    (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₁ : Closeds X) by exact ⟨hxY, hxZ₁⟩⟩ :
                        (Y ⊓ Z₁ : Closeds X)) :=
                  ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper) ⟨hxY, hxZ₁⟩
                have hA₂_nhds :
                    (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₂ : Closeds X) by exact ⟨hxY, hxZ₂⟩⟩ :
                        (Y ⊓ Z₂ : Closeds X)) :=
                  ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper) ⟨hxY, hxZ₂⟩
                obtain ⟨V₁, hxV₁, hV₁_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₁⟩ hA₁_nhds
                obtain ⟨V₂, hxV₂, hV₂_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₂⟩ hA₂_nhds
                have hInterSubset :
                    (V₁ : Set Y) ∩ (V₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hyCover with hyZ₁ | hyZ₂
                  · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                    exact hV₁_subset ⟨hy.1, hyA₁⟩
                  · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                    exact hV₂_subset ⟨hy.2, hyA₂⟩
                exact mem_nhds_iff.2 ⟨(V₁ : Set Y) ∩ (V₂ : Set Y), hInterSubset, V₁.2.inter V₂.2,
                  ⟨hxV₁, hxV₂⟩⟩
              · -- If `x` misses the second piece, its complement is already a neighborhood.
                have hA₁_nhds :
                    (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₁ : Closeds X) by exact ⟨hxY, hxZ₁⟩⟩ :
                        (Y ⊓ Z₁ : Closeds X)) :=
                  ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper) ⟨hxY, hxZ₁⟩
                obtain ⟨V₁, hxV₁, hV₁_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₁⟩ hA₁_nhds
                let W₂ : Opens Y :=
                  ⟨(((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X))ᶜ),
                    by
                      simpa using
                        ((Y ⊓ Z₂ : Closeds X).2.isOpen_compl.preimage continuous_subtype_val)⟩
                have hxW₂ : (⟨x, hxY⟩ : Y) ∈ W₂ := by
                  simp [W₂, Set.mem_preimage, Set.mem_inter_iff, hxY, hxZ₂]
                have hInterSubset :
                    (V₁ : Set Y) ∩ (W₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hy with ⟨hyV₁, hyW₂⟩
                  rcases hyCover with hyZ₁ | hyZ₂
                  · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                    exact hV₁_subset ⟨hyV₁, hyA₁⟩
                  · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                    exact False.elim (hyW₂ hyA₂)
                exact mem_nhds_iff.2 ⟨(V₁ : Set Y) ∩ (W₂ : Set Y), hInterSubset, V₁.2.inter W₂.2,
                  ⟨hxV₁, hxW₂⟩⟩
            · -- The cover forces `x` into the second piece, so the previous argument is symmetric.
              have hxZ₂ : x ∈ Z₂ := by
                have hxCover : x ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset hxY
                rcases hxCover with hxZ₁' | hxZ₂
                · exact False.elim (hxZ₁ hxZ₁')
                · exact hxZ₂
              have hA₂_nhds :
                  (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) ∈
                    𝓝 (⟨x, show x ∈ (Y ⊓ Z₂ : Closeds X) by exact ⟨hxY, hxZ₂⟩⟩ :
                      (Y ⊓ Z₂ : Closeds X)) :=
                ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper) ⟨hxY, hxZ₂⟩
              obtain ⟨V₂, hxV₂, hV₂_subset⟩ :=
                trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                  ⟨hxY, hxZ₂⟩ hA₂_nhds
              let W₁ : Opens Y :=
                ⟨(((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X))ᶜ),
                  by
                    simpa using
                      ((Y ⊓ Z₁ : Closeds X).2.isOpen_compl.preimage continuous_subtype_val)⟩
              have hxW₁ : (⟨x, hxY⟩ : Y) ∈ W₁ := by
                simp [W₁, Set.mem_preimage, Set.mem_inter_iff, hxY, hxZ₁]
              have hInterSubset :
                  (W₁ : Set Y) ∩ (V₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                intro y hy
                have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                rcases hy with ⟨hyW₁, hyV₂⟩
                rcases hyCover with hyZ₁ | hyZ₂
                · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                    simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                  exact False.elim (hyW₁ hyA₁)
                · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                    simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                  exact hV₂_subset ⟨hyV₂, hyA₂⟩
              exact mem_nhds_iff.2 ⟨(W₁ : Set Y) ∩ (V₂ : Set Y), hInterSubset, W₁.2.inter V₂.2,
                ⟨hxW₁, hxV₂⟩⟩
    -- Apply the closed-subspace induction to the universal closed subset and unwrap the subtype.
    have hTopNhds :
        ((((⊤ : Closeds X) : Set X) ↓∩ E) : Set (⊤ : Closeds X)) ∈
          𝓝 (⟨x, show x ∈ (⊤ : Closeds X) by trivial⟩ : (⊤ : Closeds X)) :=
      hTraceNhds ⊤ (by trivial)
    have hWithin : E ∈ 𝓝[(Set.univ : Set X)] x := by
      simpa using (preimage_coe_mem_nhds_subtype.1 hTopNhds)
    simpa using hWithin

end

end Topology
