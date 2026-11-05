module

public import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_12_13
import stacks_project.Chap05.Lemma_5_15_15

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: first use `IsConstructible.isFiniteUnionOfLocallyClosed` on `E`, then apply the
-- earlier irreducible-space theorem that a finite union of locally closed subsets has dense trace
-- on `Z` exactly when it contains an open dense subset of `Z`.
/-- A constructible subset has, on each irreducible closed trace, either a nonempty open subtrace
or a non-dense trace. -/
theorem IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense {E : Set X}
    (hE : IsConstructible E) (Z : IrreducibleCloseds X) :
    (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
      ¬ Dense ((Z : Set X) ↓∩ E) := by
  have hE_lc : IsFiniteUnionOfLocallyClosed E := hE.isFiniteUnionOfLocallyClosed
  letI : Nonempty Z := by
    rcases Z.isIrreducible.nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  by_cases hDense : Dense (((Z : Set X) ↓∩ E) : Set Z)
  · left
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (Z.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
        hE_lc).2 hDense
    exact ⟨U, hU_dense.nonempty, hU_subset⟩
  · exact Or.inr hDense

end

end Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: the trace of `A ∩ E` inside `Y` is the image of the trace of `E`
inside `A` under the canonical inclusion `A → Y`. -/
lemma image_trace_inclusion_eq_trace {E : Set X} {A Y : Closeds X}
    (hAY : (A : Set X) ⊆ Y) :
    ((inclusion hAY) '' ((((A : Set X) ↓∩ E) : Set A)) : Set Y) =
      ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  -- Unpack both sides pointwise and identify the same underlying ambient point.
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using And.intro a.2 ha
  · intro hy
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
    refine ⟨⟨y.1, hy.1⟩, hy.2, ?_⟩
    ext
    rfl

/-- Helper for Lemma 5.16.3: a constructible trace on a smaller closed subset remains
constructible after pushing it into the ambient closed subspace. -/
lemma constructible_trace_image_of_smaller_closed {E : Set X} {A Y : Closeds X}
    (hAY : (A : Set X) ⊆ Y) (hA : IsConstructible ((A : Set X) ↓∩ E)) :
    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  -- Push forward along the closed embedding `A → Y` and rewrite the image as the expected trace.
  have hClosedEmbedding : IsClosedEmbedding (inclusion hAY : A → Y) :=
    Topology.IsClosedEmbedding.inclusion hAY (A.2.preimage continuous_subtype_val)
  have hImage :
      IsConstructible ((inclusion hAY) '' ((((A : Set X) ↓∩ E) : Set A)) : Set Y) :=
    hA.image_of_isClosedEmbedding hClosedEmbedding
      (isRetrocompact_of_noetherianSpace ((Set.range (inclusion hAY : A → Y))ᶜ))
  simpa [image_trace_inclusion_eq_trace (E := E) hAY] using hImage

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: removing a nonempty open subset from a closed subspace produces a
proper closed subset of the ambient space whose trace in the original subspace is the complement
of that open subset. -/
lemma proper_closed_below_of_open_complement (Y : Closeds X) (U : Opens Y)
    (hU_nonempty : (U : Set Y).Nonempty) :
    ∃ A : Closeds X, A < Y ∧ ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
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
    -- A point of the nonempty open `U` witnesses that the complement is proper.
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

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: a non-dense trace is already supported on a proper closed subset of
the ambient closed subspace. -/
lemma proper_closed_below_of_not_dense_trace {E : Set X} (Y : Closeds X)
    (hNotDense : ¬ Dense (((Y : Set X) ↓∩ E) : Set Y)) :
    ∃ A : Closeds X, A < Y ∧
      ((Y : Set X) ↓∩ E) = ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  let T : Set Y := ((Y : Set X) ↓∩ E)
  let Aset : Set X := (Subtype.val : Y → X) '' closure T
  have hAclosed : IsClosed Aset := Y.2.isClosedMap_subtype_val _ isClosed_closure
  let A : Closeds X := ⟨Aset, hAclosed⟩
  have hAY : (A : Set X) ⊆ Y := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hClosureTrace : ((Y : Set X) ↓∩ (A : Set X)) = closure T := by
    -- By construction, `A` is the ambient image of the closure of the trace inside `Y`.
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
  have hTraceEq :
      T = ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
    -- Every point of the trace lies in its closure, so intersecting with `A` does not change it.
    ext y
    constructor
    · intro hy
      have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
        rw [hClosureTrace]
        exact subset_closure hy
      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy hyA ⊢
      exact ⟨hyA, hy⟩
    · intro hy
      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
      exact hy.2
  have hAneY : A ≠ Y := by
    -- If `A = Y`, then the closure of the trace is all of `Y`, contradicting non-density.
    intro hAYeq
    have hClosureUniv : closure T = (Set.univ : Set Y) := by
      calc
        closure T = ((Y : Set X) ↓∩ (A : Set X)) := hClosureTrace.symm
        _ = (Set.univ : Set Y) := by
          ext y
          simp [hAYeq]
    exact hNotDense (dense_iff_closure_eq.2 hClosureUniv)
  exact ⟨A, lt_of_le_of_ne hAY hAneY, by simpa [T] using hTraceEq⟩

/-
Domain-style sampling for constructible subsets detected on irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, tested by their traces on
  irreducible closed subspaces;
- inspected declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  the canonical subtype-trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`.

Layer triage:
- `source-facing`: the Stacks Project criterion for constructibility via traces on irreducible
  closed subsets;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: the bundled irreducible closed subspace `Z : IrreducibleCloseds X` together with
  the canonical subtype trace `(Z : Set X) ↓∩ E`.

Primitive data is the ambient Noetherian topology together with the owner predicate
`IsConstructible E`. The finite-union-of-locally-closed decomposition of a trace and the
nonempty-open trace alternative are both derived API, supplied respectively by
`IsConstructible.isFiniteUnionOfLocallyClosed` and the owner-facing theorem
`IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. The bundled irreducible closed
subspaces and the subtype-trace notation are the canonical bridge/view API, so the numbered item
should reuse that owner-facing theorem rather than carrying a parallel forward-direction argument.
-/

-- Proof sketch: the forward implication is the owner-facing theorem
-- `IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. For the converse, argue by
-- Noetherian induction on closed subsets whose trace is not constructible, reduce to the
-- irreducible case, and use the stated dichotomy to contradict minimality.
/-- Lemma 5.16.3: in a Noetherian topological space, a subset `E` is constructible if and only if
for every irreducible closed subset `Z`, the trace of `E` on `Z` either contains a nonempty open
subset of `Z` or is not dense in `Z`. -/
theorem isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense
    (E : Set X) :
    IsConstructible E ↔
      ∀ Z : IrreducibleCloseds X,
        (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
          ¬ Dense ((Z : Set X) ↓∩ E) := by
  constructor
  · intro hE Z
    exact hE.exists_nonemptyOpen_subset_trace_or_not_dense Z
  · intro hTrace
    -- Execute the textbook minimal-counterexample proof as well-founded induction on closed sets.
    have hClosedTrace : ∀ Y : Closeds X, IsConstructible ((Y : Set X) ↓∩ E) := by
      intro Y
      induction Y using WellFoundedLT.induction with
      | ind Y ih =>
          by_cases hYempty : (Y : Set X) = ∅
          · -- The empty closed subspace has empty trace.
            have hYbot : Y = ⊥ := Closeds.ext (by simpa using hYempty)
            subst hYbot
            have hEmptyTrace : ((((⊥ : Closeds X) : Set X) ↓∩ E) : Set (⊥ : Closeds X)) = ∅ := by
              ext x
              exact False.elim x.2
            rw [hEmptyTrace]
            exact IsConstructible.empty
          · by_cases hYirred : IsIrreducible (Y : Set X)
            · -- In the irreducible case, use the stated dichotomy on the trace.
              have hYtrace :
                  (∃ U : Opens Y, (U : Set Y).Nonempty ∧ (U : Set Y) ⊆ (Y : Set X) ↓∩ E) ∨
                    ¬ Dense ((Y : Set X) ↓∩ E) := by
                let Z : IrreducibleCloseds X := ⟨(Y : Set X), hYirred, Y.2⟩
                simpa [Z] using hTrace Z
              rcases hYtrace with ⟨U, hU_nonempty, hU_subset⟩ | hY_not_dense
              · -- Split the trace into the given open piece and the constructible remainder.
                obtain ⟨A, hAYlt, hAtrace⟩ :=
                  proper_closed_below_of_open_complement Y U hU_nonempty
                have hA_constructible : IsConstructible ((A : Set X) ↓∩ E) := ih A hAYlt
                have hA_in_Y :
                    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) :=
                  constructible_trace_image_of_smaller_closed hAYlt.le hA_constructible
                letI : NoetherianSpace Y := TopologicalSpace.NoetherianSpace.set (Y : Set X)
                have hU_constructible : IsConstructible (U : Set Y) :=
                  (isRetrocompact_of_noetherianSpace (U : Set Y)).isConstructible U.2
                have hTraceUnion :
                    ((Y : Set X) ↓∩ E) =
                      (U : Set Y) ∪ ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
                  ext y
                  constructor
                  · intro hy
                    by_cases hyU : y ∈ (U : Set Y)
                    · exact Or.inl hyU
                    · right
                      have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                        rw [hAtrace]
                        exact hyU
                      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy hyA ⊢
                      exact ⟨hyA, hy⟩
                  · rintro (hyU | hyA)
                    · exact hU_subset hyU
                    · simp only [Set.mem_preimage, Set.mem_inter_iff] at hyA
                      exact hyA.2
                rw [hTraceUnion]
                exact hU_constructible.union hA_in_Y
              · -- A non-dense trace is already carried by a proper closed subset.
                obtain ⟨A, hAYlt, hTraceEq⟩ :=
                  proper_closed_below_of_not_dense_trace (E := E) Y hY_not_dense
                have hA_constructible : IsConstructible ((A : Set X) ↓∩ E) := ih A hAYlt
                have hA_in_Y :
                    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) :=
                  constructible_trace_image_of_smaller_closed hAYlt.le hA_constructible
                rw [hTraceEq]
                exact hA_in_Y
            · -- If the closed subset is reducible, decompose it into two proper closed pieces.
              have hYnonempty : ((Y : Set X) : Set X).Nonempty :=
                Set.nonempty_iff_ne_empty.mpr hYempty
              have hYnotPreirred : ¬ IsPreirreducible (Y : Set X) := by
                intro hYpreirred
                exact hYirred ⟨hYnonempty, hYpreirred⟩
              simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hYnotPreirred
              obtain ⟨Z₁, Z₂, hZ₁_closed, hZ₂_closed, hY_subset, hZ₁_proper, hZ₂_proper⟩ :=
                hYnotPreirred
              lift Z₁ to Closeds X using hZ₁_closed
              lift Z₂ to Closeds X using hZ₂_closed
              have hYZ₁_constructible : IsConstructible (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) :=
                ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper)
              have hYZ₂_constructible : IsConstructible (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) :=
                ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper)
              have hYZ₁_in_Y :
                  IsConstructible ((Y : Set X) ↓∩ ((((Y ⊓ Z₁ : Closeds X) : Set X)) ∩ E)) :=
                constructible_trace_image_of_smaller_closed (E := E) inf_le_left
                  hYZ₁_constructible
              have hYZ₂_in_Y :
                  IsConstructible ((Y : Set X) ↓∩ ((((Y ⊓ Z₂ : Closeds X) : Set X)) ∩ E)) :=
                constructible_trace_image_of_smaller_closed (E := E) inf_le_left
                  hYZ₂_constructible
              have hTraceUnion :
                  ((Y : Set X) ↓∩ E) =
                    ((Y : Set X) ↓∩ ((((Y ⊓ Z₁ : Closeds X) : Set X)) ∩ E)) ∪
                      ((Y : Set X) ↓∩ ((((Y ⊓ Z₂ : Closeds X) : Set X)) ∩ E)) := by
                ext y
                constructor
                · intro hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hyCover with hyZ₁ | hyZ₂
                  · left
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy ⊢
                    exact ⟨⟨y.2, hyZ₁⟩, hy⟩
                  · right
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy ⊢
                    exact ⟨⟨y.2, hyZ₂⟩, hy⟩
                · rintro (hy | hy) <;>
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
                  · exact hy.2
                  · exact hy.2
              rw [hTraceUnion]
              exact hYZ₁_in_Y.union hYZ₂_in_Y
    -- Apply the closed-subspace induction to the universal closed subset and unwrap the subtype.
    have hTop : IsConstructible (((Set.univ : Set X) ↓∩ E) : Set (Set.univ : Set X)) := by
      simpa using hClosedTrace ⊤
    exact
      (isConstructible_preimage_iff_of_isOpenEmbedding isOpen_univ.isOpenEmbedding_subtypeVal
        (by simp [isRetrocompact_of_noetherianSpace]) (by simp)).1 hTop

end
