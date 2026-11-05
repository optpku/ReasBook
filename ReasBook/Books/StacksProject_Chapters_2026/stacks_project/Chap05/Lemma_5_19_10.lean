module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sober
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_16_4
import stacks_project.Chap05.Lemma_5_16_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

/-
Domain-style sampling for constructible subsets stable under specialization/generalization:
- primary domain: constructible subsets in Noetherian quasi-sober spaces, together with the
  canonical specialization/generalization stability predicates;
- inspected owner declarations:
  `Topology.IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace`,
  `isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open`,
  `StableUnderSpecialization`,
  `StableUnderGeneralization`;
- best owner abstraction: the source-facing conclusions `IsClosed E` and `IsOpen E`, supported by
  the canonical owner predicate `Topology.IsConstructible` and the stability predicates from
  `Topology.Inseparable`;
- primitive data: only the constructible subset `E` and its stability under specialization or
  generalization;
- derived API: openness/closedness of `E`, obtained through irreducible closed traces and the
  complement bridge `StableUnderSpecialization.compl`.

Layer triage:
- `source-facing`: Lemma 5.19.10, asserting that constructible subsets stable under specialization
  are closed and those stable under generalization are open;
- `core/canonical`: `Topology.IsConstructible`, `StableUnderSpecialization`, and
  `StableUnderGeneralization`;
- `bridge/view`: the irreducible-closed trace criteria from Lemmas `5.16.4` and `5.16.5`.

There is no earlier exact theorem owner for this statement in the chapter, so the public surface
here should stay source-facing. The redundant `T0Space` binder is not primitive data for either
part and is removed.
-/

private theorem isOpen_of_isConstructible_of_stableUnderGeneralization_aux {E : Set X}
    (hE : IsConstructible E) (hE_gen : StableUnderGeneralization E) : IsOpen E := by
  classical
  rw [isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open]
  intro Y
  by_cases hYE : ((Y : Set X) ↓∩ E : Set Y) = ∅
  · exact Or.inl hYE
  · right
    let EY : Set Y := (Y : Set X) ↓∩ E
    let hY_closedEmb := Y.isClosed.isClosedEmbedding_subtypeVal
    letI : NoetherianSpace Y := IsInducing.subtypeVal.noetherianSpace
    letI : QuasiSober Y := hY_closedEmb.quasiSober
    have hYE_constructible : IsConstructible EY := by
      simpa [EY] using
        hE.preimage_of_isClosedEmbedding hY_closedEmb (NoetherianSpace.isCompact _)
    haveI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
    have hηE : genericPoint Y ∈ EY := by
      dsimp [EY]
      obtain ⟨y, hyE⟩ : EY.Nonempty := Set.nonempty_iff_ne_empty.mpr hYE
      exact hE_gen (by
        simpa [subtype_specializes_iff] using (genericPoint_specializes y : genericPoint Y ⤳ y))
        hyE
    have hYE_nhds : EY ∈ 𝓝 (genericPoint Y) := by
      refine (hYE_constructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace).2 ?_
      intro Z hηZ
      rw [Subtype.dense_iff]
      intro z hz
      have hη_closure :
          genericPoint Y ∈ closure ((Subtype.val : Z → Y) '' ((Subtype.val : Z → Y) ⁻¹' EY)) := by
        exact subset_closure ⟨⟨genericPoint Y, hηZ⟩, hηE, rfl⟩
      have hsubset :
          (Set.univ : Set Y) ⊆ closure ((Subtype.val : Z → Y) '' ((Subtype.val : Z → Y) ⁻¹' EY)) :=
        ((genericPoint_spec Y).mem_closed_set_iff isClosed_closure).1 hη_closure
      exact hsubset trivial
    rcases mem_nhds_iff.mp hYE_nhds with ⟨U, hU_subset, hU_open, hηU⟩
    refine ⟨⟨U, hU_open⟩, ⟨genericPoint Y, hηU⟩, ?_⟩
    simpa [EY] using hU_subset

-- Proof sketch: apply the constructible irreducible-closed criterion from Lemma `5.16.3` to the
-- trace on each irreducible closed subset, use the generic point provided by quasi-sobriety, and
-- then conclude openness of the complement by Lemma `5.16.5`.
/-- Lemma 5.19.10 (1): in a Noetherian sober topological space, a constructible subset stable under
specialization is closed. -/
theorem isClosed_of_isConstructible_of_stableUnderSpecialization {E : Set X}
    (hE : IsConstructible E) (hE_spec : StableUnderSpecialization E) : IsClosed E := by
  rw [← isOpen_compl_iff]
  exact isOpen_of_isConstructible_of_stableUnderGeneralization_aux hE.compl hE_spec.compl

-- Proof sketch: for each irreducible closed subset `Y`, if the trace `E ∩ Y` is nonempty then the
-- generic point of `Y` belongs to `E` by stability under generalization, so `E ∩ Y` is dense and
-- Lemma `5.16.3` yields a nonempty open trace; conclude by Lemma `5.16.5`.
/-- Lemma 5.19.10 (2): in a Noetherian sober topological space, a constructible subset stable under
generalization is open. -/
theorem isOpen_of_isConstructible_of_stableUnderGeneralization {E : Set X}
    (hE : IsConstructible E) (hE_gen : StableUnderGeneralization E) : IsOpen E :=
  isOpen_of_isConstructible_of_stableUnderGeneralization_aux hE hE_gen

end
