module

public import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_16_3
import stacks_project.Chap05.Lemma_5_16_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for openness detected on irreducible closed traces:
- primary domain: open and constructible subsets of Noetherian spaces, tested on irreducible closed
  subspaces;
- sampled owner declarations:
  `IsOpen`,
  `Topology.IsConstructible`,
  `isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense`,
  `Topology.IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace`,
  `TopologicalSpace.IrreducibleCloseds`;
- best owner abstraction: the numbered item stays source-facing on `IsOpen E`, while using
  `IsConstructible` and `IrreducibleCloseds` as the canonical owner and bridge layers;
- primitive vs. derived split: the primitive datum is only `IsOpen E`; constructibility and the
  pointwise dense-trace criterion are derived API supplied by Lemmas `5.16.3` and `5.16.4`, so
  this file should reuse those owners instead of introducing a parallel trace wrapper.

Layer triage:
- `source-facing`: the Stacks criterion for openness via irreducible closed traces;
- `core/canonical`: `IsOpen`, `Topology.IsConstructible`, and `TopologicalSpace.IrreducibleCloseds`;
- `bridge/view`: the canonical subtype trace notation `↓∩` together with the two previous chapter
  criteria on constructibility and neighborhoods.
-/

-- Proof sketch: if `E` is open, then its trace on any irreducible closed subset is itself an open
-- subset of that subspace, so the trace is either empty or already provides the required witness.
-- Conversely, reinterpret the empty case as non-density and apply Lemma `5.16.3` to recover that
-- `E` is constructible; then for each `x ∈ E`, every irreducible closed subset through `x` has
-- nonempty trace, hence contains a nonempty open subtrace, which is dense by irreducibility. Lemma
-- `5.16.4` upgrades those dense traces to `E ∈ 𝓝 x`, and therefore `E` is open.
/-- Lemma 5.16.5: a subset `E` of a Noetherian space `X` is open if and only if for every
irreducible closed subset `Y` of `X`, the intersection `E ∩ Y` is empty or contains a nonempty
open subset of `Y`, written as `Y ∩ U` for some open subset `U` of `X`. -/
theorem isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open (E : Set X) :
    IsOpen E ↔
      ∀ Y : IrreducibleCloseds X,
        ((Y : Set X) ↓∩ E) = ∅ ∨
          ∃ U : Opens Y, (U : Set Y).Nonempty ∧ (U : Set Y) ⊆ (Y : Set X) ↓∩ E := by
  constructor
  · intro hE Y
    by_cases hYE : ((Y : Set X) ↓∩ E : Set Y) = ∅
    · exact Or.inl hYE
    · refine Or.inr ⟨⟨(Y : Set X) ↓∩ E, ?_⟩, Set.nonempty_iff_ne_empty.mpr hYE, subset_rfl⟩
      simpa using hE.preimage continuous_subtype_val
  · intro hE
    have hE_constructible : IsConstructible E :=
      (isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense E).2
        fun Y ↦
          match hE Y with
          | .inl hYE =>
              .inr <| by
                letI : Nonempty Y := by
                  rcases Y.isIrreducible.nonempty with ⟨y, hy⟩
                  exact ⟨⟨y, hy⟩⟩
                rw [hYE, dense_iff_closure_eq, closure_empty]
                exact Set.empty_ne_univ
          | .inr hU => .inl hU
    refine isOpen_iff_mem_nhds.2 fun x hxE ↦ ?_
    refine (hE_constructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace).2 ?_
    intro Y hxY
    rcases hE Y with hYE | ⟨U, hU_nonempty, hU_subset⟩
    · exfalso
      exact (Set.nonempty_iff_ne_empty.mp ⟨⟨x, hxY⟩, hxE⟩) hYE
    · letI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
      exact Dense.mono hU_subset (U.2.dense hU_nonempty)

end
