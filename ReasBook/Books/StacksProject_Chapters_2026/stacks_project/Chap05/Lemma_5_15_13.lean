module

public import Mathlib.Topology.Constructible

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] {T : Set X}

/- Domain-style sampling for compact locally closed subsets with retrocompact complement:
- core/canonical owner declarations inspected:
  `Topology.IsConstructible`,
  `PrespectralSpace.exists_isCompact_and_isOpen_between`,
  `IsCompact.isConstructible`,
  `IsConstructible.sdiff`
- target layer here: `source-facing`. This item adds the extra source content that a compact
  locally closed subset with retrocompact complement is constructible, so it should stay as a
  theorem rather than collapse to a recall.

Best owner abstraction: `Topology.IsConstructible` is the canonical owner predicate, and the
source-facing theorem is most naturally attached to the primitive hypothesis `IsLocallyClosed T`
rather than kept as a standalone wrapper theorem.

Primitive data for the statement are exactly the locally closed subset `T`, its compactness, and
the retrocompactness of `Tᶜ`. The compact open neighborhood `U` and the auxiliary open
compact subset `V` are derived proof data from the prespectral owner API and should remain
internal.
-/

-- Proof sketch: choose a compact open `U` with `T ⊆ U ⊆ coborder T`, so `T = U ∩ closure T`.
-- Then `V = U ∩ Tᶜ` is a compact open subset of `X`, and inside `U` one has
-- `V = U ∩ (closure T)ᶜ`. Hence `T = U \ V`, a difference of constructible sets.
/-- Lemma 5.15.13: let `X` be a quasi-compact topological space having a basis consisting of
quasi-compact opens such that the intersection of any two quasi-compact opens is quasi-compact.
Let `T ⊆ X` be a locally closed subset such that `T` is quasi-compact and `Tᶜ` is retrocompact in
`X`. Then `T` is constructible in `X`.

The ambient quasi-compactness hypothesis from the source is redundant for this conclusion, so the
Lean statement keeps only the hypotheses actually used by the proof. -/
theorem IsLocallyClosed.isConstructible_of_isCompact_of_retrocompact_compl
    (hT_loc : IsLocallyClosed T) (hT_compact : IsCompact T) (hTc_retro : IsRetrocompact Tᶜ) :
    IsConstructible T := by
  obtain ⟨U, hU_compact, hU_open, hTU, hUcob⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hT_compact hT_loc.isOpen_coborder
      subset_coborder
  let V : Set X := U ∩ Tᶜ
  have hV_eq : V = U ∩ (closure T)ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxCob : x ∈ T ∪ (closure T)ᶜ := by
        simpa [coborder_eq_union_closure_compl] using hUcob hx.1
      rcases hxCob with hxT | hxclosure
      · exact (hx.2 hxT).elim
      · exact hxclosure
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxT
      exact hx.2 (subset_closure hxT)
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact hU_open.inter isClosed_closure.isOpen_compl
  have hV_compact : IsCompact V := by
    simpa [V, inter_left_comm, inter_comm, inter_assoc] using hTc_retro hU_compact hU_open
  have hU_constructible : IsConstructible U := hU_compact.isConstructible hU_open
  have hV_constructible : IsConstructible V := hV_compact.isConstructible hV_open
  have hT_eq : T = U \ V := by
    ext x
    constructor
    · intro hx
      refine ⟨hTU hx, ?_⟩
      simp [V, hx]
    · intro hx
      by_contra hxT
      exact hx.2 (by simpa [V, hxT] using hx.1)
  simpa [hT_eq] using hU_constructible.sdiff hV_constructible

end

end Topology
