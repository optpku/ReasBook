module

public import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology TopologicalSpace

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.8:
- primary domain: local behavior of `T₀`, quasi-sobriety, and sobriety under covers of a
  topological space;
- sampled owner declarations:
  `T0Space.of_cover`,
  `T0Space.of_open_cover`,
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`,
  `IsLocallyClosed.sober`;
- best owner abstractions: `T0Space` for the separation axiom, `QuasiSober` for generic-point
  existence, and `TopologicalSpace.IsOpenCover` for the canonical open-cover descent API, with
  `IsLocallyClosed.sober` as the chapter bridge for open pieces;
- primitive-vs-derived split: the primitive input is only a cover together with local-closed/open
  hypotheses on its pieces. The local `T₀`, quasi-sober, and sober conclusions are derived from
  the owner abstractions above, so this file should expose only the minimal bridge statements and
  direct recalls.

Source/core/bridge triage:
- `source-facing`: Lemma 5.8.8, asserting that `T₀`, quasi-sobriety, and sobriety are local on the
  covers described in the source;
- `core/canonical`: `T0Space.of_cover`, `T0Space.of_open_cover`, and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`;
- `bridge/view`: the locally closed cover statement for `T₀`, and the owner-level open-cover
  sobriety theorem obtained from `T0Space.of_open_cover`, `TopologicalSpace.IsOpenCover.quasiSober`,
  and the earlier locally closed bridge `IsLocallyClosed.sober`.
-/

/-- Helper for Lemma 5.8.8: inseparable points have the same membership in a locally closed
subset. -/
theorem Inseparable.mem_iff_of_isLocallyClosed {x y : X} {s : Set X}
    (hxy : Inseparable x y) (hs : IsLocallyClosed s) : x ∈ s ↔ y ∈ s := by
  -- Unpack the locally closed set into an open part and a closed part.
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  constructor
  · intro hx
    rcases hx with ⟨hxU, hxZ⟩
    -- Inseparable points agree on membership in open and closed sets separately.
    exact ⟨(hxy.mem_open_iff hU).1 hxU, (hxy.mem_closed_iff hZ).1 hxZ⟩
  · intro hy
    rcases hy with ⟨hyU, hyZ⟩
    -- Reversing the same argument gives the converse implication.
    exact ⟨(hxy.mem_open_iff hU).2 hyU, (hxy.mem_closed_iff hZ).2 hyZ⟩

/-- Lemma 5.8.8 (1): for a cover of `X` by locally closed subsets, `X` is Kolmogorov if and only
if every member of the cover is Kolmogorov. -/
-- Proof sketch: for the forward implication, each subtype inherits `T0Space`. For the reverse
-- implication, use the canonical descent theorem `T0Space.of_cover` and the locally closed
-- decomposition to show any pair of topologically indistinguishable points lies in a common
-- `T₀` cover piece.
theorem t0Space_iff_forall_of_locallyClosed_cover
    (S : ι → Set X) (hcover : ⋃ i, S i = univ) (hloc : ∀ i, IsLocallyClosed (S i)) :
    T0Space X ↔ ∀ i, T0Space (S i) := by
  constructor
  · intro hX i
    -- Each cover piece is a subspace, so it inherits `T₀`.
    letI : T0Space X := hX
    infer_instance
  · intro hS
    -- Apply the canonical cover descent theorem and force inseparable points into one `T₀` piece.
    refine T0Space.of_cover ?_
    intro x y hxy
    have hxcover : x ∈ ⋃ i, S i := by
      simp [hcover]
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hxcover
    have hyi : y ∈ S i := (hxy.mem_iff_of_isLocallyClosed (hloc i)).1 hxi
    exact ⟨S i, hxi, hyi, hS i⟩

/- Open-cover quasi-sobriety descent is provided canonically by
`TopologicalSpace.IsOpenCover.quasiSober_iff_forall`. -/
recall IsOpenCover.quasiSober_iff_forall

namespace TopologicalSpace.IsOpenCover

/- The `T₀` half of sober descent along an open cover is the canonical theorem
`T0Space.of_open_cover` together with the subtype instance on each `U i`. -/
/-- Helper for Lemma 5.8.8: `T₀` is local on an open cover. -/
theorem t0Space_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    T0Space X ↔ ∀ i, T0Space (U i) := by
  constructor
  · intro hX i
    -- Each open piece is a subspace of `X`, hence inherits `T₀`.
    letI : T0Space X := hX
    infer_instance
  · intro hUi
    -- The owner theorem `T0Space.of_open_cover` reduces the proof to one open `T₀` neighborhood
    -- through each point.
    refine T0Space.of_open_cover ?_
    intro x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact ⟨U i, hi, (U i).2, hUi i⟩

/-- Lemma 5.8.8 (2): for an open cover `U` of `X`, sobriety is local on the cover, expressed via
the canonical `T0Space` and `QuasiSober` components. -/
-- Proof sketch: the `T₀` component descends by `T0Space.of_open_cover`, and the quasi-sober
-- component is exactly `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`.
theorem sober_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    (T0Space X ↔ ∀ i, T0Space (U i)) ∧ (QuasiSober X ↔ ∀ i, QuasiSober (U i)) := by
  -- The two source clauses are exactly the canonical `T₀` and quasi-sober descent theorems.
  exact ⟨hU.t0Space_iff_forall, hU.quasiSober_iff_forall⟩

end TopologicalSpace.IsOpenCover
