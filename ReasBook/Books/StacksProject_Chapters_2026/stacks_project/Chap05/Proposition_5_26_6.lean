module

public import Mathlib.Topology.ExtremallyDisconnected
import stacks_project.Chap05.Lemma_5_3_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function

/- Domain-style sampling for Proposition 5.26.6:
- primary domain: projective compact Hausdorff spaces and extremal disconnectedness
- sampled owner declarations:
  `CompactT2.Projective`,
  `CompactT2.Projective.extremallyDisconnected`,
  `CompactT2.ExtremallyDisconnected.projective`,
  `CompactT2.projective_iff_extremallyDisconnected`
- best owner abstraction: `CompactT2.Projective`
- primitive data: the lifting property against surjective maps in compact Hausdorff spaces
- derived API: the special section property for surjections onto `X`, and the equivalence with
  `ExtremallyDisconnected`

Layer triage:
- `source-facing`: the three-way equivalence in Proposition 5.26.6
- `core/canonical`: `CompactT2.Projective`
- `bridge/view`: the section-property reformulation below

The section clause is not a second owner. It is the `Z = X`, `f = id` specialization of
projectivity, and the converse is recovered from the pullback projection `X ×_Z Y → X`.
-/

-- Proof sketch: use `CompactT2.projective_iff_extremallyDisconnected` for the equivalence of
-- `(1)` and `(3)`. Condition `(2)` is the special case of projectivity obtained by taking
-- `Z = X` and `f = id`, while conversely a lifting problem against a surjection `Y → Z` is
-- converted into a section problem for the pullback projection `X ×_Z Y → X`.
/-- For a compact Hausdorff space, projectivity is equivalent to the section property for
surjective maps onto `X`. This isolates condition `(2)` of Proposition 5.26.6 in the canonical
language of `CompactT2.Projective`. -/
theorem compactT2_projective_iff_surjective_has_section
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    CompactT2.Projective X ↔
      ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
        Continuous f → Surjective f →
          ∃ s : X → Y, Continuous s ∧ RightInverse s f := by
  constructor
  · intro h Y _ _ _ f hf hsurj
    rcases h continuous_id hf hsurj with ⟨s, hs, hsf⟩
    exact ⟨s, hs, fun x ↦ congr_fun hsf x⟩
  · intro h Y Z _ _ _ _ _ _ f g hf hg hsurj
    let E := { p : X × Y // f p.1 = g p.2 }
    have hE_closed : IsClosed { p : X × Y | f p.1 = g p.2 } :=
      isClosed_fiberProduct_subset hf hg
    haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE_closed.isCompact
    haveI : T2Space E := inferInstance
    let fst : E → X := fun p ↦ p.1.1
    have hfst : Continuous fst := continuous_fst.comp continuous_subtype_val
    have hfst_surj : Surjective fst := by
      intro x
      rcases hsurj (f x) with ⟨y, hy⟩
      refine ⟨⟨(x, y), ?_⟩, rfl⟩
      simp [hy]
    rcases h hfst hfst_surj with ⟨s, hs, hsfst⟩
    refine ⟨fun x ↦ (s x).1.2, continuous_snd.comp <| continuous_subtype_val.comp hs, ?_⟩
    ext x
    have hs_mem : f (s x).1.1 = g (s x).1.2 := (s x).2
    simpa [fst, hsfst x] using hs_mem.symm

/-- Proposition 5.26.6: for a compact Hausdorff space `X`, the following are equivalent:
`X` is extremally disconnected; every surjective continuous map `f : Y → X` from a compact
Hausdorff space admits a continuous section; and `X` is projective in the category of compact
Hausdorff spaces. The canonical projectivity clause is `CompactT2.Projective X`. -/
theorem compactT2_extremallyDisconnected_tfae
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    List.TFAE
      [ ExtremallyDisconnected X,
        ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : Y → X},
          Continuous f → Surjective f →
            ∃ s : X → Y, Continuous s ∧ RightInverse s f,
        CompactT2.Projective X ] := by
  tfae_have 1 ↔ 3 := CompactT2.projective_iff_extremallyDisconnected.symm
  tfae_have 2 ↔ 3 := compactT2_projective_iff_surjective_has_section.symm
  tfae_finish
