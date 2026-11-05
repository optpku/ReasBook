module

public import Mathlib.Topology.Category.Profinite.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

/- Domain-style sampling for connected components and profinite quotients:
- primary domain: connected components of compact spaces and the profinite owner `Profinite`;
- same-domain owner declarations inspected:
  `ConnectedComponents.t2`,
  `ConnectedComponents.totallyDisconnectedSpace`,
  `connectedComponent_eq_iInter_isClopen`,
  `exists_profinite_iff_t2Space_compactSpace_totallyDisconnectedSpace`;
- best owner abstraction: the public owner object is `ConnectedComponents X`, with profiniteness
  derived canonically through `Profinite` once the Hausdorff instance on the quotient is supplied.

Layer triage:
- `source-facing`: the Hausdorff criterion on `ConnectedComponents X` under the Stacks hypothesis
  that each connected component is the intersection of the clopen neighborhoods of its points;
- `core/canonical`: `ConnectedComponents`, `T2Space`, and the chapter owner theorem
  `exists_profinite_iff_t2Space_compactSpace_totallyDisconnectedSpace`;
- `bridge/view`: the profinite existence statement, which should be a thin specialization of the
  canonical profinite criterion rather than a second hand-built witness construction.

Primitive data is only the quotient owner `ConnectedComponents X` and the source hypothesis
`hcomponents`; compactness and total disconnectedness of the quotient are already owned upstream by
canonical instances. The profinite statement is therefore derived API and should reuse the chapter
owner theorem directly.
-/

-- Proof sketch: compactness makes `ConnectedComponents X` quasi-compact, and it is totally
-- disconnected by the canonical quotient construction. For Hausdorffness, take distinct connected
-- components `C` and `D`; write `D` as the intersection of the clopen neighborhoods of a point
-- `b ∈ D`, use compactness of `C` and the finite-intersection argument to find one clopen
-- neighborhood of `b` disjoint from `C`, then descend that clopen set to the quotient by
-- connected components.
/-- Supporting Hausdorff criterion for Lemma 5.22.5. Compactness and total disconnectedness of
`ConnectedComponents X` are already canonical, so the remaining nontrivial input for profiniteness
is Hausdorffness. -/
instance ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z)
    :
    T2Space (ConnectedComponents X) := by
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b hne ↦ ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at hne
  have hdisj := connectedComponent_disjoint hne
  rw [hcomponents b, disjoint_iff_inter_eq_empty] at hdisj
  obtain ⟨U, V, hU, hUa, hUb, rfl⟩ : ∃ (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧ (↑) ⁻¹' V = U := by
    have hfinite :=
      isClosed_connectedComponent.isCompact.elim_finite_subfamily_closed
        _ (fun Z : { Z : Set X // IsClopen Z ∧ b ∈ Z } ↦ Z.2.1.1) hdisj
    obtain ⟨s, hs⟩ := hfinite
    set U : Set X := ⋂ Z ∈ s, (Z : Set X)
    have hU : IsClopen U := isClopen_biInter_finset fun Z _ ↦ Z.2.1
    exact ⟨U, (↑) '' U, hU, hs,
      subset_iInter₂ fun Z _ ↦ Z.2.1.connectedComponent_subset Z.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hUb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h ↦ flip Set.Nonempty.ne_empty hUa ⟨a, mem_connectedComponent, h⟩

/-- Lemma 5.22.5 (Stacks tag `0900`): if `X` is quasi-compact and for every point `x`, the
connected component `connectedComponent x` is the intersection of the clopen neighborhoods of `x`,
then `π₀(X)` is profinite. The
canonical Lean model of `π₀(X)` is `ConnectedComponents X`, and the bundled profinite space is
therefore `Profinite.of (ConnectedComponents X)`. -/
theorem connectedComponents_exists_profinite
    (hcomponents :
      ∀ x : X,
        connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z)
    :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := by
  let _ : T2Space (ConnectedComponents X) :=
    ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen hcomponents
  exact ⟨Profinite.of (ConnectedComponents X), ⟨Homeomorph.refl _⟩⟩

end
