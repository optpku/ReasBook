module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

/- Domain-style sampling for profinite topological groups:
- primary domain: profinite topological groups and their canonical finite-quotient limit
  presentation;
- inspected owner declarations:
  `ProfiniteGrp.of`,
  `ProfiniteGrp.ofContinuousMulEquiv`,
  `ProfiniteGrp.toFiniteQuotientFunctor`,
  `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`.

Best owner abstraction:
- `ProfiniteGrp`, with the bridge predicate `∃ P : ProfiniteGrp, Nonempty (G ≃ₜ* P)` for an
  arbitrary topological group `G`.

Primitive data vs derived API:
- primitive data: the topological-group structure on `G`, plus compactness and total
  disconnectedness packaged canonically by `ProfiniteGrp.of`;
- derived API: forgetting to a profinite space, and the finite-discrete inverse-system
  presentation via `toFiniteQuotientFunctor` and
  `continuousMulEquivLimittoFiniteQuotientFunctor`.

Layer triage:
- `source-facing`: the three-way equivalence in Lemma 5.30.4;
- `core/canonical`: `ProfiniteGrp`;
- `bridge/view`: the equivalence between the source-facing profinite-space clause and the canonical
  bundled profinite-group clause.

The profinite-space condition is not a second owner in the group setting: for topological groups it
is exactly the forgetful view of the canonical `ProfiniteGrp` owner. The finite-group limit clauses
are derived from the owner theorem on open normal finite quotients, so this file should route
through that owner instead of keeping a parallel local construction.
-/

section

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is homeomorphic to a profinite space exactly when it is topologically
isomorphic to a bundled profinite group. -/
theorem exists_profinite_iff_exists_profiniteGrp :
    (∃ P : Profinite.{u}, Nonempty (G ≃ₜ P)) ↔
      ∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P) := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    let _ : CompactSpace G := e.symm.compactSpace
    let _ : TotallyDisconnectedSpace G := e.symm.totallyDisconnectedSpace
    exact ⟨ProfiniteGrp.of G, ⟨ContinuousMulEquiv.refl G⟩⟩
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨P.toProfinite, ⟨e.toHomeomorph⟩⟩

/-- A topological group is topologically isomorphic to a profinite group exactly when it is compact
and totally disconnected. -/
theorem exists_profiniteGrp_iff_compact_totallyDisconnected :
    (∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P)) ↔
      CompactSpace G ∧ TotallyDisconnectedSpace G := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨e.symm.compactSpace, e.symm.totallyDisconnectedSpace⟩
  · rintro ⟨hCompact, hTot⟩
    let _ : CompactSpace G := hCompact
    let _ : TotallyDisconnectedSpace G := hTot
    exact ⟨ProfiniteGrp.of G, ⟨ContinuousMulEquiv.refl G⟩⟩

-- Proof sketch: route the profinite-space clause through the canonical owner
-- `∃ P : ProfiniteGrp, Nonempty (G ≃ₜ* P)`. The cofiltered limit clause is then the canonical
-- finite-quotient presentation of a profinite group given by
-- `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`; forgetting cofilteredness gives
-- the non-cofiltered clause, and any exhibited limit of finite discrete groups is automatically a
-- profinite group.
/-- Lemma 5.30.4: for a topological group, the following are equivalent: the canonical profinite
space condition that `G` be homeomorphic to a bundled profinite space; being topologically
isomorphic to a limit of finite groups endowed with the discrete topology; and admitting such a
presentation over a cofiltered index category. -/
theorem topologicalGroup_profinite_tfae :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (G ≃ₜ P),
        ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ FiniteGrp.{u}),
          Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)),
        ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FiniteGrp.{u}),
          Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)) ] := by
  tfae_have 1 → 3 := by
    rintro h
    rcases (exists_profinite_iff_exists_profiniteGrp G).1 h with ⟨P, ⟨e⟩⟩
    let _ : Nonempty (OpenNormalSubgroup P) := ⟨{
      toOpenSubgroup := ⊤
      isNormal' := by
        simp }⟩
    refine ⟨OpenNormalSubgroup P, inferInstance, inferInstance, P.toFiniteQuotientFunctor, ?_⟩
    change Nonempty (G ≃ₜ* ProfiniteGrp.limit (P.diagram))
    exact ⟨e.trans (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P)⟩
  tfae_have 3 → 2 := by
    rintro ⟨J, _, _, F, hF⟩
    exact ⟨J, inferInstance, F, hF⟩
  tfae_have 2 → 1 := by
    rintro ⟨J, _, F, ⟨e⟩⟩
    exact
      (exists_profinite_iff_exists_profiniteGrp G).2
        ⟨ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp), ⟨e⟩⟩
  tfae_finish

end
