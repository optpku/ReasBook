module

public import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.AsLimit

@[expose] public section

open CategoryTheory Limits
open CompHausLike

universe u

/- Domain-style sampling for profinite spaces and their finite-discrete limit presentation:
- primary domain: profinite topological spaces
- inspected owner declarations:
  `Profinite`,
  `FintypeCat.toProfinite`,
  `Profinite.diagram`,
  `Profinite.lim`

Layer triage:
- `source-facing`: the cofiltered-limit presentation by finite discrete spaces
- `core/canonical`: the bundled owner `Profinite`
- `bridge/view`: the equivalence between an arbitrary space and a profinite limit presentation

Primitive data belongs to the owner `Profinite`; the finite-discrete presentation data are derived
from `P.fintypeDiagram`, `P.diagram`, and `P.lim`. Since Lean packages existential
homeomorphisms propositionally via `Nonempty`, the source-facing bridge below keeps the bundled
profinite witness explicit and uses only the standard proposition wrapper for the homeomorphism
witness. -/

/- Definition 5.22.1: the canonical mathlib owner abstraction for profinite spaces is the bundled
type `Profinite`. Its objects are precisely the compact Hausdorff totally disconnected spaces, and
the source-text cofiltered limit presentation below recovers the same notion. -/
recall Profinite

/- Canonical finite-discrete inclusion used in the profinite limit presentation. -/
recall FintypeCat.toProfinite

/- Canonical profinite presentation by finite discrete quotients. -/
recall Profinite.fintypeDiagram

/- Canonical profinite-valued diagram attached to a profinite space. -/
recall Profinite.diagram

/- Bundled limit cone for the canonical finite-discrete presentation of a profinite space. -/
recall Profinite.lim

/-- Source-text form of Definition 5.22.1, expressed through the canonical bundled profinite-space
interface and the standard cofiltered limit presentation by finite discrete spaces. -/
theorem exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete
    (X : Type u) [TopologicalSpace X] :
    (∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) ↔
      ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FintypeCat.{u}),
        Nonempty (X ≃ₜ (limit (F ⋙ FintypeCat.toProfinite) : Profinite.{u})) := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    refine ⟨DiscreteQuotient P, inferInstance, inferInstance, P.fintypeDiagram, ?_⟩
    change Nonempty (X ≃ₜ (limit P.diagram : Profinite.{u}))
    exact ⟨e.trans (homeoOfIso (limit.isoLimitCone P.lim).symm)⟩
  · rintro ⟨J, _, _, F, ⟨e⟩⟩
    exact ⟨limit (F ⋙ FintypeCat.toProfinite), ⟨e⟩⟩
