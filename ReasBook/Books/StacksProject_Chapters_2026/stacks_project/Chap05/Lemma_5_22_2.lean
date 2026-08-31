module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Category.Profinite.Basic
import stacks_project.Chap05.Definition_5_22_1

@[expose] public section

open CategoryTheory Limits

universe u

/- Domain-style sampling for profinite topological spaces:
- owner abstraction: `Profinite`
- same-domain declarations inspected:
  `Profinite`,
  `Profinite.of`,
  `exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete`,
  `FintypeCat.toProfinite`

Layer triage:
- `source-facing`: the Stacks characterization of profinite spaces by separation, compactness, and
  total disconnectedness
- `core/canonical`: the bundled owner `Profinite`
- `bridge/view`: the equivalence between the source-facing conjunction and existence of a
  homeomorphism to a profinite space, together with the derived cofiltered-limit presentation

Primitive data is exactly the ambient topology plus the three typeclass fields
`T2Space X`, `CompactSpace X`, and `TotallyDisconnectedSpace X`, which are precisely what
construct `Profinite.of X`. The cofiltered-limit presentation is derived API owned upstream by
`exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete`, so this file should keep only
the thin bridge from the source conjunction to that owner theorem and reuse it for the derived
cofiltered-limit presentation.
-/

section

variable (X : Type u) [TopologicalSpace X]

-- Proof sketch: transport the Hausdorff instance across a homeomorphism from `X` to a profinite
-- space.
/-- Lemma 5.22.2 (1): if a topological space is homeomorphic to a profinite space, then it is
Hausdorff. -/
theorem exists_profinite_implies_t2Space
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : T2Space X := by
  -- Unpack the profinite model and transport Hausdorffness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.t2Space

-- Proof sketch: transport compactness across a homeomorphism from `X` to a profinite space.
/-- Lemma 5.22.2 (2): if a topological space is homeomorphic to a profinite space, then it is
quasi-compact. -/
theorem exists_profinite_implies_compactSpace
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : CompactSpace X := by
  -- Unpack the profinite model and transport compactness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.compactSpace

-- Proof sketch: transport total disconnectedness across a homeomorphism from `X` to a profinite
-- space.
/-- Lemma 5.22.2 (3): if a topological space is homeomorphic to a profinite space, then it is
totally disconnected. -/
theorem exists_profinite_implies_totallyDisconnectedSpace
    (h : ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) : TotallyDisconnectedSpace X := by
  -- Unpack the profinite model and transport total disconnectedness back along the homeomorphism.
  rcases h with ⟨P, ⟨e⟩⟩
  exact e.symm.totallyDisconnectedSpace

-- Proof sketch: use the canonical bundled profinite space `Profinite.of X` once the Hausdorff,
-- compact, and totally disconnected instances are available.
/-- Lemma 5.22.2 (4): a Hausdorff, quasi-compact, and totally disconnected space is homeomorphic
to a profinite space. -/
theorem t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P) := by
  -- Package the given structure into the canonical bundled profinite owner.
  exact ⟨Profinite.of X, ⟨Homeomorph.refl _⟩⟩

-- Proof sketch: first obtain a profinite model from the Hausdorff, compact, and totally
-- disconnected hypotheses, then apply the cofiltered-limit presentation of profinite spaces from
-- `Definition 5.22.1`.
/-- Lemma 5.22.2 (5): a Hausdorff, quasi-compact, and totally disconnected space is a cofiltered
limit of finite discrete spaces. -/
theorem hausdorff_compact_totallyDisconnected_has_cofiltered_limit_presentation
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FintypeCat.{u}),
      Nonempty (X ≃ₜ (limit (F ⋙ FintypeCat.toProfinite) : Profinite.{u})) := by
  -- First realize `X` as a profinite space, then invoke the canonical finite-discrete presentation.
  exact
    (exists_profinite_iff_homeomorphic_cofiltered_limit_finite_discrete X).1
      (t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite (X := X))

end
