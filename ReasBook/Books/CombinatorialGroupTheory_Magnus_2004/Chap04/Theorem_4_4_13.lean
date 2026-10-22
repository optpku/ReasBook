/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Group.FG G] [Group.ResiduallyFinite G]

-- Primary domain: Hopfianity of finitely generated residually finite groups.
--
-- Layer triage:
-- `source-facing`: a group `G` that is both finitely generated and residually finite.
-- `core/canonical`: `Group.FG`, `Group.ResiduallyFinite`, and the chapter owner `IsHopfian`.
-- `bridge/view`: the textbook endomorphism formulation is a thin consequence of the owner
-- predicate `IsHopfian`.
-- Domain sampling:
-- 1. `Group.FG` from `Mathlib.GroupTheory.Finiteness` is the canonical owner predicate for finite
--    generation of a group.
-- 2. `Group.ResiduallyFinite` from `Mathlib.GroupTheory.ResiduallyFinite` is the canonical owner
--    predicate for residual finiteness.
-- 3. `IsHopfian` from Proposition `1-3-5` is the project's owner predicate for the Hopfian
--    conclusion.
-- 4. `MonoidHom.injective_of_surjective` is the canonical bridge from `IsHopfian G` back to the
--    source-facing endomorphism statement.
--
-- Primitive vs. derived:
-- the primitive public content is the owner instance `IsHopfian G`; the endomorphism-level
-- injectivity statement is derived API and should not remain the main declaration.

/-- Theorem 4-4-13: every finitely generated residually finite group is Hopfian. -/
-- Proof sketch: let `φ : G →* G` be surjective with kernel `K`. For each positive index `n`,
-- finite generation gives only finitely many subgroups of index `n`; surjectivity permutes them by
-- inverse image, so `K` lies in every subgroup of index `n`. Since this holds for every finite
-- index and `G` is residually finite, the intersection of all finite-index subgroups is trivial,
-- forcing `K = ⊥` and hence `φ` to be injective.
instance isHopfian_of_fg_residuallyFinite : IsHopfian G where
  injective_of_surjective (φ : G →* G) (hφ : Function.Surjective φ) := by
    sorry

/-- Source-facing reformulation of Theorem `4-4-13`: every surjective endomorphism of a finitely
generated residually finite group is injective. -/
theorem injective_of_surjective_endomorphism_of_fg_residuallyFinite (φ : G →* G)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  letI : IsHopfian G := isHopfian_of_fg_residuallyFinite
  exact MonoidHom.injective_of_surjective φ hφ

end
