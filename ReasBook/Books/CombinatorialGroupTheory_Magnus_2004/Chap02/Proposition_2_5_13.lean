/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_8
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open FreeGroup

universe u v

-- Layer triage:
-- `source-facing`: the standard orientable and nonorientable one-relator surface groups, the
-- property that an arbitrary group is isomorphic to one of them, and the assertion that such a
-- group is freely indecomposable.
-- `core/canonical`: `PresentedGroup` for the one-relator presentations and
-- `FreeGroupBasis.pairedCommutatorProduct` for the orientable surface relator, together with
-- `IsFreelyIndecomposable` from Proposition `2-5-12` for the ambient free-product conclusion.
-- `bridge/view`: group isomorphisms transporting the source-facing surface-group and
-- freely-indecomposable predicates.
-- Domain sampling:
-- 1. `PresentedGroup` is mathlib's owner abstraction for groups defined by generators and
--    relators, so the standard surface presentations should be recorded directly with that owner.
-- 2. `(FreeGroupBasis.ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct` from Proposition
--    `1-6-8` is the chapter owner for the orientable genus-`g` commutator relator, so the target
--    file should reuse that expression directly inside the orientable presentation.
-- 3. `IsFreelyIndecomposable` is the chapter owner abstraction for saying a group admits no
--    nontrivial free-product decomposition.
-- 4. Multiplicative equivalences `G ≃* H` are the canonical bridge for invariance statements
--    about the source-facing surface presentations.
-- Primitive vs. derived:
-- the primitive data are the nonorientable surface relator word together with the chapter owner
-- `FreeGroupBasis.pairedCommutatorProduct` for the orientable relator, and the owner predicate
-- `IsFreelyIndecomposable`; the corresponding singleton-relator `PresentedGroup`s and the
-- surface-group property are derived directly from that data.

namespace SurfaceGroup

open FreeGroupBasis

/-- The closed nonorientable surface relator of genus `n`. -/
def nonorientableRelator (n : ℕ) : FreeGroup (Fin n) :=
  (List.ofFn fun i : Fin n ↦ of i ^ (2 : ℕ)).prod

/-- The closed orientable surface group of genus `g`. -/
abbrev Orientable (g : ℕ) : Type :=
  PresentedGroup ({(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} : Set _)

/-- The closed nonorientable surface group of genus `n`. -/
abbrev Nonorientable (n : ℕ) : Type :=
  PresentedGroup ({nonorientableRelator n} : Set _)

end SurfaceGroup

open SurfaceGroup

/-- A group is a surface group if it is isomorphic to one of the standard orientable or
nonorientable one-relator surface groups. -/
def IsSurfaceGroup (G : Type u) [Group G] : Prop :=
  (∃ g : ℕ, Nonempty (G ≃* Orientable g)) ∨
    ∃ n : ℕ, Nonempty (G ≃* Nonorientable n)

namespace IsSurfaceGroup

/-- Being a surface group is invariant under multiplicative equivalence. -/
theorem of_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G') :
    IsSurfaceGroup G → IsSurfaceGroup G' := by
  rintro (⟨g, ⟨φ⟩⟩ | ⟨n, ⟨φ⟩⟩)
  · exact Or.inl ⟨g, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨n, ⟨e.symm.trans φ⟩⟩

/-- Being a surface group is preserved and reflected by multiplicative equivalence. -/
theorem iff_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G') :
    IsSurfaceGroup G ↔ IsSurfaceGroup G' :=
  ⟨of_mulEquiv e, of_mulEquiv e.symm⟩

end IsSurfaceGroup

/-- Every standard orientable surface group is a surface group. -/
-- Proof sketch: apply the orientable constructor using the identity equivalence of
-- `SurfaceGroup.Orientable g`.
theorem isSurfaceGroup_orientable (g : ℕ) :
    IsSurfaceGroup (Orientable g) :=
  Or.inl ⟨g, ⟨MulEquiv.refl _⟩⟩

/-- Every standard nonorientable surface group is a surface group. -/
-- Proof sketch: apply the nonorientable constructor using the identity equivalence of
-- `SurfaceGroup.Nonorientable n`.
theorem isSurfaceGroup_nonorientable (n : ℕ) :
    IsSurfaceGroup (Nonorientable n) :=
  Or.inr ⟨n, ⟨MulEquiv.refl _⟩⟩

/-- The standard orientable surface group of genus `g` is freely indecomposable. -/
theorem isFreelyIndecomposable_orientable (g : ℕ) :
    IsFreelyIndecomposable (Orientable g) := by
  sorry

/-- The standard nonorientable surface group of genus `n` is freely indecomposable. -/
theorem isFreelyIndecomposable_nonorientable (n : ℕ) :
    IsFreelyIndecomposable (Nonorientable n) := by
  sorry

-- Proof sketch: choose an orientable or nonorientable presentation by cases on
-- `IsSurfaceGroup`, apply the corresponding standard indecomposability theorem for that canonical
-- one-relator presentation, and transport the result along the presentation equivalence via
-- `IsFreelyIndecomposable.of_mulEquiv`.
/-- Proposition 2-5-13, in owner form: every surface group is freely indecomposable. -/
theorem surface_group_not_proper_free_product (G : Type u) [Group G] (hG : IsSurfaceGroup G) :
    IsFreelyIndecomposable G := by
  rcases hG with ⟨g, ⟨e⟩⟩ | ⟨n, ⟨e⟩⟩
  · refine ⟨?_⟩
    intro A B _ _ eAB
    exact
      (isFreelyIndecomposable_orientable g).of_mulEquiv_coprod
        (e.symm.trans eAB)
  · refine ⟨?_⟩
    intro A B _ _ eAB
    exact
      (isFreelyIndecomposable_nonorientable n).of_mulEquiv_coprod
        (e.symm.trans eAB)
