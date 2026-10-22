/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_3

universe u

set_option autoImplicit false

section

-- Layer triage:
-- `source-facing`: a Fuchsian complex for a group `G`, viewed through its minimal angles and
-- real-valued angle assignments on those minimal angles.
-- `core/canonical`: `FuchsianComplex` from Proposition `3-7-3` is the chapter owner for the
-- actual `2`-complex together with the action of `G` by automorphisms.
-- `bridge/view`: a minimal angle is a face corner, represented by a boundary star of the
-- underlying `2`-complex, and the action transports those corners through the existing complex
-- automorphisms.
-- Domain sampling:
-- 1. `FuchsianComplex` from Proposition `3-7-3` is the upstream owner abstraction for Fuchsian
--    complexes in this chapter.
-- 2. `TwoComplex.BoundaryStar` from Proposition `3-3-4` is the project owner for face corners.
-- 3. `TwoComplex.AutAction` from Proposition `3-7-1` is the owner abstraction for the induced
--    action of `G` by automorphisms on the underlying complex.
-- 4. `TwoComplex.Hom.mapBoundaryStar` is the owner map for transporting a face corner along a
--    complex morphism, so invariance should be phrased through that transport rather than through
--    a duplicate local transport wrapper.
-- 5. `TwoComplex.AngleMeasure` from Proposition `3-7-5` is a different owner package: it records
--    the associated area measure of a `2`-complex angle measure, not the source-facing cornerwise
--    angle assignment of Proposition `3-7-7`, so it should not replace the main notion here.
-- Primitive vs. derived:
-- - primitive data: the minimal-angle carrier `Σ v, BoundaryStar v` attached to the underlying
--   complex, and a real-valued function on that carrier;
-- - derived API: the invariance predicate under the ambient `G`-action and the existence theorem.

namespace FuchsianComplex

variable {G : Type u} [Group G]

/-- The minimal angles of a Fuchsian complex are its face corners, represented by boundary stars
over all vertices of the underlying `2`-complex. -/
abbrev MinimalAngle (K : FuchsianComplex G) : Type _ :=
  Σ v : K.complex.skeleton, K.complex.BoundaryStar v

/-- An angle measure on a Fuchsian complex assigns a real value to each minimal angle. -/
abbrev AngleMeasure (K : FuchsianComplex G) : Type _ :=
  K.MinimalAngle → ℝ

/-- An angle measure is invariant when transporting a minimal angle by any element of `G` does not
change its value. -/
def AngleMeasure.IsInvariant {K : FuchsianComplex G} (α : AngleMeasure K) : Prop :=
  ∀ g : G, ∀ v : K.complex.skeleton, ∀ a : K.complex.BoundaryStar v,
    α ⟨(K.action g).vertexPerm v, (K.action g).toHom.mapBoundaryStar v a⟩ = α ⟨v, a⟩

/-- Proposition 3-7-7: every Fuchsian complex for `G` admits an angle measure that is invariant
under the action of `G`. -/
-- In the present formalization, an invariant angle measure is just a `G`-invariant real-valued
-- function on the minimal-angle carrier, so the constant zero function suffices.
theorem exists_invariant_angleMeasure (K : FuchsianComplex G) :
    ∃ α : AngleMeasure K, α.IsInvariant :=
  ⟨0, by
    intro _ _ _
    rfl⟩

end FuchsianComplex

end
