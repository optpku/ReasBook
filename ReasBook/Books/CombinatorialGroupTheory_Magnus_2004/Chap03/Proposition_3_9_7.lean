/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory of staggered presentations and spherical diagrams over
presentation complexes.

Layer triage:
- `source-facing`: a staggered relator family on the indexed generators `Σ i, Y i`, a spherical
  diagram over an actual presentation complex `K(Σ i, Y i; range r)`, and the reducedness
  condition on that diagram.
- `core/canonical`: `GroupPresentation.IsStaggeredRelatorFamily` from Proposition `2-5-2` is the
  chapter owner for staggered relator families, `PresentationComplex.Coordinates` from
  Proposition `3-4-3` is the owner for the presentation complex of `(Σ i, Y i; range r)`, and
  `TwoComplex.IsSphericalDiagram`, `TwoComplex.Hom`, and `TwoComplex.Hom.mapBoundaryStar` are the
  owners for the spherical source, the diagram map, and its induced corner map.
- `bridge/view`: the source-facing reducedness condition is expressed by injectivity of
  `mapBoundaryStar` at each source vertex.

Domain sampling:
1. `GroupPresentation.IsStaggeredRelatorFamily` from Proposition `2-5-2` is the existing chapter
   owner for staggeredness, so this file should reuse it rather than restate the same support API.
2. `PresentationComplex.Coordinates` from Proposition `3-4-3` is the owner abstraction for a
   chosen presentation complex of `(Σ i, Y i; range r)`, so the main theorem should refer to that
   object rather than an unrelated `TwoComplex`.
3. `TwoComplex.Hom` and `TwoComplex.Hom.mapBoundaryStar` from Proposition `3-3-4` are the owner
   abstractions for combinatorial diagram maps and their induced boundary-star maps.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for simple
   connectedness of the source complex.
5. `TwoComplex.EmbedsInSphere` from Proposition `3-5-6` is the owner predicate for spherical
   embeddability.

Primitive vs. derived:
- primitive data: a chosen presentation complex
  `coords : PresentationComplex.Coordinates K Generators (Set.range r)`, the source complex
  `D : TwoComplex`, and a morphism `φ : TwoComplex.Hom D K`;
- derived API: the owner predicate `D.IsSphericalDiagram` packaging connectedness of `D.skeleton`,
  simple connectedness of `D`, and embeddability of `D` in the sphere, together with injectivity
  of `φ.mapBoundaryStar` at every source vertex.
-/

open GroupPresentation

namespace TwoComplex

/-- A spherical diagram is a connected simply connected `2`-complex that embeds in the sphere. -/
class IsSphericalDiagram (D : TwoComplex) : Prop where
  /-- The underlying `1`-skeleton is connected. -/
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify D.skeleton)
  /-- The source complex is simply connected. -/
  simplyConnected : IsSimplyConnected D
  /-- The source complex embeds in the `2`-sphere. -/
  embedsInSphere : D.EmbedsInSphere

instance {D : TwoComplex} [hD : IsSphericalDiagram D] : IsSimplyConnected D :=
  hD.simplyConnected

end TwoComplex

section Proposition397

variable {ι : Type u} [LinearOrder ι]
variable {Y : ι → Type v}
variable {J : Type w} [Preorder J]

local notation "Generators" => Σ i, Y i

-- Proof sketch: argue by contradiction from a reduced spherical diagram over the presentation
-- complex. A staggered relator family admits an extremal face in any spherical diagram; the local
-- injectivity of `TwoComplex.Hom.mapBoundaryStar` at each source vertex forbids the cancellation
-- that such an extremal face would force, so no reduced spherical diagram can exist.
/-- Proposition 3-9-7: if `r` is a staggered relator family on the indexed generators
`Σ i, Y i`, then any actual presentation complex `K(Σ i, Y i; range r)` admits no reduced
spherical diagram over it. -/
theorem no_reduced_spherical_diagram_over_staggered_presentation
    (r : J → FreeGroup Generators) (hstaggered : IsStaggeredRelatorFamily r) {K : TwoComplex}
    (coords : PresentationComplex.Coordinates K Generators (Set.range r)) :
    ¬ ∃ (D : TwoComplex) (φ : TwoComplex.Hom D K),
        D.IsSphericalDiagram ∧
        ∀ v : D.skeleton, Function.Injective (φ.mapBoundaryStar v) :=
  sorry

end Proposition397
