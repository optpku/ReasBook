/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_1

universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: planar `2`-complexes, modified Cayley complexes, and their dual Fuchsian
complexes.

Layer triage:
- `source-facing`: a finite modified presentation together with its strictly planar modified
  Cayley complex, and the dual Fuchsian complex attached to that complex.
- `core/canonical`: `TwoComplex` is the owner for the actual `2`-complex, `ModifiedPresentation`
  and `ModifiedCayleyComplex` from Proposition `3-7-1` are the chapter owners for modified
  presentation data and its Cayley realization, `TwoComplex.Duality` and
  `ModifiedCayleyComplex.RealizesFuchsianDuality` are the chapter owners for the duality data and
  its equivariance, and `FuchsianComplex` with `FuchsianComplex.WithoutReflections` is the owner
  for the dual group action.
- `bridge/view`: the source phrase "strictly planar" is expressed by the existing owner predicates
  `TwoComplex.EmbedsInPlane` and `TwoComplex.HasSimpleBoundary`.

Domain sampling:
1. `ModifiedPresentation` from Proposition `3-7-1` is the chapter owner for the generator,
   reflection, and relator data of a modified presentation.
2. `ModifiedCayleyComplex` from Proposition `3-7-1` is the owner for the associated actual
   `2`-complex with Cayley coordinates.
3. `TwoComplex.Duality` and `ModifiedCayleyComplex.RealizesFuchsianDuality` from Proposition
   `3-7-1` are the chapter owner abstractions for the duality data and its equivariance between a
   modified Cayley complex and a Fuchsian complex.
4. `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` and `TwoComplex.HasSimpleBoundary` from
   Definition `3-2-4` are the owner predicates for the two components of strict planarity.

Primitive vs. derived:
- primitive data: the modified presentation `P`, its modified Cayley complex `C`, and the strict
  planarity of `C.complex`;
- derived API: the dual Fuchsian complex together with the canonical realization witness
  `C.RealizesFuchsianDuality K dual`, and the reflection criterion
  `K.WithoutReflections ↔ P.IsOrdinary`.
-/

namespace ModifiedCayleyComplex

variable {G : Type u} [Group G]
variable {P : ModifiedPresentation G} [Finite P.X] [Finite P.J] [Finite P.Rel]
variable (C : ModifiedCayleyComplex P)

local notation "Complex" => C.complex

/-- Proposition 3-7-2: a finite modified presentation together with a strictly planar modified
Cayley complex admits a dual Fuchsian complex, and that dual complex is without reflections
exactly in the ordinary case. -/
-- Proof sketch: embed the modified Cayley complex in the plane, barycentrically subdivide each
-- face, and glue the regions around each original vertex to obtain the dual polygons. The left
-- translations on the modified Cayley complex transport to automorphisms of the dual complex and
-- give the required Fuchsian action. A nontrivial element fixes a geometric dual edge exactly
-- when it reverses the crossed edge of the modified Cayley complex, which occurs precisely for
-- reflection letters; hence the dual is reflection-free exactly when `P` is ordinary.
theorem exists_dualFuchsianComplex_of_strictlyPlanar
    (hplanar : TwoComplex.EmbedsInPlane Complex)
    (hsimple : ∀ D : C.complex.Face, TwoComplex.HasSimpleBoundary Complex D) :
    ∃ K : FuchsianComplex G, ∃ dual : TwoComplex.Duality Complex K.complex,
      C.RealizesFuchsianDuality K dual ∧ (K.WithoutReflections ↔ P.IsOrdinary) := sorry

end ModifiedCayleyComplex
