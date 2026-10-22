/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation

/-!
Primary domain: planar Cayley complexes and quadratic relator-root systems.

Layer triage:
- `source-facing`: a Cayley complex `C(X; R)` realized as an actual `TwoComplex`, together with a
  planar realization of that complex and the conclusion that the root system `S` of the relators
  is quadratic over the generator set `X`.
- `core/canonical`: `PresentationCoordinates C R` is the chapter owner for realizing an actual
  `TwoComplex` as `C(X; R)`, `C.EmbedsInPlane` is the chapter owner for planarity, and
  `IsQuadraticWordSet` is the chapter owner predicate for “quadratic over `X`”.
- `bridge/view`: `GroupPresentation.IsRelatorRootSet R S` is the source-facing bridge
  identifying `S` as a chosen relator-root system attached to `R`.

Domain sampling:
1. `PresentationCoordinates C R` from Proposition `3-4-1` is the owner abstraction for an actual
   Cayley complex with presentation data `(X; R)`.
2. `C.EmbedsInPlane` from Proposition `3-5-6` is the chapter owner proposition for planarity,
   with `TwoComplex.TwoManifoldEmbedding` as its witness layer.
3. `GroupPresentation.IsRelatorRootSet` from Definition `3-5-3` is the source-facing owner
   predicate identifying a chosen relator-root family attached to a relator family.
4. `IsQuadraticWordSet` from Proposition `1-7-4` is the chapter owner predicate for quadraticity
   over the canonical basis of `FreeGroup X`.

Primitive vs. derived:
- primitive data: the actual Cayley complex `C`, its coordinate realization over `(X; R)`, the
  planar hypothesis, and the source-facing root set `S`;
- derived API: the quadraticity conclusion on `S`, stated directly through
  `IsQuadraticWordSet`.
-/

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Proposition 3-5-1: if a Cayley complex `C(X; R)` is planar and `S` is a chosen relator-root
family for `R`, then `S` is quadratic over `X`. -/
-- Proof sketch: at a fixed vertex of the planar Cayley complex, each signed generator determines
-- a unique incident oriented edge. Planarity bounds the number of face-boundary loops beginning
-- with that edge by `2`, and the cyclic-permutation correspondence between relators and their
-- chosen roots transfers this bound to the occurrences of each generator in the chosen root
-- system.
theorem quadraticWordSet_of_planar
    (coords : PresentationCoordinates C R)
    (hplanar : C.EmbedsInPlane)
    {S : Set (FreeGroup X)}
    (hS : IsRelatorRootSet R S) :
    IsQuadraticWordSet (FreeGroupBasis.ofFreeGroup X) S := sorry

end CayleyComplex.Coordinates
