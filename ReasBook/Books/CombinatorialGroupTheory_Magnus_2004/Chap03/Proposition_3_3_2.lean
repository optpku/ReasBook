/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_1

universe u v

namespace OneComplex

/-
Layer triage:
- `source-facing`: a connected `1`-complex `C`, a base vertex `v : C`, a subgroup
  `H ≤ π(C, v)`, and a connected covering of `C` whose induced map on the based fundamental
  group realizes exactly `H`.
- `core/canonical`: `OneComplex.Hom` is the owner abstraction for maps of `1`-complexes,
  `Quiver.Prefunctor.IsCovering` for `φ.toPrefunctor` is the canonical covering-side structure,
  `Hom.inducedFundamentalGroupHomOver` is the induced based fundamental-group homomorphism, and
  `Subgroup` is the owner abstraction for subgroups.
- `bridge/view`: the chosen vertex `v'` over `v` gives an equality `φ.toVertex v' = v`, which
  transports the canonical induced map to codomain `π(C, v)`.

Domain sampling:
1. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for morphisms of `1`-complexes.
2. `Quiver.Prefunctor.IsCovering` for `Hom.toPrefunctor` is the owner predicate for coverings of
   the underlying quivers.
3. `Hom.inducedFundamentalGroupHomOver` is the canonical induced map on based fundamental groups.
4. `Subgroup` is the owner abstraction for subgroups of `π(C, v)`.

Primitive vs. derived:
- primitive data: the covering morphism `φ : Hom C' C` with its chosen lift `v'` of `v`, and the
  equality identifying the image of the induced homomorphism with `H`;
- derived API: injectivity of the induced homomorphism, which is already the canonical conclusion
  of Proposition `3-3-1` for any covering map, and hence should not be packaged as primitive
  output here.
-/

/-- Proposition 3-3-2: every subgroup `H ≤ π(C, v)` is realized by a connected covering
`1`-complex over `C`, with a chosen vertex over `v`, such that the induced homomorphism
`π(C', v') → π(C, v)` has image exactly `H`. Injectivity is the canonical downstream consequence
of Proposition `3-3-1` for covering maps. -/
-- Proof sketch: choose a maximal tree in `C`, form the covering complex whose vertices are the
-- right cosets of `H`, use the canonical quiver covering map to show local bijectivity on stars,
-- and apply path lifting to identify the induced fundamental-group map with the subgroup `H`.
theorem exists_connected_covering_inducing_subgroup
    (C : OneComplex.{u, v}) (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C))
    (v : C) (H : Subgroup (π(C, v))) :
    ∃ (C' : OneComplex.{u, v})
      (_ : Quiver.IsStronglyConnected (Quiver.Symmetrify C')) (φ : Hom C' C)
      (_ : φ.toPrefunctor.IsCovering) (v' : C') (hv' : φ.toVertex v' = v),
      (φ.inducedFundamentalGroupHomOver v' v hv').range = H := by
  sorry

end OneComplex
