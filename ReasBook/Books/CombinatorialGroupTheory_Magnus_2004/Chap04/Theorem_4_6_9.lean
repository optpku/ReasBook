/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_13_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped MatrixGroups

set_option autoImplicit false

section

variable {K : Type u} [Field K]

/-!
Primary domain: Bass-Serre decompositions of matrix groups over polynomial rings.

Layer triage:
- `source-facing`: the decomposition of `GL₂(K[x])` as the amalgamated free product of the
  constant copy of `GL₂(K)` and the upper triangular subgroup `T(K[x])`, with common subgroup
  `T(K)`.
- `core/canonical`: `Subgroup.amalgamatedProductComparison`, together with the owner-side subgroup
  declarations `constantLinearSubgroup` and `upperTriangularSubgroup`.
- `bridge/view`: Proposition `3-13-8` already provides the constant-coefficient subgroup, the
  upper triangular subgroup, and the identification of `T(K)` with their intersection, so this
  file should recall the resulting comparison theorem directly rather than rebuild a local
  `Monoid.PushoutI` presentation.

Domain sampling:
1. `Subgroup.amalgamatedProductComparison` from Proposition `3-12-5` is the chapter owner for the
   comparison map from a two-factor amalgamated product into the ambient group.
2. `upperTriangularSubgroup` from Proposition `3-13-8` is the source-facing subgroup `T(K[x])`.
3. `constantLinearSubgroup` from Proposition `3-13-8` is the constant copy of `GL₂(K)` inside
   `GL₂(K[x])`.
4. `glPolynomial_amalgamatedProductComparison_bijective` from Proposition `3-13-8` already states
   the exact owner-level Bass-Serre decomposition used here.

Primitive vs. derived:
- primitive source objects: the two actual subgroups inside `GL (Fin 2) (Polynomial K)`;
- derived owner-side API: their amalgamated product and the canonical comparison map into the
  ambient matrix group.
-/

/- Theorem 4-6-9 adds no new owner-level API beyond Proposition `3-13-8`. The upstream theorem
already states the source-faithful Bass-Serre decomposition on the canonical subgroup objects, so
this file keeps only a direct recall instead of a parallel local `Monoid.PushoutI` presentation. -/
#check (glPolynomial_amalgamatedProductComparison_bijective K :
  Function.Bijective
    (Subgroup.amalgamatedProductComparison
      (constantLinearSubgroup K)
      (upperTriangularSubgroup : Subgroup (GL (Fin 2) (Polynomial K)))))

end
