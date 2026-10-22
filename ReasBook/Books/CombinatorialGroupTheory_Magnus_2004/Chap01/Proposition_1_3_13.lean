/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 1-3-13: every nontrivial finitely generated normal subgroup of a free group has
finite index.

Layer triage:
- `source-facing`: a nontrivial finitely generated normal subgroup `N : Subgroup F`.
- `core/canonical`: the subgroup owner `Subgroup F` together with the owner predicates
  `Subgroup.FG`, `Subgroup.Normal`, and `Subgroup.FiniteIndex`.
- `bridge/view`: Proposition `1-3-13` is exactly the specialization `H = N` of Proposition
  `1-3-12`, which already expresses the canonical owner theorem for a finitely generated subgroup
  containing a nontrivial normal subgroup.

Domain sampling:
1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for finite generation
   of a subgroup.
2. `Subgroup.fg_iff` in `Mathlib/GroupTheory/Finiteness` shows that finite generation is derived
   from the canonical subgroup owner via closure of a finite set, not from extra packaged data.
3. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite index,
   and `finiteIndex_iff_finite_quotient` is its standard quotient-level bridge.
4. `finiteIndex_of_fg_of_contains_nontrivial_normal` in Proposition `1-3-12` is the chapter owner
   theorem whose diagonal specialization `H = N` is exactly this proposition.

Best owner abstraction:
the public mathematics already lives at the canonical subgroup-owner level of Proposition
`1-3-12`; this proposition adds no new owner data beyond the diagonal specialization `H = N`.

Primitive vs. derived:
the primitive mathematical data are just the subgroup `N` and the owner predicates `N.FG`,
`N.Normal`, and `N ≠ ⊥`; the finite-index conclusion is derived. Since Proposition `1-3-12`
already consumes exactly those owner-level inputs after the canonical inclusion `N ≤ N = le_rfl`,
keeping a separate local theorem would duplicate the API surface without adding mathematics.

Accordingly, this file keeps only the exact diagonal recall term rather than a parallel local
specialization theorem. -/
#check
  (fun {F : Type u} [Group F] [IsFreeGroup F] (N : Subgroup F)
      (hfg : N.FG) (hN_normal : N.Normal) (hN : N ≠ ⊥) ↦
    finiteIndex_of_fg_of_contains_nontrivial_normal N N hfg le_rfl hN_normal hN :
      ∀ {F : Type u} [Group F] [IsFreeGroup F] (N : Subgroup F),
        N.FG → N.Normal → N ≠ ⊥ → N.FiniteIndex)
