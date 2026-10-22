/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Monoid.Coprod

set_option autoImplicit false

section

/-!
Primary domain: countable-group embedding theorems together with existential closure properties of
groups.

Layer triage:
- `source-facing`: the countable embedding theorem together with the chapter definition of an
  algebraically closed group.
- `core/canonical`: `G ∗ FreeGroup ι` for coefficient words, `Monoid.Coprod.lift` for evaluation
  in an overgroup, `Finset` for finite systems, `Countable` for countability, and
  `Function.Injective` on a homomorphism `C →* A` for an embedding.
- `bridge/view`: the textbook finite systems of equations and inequations over `G` are expressed as
  finite `Finset`s of coefficient words in `G ∗ FreeGroup ι`.

Domain sampling:
1. `Countable` is the canonical mathlib owner for countability of a type.
2. A group embedding is canonically represented by a homomorphism together with
   `Function.Injective`, as in earlier embedding theorems in this chapter.
3. `Monoid.Coprod.lift` is the canonical owner for evaluating a coefficient word in a target group
   once coefficient values and variable values are fixed.
4. Theorems `4-3-3`, `4-3-5`, and `4-3-6` in this chapter already use the source-facing
   existential-overgroup pattern, so Theorem `4-8-1` should keep that surface while deriving its
   algebraic-closedness hypothesis from the owner predicate defined here.

Primitive vs. derived:
- primitive public data for algebraic closedness: the ambient group `G`, a variable type `ι`, an
  overgroup `H`, an embedding `e : G →* H`, and finite sets of equations and inequations in
  `G ∗ FreeGroup ι`; the finiteness of the system is already carried by the two `Finset`s, so no
  separate finiteness hypothesis on `ι` belongs in the owner field;
- primitive owner-side relation on that data: `IsAlgebraicallyClosedGroup.IsSolution`;
- primitive public data for Theorem `4-8-1`: the ambient overgroup `A` and the embedding
  `f : C →* A`;
- derived public properties: countability of `A`, algebraic closedness of `A`, and injectivity
  of `f`.
-/

variable {G : Type u} [Group G] {ι : Type v}

namespace IsAlgebraicallyClosedGroup

/-- A valuation satisfies a finite coefficient system over `G` when it solves every equation and
avoids every inequation after evaluation in the target group. -/
def IsSolution {H : Type u} [Group H] (e : G →* H)
    (equations inequations : Finset (G ∗ FreeGroup ι)) (x : ι → H) : Prop :=
  let φ := Monoid.Coprod.lift e (FreeGroup.lift x)
  (∀ w ∈ equations, φ w = 1) ∧ ∀ w ∈ inequations, φ w ≠ 1

end IsAlgebraicallyClosedGroup

/-- An algebraically closed group is one in which every finite system of equations and inequations
with coefficients in the group that has a solution in some extension already has a solution in the
group itself. -/
class IsAlgebraicallyClosedGroup (G : Type u) [Group G] : Prop where
  /-- Any finite satisfiable system of equations and inequations over `G` already has a solution
  in `G`. -/
  exists_solution_of_satisfiable {ι : Type v} {H : Type u} [Group H]
      (e : G →* H) (_ : Function.Injective e)
      (equations inequations : Finset (G ∗ FreeGroup ι))
      (hsol : ∃ x : ι → H, IsAlgebraicallyClosedGroup.IsSolution e equations inequations x) :
      ∃ x : ι → G,
        IsAlgebraicallyClosedGroup.IsSolution (MonoidHom.id G) equations inequations x

variable (C : Type u) [Group C] [Countable C]

/-- Theorem 4-8-1: every countable group can be embedded in a countable algebraically closed
group. -/
-- Proof sketch: enumerate all finite systems of equations and inequations with coefficients in the
-- current countable group, solve each system whenever it is consistent in some extension, and take
-- the union of the resulting countable chain. Iterating that construction yields a countable union
-- in which every finitely consistent coefficient system over the final group already has a
-- solution, giving a countable algebraically closed overgroup of `C`.
theorem countable_group_embeds_in_countable_algebraically_closed_group :
    ∃ (A : Type u) (_ : Group A) (f : C →* A),
      Countable A ∧ IsAlgebraicallyClosedGroup A ∧ Function.Injective f := sorry

end
