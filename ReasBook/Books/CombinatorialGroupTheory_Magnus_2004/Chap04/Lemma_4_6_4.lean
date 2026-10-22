/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Lemma_4_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: an element of a sector `XY` that is irreducible, meaning it does not admit a
  two-step factorization through an intermediate pole.
- `core/canonical`: `BipolarStructure` from Definition `4-6-1`, its sector family `B X Y`, its
  fixed subgroup `B.F`, and the owner predicate `HasSectorFactorization`.
- `bridge/view`: the right- and left-multiplication actions of the fixed subgroup on a sector,
  expressed directly through sector membership together with the chapter-facing irreducibility
  predicate `B.IsIrreducible g`.

Domain sampling:
1. `BipolarStructure` is the owner abstraction for the bipolar axioms.
2. `B.sector_mul_mem` is the canonical owner-side API for the axiom that right multiplication by an
   element of `F` preserves a sector.
3. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner for irreducibility.
4. `B.inv_mem_sector` is the owner-side API for the inverse axiom used in the second clause.

Primitive vs. derived:
the primitive public data for this item are a bipolar structure `B`, poles `X Y`, an element
`g ∈ B X Y`, the irreducibility predicate `B.IsIrreducible g`, and an element `f ∈ B.F`. The old
local structure `IsIrreducibleIn` duplicated those primitives, so the public surface is refined to
the canonical conjunction of sector membership and the owner-side irreducibility API instead.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-4: right multiplication by an element of the fixed subgroup preserves
irreducibility in a sector. -/
-- Proof sketch: use the bipolar axiom that right multiplication by an element of `F` preserves the
-- sector `XY`. If `g * f` factored through some intermediate pole, multiply the second factor on
-- the right by `f⁻¹ ∈ F` to obtain a forbidden factorization of `g`.
theorem isIrreducibleIn_mul_fixed_right
    (B : BipolarStructure G) {X Y : Pole} {g f : G}
    (hg : g ∈ B X Y) (hgirr : B.IsIrreducible g) (hf : f ∈ B.F) :
    g * f ∈ B X Y ∧ B.IsIrreducible (g * f) := sorry

/-- Left multiplication by an element of the fixed subgroup also preserves irreducibility in a
sector. -/
-- Proof sketch: apply the inverse axiom to transport irreducibility of `g` in `XY` to
-- irreducibility of `g⁻¹` in `YX`, use the right-multiplication statement on `g⁻¹ * f⁻¹`, and then
-- invert again to conclude that `f * g` is irreducible in `XY`.
theorem isIrreducibleIn_mul_fixed_left
    (B : BipolarStructure G) {X Y : Pole} {g f : G}
    (hg : g ∈ B X Y) (hgirr : B.IsIrreducible g) (hf : f ∈ B.F) :
    f * g ∈ B X Y ∧ B.IsIrreducible (f * g) := sorry

end

end BipolarStructure
