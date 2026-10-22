/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: sector membership statements `g ∈ XY`, `h ∈ YZ`, the irreducibility of `h`,
  and the conclusion that `gh` is either fixed or lies in a sector with left pole `X`.
- `core/canonical`: `BipolarStructure` is the owner abstraction for the subgroup piece `F`, the
  sector family, and the owner-side irreducibility predicate `B.IsIrreducible g`.
- `bridge/view`: this lemma converts the source word “irreducible” into the canonical owner API
  from Definition `4-6-1`.

Domain sampling:
1. `BipolarStructure` is the project owner for the five-piece bipolar decomposition.
2. Its coercion to `Pole → Pole → Set G` supplies the sector notation `B X Y`.
3. `HasSectorFactorization` from Definition `4-6-1` is the primitive notion for admissible
   products along poles.
4. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner API for the source
   notion “`g` admits no length-two admissible sector factorization”.

Primitive vs. derived:
the primitive source data are the bipolar structure `B`, the poles `X,Y,Z`, and the elements
`g,h` with their sector-membership assumptions. The irreducibility notion is already part of the
owner-side API imported from Definition `4-6-1`, so this file only states the first structural
consequence of that owner predicate.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-2: if `g ∈ XY`, `h ∈ YZ`, and `h` admits no length-two admissible sector
factorization, then `gh` lies either in the fixed subgroup piece `F` or in some sector `XW`. -/
-- Proof sketch: if `gh ∉ F`, the covering axiom places `gh` in some sector `UW`. If `U ≠ X`,
-- then `U = star X`; inversion puts `g⁻¹` in `YX`, so the equality `h = g⁻¹ * (gh)` gives a
-- forbidden length-two sector factorization of `h`. Hence the only non-fixed possibility is a
-- sector with left pole `X`.
theorem mul_mem_fixed_or_sector_of_irreducible
    (B : BipolarStructure G) {X Y Z : Pole} {g h : G}
    (hg : g ∈ B X Y) (hh : h ∈ B Y Z) (hirr : B.IsIrreducible h) :
    g * h ∈ B.F ∨ ∃ W : Pole, g * h ∈ B X W := sorry

end

end BipolarStructure
