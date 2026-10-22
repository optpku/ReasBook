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
- `source-facing`: products `g * h` of irreducible sector elements with `g ∈ XY` and `h ∈ YZ`.
- `core/canonical`: `BipolarStructure`, its fixed subgroup `B.F`, its sector family `B X Y`, and
  the sector-factorization predicate `HasSectorFactorization`.
- `bridge/view`: the chapter-facing irreducibility predicate `B.IsIrreducible g` together with the
  union `(B.F : Set G) ∪ B X Z`, which records the textbook phrase “an irreducible element of
  `F ∪ XZ`” without introducing a surrogate wrapper.

Domain sampling:
1. `BipolarStructure` is the owner abstraction for the bipolar axioms and sector notation.
2. `B.IsIrreducible g` from Definition `4-6-1` is the chapter-facing owner for irreducibility.
3. `HasSectorFactorization` is the primitive owner-side predicate for admissible sector
   decompositions.
4. The subgroup piece is used canonically through the subgroup-to-set coercion `(B.F : Set G)`.

Primitive vs. derived:
the primitive public data are the bipolar structure `B`, poles `X Y Z`, elements `g h`, their
sector-membership assumptions, and the primitive factorization predicate behind irreducibility.
The public source-facing statement uses the derived owner predicate `B.IsIrreducible` for both the
inputs and the output, while the union-membership conclusion remains the direct set-level view.
-/

namespace BipolarStructure

section

variable {G : Type u} [Group G]

/-- Lemma 4-6-3: if `g ∈ XY` and `h ∈ YZ` are both irreducible, meaning that neither admits a
length-two sector factorization, then `gh` is an irreducible element of `F ∪ XZ`. -/
-- Proof sketch: Lemma `4-6-2` gives the membership of `g * h` in `F ∪ XZ`. If `g * h` admitted a
-- length-two sector factorization, rewrite `g = p * (q * h⁻¹)` and use irreducibility of `h` to
-- show `q * h⁻¹ ∈ F`; then the bipolar axioms force `g` and `h` into incompatible sectors,
-- contradicting the irreducibility assumptions.
theorem mul_mem_fixed_union_sector_and_isIrreducible
    (B : BipolarStructure G) {X Y Z : Pole} {g h : G}
    (hg : g ∈ B X Y) (hh : h ∈ B Y Z)
    (hgirr : B.IsIrreducible g) (hhirr : B.IsIrreducible h) :
    g * h ∈ (B.F : Set G) ∪ B X Z ∧ B.IsIrreducible (g * h) := sorry

end

end BipolarStructure
