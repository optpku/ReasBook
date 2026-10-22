/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G] (A B : Subgroup G) (d : TransversalPair G B A)

/-!
Primary domain: HNN extensions and Britton normal forms with chosen transversals.

Layer triage:
- `source-facing`: a normal form is a reduced HNN word
  `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` in which each `gᵢ` is the chosen representative of the
  appropriate right coset of `A` or `B`, and there is no pinch `t^ε, 1, t^{-ε}`.
- `core/canonical`: `TransversalPair G B A` is mathlib's owner for the source choice of
  right-coset representatives, and `NormalWord d` is the canonical owner for words in normal form
  relative to that choice.
- `bridge/view`: the source sequence is encoded by the initial base-group term `head := g₀` and
  the signed syllable list `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`, with the representative
  condition carried by `mem_set` and the no-pinch condition inherited from `ReducedWord.chain`.

Domain sampling:
1. `TransversalPair G B A` stores the chosen representatives of the right cosets of `B` and `A`,
   with `1` representing the subgroup coset.
2. `NormalWord d` is mathlib's canonical owner for HNN words whose syllable entries lie in that
   chosen transversal.
3. `NormalWord.mem_set` records the representative condition for each non-initial `gᵢ`.
4. `NormalWord` extends `ReducedWord`, so the reduced-word chain field remains the owner of the
   no-pinch condition.

Primitive vs. derived:
the primitive source data are the chosen transversal pair and the normal-form word relative to that
pair. The initial element `g₀`, the signed list of syllables, the representative condition, and
the exclusion of the pinch `t^ε, 1, t^{-ε}` are all already primitive in the canonical
`NormalWord` API, so this item is a direct recall of that owner rather than a new wrapper.
-/

/- Definition 4-2-3: after choosing right-coset representatives for `A` and `B`, a normal form in
the HNN extension is mathlib's canonical type `NormalWord d`.

Here `d : TransversalPair G B A` records the chosen representative of each right coset of `B` and
of `A`, with `1` as the representative of the subgroup coset itself. A value of
`NormalWord d` is exactly a sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` in which the syllable `gᵢ`
lies in the chosen transversal for `B` when `εᵢ = 1` and in the chosen transversal for `A` when
`εᵢ = -1`, and the inherited reduced-word chain condition excludes a consecutive subsequence
`t^ε, 1, t^{-ε}`. -/
#check (NormalWord d)

end
