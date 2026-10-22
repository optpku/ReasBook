/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_11_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

/- Layer triage:
- `source-facing`: the Section `11` shortening lemma for conjugates of elements in the upstream
  subset `U = shortSyllableConjugates d`.
- `core/canonical`: the amalgamated-product owner `PushoutI φ`, the chosen normal-form data
  `NormalWord.Transversal φ`, the derived length `syllableLength d`, and the upstream owner subset
  `shortSyllableConjugates d`.
- `bridge/view`: none. This file should reuse the existing source-facing subset `U` rather than
  redefine it locally.

Domain sampling:
1. `Monoid.PushoutI` is the owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` and `Monoid.PushoutI.syllableLength` from
   Definition `1-11-2` are the canonical chosen-normal-form and length APIs.
3. `Monoid.PushoutI.shortSyllableConjugates` from Definition `1-11-2` is the upstream source-facing
   owner for the Section `11` subset `U`.

Primitive vs. derived:
the primitive public data are only the element `u`, the chosen transversal `d`, and membership in
the upstream owner subset `shortSyllableConjugates d`. The shortening inequality in the conclusion
is derived API on that owner abstraction.
-/

/-- Lemma 1-11-14: if `u` belongs to the Section `11` subset `U`, `v` is strictly shorter than
`u`, and the product `u * v` has length at most that of `v`, then the conjugate `v⁻¹ * u * v`
is strictly shorter than `u`. -/
-- Proof sketch: write `u = p⁻¹ * h * p` with `syllableLength h ≤ 1`. In the product `u * v`, the
-- end of `p` cancels and the short factor `h` merges with the first syllable of `v`, so
-- `v = p⁻¹ * h₁ * z` with `syllableLength h₁ = 1` and `syllableLength (h * h₁) ≤ 1`. Since
-- `syllableLength v < syllableLength u`, the remaining conjugating word `z` is shorter than
-- `p`, and `v⁻¹ * u * v = z⁻¹ * (h₁⁻¹ * h * h₁) * z` is therefore strictly shorter than `u`.
theorem syllableLength_conj_lt_of_mem_shortSyllableConjugates_of_lt_of_mul_le
    (d : NormalWord.Transversal φ) {u v : PushoutI φ}
    (hu : u ∈ shortSyllableConjugates d)
    (hv : syllableLength d v < syllableLength d u)
    (huv : syllableLength d (u * v) ≤ syllableLength d v) :
    syllableLength d (v⁻¹ * u * v) < syllableLength d u := sorry

end

end Monoid.PushoutI
