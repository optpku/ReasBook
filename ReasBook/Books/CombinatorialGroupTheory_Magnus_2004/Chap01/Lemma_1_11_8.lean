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

open NormalWord

/- Layer triage:
- `source-facing`: an element `u = p⁻¹ * h * p`, a base element `a : H`, the condition
  `syllableLength d h = 1`, and the source subset membership
  `u * base φ a ∈ shortSyllableConjugates d`.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form data
  `NormalWord.Transversal φ`, the derived owner length `syllableLength d`, the amalgamated
  subgroup `(base φ).range`, and the distinguished subset `shortSyllableConjugates d`.
- `bridge/view`: the source clause "`a ∈ A`" is represented primitively by an element `a : H`,
  while the conclusion "`a^p ∈ A`" is expressed owner-level as membership of the pointwise
  conjugate `p⁻¹ * base φ a * p` in `(base φ).range`.

Domain sampling:
1. `Monoid.PushoutI.base` from mathlib is the owner map for the amalgamated subgroup inside the
   pushout.
2. `Monoid.PushoutI.NormalWord.Transversal` from mathlib is the canonical chosen normal-form data.
3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner declaration for
   the Section `11` length.
4. `Monoid.PushoutI.shortSyllableConjugates` from Definition `1-11-2` is the chapter owner for
   the distinguished subset `U`, while the pointwise source conjugate `a^p = p⁻¹ * a * p` is
   already the native group expression and does not need an extra wrapper.

Primitive vs. derived:
the primitive public data are the pushout diagram `φ`, the transversal `d`, the conjugacy datum
`u = p⁻¹ * h * p`, the base element `a : H`, and the two source hypotheses on `h` and
`u * base φ a`. The conclusion that the conjugate of `base φ a` lies in the amalgamated subgroup
is derived owner-level membership, so the theorem exposes subgroup membership directly.
-/

/-- Lemma 1-11-8: if `u = p⁻¹ * h * p`, if `|h| = 1`, and if `u * a` belongs to the Section `11`
subset `U`, then the conjugate `a^p` lies in the amalgamated subgroup `A`.

Here the canonical owner translation is:
- `|.| = syllableLength d`,
- `A = (base φ).range`,
- `U = shortSyllableConjugates d`,
- `a ∈ A` is represented primitively by `a : H`,
- `a^p = p⁻¹ * a * p` is represented directly by the ambient group product. -/
-- Proof sketch: rewrite `u * base φ a` as `p⁻¹ * (h * (p⁻¹ * base φ a * p)) * p` using
-- `u = p⁻¹ * h * p`. Since `syllableLength d h = 1`, the normal-form criterion defining
-- `shortSyllableConjugates d` forces the middle factor `h * (p⁻¹ * base φ a * p)` to represent
-- the same short syllable, so the textbook conjugate `a^p = p⁻¹ * a * p` lies in
-- `(base φ).range`.
theorem conjugate_base_mem_base_range_of_mul_mem_shortSyllableConjugates
    (d : Transversal φ) {u h p : PushoutI φ} (a : H)
    (hu : u = p⁻¹ * h * p) (hh : syllableLength d h = 1)
    (hua : u * base φ a ∈ shortSyllableConjugates d) :
    p⁻¹ * base φ a * p ∈ (base φ).range := sorry

end

end Monoid.PushoutI
