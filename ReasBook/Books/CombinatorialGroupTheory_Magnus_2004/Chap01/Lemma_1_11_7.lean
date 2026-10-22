/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

/- Layer triage:
- `source-facing`: conjugates `u = p⁻¹ * h * p` and `v = q⁻¹ * k * q` of non-base elements from
  factor ranges, their product lying in the Section `11` subset `U`, and the comparison between
  the conjugator lengths.
- `core/canonical`: the amalgamated product owner `PushoutI φ`, the chosen normal-form data
  `NormalWord.Transversal φ`, the derived length `syllableLength d`, the source-facing subset
  `shortSyllableConjugates d`, the amalgamated subgroup `(base φ).range`, and the factor subgroups
  `(of μ).range`.
- `bridge/view`: none. The previous local setup structure duplicated the owner data already carried
  by `PushoutI φ`, so this file now states the textbook lemmas directly over the canonical owner.

Domain sampling:
1. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner API for the
   Section `11` length.
2. `Monoid.PushoutI.shortSyllableConjugates` from Lemma `1-11-14` is the source-facing owner for
   the distinguished subset `U`.
3. `(base φ).range` is the canonical subgroup representing the amalgamated subgroup.
4. `(of μ).range` is the canonical subgroup representing the factor `H_μ`.

Primitive vs. derived:
the primitive public data are the pushout diagram `φ`, the transversal `d`, the two conjugacy
expressions, the factor/base membership hypotheses on `h` and `k`, and the product-length
hypothesis. The rewrite data in conclusions (new middle element, shorter prefix, amalgamated
element) are derived theorem output and therefore belong in direct existential conclusions rather
than in separate public witness structures.
-/

/-- Lemma 1-11-7 (1): if `u = p⁻¹ * h * p` and `v = q⁻¹ * k * q` are conjugates of elements in
factor ranges but outside the amalgamated subgroup, their product lies in the Section `11` subset
`U`, and the conjugators `p` and `q` have the same syllable length, then the two core elements
come from the same factor. -/
-- Proof sketch: compare the terminal segment of `p` with the initial segment of `q`. If the two
-- factor cosets determined by `p` and `q` differ, the normal form of `u * v` stays too long to
-- lie in `shortSyllableConjugates d`. Hence `q` differs from `p` by a base element, so the two
-- middle syllables must consolidate inside one common factor range, forcing the factor indices to
-- agree.
theorem equal_length_conjugates_share_factor_of_product_mem_U
    (d : Transversal φ) {μ ν : ι} {u v h k p q : PushoutI φ}
    (hu : u = p⁻¹ * h * p)
    (hv : v = q⁻¹ * k * q)
    (hhμ : h ∈ (of μ).range) (hhA : h ∉ (base φ).range)
    (hkν : k ∈ (of ν).range) (hkA : k ∉ (base φ).range)
    (huv : u * v ∈ shortSyllableConjugates d)
    (hpq : syllableLength d p = syllableLength d q) :
    μ = ν := sorry

/-- Lemma 1-11-7 (2): under the same equal-length hypotheses, `v` can be rewritten with
conjugator `p`, and the new core element lies in the same factor range as `h` but remains outside
the amalgamated subgroup. -/
-- Proof sketch: the same overlap argument that proves `μ = ν` also shows that `q` differs from
-- `p` by an element of the base subgroup. Transporting `k` across that base element produces a
-- new core element `k₁` in the factor range `(of μ).range`, and the normal-form calculation keeps
-- `k₁` outside `(base φ).range`.
theorem equal_length_conjugates_rewrite_with_same_conjugator_of_product_mem_U
    (d : Transversal φ) {μ ν : ι} {u v h k p q : PushoutI φ}
    (hu : u = p⁻¹ * h * p)
    (hv : v = q⁻¹ * k * q)
    (hhμ : h ∈ (of μ).range) (hhA : h ∉ (base φ).range)
    (hkν : k ∈ (of ν).range) (hkA : k ∉ (base φ).range)
    (huv : u * v ∈ shortSyllableConjugates d)
    (hpq : syllableLength d p = syllableLength d q) :
    ∃ k₁ : PushoutI φ,
      v = p⁻¹ * k₁ * p ∧
        k₁ ∈ (of μ).range ∧
        k₁ ∉ (base φ).range := sorry

/-- Lemma 1-11-7 (3): if `u = p⁻¹ * h * p` and `v = q⁻¹ * k * q` are conjugates of non-base
factor elements, their product lies in the Section `11` subset `U`, and `p` is strictly shorter
than `q`, then `q` has the form `q₁ * p` with `q₁` of positive syllable length, the element `h`
is conjugate by `q₁` to an element of the amalgamated subgroup, and consequently `u` is the
conjugate of that amalgamated element by `q`. -/
-- Proof sketch: if `q` did not end in `p`, then the terminal segment of `p⁻¹` and the initial
-- segment of `q` would survive in the normal form of `u * v`, contradicting
-- `u * v ∈ shortSyllableConjugates d`. Thus `q = q₁ * p` with positive `q₁`-length. Rewriting
-- through this factorization shows that the middle term must consolidate into a base element
-- `b`, giving `h = q₁⁻¹ * b * q₁` and hence `u = q⁻¹ * b * q`.
theorem shorter_conjugator_forces_amalgamated_conjugate_of_product_mem_U
    (d : Transversal φ) {μ ν : ι} {u v h k p q : PushoutI φ}
    (hu : u = p⁻¹ * h * p)
    (hv : v = q⁻¹ * k * q)
    (hhμ : h ∈ (of μ).range) (hhA : h ∉ (base φ).range)
    (hkν : k ∈ (of ν).range) (hkA : k ∉ (base φ).range)
    (huv : u * v ∈ shortSyllableConjugates d)
    (hpq : syllableLength d p < syllableLength d q) :
    ∃ q₁ b : PushoutI φ,
      q = q₁ * p ∧
        1 ≤ syllableLength d q₁ ∧
        h = q₁⁻¹ * b * q₁ ∧
        b ∈ (base φ).range ∧
        u = q⁻¹ * b * q := sorry

end

end Monoid.PushoutI
