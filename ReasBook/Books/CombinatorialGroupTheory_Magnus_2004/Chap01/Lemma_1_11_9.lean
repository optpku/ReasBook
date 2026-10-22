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
- `source-facing`: conjugates `u = p⁻¹ * h * p` and `v = q⁻¹ * k * q` of non-base elements from
  factor ranges, the Section `11` subset `U`, and the shortening inequality on the conjugate
  `v⁻¹ * u * v`.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
  data `NormalWord.Transversal φ`, the derived length `syllableLength d`, the source-facing
  subset `shortSyllableConjugates d`, the amalgamated subgroup `(base φ).range`, and the factor
  subgroups `(of i).range`.
- `bridge/view`: the textbook subset `U` is the established chapter owner
  `shortSyllableConjugates d`, and the source conjugates are already expressed canonically by the
  ambient group terms `p⁻¹ * h * p` and `q⁻¹ * k * q`.

Domain sampling:
1. `Monoid.PushoutI` is the owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` and `Monoid.PushoutI.syllableLength` from
   Definition `1-11-2` are the chapter owner APIs for the chosen normal forms and their length.
3. `Monoid.PushoutI.shortSyllableConjugates` from Definition `1-11-2` is the upstream owner for
   the source subset `U`.
4. `(base φ).range` and `(of i).range` are the canonical owner subgroups for the amalgamated
   subgroup and the factors.

Primitive vs. derived:
the primitive source data are the pushout diagram `φ`, the transversal `d`, the explicit
conjugacy witnesses `hu` and `hv`, and the owner-level factor-membership and base-exclusion
hypotheses on `h` and `k`.
The “second alternative” is derived theorem output, so it should be stated directly as the three
resulting inequalities/equality rather than packaged into a parallel witness structure.
-/

-- Proof sketch: if `u * v` is not already in `shortSyllableConjugates d`, then the overlap
-- analysis for normal forms in Section `11` forces the conjugating word `q` for `v` to be
-- strictly shorter than the conjugating word `p` for `u`. The same reduction rewrites the
-- conjugate `v⁻¹ * u * v` as the conjugate of `h` by the canonical new conjugator `p * v`,
-- whose syllable length is at most that of `p`.
/-- Lemma 1-11-9: if `u = p⁻¹ * h * p` and `v = q⁻¹ * k * q` are conjugates of elements from
factor ranges but outside the amalgamated subgroup, and conjugation of `u` by `v` does not
increase syllable length, then either `u * v` lies in the Section `11` subset `U`, or `q` is
shorter than `p` and `v⁻¹ * u * v` is the conjugate of `h` by `p * v`, whose length is at most
that of `p`. -/
theorem mul_mem_U_or_conjugate_with_shorter_conjugator_of_conjugate_length_le
    (d : Transversal φ) {u v h k p q : PushoutI φ}
    (hu : u = p⁻¹ * h * p)
    (hv : v = q⁻¹ * k * q)
    (hh : ∃ μ : ι, h ∈ (of μ).range) (hhA : h ∉ (base φ).range)
    (hk : ∃ ν : ι, k ∈ (of ν).range) (hkA : k ∉ (base φ).range)
    (hshort : syllableLength d (v⁻¹ * u * v) ≤ syllableLength d u) :
    u * v ∈ shortSyllableConjugates d ∨
      syllableLength d q < syllableLength d p ∧
        syllableLength d (p * v) ≤ syllableLength d p ∧
        v⁻¹ * u * v = (p * v)⁻¹ * h * (p * v) := sorry

end

end Monoid.PushoutI
