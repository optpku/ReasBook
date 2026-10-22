/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

open Monoid
open NormalWord

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

/- Layer triage:
- `source-facing`: the Section `11` bridge-step product `g * v`, where `g` is a bridge word as in
  Lemma `1-11-3`, and `v = r⁻¹ * k * s` is a balanced decomposition with the middle term `k`
  either lying in one factor subgroup outside the amalgamated subgroup or equaling `1`.
- `core/canonical`: `Monoid.PushoutI φ`, `NormalWord.Transversal φ`, `syllableLength d`,
  `(of ν).range`, `(base φ).range`, and the upstream owner predicate
  `IsSection11BridgeStep d v g`.
- `bridge/view`: none. The source lemma is already a direct theorem about the canonical owner
  `PushoutI φ`, and the bridge-word hypotheses are already packaged canonically by
  `IsSection11BridgeStep`, so this file should reuse that owner predicate instead of restating the
  bridge data entrywise.

Domain sampling:
1. `Monoid.PushoutI` is the chapter/mathlib owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical owner for the chosen normal-form
   data used throughout Section `11`.
3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner for the
   textbook length notation.
4. `Monoid.PushoutI.IsSection11BridgeStep` from Lemma `1-11-3` is the owner abstraction for the
   bridge word `g = g₁ ... gₙ` together with the source hypotheses `|gⱼ| ≤ |v|` and
   `|gⱼ ... gₙ v| = |v|`.
5. `(Monoid.PushoutI.of ν).range` and `(Monoid.PushoutI.base φ).range` are the canonical factor
   and amalgamated subgroup realizations, so the source condition on `k` should be recorded
   directly with those owner objects rather than through a generic family `H` and subset `A`.

Primitive vs. derived:
the primitive public data are the bridge-step hypothesis on `g`, the balanced decomposition of
`v`, and the source condition on the middle factor `k`. The new left factor `r'`, middle factor
`k'`, the preserved syllable length, and the common-factor/trivial alternative are derived theorem
output, so they belong directly in the theorem conclusion rather than in a public packaging layer.
-/

-- Proof sketch: the source lemma applies only to a bridge word `g` satisfying the owner predicate
-- `IsSection11BridgeStep d v g`, which packages the hypotheses `|gⱼ| ≤ |v|` and
-- `|gⱼ ... gₙ v| = |v|` for the successive bridge factors. Comparing the normal forms of `g` and
-- `r⁻¹`, either no new cancellation occurs, so the left factor stays `r`, or one cancellation
-- shifts it to `r * g⁻¹`. The Section `11` normal-form analysis preserves the factor supporting
-- the middle term unless the middle term is trivial, and the syllable length of the left factor
-- is unchanged.
/-- Lemma 1-11-4: if `g` is a Section `11` bridge step for `v`, and
`v = r⁻¹ * k * s` is a balanced decomposition with `k` either in one factor range outside the
amalgamated subgroup or equal to `1`, then `g * v` admits a decomposition with the same right
factor `s`, the left factor either unchanged or shifted to `r * g⁻¹`, the same syllable length as
`r`, and the middle term staying in the same factor subgroup outside the amalgamated subgroup
unless both middle terms are trivial. -/
theorem exists_left_mul_decomposition_of_eq_inv_mul_of_factor_or_one
    (d : Transversal φ) {g v r k s : PushoutI φ}
    (hg : IsSection11BridgeStep d v g)
    (hv : v = r⁻¹ * k * s)
    (hrs : syllableLength d r = syllableLength d s)
    (hk : (∃ ν : ι, k ∈ (of ν).range ∧ k ∉ (base φ).range) ∨ k = 1) :
    ∃ r' k' : PushoutI φ,
      g * v = r'⁻¹ * k' * s ∧
        (r' = r ∨ r' = r * g⁻¹) ∧
        syllableLength d r' = syllableLength d r ∧
        ((∃ ν : ι,
            (k ∈ (of ν).range ∧ k ∉ (base φ).range) ∧
              k' ∈ (of ν).range ∧
              k' ∉ (base φ).range) ∨
          (k = 1 ∧ k' = 1)) := by
  sorry

end

end Monoid.PushoutI
