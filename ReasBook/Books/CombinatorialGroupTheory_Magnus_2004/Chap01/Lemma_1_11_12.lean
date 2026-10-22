/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} [Group G]
variable {I : Type v}

/- Layer triage:
- `source-facing`: the direct Section `11` left-multiplication decomposition theorem over the
  amalgamated product owner.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
  data `NormalWord.Transversal φ`, the length `syllableLength d`, and the factor/base ranges
  `(of ν).range` and `(base φ).range`.
- `bridge/view`: none. The target lemma is already stated directly over `Monoid.PushoutI`.

Domain sampling:
1. `Monoid.PushoutI.exists_left_mul_decomposition_of_eq_inv_mul_of_factor_or_one` is the direct
   owner theorem for the left-multiplication step.
2. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner length API.
3. `(Monoid.PushoutI.of ν).range` and `(Monoid.PushoutI.base φ).range` are the canonical factor
   and amalgamated subgroup owners used inside the theorem statement.

Primitive vs. derived:
the primitive data are the Section `11` bridge-step hypothesis on `g`, the balanced decomposition
`v = r⁻¹ * k * s`, and the source condition on `k`. The new factors for `g * v`, the preserved
syllable length, and the same-factor alternative are derived theorem output, so this file recalls
the direct owner theorem instead of adding any local wrapper. -/

/- Lemma 1-11-12: Section `11`'s left-multiplication step is already encoded directly by the
owner theorem on `Monoid.PushoutI`. -/
#check Monoid.PushoutI.exists_left_mul_decomposition_of_eq_inv_mul_of_factor_or_one

end
