/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_11_2
import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

/- Layer triage:
- `source-facing`: the Section `11` decomposition step inside the amalgamated product
  `PushoutI φ`, with a chosen transversal `d`, the chapter length `syllableLength d`, the factor
  subgroups `(of ν).range`, and the amalgamated subgroup `(base φ).range`.
- `core/canonical`: `Monoid.PushoutI`, `NormalWord.Transversal φ`, `syllableLength d`,
  `(of ν).range`, and `(base φ).range`.
- `bridge/view`: none. Lemma `1-11-4` already states the textbook left-multiplication theorem
  directly over the canonical owner.

Domain sampling:
1. `Monoid.PushoutI` is the owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical owner for the chosen normal-form
   data.
3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner for the
   Section `11` length.
4. `(Monoid.PushoutI.of ν).range` and `(Monoid.PushoutI.base φ).range` are the canonical factor
   and amalgamated subgroup realizations inside `PushoutI φ`.

Primitive vs. derived:
the primitive public data are the chosen transversal `d`, the element identity
`v = r⁻¹ * k * s`, the balanced-length condition on `r` and `s`, the source hypothesis that `k`
either lies in one factor range outside the base subgroup or is trivial, and the Section `11`
bridge-step hypothesis on `g`. The new decomposition data for `g * v` are derived theorem output,
so they are already exposed directly by the owner theorem from Lemma `1-11-4`.
-/

/- Lemma 1-11-13 adds no new API beyond the owner theorem from Lemma `1-11-4`, so this file keeps
only a direct recall of that theorem. -/
#check Monoid.PushoutI.exists_left_mul_decomposition_of_eq_inv_mul_of_factor_or_one

end

end Monoid.PushoutI
