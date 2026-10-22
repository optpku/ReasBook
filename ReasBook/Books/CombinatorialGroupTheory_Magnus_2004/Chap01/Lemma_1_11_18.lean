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

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

variable {d : Transversal φ} {A_lt : PushoutI φ → PushoutI φ → Prop}
variable {u a p h q : Fin 2 → PushoutI φ}

/- Layer triage:
- `source-facing`: the two-step Section `11` reduction step with endpoint syllables `u₀`, `u₁`,
  bridge term `a₀`, decompositions `uᵢ = pᵢ⁻¹ * hᵢ * qᵢ`, and the textbook bound by the middle
  product `u₀ * a₀ * u₁`.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
  data `NormalWord.Transversal φ`, the owner length `syllableLength d`, and the Section `11`
  owner predicate `IsSection11ReductionChain`.
- `bridge/view`: the specialization `n = 1` of the non-strict comparison clause already packaged
  by `IsSection11ReductionChain`.

Domain sampling:
1. `Monoid.PushoutI` is the chapter/mathlib owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical chosen normal-form data.
3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner for the Section
   `11` length.
4. `Monoid.PushoutI.IsSection11ReductionChain` from Lemma `1-11-3` is the canonical owner
   abstraction for the two-sided length comparisons in a finite Section `11` reduction chain.

Primitive vs. derived:
the primitive public data are the two-step chain entries `u`, `a`, `p`, `h`, `q`, the source
comparison relation `A_lt`, and the owner predicate `IsSection11ReductionChain d A_lt u a p h q`.
The max-bound on the two endpoint syllable lengths is derived API from that owner predicate, so it
should be stated directly as its `n = 1` consequence rather than through an ad hoc subset `W` and
middle element `g`. -/

/-- Lemma 1-11-18: in the two-step Section `11` reduction-chain situation, the larger of the two
endpoint syllable lengths is bounded by the syllable length of the middle product
`u₀ * a₀ * u₁`. -/
theorem max_syllableLength_le_mul_middle_of_reductionChain
    (hchain : IsSection11ReductionChain d A_lt u a p h q) :
    max (syllableLength d (u 0)) (syllableLength d (u 1)) ≤
      syllableLength d (u 0 * a 0 * u 1) := by
  rcases hchain with ⟨_, _, _, hbound, _, _⟩
  exact max_le_iff.mpr (hbound 0)

end

end Monoid.PushoutI
