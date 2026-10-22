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

/- Layer triage:
- `source-facing`: the two-step Section `11` reduction step with syllables `u₀`, `u₁`, bridge
  data `a`, decompositions `uᵢ = pᵢ⁻¹ * hᵢ * qᵢ`, and the source comparison `A p₀ < A q₀`.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
  data `NormalWord.Transversal φ`, the chapter length `syllableLength d`, and the Section `11`
  owner predicates `IsSection11BridgeStep` and `IsSection11ReductionChain`.
- `bridge/view`: the specialization `n = 1` of the general reduction-chain API from
  Lemma `1-11-3`.

Domain sampling:
1. `Monoid.PushoutI` is the chapter/mathlib owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner for the Section
   `11` length notation.
3. `Monoid.PushoutI.IsSection11BridgeStep` from Lemma `1-11-3` is the canonical owner predicate
   for the bridge between adjacent Section `11` syllables.
4. `Monoid.PushoutI.IsSection11ReductionChain` from Lemma `1-11-3` is the canonical owner
   predicate for the full finite reduction chain, and its forward-comparison clause already
   packages the strict inequality proved in this two-step case.

Primitive vs. derived:
the primitive public data here are the chain entries `u`, `a`, `p`, `h`, `q`, together with the
source comparison relation `A_lt` and the canonical reduction-chain predicate relating them. The
strict inequality for the right syllable is derived from that owner predicate and should not be
repackaged through a chosen bridge list or an auxiliary preorder-valued key. -/

/-- Lemma 1-11-19: in the two-step Section `11` reduction-chain situation, if the left
decomposition satisfies `A p < A q`, then the right syllable is strictly shorter than the middle
product `u₀ * a₀ * u₁`. -/
theorem syllableLength_right_lt_mul_middle_of_A_lt
    (d : Transversal φ) (A_lt : PushoutI φ → PushoutI φ → Prop)
    (u a p h q : Fin 2 → PushoutI φ)
    (hchain : IsSection11ReductionChain d A_lt u a p h q)
    (hpq : A_lt (p 0) (q 0)) :
    syllableLength d (u 1) < syllableLength d (u 0 * a 0 * u 1) := by
  rcases hchain with ⟨_, _, _, _, hforward, _⟩
  simpa using hforward 0 hpq

end

end Monoid.PushoutI
