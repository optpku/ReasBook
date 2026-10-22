/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension

section

private def unitsIntEquivBool : ℤˣ ≃ Bool where
  toFun u := decide (u = 1)
  invFun b := if b then 1 else -1
  left_inv u := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  right_inv b := by
    cases b <;> simp

local instance corollary_4_2_5_primcodableUnitsInt : Primcodable ℤˣ :=
  Primcodable.ofEquiv Bool unitsIntEquivBool

/-!
Primary domain: algorithmic solvability of the word problem for HNN extensions.

Layer triage:
- `source-facing`: the base group `G`, the associated subgroups `A`, `B`, the subgroup-membership
  problems for `A` and `B`, the computable group isomorphism `φ : A ≃* B`, and the word problem
  on finite HNN input words `g₀, t^{ε₁} g₁, ..., t^{εₙ} gₙ`, encoded by `ℤˣ`-signed syllables.
- `core/canonical`: `HNNExtension G A B φ` is mathlib's owner for the HNN extension,
  `HNNExtension.NormalWord.ReducedWord G B A` is the chapter's canonical owner for reduced HNN
  words in the source convention, `Equiv.Computable` is the canonical owner for an effectively
  calculable equivalence, and `ComputablePred` is the canonical owner for algorithmic predicates on
  coded inputs.
- `bridge/view`: the source raw HNN word problem is stated directly as the canonical predicate
  `ComputablePred` on `G × List (ℤˣ × G)`, while the auxiliary computability coding of `ℤˣ` is
  supplied internally through the equivalence with `Bool`, and Britton reduction passes internally
  through the canonical reduced-word owner.

Domain sampling:
1. `HNNExtension G A B φ` is mathlib's canonical owner abstraction for the source HNN extension.
2. `HNNExtension.NormalWord.ReducedWord G B A` is the chapter's canonical owner abstraction for
   reduced HNN words in the source stable-letter convention.
3. `ReducedWord.prod φ.symm` and its transported source-facing variant are the canonical evaluation
   maps from normal-form words to the HNN extension.
4. `ComputablePred fun g : G ↦ g = 1` and `ComputablePred fun g : G ↦ g ∈ H` are the canonical
   computability owners for the ordinary and generalized word problems in the base group.
5. `φ.toEquiv.Computable` is the canonical way to express that both `φ` and `φ⁻¹` are effectively
   calculable.

Primitive vs. derived:
- primitive source data: the group `G`, the subgroups `A`, `B`, the isomorphism `φ`,
  computable triviality in `G`, computable membership in `A` and `B`, and computability of the
  equivalence `φ`;
- derived API: the direct `ComputablePred` on raw HNN words, whose inputs are raw HNN words rather
  than coded quotient elements.
-/

variable {G : Type u} [Group G] [Primcodable G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "t" => (HNNExtension.t : E)

/-- Corollary 4-2-5: if the base group `G` has solvable word problem, the generalized word
problems for `A` and `B` are solvable in `G`, and the subgroup isomorphism `φ : A ≃* B` is
effectively calculable, then the HNN extension has solvable word problem. The conclusion is stated
on raw HNN input words, while Britton reduction through reduced words is a derived internal step.
-/
-- Proof sketch: reduce an arbitrary HNN input word to Britton normal form by using the word
-- problem in `G`, the membership tests for `A` and `B`, and the computable equivalence `φ` to
-- detect and cancel pinches. The normal-form theorem from Theorem `4-2-4` then shows that the
-- resulting reduced word represents the identity exactly when no stable-letter syllables remain
-- and the residual base-group element is trivial in `G`.
theorem hnnExtension_hasSolvableWordProblem
    [Primcodable A] [Primcodable B]
    (hG : ComputablePred fun g : G ↦ g = 1)
    (hA : ComputablePred fun g : G ↦ g ∈ A)
    (hB : ComputablePred fun g : G ↦ g ∈ B)
    (hφ : φ.toEquiv.Computable) :
    ComputablePred fun w : G × List (ℤˣ × G) ↦
      of w.1 * (w.2.map fun x ↦ t ^ (x.1 : ℤ) * of x.2).prod = 1 := sorry

end
