/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord
open HNNExtension.NormalWord.ReducedWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: HNN extensions and Britton's lemma.

Layer triage:
- `source-facing`: a reduced sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with `n ≥ 1`, viewed as a
  reduced word in the HNN extension.
- `core/canonical`: `ReducedWord G B A` is mathlib's owner abstraction for reduced words in the
  source stable-letter convention, and
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` is Britton's lemma for that owner.
- `bridge/view`: the textbook integer `n` counting occurrences of the stable letter is the length
  of `w.toList`, while `w.toHNNExtension φ` evaluates the source word in the original HNN
  extension `HNNExtension G A B φ`.

Domain sampling:
1. `ReducedWord G B A` is the canonical reduced-word owner for the source stable-letter
   convention.
2. `HNNExtension.swapEquiv φ` is the canonical stable-letter inversion equivalence between the two
   HNN-extension conventions.
3. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in the
   original HNN extension.
4. `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` is the owner Britton theorem asserting
   that a reduced word whose product lies in the embedded base group has no stable letters.

Primitive vs. derived:
- primitive public data: the reduced word `w : ReducedWord G B A`;
- derived source hypothesis: `w.toList ≠ []`, encoding that the reduced sequence has at least one
  stable-letter syllable;
- derived conclusion: `w.toHNNExtension φ ≠ 1`, the thin source-facing contrapositive of Britton's
  lemma transported through `swapEquiv`.
-/

/-- Lemma 4-2-2: if a reduced HNN word has at least one stable-letter syllable, then its product
in the HNN extension is not the identity. Equivalently, a reduced sequence
`g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with `n ≥ 1` does not represent `1`. -/
theorem reducedWord_toHNNExtension_ne_one_of_toList_ne_nil
    (w : ReducedWord G B A) (hw : w.toList ≠ []) :
    w.toHNNExtension φ ≠ 1 := by
  intro h
  have hprod : w.prod φ.symm = 1 := by
    apply (swapEquiv φ).injective
    simpa [toHNNExtension] using h
  have hrange : w.prod φ.symm ∈ (of.range : Subgroup (HNNExtension G B A φ.symm)) :=
    ⟨1, by simpa using hprod.symm⟩
  exact hw (HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ.symm w hrange)

end
