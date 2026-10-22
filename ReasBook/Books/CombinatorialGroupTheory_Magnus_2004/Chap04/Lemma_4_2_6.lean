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
Primary domain: uniqueness of the stable-letter pattern in reduced HNN words.

Layer triage:
- `source-facing`: two reduced words
  `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` and `h₀, t^{δ₁}, h₁, ..., t^{δₘ}, hₘ`
  that represent the same element of the HNN extension.
- `core/canonical`: `ReducedWord G B A` is mathlib's owner abstraction for reduced HNN words in
  the source stable-letter convention.
- `bridge/view`: the sequence of exponents `ε₁, ..., εₙ` is encoded by
  `w.toList.map Prod.fst : List ℤˣ`, while equality of the represented HNN-extension elements is
  expressed by `w.toHNNExtension φ`.

Domain sampling:
1. `ReducedWord G B A` is the canonical owner for reduced HNN words in the source convention.
2. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in the
   original HNN extension.
3. `ReducedWord.map_fst_eq_and_of_prod_eq` is mathlib's canonical uniqueness theorem for the
   stable-letter sign pattern of reduced words with equal product in the swapped convention.

Primitive vs. derived:
- primitive public data: the reduced words `w₁`, `w₂`;
- source hypothesis: equality of their products in the HNN extension;
- source conclusion: equality of the exponent-sign lists, which is exactly the textbook assertion
  that the two words have the same number of stable letters and the same exponents in order.
-/

/-- Lemma 4-2-6: if two reduced HNN words represent the same element, then their stable-letter
exponent lists agree. Equivalently, the two words have the same number of stable letters and the
same exponent `±1` at each position. -/
-- Proof sketch: apply mathlib's canonical reduced-word uniqueness theorem
-- `ReducedWord.map_fst_eq_and_of_prod_eq` to the swapped-convention words after transporting the
-- hypothesis through the injective equivalence `swapEquiv φ`.
theorem reducedWord_exponentList_eq_of_toHNNExtension_eq
    (w₁ w₂ : ReducedWord G B A) (hprod : w₁.toHNNExtension φ = w₂.toHNNExtension φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst := by
  refine (ReducedWord.map_fst_eq_and_of_prod_eq φ.symm ?_).1
  exact (swapEquiv φ).injective hprod

end
