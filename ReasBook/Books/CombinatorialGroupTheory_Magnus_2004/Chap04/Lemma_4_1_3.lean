/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Monoid.Coprod
open Monoid.Coprod

universe u v

set_option autoImplicit false

/-!
Primary domain: free products of groups and their canonical factor subgroups.

Layer triage:
- `source-facing`: the free product `A ∗ B`, its two canonical factor subgroups, and the textbook
  claims that the free product depends only on the factor groups and contains isomorphic copies of
  the factors generating the whole group with trivial intersection.
- `core/canonical`: `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner for the free
  product, `MulEquiv.coprodCongr` is the canonical invariance theorem under factor isomorphisms,
  and the canonical injections `inl`, `inr` together with `MonoidHom.ofInjective` and
  `range_inl_sup_range_inr` give the range-level factor API.
- `bridge/view`: the subgroup-valued view of the two factors inside `A ∗ B` is obtained by passing
  from the canonical injections to their ranges.

Domain sampling:
1. `Monoid.Coprod` is the canonical free-product owner abstraction in mathlib.
2. `MulEquiv.coprodCongr` is the canonical statement that free products are preserved by
   equivalences of factors.
3. `MonoidHom.ofInjective` is the canonical equivalence from a group to the range of an
   injective homomorphism; the canonical projections prove injectivity here.
4. `Monoid.Coprod.range_inl_sup_range_inr` is the canonical generation statement for the two
   factor ranges inside a free product.

Primitive vs. derived:
- primitive public data: the factor groups `A`, `B`, the free product `A ∗ B`, and the canonical
  injections of the two factors;
- derived API: the factor ranges `(inl : A →* A ∗ B).range` and `(inr : B →* A ∗ B)`, the induced
  equivalences from `A` and `B` onto those ranges via the canonical projections `fst` and `snd`,
  and the facts that these subgroups generate the free product and intersect trivially.
-/

/- Lemma 4-1-3: the free product is uniquely determined by the factor groups, via the canonical
equivalence `MulEquiv.coprodCongr` induced from equivalences of the two factors. -/
#check MulEquiv.coprodCongr

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

/- Lemma 4-1-3 (1): the canonical left factor subgroup of `A ∗ B` is isomorphic to `A`. -/
#check (MonoidHom.ofInjective
  (show Function.LeftInverse (fst : A ∗ B →* A) (inl : A →* A ∗ B) from
      fst_apply_inl).injective :
    A ≃* (inl : A →* A ∗ B).range)

/- Lemma 4-1-3 (2): the canonical right factor subgroup of `A ∗ B` is isomorphic to `B`. -/
#check (MonoidHom.ofInjective
  (show Function.LeftInverse (snd : A ∗ B →* B) (inr : B →* A ∗ B) from
      snd_apply_inr).injective :
    B ≃* (inr : B →* A ∗ B).range)

/-- Lemma 4-1-3 (3): the canonical left and right factor subgroups generate the free product
`A ∗ B`. -/
theorem leftFreeProductFactor_sup_rightFreeProductFactor :
    (inl : A →* A ∗ B).range ⊔ (inr : B →* A ∗ B).range = ⊤ := by
  exact
    (range_inl_sup_range_inr : (inl : A →* A ∗ B).range ⊔ (inr : B →* A ∗ B).range = ⊤)

/-- Lemma 4-1-3 (4): the canonical left and right factor subgroups of `A ∗ B` intersect
trivially. -/
theorem leftFreeProductFactor_disjoint_rightFreeProductFactor :
    Disjoint ((inl : A →* A ∗ B).range) ((inr : B →* A ∗ B).range) := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have ha : a = 1 := by
    simpa using congrArg fst hb.symm
  simp [ha]

end
