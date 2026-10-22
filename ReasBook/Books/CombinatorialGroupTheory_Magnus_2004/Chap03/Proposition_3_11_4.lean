/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_10_4

-- Declarations for this item are recorded in this dedicated item file.

universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: staggered presentations, interval support, and Peiffer reductions of identities
among positive relator conjugates.

Layer triage:
- `source-facing`: a finite formal product of conjugates `u * r * u⁻¹` of relators in a staggered
  presentation, together with the proposition that if the total product only involves special
  generators from an interval `[xₐ, x_b]`, then Peiffer transformations can rewrite the formal
  product so that every relator term itself lies in that interval.
- `core/canonical`: `GroupPresentation.IsStaggeredPresentation` and
  `GroupPresentation.SupportedOnDistinguishedInterval` from Proposition `3-9-5`, the free-group
  list owner `List (FreeGroup X)`, `IsConj` as the owner for conjugacy in the free group, and
  `GroupPresentation.PeifferStep` with its reflexive transitive closure from Proposition `3-10-4`.
- `bridge/view`: the proof-support normal-closure consequence is phrased through the canonical
  owner set `relatorsSupportedOnDistinguishedInterval`, but the main proposition remains
  source-facing over the indexed relator family `r`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` is already the chapter owner for the source phrase
   “`(X; R)` is a staggered presentation, as in (9.5)”.
2. `GroupPresentation.SupportedOnDistinguishedInterval` is the owner for the statement that only
   distinguished generators in `[xₐ, x_b]` occur in a word or relator.
3. `IsConj` is mathlib's canonical owner for “is a conjugate of”, so the source-facing statement
   should quantify only the relator index `j` and assert `IsConj p (r j)` rather than introduce a
   bespoke witness package.
4. `GroupPresentation.PeifferStep` and `Relation.ReflTransGen` are the canonical owners for
   “carried into by Peiffer transformations”.
5. `Subgroup.normalClosure` remains the owner for the ambient relator subgroup consequence that the
   transformed product still lies in the interval-supported normal closure.

Primitive vs. derived:
- primitive data: the indexed relator family `r`, the list `π` of positive relator conjugates, and
  the interval `[xₐ, x_b]`;
- derived API: the termwise list conditions expressed through the list owner `List.Forall`, the
  Peiffer-chain product invariance, and the normal-closure consequence phrased via
  `relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b`.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

open Subgroup

-- Proof sketch: each elementary Peiffer step from Proposition `3-10-4` preserves the list
-- product; compose those equalities along the reflexive-transitive closure.
private theorem prod_eq_of_peifferTransformations
    {π π' : List (FreeGroup X)}
    (h : Relation.ReflTransGen PeifferStep π π') :
    π.prod = π'.prod := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl _ => rfl
  | @single π π' hstep =>
      rcases hstep with hswap | hswap | hdelete | hinsert
      · exact (List.prod_eq_of_isAdjacentConjugatingSwap hswap).symm
      · exact List.prod_eq_of_isAdjacentConjugatingSwap hswap
      · rcases hdelete with ⟨left, right, a, rfl, rfl⟩
        simp [List.prod_append]
      · rcases hinsert with ⟨left, right, a, rfl, rfl⟩
        simp [List.prod_append]
  | @trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem mem_normalClosure_of_intervalSupportedPositiveRelatorConjugate
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X)
    {p : FreeGroup X}
    (hp : ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j)) :
    p ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := by
  let N := normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b)
  rcases hp with ⟨j, hj, hpconj⟩
  have hrj : r j ∈ relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b := by
    exact ⟨⟨j, rfl⟩, hj⟩
  have hrj_mem : r j ∈ N := by
    exact Subgroup.subset_normalClosure hrj
  rcases isConj_iff.mp hpconj with ⟨c, hc⟩
  have hconj : c⁻¹ * r j * c ∈ N := by
    simpa [N, inv_inv] using
      ((Subgroup.normalClosure_normal
        (s := relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b)).conj_mem
          (n := r j) hrj_mem c⁻¹)
  have hp_eq : p = c⁻¹ * r j * c := by
    calc
      p = c⁻¹ * (c * p * c⁻¹) * c := by simp [mul_assoc]
      _ = c⁻¹ * r j * c := by rw [hc]
  simpa [hp_eq] using hconj

-- Proof sketch: each list entry is a conjugate of a relator already belonging to the
-- interval-restricted relator family, hence each term lies in its normal closure; then use
-- subgroup closure under multiplication to conclude that the full list product lies there as well.
private theorem prod_mem_normalClosure_of_intervalSupportedPositiveRelatorConjugates
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X)
    {π : List (FreeGroup X)}
    (hπ : π.Forall
      (fun p ↦ ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j))) :
    π.prod ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := by
  rw [List.forall_iff_forall_mem] at hπ
  induction π with
  | nil =>
      simp
  | cons p π ih =>
      have hp : ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj p (r j) :=
        hπ p (by simp)
      have hπ' :
          ∀ q ∈ π, ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj q (r j) := by
        intro q hq
        exact hπ q (by simp [hq])
      have hp_mem :
          p ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) :=
        mem_normalClosure_of_intervalSupportedPositiveRelatorConjugate X₀ r xₐ x_b hp
      simpa using
        Subgroup.mul_mem
          (normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b))
          hp_mem (ih hπ')

-- Proof sketch: use the interval-control statement from Proposition `3-9-5` on the total product
-- `π.prod`, then apply Peiffer reductions to rewrite the formal product until every relator term
-- itself is supported in `[xₐ, x_b]`. The parenthetical product-preservation claim follows from
-- `prod_eq_of_peifferTransformations`.
/-- Proposition 3-11-4: if `(X₀; r)` is staggered, every term of a formal product `π` is a
positive relator conjugate, and the total product `π.prod` contains distinguished generators only
from the interval `[xₐ, x_b]`, then Peiffer transformations carry `π` to a formal product all of
whose relator terms are supported in that same interval. -/
theorem exists_peiffer_reduction_to_interval_supported_positive_relators
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    (xₐ x_b : X) (π : List (FreeGroup X))
    (hπ : π.Forall (fun p ↦ ∃ j, IsConj p (r j)))
    (hsupp : SupportedOnDistinguishedInterval X₀ xₐ x_b π.prod) :
    ∃ π' : List (FreeGroup X),
      Relation.ReflTransGen PeifferStep π π' ∧
        π'.Forall
          (fun q ↦ ∃ j, SupportedOnDistinguishedInterval X₀ xₐ x_b (r j) ∧ IsConj q (r j)) := sorry

end

end GroupPresentation
