/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups
open CongruenceSubgroup
open ConjAct

set_option autoImplicit false

section

/-!
Primary domain: special linear groups over localizations of `ℤ` and Bass-Serre amalgams.

Layer triage:
- `source-facing`: the congruence subgroup `Γ₀(p) ≤ SL(2, ℤ)`, the two adjacent-vertex
  stabilizers inside `SL(2, ℤ[1/p])`, and the claim that `SL(2, ℤ[1/p])` is their amalgamated
  free product over the common edge stabilizer.
- `core/canonical`: `SL(2, ℤ)`, `Gamma0 p`, `SL(2, Localization.Away (p : ℤ))`, `Subgroup`, and
  the chapter owner API `Subgroup.amalgamatedProductComparison`.
- `bridge/view`: the integral copy of `SL(2, ℤ)` inside the localization, the diagonal element
  `diag(1, p)` in the ambient general linear group, the induced conjugation of
  `SL(2, ℤ[1/p])`, and the resulting ambient image of `Γ₀(p)`.

Domain sampling:
1. `SL(2, R)` from `Matrix.SpecialLinearGroup` is the canonical owner for determinant-one `2 × 2`
   matrices over a commutative ring `R`.
2. `Gamma0 p` from mathlib is the canonical owner for the subgroup of `SL(2, ℤ)` cut out by the
   condition that the lower-left entry is `0 mod p`.
3. `Localization.Away (p : ℤ)` is the canonical localization model for the source ring `ℤ[1/p]`.
4. `ConjAct.toConjAct` is the canonical owner for conjugation by an ambient invertible element,
   so the adjacent vertex stabilizer should be expressed as the `diag(1, p)`-conjugate of the
   integral stabilizer rather than via an entrywise duplicate embedding.
5. `Subgroup.map` and `Subgroup.range` are the canonical subgroup owners for the integral vertex
  stabilizer, its `diag(1, p)`-conjugate, and the ambient image of `Γ₀(p)`.
6. Proposition `3-12-5` already exposes `Subgroup.amalgamatedProduct` and
   `Subgroup.amalgamatedProductComparison` as the chapter owner API for a two-factor amalgam.

Primitive vs. derived:
- primitive public data: the canonical congruence subgroup `Gamma0 p ≤ SL(2, ℤ)`;
- derived API: the integral vertex stabilizer, its `diag(1, p)`-conjugate adjacent stabilizer,
  the ambient image of `Gamma0 p`, its distinct conjugate copy inside the adjacent vertex
  stabilizer, the identification of the integral copy with the subgroup intersection, and the
  canonical amalgamated-product comparison map supplied by Proposition `3-12-5`.
-/

/-- The integral vertex stabilizer inside `SL(2, ℤ[1/p])`. -/
private noncomputable def integralSpecialLinearEmbedding (p : ℕ) :
    SL(2, ℤ) →* SL(2, Localization.Away (p : ℤ)) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (Localization.Away (p : ℤ)))

/-- The diagonal element `diag(1, p)` in `GL(2, ℤ[1/p])`. -/
private noncomputable def diagonalPrimeGeneralLinear (p : ℕ) :
    GL (Fin 2) (Localization.Away (p : ℤ)) := by
  refine Matrix.GeneralLinearGroup.mk''
    !![1, 0; 0, (algebraMap ℤ (Localization.Away (p : ℤ))) (p : ℤ)] ?_
  have hp : IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) (p : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit (p : ℤ)
  simpa [Matrix.det_fin_two] using hp

/-- Conjugation on `SL(2, ℤ[1/p])` by the diagonal element `diag(1, p)`. -/
private noncomputable def diagonalPrimeConjugation (p : ℕ) :
    SL(2, Localization.Away (p : ℤ)) →* SL(2, Localization.Away (p : ℤ)) where
  toFun g := by
    let δ : GL (Fin 2) (Localization.Away (p : ℤ)) := diagonalPrimeGeneralLinear p
    refine ⟨(toConjAct δ) •
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))), ?_⟩
    change Matrix.det (((δ : GL (Fin 2) (Localization.Away (p : ℤ))) :
        Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))) *
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))) *
      (((δ : GL (Fin 2) (Localization.Away (p : ℤ)))⁻¹ :
        GL (Fin 2) (Localization.Away (p : ℤ))) :
        Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ)))) = 1
    simpa [δ] using (Matrix.det_units_conj δ
      (g : Matrix (Fin 2) (Fin 2) (Localization.Away (p : ℤ))))
  map_one' := by
    ext i j
    simp
  map_mul' g h := by
    ext i j
    simp

/-- The integral copy of `SL(2, ℤ)` inside `SL(2, ℤ[1/p])`. -/
noncomputable def integralSpecialLinearSubgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  (integralSpecialLinearEmbedding p).range

/-- The adjacent copy of `SL(2, ℤ)` inside `SL(2, ℤ[1/p])`, obtained from the integral copy by
conjugation with `diag(1, p)`. -/
noncomputable def adjacentSpecialLinearSubgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  Subgroup.map (diagonalPrimeConjugation p) (integralSpecialLinearSubgroup p)

/-- The ambient copy of `Γ₀(p)` inside `SL(2, ℤ[1/p])`. -/
noncomputable def gamma0Subgroup (p : ℕ) :
    Subgroup (SL(2, Localization.Away (p : ℤ))) :=
  Subgroup.map (integralSpecialLinearEmbedding p) (Gamma0 p)

/-- The ambient image of `Γ₀(p)` is the common edge stabilizer, namely the intersection of the
two adjacent vertex stabilizers. -/
theorem gamma0Subgroup_eq_inf (p : ℕ) :
    gamma0Subgroup p =
      integralSpecialLinearSubgroup p ⊓ adjacentSpecialLinearSubgroup p := by
  sorry

/-- Bridge theorem: the chapter-owner comparison map for the intersection-based amalgam of the two
adjacent vertex stabilizers is bijective. The source-facing edge subgroup remains
`gamma0Subgroup p`, identified with the intersection by `gamma0Subgroup_eq_inf p`. -/
-- Proof sketch: let `SL(2, Localization.Away (p : ℤ))` act on the Behr tree for the prime `p`.
-- The stabilizers of two adjacent vertices are the integral copy and the `diag(1, p)`-conjugate
-- copy of `SL(2, ℤ)`, and their common edge stabilizer is the ambient subgroup
-- `gamma0Subgroup p`, identified with the subgroup intersection by `gamma0Subgroup_eq_inf p`.
-- The quotient graph is a single edge. Bass-Serre theory then identifies the ambient group with
-- the pushout of those two vertex stabilizers over that edge stabilizer.
private theorem integralAdjacentSpecialLinearSubgroup_amalgamatedProductComparison_bijective
    (p : ℕ) (hp : p.Prime) :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (integralSpecialLinearSubgroup p)
        (adjacentSpecialLinearSubgroup p)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  sorry

/-- Proposition 3-13-7: the canonical comparison map from the source-facing pushout of the two
adjacent copies of `SL(2, ℤ)` in `SL(2, ℤ[1/p])` onto `SL(2, ℤ[1/p])` is bijective. The
source-facing subgroup `gamma0Subgroup p` coming from `Γ₀(p)` is the common edge stabilizer,
identified with the intersection used by the chapter owner API via `gamma0Subgroup_eq_inf p`. -/
theorem specialLinearGroup_away_prime_is_amalgamatedProduct_of_Gamma0
    (p : ℕ) (hp : p.Prime) :
    Function.Bijective
      (Subgroup.amalgamatedProductComparison
        (integralSpecialLinearSubgroup p)
        (adjacentSpecialLinearSubgroup p)) := by
  exact
    integralAdjacentSpecialLinearSubgroup_amalgamatedProductComparison_bijective p hp

end
