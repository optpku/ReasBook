/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_64

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (ofLp toLp)
open scoped BigOperators

section

variable {n : ℕ}

local notation "E₂" => EuclideanSpace ℝ (Fin n)
local notation "E" => WithLp (⊤ : ENNReal) (Fin n → ℝ)
local notation "E*" => WithLp (1 : ENNReal) (Fin n → ℝ)
local notation "coordToLinf" => (fun z : E₂ ↦ toLp (⊤ : ENNReal) (ofLp z))

/- Proposition 10.61 is a `bridge/view` item in the chapter's non-Euclidean duality API. The
Chapter 10 source-facing owner is `Λ[a]` from Lemma 10.61 / Definition 10.64. Domain sampling in
the surrounding `ℓ∞/ℓ¹` pair identifies:
- `lpPairingDual` and `lpPairingDual_apply` from Proposition 1.9 as the canonical owner for the
  coordinate functional represented by an `ℓ¹` vector on `WithLp (⊤ : ENNReal)`;
- `LinearMap.toContinuousLinearMap` as the canonical bridge from that finite-dimensional linear
  functional to the continuous-dual owner used by `Λ[·]`;
- `euclideanSubdifferentialAt` as the Chapter 3 owner on the Euclidean coordinate model, with
  `subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints` and
  `l1CoordinateSubgradientVectors` giving its coordinatewise `ℓ¹` sign-cube companion;
- `primalCounterparts_eq_preimage_subdifferentialAt_norm` from Definition 10.64 as the chapter
  bridge from `Λ[·]` to the canonical subdifferential owner.

The primitive data are only the coefficient vector `a : E*`, so the public statement should stay
on `Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))]` rather than
introducing a second local name for the same functional. The Euclidean point `toLp 2 (ofLp a)` and
the coordinate transport `coordToLinf` are derived bridge data. The first theorem therefore uses
the Chapter 3 owner `euclideanSubdifferentialAt`, and the coordinatewise sign-cube description is
kept as a companion theorem. -/

-- Proof sketch: use `primalCounterparts_eq_preimage_subdifferentialAt_norm` to identify
-- `Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))]` with the
-- subdifferential of the `ℓ¹` norm in the `ℓ∞/ℓ¹` dual pair, then transport that owner set along
-- the canonical `WithLp` equivalence between the Euclidean coordinate model `E₂` and the primal
-- `ℓ∞` model `E`.
/-- Helper for Proposition 10.61: a point of the `ℓ∞` unit ball has all coordinates in
`[-1, 1]`. -/
lemma abs_le_one_of_linf_norm_le_one
    {x : E} (hx : ‖x‖ ≤ 1) :
    ∀ i, |x i| ≤ 1 := by
  -- Rewrite the `WithLp` norm as the ambient sup norm on coordinates.
  have hx' : ‖ofLp x‖ ≤ 1 := by
    simpa using hx
  intro i
  have hcoord_nnnorm : ‖ofLp x i‖₊ ≤ ‖ofLp x‖₊ := by
    rw [Pi.nnnorm_def]
    exact
      @Finset.le_sup NNReal (Fin n) _ _ Finset.univ
        (fun b : Fin n ↦ ‖ofLp x b‖₊) i (Finset.mem_univ i)
  have hcoord : ‖ofLp x i‖ ≤ ‖ofLp x‖ := by
    exact_mod_cast hcoord_nnnorm
  simpa [Real.norm_eq_abs] using hcoord.trans hx'

/-- Helper for Proposition 10.61: coordinatewise bounds by `1` put an `ℓ∞` vector in the unit
ball. -/
lemma linf_norm_le_one_of_abs_le_one
    {x : E} (hx : ∀ i, |x i| ≤ 1) :
    ‖x‖ ≤ 1 := by
  -- Reassemble the sup-norm bound from the coordinate inequalities.
  have hx'_nnnorm : ‖ofLp x‖₊ ≤ 1 := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_le_iff.mpr ?_
    intro i hi
    have hcoord : ‖ofLp x i‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using hx i
    exact_mod_cast hcoord
  have hx' : ‖ofLp x‖ ≤ 1 := by
    exact_mod_cast hx'_nnnorm
  simpa using hx'

/-- Helper for Proposition 10.61: `Real.sign` recovers the absolute value by multiplication. -/
private lemma real_sign_mul_self
    (t : ℝ) :
    Real.sign t * t = |t| := by
  -- Split by the sign of the scalar and reduce to the defining formulas for `Real.sign`.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- Helper for Proposition 10.61: the operator norm of the `ℓ∞/ℓ¹` coordinate pairing equals the
`ℓ¹` norm of its coefficient vector. -/
lemma lpPairingDual_top_norm_eq_l1_norm
    (a : E*) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ = ‖a‖ := by
  -- Proposition 1.9 computes the same norm through the canonical conjugate exponent `1`.
  letI : Fact (1 ≤ (⊤ : ENNReal)) := ⟨by simp⟩
  have htop : ENNReal.conjExponent (⊤ : ENNReal) = 1 := by
    simp [ENNReal.conjExponent]
  have hconj : ‖toLp (ENNReal.conjExponent (⊤ : ENNReal)) (ofLp a)‖ = ‖a‖ := by
    rw [htop]
  simpa [dualNorm] using
    (dualNorm_lpPairingDual_eq_conjExponent_lp_norm (p := (⊤ : ENNReal)) (y := ofLp a)).trans
      hconj

/-- Helper for Proposition 10.61: membership in the transported Euclidean image can be rewritten
using the inverse coordinate transport. -/
lemma mem_image_coordToLinf_iff
    (S : Set E₂) {x : E} :
    x ∈ coordToLinf '' S ↔ toLp 2 (ofLp x) ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa
  · intro hx
    refine ⟨toLp 2 (ofLp x), hx, ?_⟩
    simp

/-- Helper for Proposition 10.61: the Chapter 10 owner `Λ_a` for the `ℓ∞/ℓ¹` pairing is exactly
the coordinatewise sign cube. -/
lemma mem_primalCounterparts_lpPairingDual_top_iff
    (a : E*) {x : E} :
    x ∈ Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] ↔
      (∀ i, a i ≠ 0 → x i = Real.sign (a i)) ∧
        ∀ i, a i = 0 → |x i| ≤ 1 := by
  constructor
  · intro hx
    rcases hx with ⟨hx_norm, hx_pairing⟩
    -- Control every coordinate of `x` by the `ℓ∞` unit-ball hypothesis.
    have hx_coord : ∀ i, |x i| ≤ 1 :=
      abs_le_one_of_linf_norm_le_one hx_norm
    have hsum :
        ∑ i, x i * a i = ∑ i, |a i| := by
      -- Rewrite the attained pairing and the dual norm in explicit coordinate form.
      calc
        ∑ i, x i * a i =
            LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x := by
              simp [lpPairingDual_apply, dotProduct]
        _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ :=
              hx_pairing
        _ = ‖a‖ := lpPairingDual_top_norm_eq_l1_norm a
        _ = ∑ i, |a i| := by
              simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 a)
    have hterm_le : ∀ i, x i * a i ≤ |a i| := by
      intro i
      calc
        x i * a i ≤ |x i * a i| := le_abs_self _
        _ = |x i| * |a i| := by rw [abs_mul]
        _ ≤ 1 * |a i| := mul_le_mul_of_nonneg_right (hx_coord i) (abs_nonneg _)
        _ = |a i| := by ring
    refine ⟨?_, ?_⟩
    · intro i hai
      -- Equality of the total sums forces equality in each nonzero coordinate term.
      have hterm_eq : x i * a i = |a i| := by
        refine le_antisymm (hterm_le i) ?_
        by_contra hlt
        have hsum_lt :
            ∑ j, x j * a j < ∑ j, |a j| := by
          refine Finset.sum_lt_sum (fun j _ ↦ hterm_le j) ?_
          exact ⟨i, Finset.mem_univ i, lt_of_not_ge hlt⟩
        exact hsum_lt.ne hsum
      -- Compare the attained product with the canonical sign identity `sign(a_i) * a_i = |a_i|`.
      exact mul_right_cancel₀ hai (hterm_eq.trans (real_sign_mul_self (a i)).symm)
    · intro i hai
      exact hx_coord i
  · rintro ⟨hsign, hzero⟩
    have hx_coord : ∀ i, |x i| ≤ 1 := by
      intro i
      by_cases hai : a i = 0
      · exact hzero i hai
      · rw [hsign i hai]
        rcases lt_or_gt_of_ne hai with hneg | hpos
        · simp [Real.sign_of_neg hneg]
        · simp [Real.sign_of_pos hpos]
    have hx_norm : ‖x‖ ≤ 1 :=
      linf_norm_le_one_of_abs_le_one hx_coord
    have hx_pairing :
        LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x =
          ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ := by
      -- Evaluate the pairing coordinatewise and substitute the sign constraints.
      calc
        LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x =
            ∑ i, x i * a i := by
              simp [lpPairingDual_apply, dotProduct]
        _ = ∑ i, |a i| := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hai : a i = 0
              · simp [hai]
              · rw [hsign i hai, real_sign_mul_self]
        _ = ‖a‖ := by
              simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 a).symm
        _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ := by
              rw [lpPairingDual_top_norm_eq_l1_norm]
    exact ⟨hx_norm, hx_pairing⟩

/-- Bridge/view form of Proposition 10.61: for a coefficient vector `a` in the `ℓ∞/ℓ¹` coordinate
dual pair, the source set `Λ_a` is the canonical transport of Chapter 3's Euclidean
subdifferential owner for the `ℓ¹` norm from the coordinate model to the primal `ℓ∞` model. -/
theorem primalCounterparts_lpPairingDual_top_eq_image_euclideanSubdifferentialAt_l1
    (a : E*) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] =
      coordToLinf ''
        euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 (ofLp y)‖) (toLp 2 (ofLp a)) := by
  ext z
  -- Compare both sides through the same coordinatewise sign constraints.
  calc
    z ∈ Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] ↔
        (∀ i, a i ≠ 0 → z i = Real.sign (a i)) ∧
          ∀ i, a i = 0 → |z i| ≤ 1 :=
      mem_primalCounterparts_lpPairingDual_top_iff a
    _ ↔ toLp 2 (ofLp z) ∈
        euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 (ofLp y)‖) (toLp 2 (ofLp a)) := by
          simpa using
            (mem_euclideanSubdifferentialAt_l1_norm_iff
              (x := toLp 2 (ofLp a)) (z := toLp 2 (ofLp z))).symm
    _ ↔ z ∈
        coordToLinf ''
          euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 (ofLp y)‖) (toLp 2 (ofLp a)) :=
      (mem_image_coordToLinf_iff
        (euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 (ofLp y)‖) (toLp 2 (ofLp a)))).symm

-- Proof sketch: combine the transported-owner theorem above with
-- `subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. Under the `coordToLinf`
-- transport, Euclidean coordinates are exactly the original `Fin n → ℝ` coordinates, so the
-- right-hand side becomes the familiar coordinatewise sign-cube formula.
/-- Proposition 10.61: after unpacking the transported Chapter 3 owner
`euclideanSubdifferentialAt`, the source set `Λ_a` is the coordinatewise sign cube
`{z : ℝ^n | z_i = sgn(a_i)` on the nonzero coordinates of `a`, and `|z_j| ≤ 1` on the zero
coordinates}. In the textbook nonzero case, this is the usual description of
`∂ h(a)` for `h(x) = ‖x‖₁`. -/
theorem primalCounterparts_lpPairingDual_top_eq_coordinatewise_sign_cube
    (a : E*) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] =
      { z : E |
          (∀ i, a i ≠ 0 → z i = Real.sign (a i)) ∧
            ∀ i, a i = 0 → |z i| ≤ 1 } := by
  ext z
  -- The source owner is already characterized by the coordinatewise sign-cube conditions.
  exact mem_primalCounterparts_lpPairingDual_top_iff a

end
